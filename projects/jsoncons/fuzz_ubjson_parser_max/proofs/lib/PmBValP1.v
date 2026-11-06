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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bvlE00 LibSegJb_bvlE01 LibSegJb_bvlEn LibSegJb_bvlHf LibSegJb_bvlHs LibSegJb_bvlSZ LibSegJb_bvlSP1 LibSegJb_bvlSP2 LibSegJb_bvlSP3 LibSegJb_bvlSP4 LibSegJb_bvlSP5 LibSegJb_bvlSP6 LibSegJb_bvlSP7 LibSegJb_bvlT0 LibSegJb_bvlT1a LibSegJb_bvlT1b LibSegJb_bvlT2a LibSegJb_bvlT2b LibSegJb_bvlT3a LibSegJb_bvlT3b LibSegJb_bvlTbig LibSegJb_bvlL LibSegJb_bvlB LibSegJb_bvlX.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBVALP1.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bvlE00 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlE00.regs0 LibSegJb_bvlE00.regs_out0).
Lemma KS_bvlE00_ok : BG.kept_ok 60 LibSegJb_bvlE00.regs0 LibSegJb_bvlE00.regs_out0 KS_bvlE00 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bvlE00_conc_s := ",<A#v2p#2#40A#v21p#2#40S,2v2S,:v21S,;#O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801070v2#800000000000Hv2#10I_v2#70#70B#v21#,1_v2#68#68,1,13X#;11<8#;1574Y,T,2_v2#70T,<#1T,=#T,>#1Lb_v2#68r1;Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bvlE00_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlE00] fx R M V bvlE00_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlE00] LibSegJb_bvlE00.regs0 LibSegJb_bvlE00.kn0 LibSegJb_bvlE00.BR LibSegJb_bvlE00.PSS LibSegJb_bvlE00.NX0 LibSegJb_bvlE00.F0 725448 LibSegJb_bvlE00.seg_sound_ax fx R M V bvlE00_conc_s. Qed.
Definition KS_bvlE01 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlE01.regs0 LibSegJb_bvlE01.regs_out0).
Lemma KS_bvlE01_ok : BG.kept_ok 60 LibSegJb_bvlE01.regs0 LibSegJb_bvlE01.regs_out0 KS_bvlE01 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlE01_conc_s := ",<A#v2p#2#40A#v21p#2#40S,2v2S,:v21S,;#O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801070v2#800000000000Hv2#10I_v2#70#70B#1v21#800000000000,1_v2#68#68,1,13X#;11<8#;1574Y,T,2_v2#70T,<#1T,=v21T,>#Lb_v2#68r1;Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bvlE01_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlE01] fx R M V bvlE01_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlE01] LibSegJb_bvlE01.regs0 LibSegJb_bvlE01.kn0 LibSegJb_bvlE01.BR LibSegJb_bvlE01.PSS LibSegJb_bvlE01.NX0 LibSegJb_bvlE01.F0 725448 LibSegJb_bvlE01.seg_sound_ax fx R M V bvlE01_conc_s. Qed.
Definition KS_bvlEn : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlEn.regs0 LibSegJb_bvlEn.regs_out0).
Lemma KS_bvlEn_ok : BG.kept_ok 60 LibSegJb_bvlEn.regs0 LibSegJb_bvlEn.regs_out0 KS_bvlEn = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlEn_conc_s := ",?A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2v2S,:v21S,;v23O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801070v2#800000000000Hv2#10I_v2#70#70B#1v21#800000000000B#1v23#3??????B#1+v21v23#800000000000,1_v2#68#68,1,27X#;11<8#;1278Y,T,2_v2#70T,5#?5T,6#2T,7^#?#?????????????;?T,8#9?T,9#?0T,;#13<:38T,<#23228T,=+v21v23T,>#8T,?^#?#???????????????T,10#1T,11^#?#?????????????<2T,12#2325=T,13^#?#??????????=<=:2T,14#7???8000T,15#90T,16#?4T,17#8?T,18#3T,1<#>?T,1=#>0T,1>#:0T,1?#>=Lb_v2#68r1;Lb_v2#60r1:Lb_v2#58r19Lb_v2#50r18Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma bvlEn_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlEn] fx R M V bvlEn_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlEn] LibSegJb_bvlEn.regs0 LibSegJb_bvlEn.kn0 LibSegJb_bvlEn.BR LibSegJb_bvlEn.PSS LibSegJb_bvlEn.NX0 LibSegJb_bvlEn.F0 725448 LibSegJb_bvlEn.seg_sound_ax fx R M V bvlEn_conc_s. Qed.
Definition KS_bvlHf_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlHf.regs0 LibSegJb_bvlHf.regs_out0).
Lemma KS_bvlHf_0_ok : BG.kept_ok 60 LibSegJb_bvlHf.regs0 LibSegJb_bvlHf.regs_out0 KS_bvlHf_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlHf_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlHf.regs0 LibSegJb_bvlHf.regs_out1).
Lemma KS_bvlHf_1_ok : BG.kept_ok 60 LibSegJb_bvlHf.regs0 LibSegJb_bvlHf.regs_out1 KS_bvlHf_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlHf_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Nav21v24B#v24#??Ka+/v21#8#7???8000#1,,2,2X#;1278#;138<Y,,2X#;1278#;12:0Y,1"%pstring.
Lemma bvlHf_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlHf_0; KS_bvlHf_1] fx R M V bvlHf_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlHf_0; KS_bvlHf_1] LibSegJb_bvlHf.regs0 LibSegJb_bvlHf.kn0 LibSegJb_bvlHf.BR LibSegJb_bvlHf.PSS LibSegJb_bvlHf.NX0 LibSegJb_bvlHf.F0 725624 LibSegJb_bvlHf.seg_sound_ax fx R M V bvlHf_conc_s. Qed.
Definition KS_bvlHs : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlHs.regs0 LibSegJb_bvlHs.regs_out0).
Lemma KS_bvlHs_ok : BG.kept_ok 60 LibSegJb_bvlHs.regs0 LibSegJb_bvlHs.regs_out0 KS_bvlHs = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlHs_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#7B#1+v21v23#800000000000,,1,3X#;1278#;138<Y,T,;v23"%pstring.
Lemma bvlHs_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlHs] fx R M V bvlHs_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlHs] LibSegJb_bvlHs.regs0 LibSegJb_bvlHs.kn0 LibSegJb_bvlHs.BR LibSegJb_bvlHs.PSS LibSegJb_bvlHs.NX0 LibSegJb_bvlHs.F0 725624 LibSegJb_bvlHs.seg_sound_ax fx R M V bvlHs_conc_s. Qed.
Definition KS_bvlSZ : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlSZ.regs0 LibSegJb_bvlSZ.regs_out0).
Lemma KS_bvlSZ_ok : BG.kept_ok 60 LibSegJb_bvlSZ.regs0 LibSegJb_bvlSZ.regs_out0 KS_bvlSZ = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlSZ_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000Nav21v25B#v25#??Ka+/v21#8#7???8000#1Ka#7???<648#2<,,1,5X#;138<#;13;<Y,T,;+v25#2325=T,<#T,19v25"%pstring.
Lemma bvlSZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlSZ] fx R M V bvlSZ_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlSZ] LibSegJb_bvlSZ.regs0 LibSegJb_bvlSZ.kn0 LibSegJb_bvlSZ.BR LibSegJb_bvlSZ.PSS LibSegJb_bvlSZ.NX0 LibSegJb_bvlSZ.F0 725900 LibSegJb_bvlSZ.seg_sound_ax fx R M V bvlSZ_conc_s. Qed.
Definition KS_bvlSP1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlSP1.regs0 LibSegJb_bvlSP1.regs_out0).
Lemma KS_bvlSP1_ok : BG.kept_ok 60 LibSegJb_bvlSP1.regs0 LibSegJb_bvlSP1.regs_out0 KS_bvlSP1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlSP1_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000Nav21v25B#v25#??Na+/v21#8#7???8000#1B#&v21#7#Ka#7???<648#2<,,1,5X#;138<#;13;<Y,T,;+v25#2325=T,<#T,19v25"%pstring.
Lemma bvlSP1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlSP1] fx R M V bvlSP1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlSP1] LibSegJb_bvlSP1.regs0 LibSegJb_bvlSP1.kn0 LibSegJb_bvlSP1.BR LibSegJb_bvlSP1.PSS LibSegJb_bvlSP1.NX0 LibSegJb_bvlSP1.F0 725900 LibSegJb_bvlSP1.seg_sound_ax fx R M V bvlSP1_conc_s. Qed.
Definition KS_bvlSP2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlSP2.regs0 LibSegJb_bvlSP2.regs_out0).
Lemma KS_bvlSP2_ok : BG.kept_ok 60 LibSegJb_bvlSP2.regs0 LibSegJb_bvlSP2.regs_out0 KS_bvlSP2 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlSP2_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000Nav21v25B#v25#??Na+/v21#8#7???8000#2B#&v21#7#1Ka#7???<648#2<,,1,5X#;138<#;13;<Y,T,;+v25#2325=T,<#T,19v25"%pstring.
Lemma bvlSP2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlSP2] fx R M V bvlSP2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlSP2] LibSegJb_bvlSP2.regs0 LibSegJb_bvlSP2.kn0 LibSegJb_bvlSP2.BR LibSegJb_bvlSP2.PSS LibSegJb_bvlSP2.NX0 LibSegJb_bvlSP2.F0 725900 LibSegJb_bvlSP2.seg_sound_ax fx R M V bvlSP2_conc_s. Qed.
Definition KS_bvlSP3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlSP3.regs0 LibSegJb_bvlSP3.regs_out0).
Lemma KS_bvlSP3_ok : BG.kept_ok 60 LibSegJb_bvlSP3.regs0 LibSegJb_bvlSP3.regs_out0 KS_bvlSP3 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlSP3_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000Nav21v25B#v25#??Na+/v21#8#7???8000#3B#&v21#7#2Ka#7???<648#2<,,1,5X#;138<#;13;<Y,T,;+v25#2325=T,<#T,19v25"%pstring.
Lemma bvlSP3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlSP3] fx R M V bvlSP3_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlSP3] LibSegJb_bvlSP3.regs0 LibSegJb_bvlSP3.kn0 LibSegJb_bvlSP3.BR LibSegJb_bvlSP3.PSS LibSegJb_bvlSP3.NX0 LibSegJb_bvlSP3.F0 725900 LibSegJb_bvlSP3.seg_sound_ax fx R M V bvlSP3_conc_s. Qed.
Definition KS_bvlSP4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlSP4.regs0 LibSegJb_bvlSP4.regs_out0).
Lemma KS_bvlSP4_ok : BG.kept_ok 60 LibSegJb_bvlSP4.regs0 LibSegJb_bvlSP4.regs_out0 KS_bvlSP4 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlSP4_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000Nav21v25B#v25#??Na+/v21#8#7???8000#4B#&v21#7#3Ka#7???<648#2<,,1,5X#;138<#;13;<Y,T,;+v25#2325=T,<#T,19v25"%pstring.
Lemma bvlSP4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlSP4] fx R M V bvlSP4_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlSP4] LibSegJb_bvlSP4.regs0 LibSegJb_bvlSP4.kn0 LibSegJb_bvlSP4.BR LibSegJb_bvlSP4.PSS LibSegJb_bvlSP4.NX0 LibSegJb_bvlSP4.F0 725900 LibSegJb_bvlSP4.seg_sound_ax fx R M V bvlSP4_conc_s. Qed.
Definition KS_bvlSP5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlSP5.regs0 LibSegJb_bvlSP5.regs_out0).
Lemma KS_bvlSP5_ok : BG.kept_ok 60 LibSegJb_bvlSP5.regs0 LibSegJb_bvlSP5.regs_out0 KS_bvlSP5 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlSP5_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000Nav21v25B#v25#??Na+/v21#8#7???8000#5B#&v21#7#4Ka#7???<648#2<,,1,5X#;138<#;13;<Y,T,;+v25#2325=T,<#T,19v25"%pstring.
Lemma bvlSP5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlSP5] fx R M V bvlSP5_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlSP5] LibSegJb_bvlSP5.regs0 LibSegJb_bvlSP5.kn0 LibSegJb_bvlSP5.BR LibSegJb_bvlSP5.PSS LibSegJb_bvlSP5.NX0 LibSegJb_bvlSP5.F0 725900 LibSegJb_bvlSP5.seg_sound_ax fx R M V bvlSP5_conc_s. Qed.
Definition KS_bvlSP6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlSP6.regs0 LibSegJb_bvlSP6.regs_out0).
Lemma KS_bvlSP6_ok : BG.kept_ok 60 LibSegJb_bvlSP6.regs0 LibSegJb_bvlSP6.regs_out0 KS_bvlSP6 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlSP6_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000Nav21v25B#v25#??Na+/v21#8#7???8000#6B#&v21#7#5Ka#7???<648#2<,,1,5X#;138<#;13;<Y,T,;+v25#2325=T,<#T,19v25"%pstring.
Lemma bvlSP6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlSP6] fx R M V bvlSP6_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlSP6] LibSegJb_bvlSP6.regs0 LibSegJb_bvlSP6.kn0 LibSegJb_bvlSP6.BR LibSegJb_bvlSP6.PSS LibSegJb_bvlSP6.NX0 LibSegJb_bvlSP6.F0 725900 LibSegJb_bvlSP6.seg_sound_ax fx R M V bvlSP6_conc_s. Qed.
Definition KS_bvlSP7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlSP7.regs0 LibSegJb_bvlSP7.regs_out0).
Lemma KS_bvlSP7_ok : BG.kept_ok 60 LibSegJb_bvlSP7.regs0 LibSegJb_bvlSP7.regs_out0 KS_bvlSP7 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlSP7_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000Nav21v25B#v25#??Na+/v21#8#7???8000#7B#&v21#7#6Ka#7???<648#2<,,1,5X#;138<#;13;<Y,T,;+v25#2325=T,<#T,19v25"%pstring.
Lemma bvlSP7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlSP7] fx R M V bvlSP7_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlSP7] LibSegJb_bvlSP7.regs0 LibSegJb_bvlSP7.kn0 LibSegJb_bvlSP7.BR LibSegJb_bvlSP7.PSS LibSegJb_bvlSP7.NX0 LibSegJb_bvlSP7.F0 725900 LibSegJb_bvlSP7.seg_sound_ax fx R M V bvlSP7_conc_s. Qed.
Definition KS_bvlT0_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlT0.regs0 LibSegJb_bvlT0.regs_out0).
Lemma KS_bvlT0_0_ok : BG.kept_ok 60 LibSegJb_bvlT0.regs0 LibSegJb_bvlT0.regs_out0 KS_bvlT0_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlT0_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlT0.regs0 LibSegJb_bvlT0.regs_out1).
Lemma KS_bvlT0_1_ok : BG.kept_ok 60 LibSegJb_bvlT0.regs0 LibSegJb_bvlT0.regs_out1 KS_bvlT0_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlT0_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlT0.regs0 LibSegJb_bvlT0.regs_out2).
Lemma KS_bvlT0_2_ok : BG.kept_ok 60 LibSegJb_bvlT0.regs0 LibSegJb_bvlT0.regs_out2 KS_bvlT0_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlT0_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1;#S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000B#v25#??,,3,4X#;13<0#;1574Y,T,;#6T,1:+v21#1,5X#;13<0#;14:8Y,1T,;#6T,1:+v21#1Cv25#?5,5X#;13<0#;1574Y,2T,;#6T,1:+v21#1D#?5v25"%pstring.
Lemma bvlT0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlT0_0; KS_bvlT0_1; KS_bvlT0_2] fx R M V bvlT0_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlT0_0; KS_bvlT0_1; KS_bvlT0_2] LibSegJb_bvlT0.regs0 LibSegJb_bvlT0.kn0 LibSegJb_bvlT0.BR LibSegJb_bvlT0.PSS LibSegJb_bvlT0.NX0 LibSegJb_bvlT0.F0 725952 LibSegJb_bvlT0.seg_sound_ax fx R M V bvlT0_conc_s. Qed.
Definition KS_bvlT1a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlT1a.regs0 LibSegJb_bvlT1a.regs_out0).
Lemma KS_bvlT1a_ok : BG.kept_ok 60 LibSegJb_bvlT1a.regs0 LibSegJb_bvlT1a.regs_out0 KS_bvlT1a = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlT1a_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1;#1S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#1B#1+v21v23#800000000000B#v25#??,,1,3X#;13<0#;1574Y,T,;#5"%pstring.
Lemma bvlT1a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlT1a] fx R M V bvlT1a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlT1a] LibSegJb_bvlT1a.regs0 LibSegJb_bvlT1a.kn0 LibSegJb_bvlT1a.BR LibSegJb_bvlT1a.PSS LibSegJb_bvlT1a.NX0 LibSegJb_bvlT1a.F0 725952 LibSegJb_bvlT1a.seg_sound_ax fx R M V bvlT1a_conc_s. Qed.
Definition KS_bvlT1b : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlT1b.regs0 LibSegJb_bvlT1b.regs_out0).
Lemma KS_bvlT1b_ok : BG.kept_ok 60 LibSegJb_bvlT1b.regs0 LibSegJb_bvlT1b.regs_out0 KS_bvlT1b = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlT1b_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1;#1S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#2v23#4000000B#1+v21v23#800000000000B#v25#??,,1,5X#;13<0#;143<Y,T,;#1T,<+v21#2T,1:+v21#2"%pstring.
Lemma bvlT1b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlT1b] fx R M V bvlT1b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlT1b] LibSegJb_bvlT1b.regs0 LibSegJb_bvlT1b.kn0 LibSegJb_bvlT1b.BR LibSegJb_bvlT1b.PSS LibSegJb_bvlT1b.NX0 LibSegJb_bvlT1b.F0 725952 LibSegJb_bvlT1b.seg_sound_ax fx R M V bvlT1b_conc_s. Qed.
Definition KS_bvlT2a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlT2a.regs0 LibSegJb_bvlT2a.regs_out0).
Lemma KS_bvlT2a_ok : BG.kept_ok 60 LibSegJb_bvlT2a.regs0 LibSegJb_bvlT2a.regs_out0 KS_bvlT2a = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlT2a_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1;#2S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#2B#1+v21v23#800000000000B#v25#??,,1,3X#;13<0#;1574Y,T,;#5"%pstring.
Lemma bvlT2a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlT2a] fx R M V bvlT2a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlT2a] LibSegJb_bvlT2a.regs0 LibSegJb_bvlT2a.kn0 LibSegJb_bvlT2a.BR LibSegJb_bvlT2a.PSS LibSegJb_bvlT2a.NX0 LibSegJb_bvlT2a.F0 725952 LibSegJb_bvlT2a.seg_sound_ax fx R M V bvlT2a_conc_s. Qed.
Definition KS_bvlT2b : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlT2b.regs0 LibSegJb_bvlT2b.regs_out0).
Lemma KS_bvlT2b_ok : BG.kept_ok 60 LibSegJb_bvlT2b.regs0 LibSegJb_bvlT2b.regs_out0 KS_bvlT2b = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlT2b_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1;#2S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#3v23#4000000B#1+v21v23#800000000000B#v25#??,,1,6X#;13<0#;141<Y,T,1+v21#3T,;#1T,<+v21#2T,1:+v21#3"%pstring.
Lemma bvlT2b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlT2b] fx R M V bvlT2b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlT2b] LibSegJb_bvlT2b.regs0 LibSegJb_bvlT2b.kn0 LibSegJb_bvlT2b.BR LibSegJb_bvlT2b.PSS LibSegJb_bvlT2b.NX0 LibSegJb_bvlT2b.F0 725952 LibSegJb_bvlT2b.seg_sound_ax fx R M V bvlT2b_conc_s. Qed.
Definition KS_bvlT3a : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlT3a.regs0 LibSegJb_bvlT3a.regs_out0).
Lemma KS_bvlT3a_ok : BG.kept_ok 60 LibSegJb_bvlT3a.regs0 LibSegJb_bvlT3a.regs_out0 KS_bvlT3a = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlT3a_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1;#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#3B#1+v21v23#800000000000B#v25#??,,1,3X#;13<0#;1574Y,T,;#5"%pstring.
Lemma bvlT3a_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlT3a] fx R M V bvlT3a_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlT3a] LibSegJb_bvlT3a.regs0 LibSegJb_bvlT3a.kn0 LibSegJb_bvlT3a.BR LibSegJb_bvlT3a.PSS LibSegJb_bvlT3a.NX0 LibSegJb_bvlT3a.F0 725952 LibSegJb_bvlT3a.seg_sound_ax fx R M V bvlT3a_conc_s. Qed.
Definition KS_bvlT3b : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlT3b.regs0 LibSegJb_bvlT3b.regs_out0).
Lemma KS_bvlT3b_ok : BG.kept_ok 60 LibSegJb_bvlT3b.regs0 LibSegJb_bvlT3b.regs_out0 KS_bvlT3b = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlT3b_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1;#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#4v23#4000000B#1+v21v23#800000000000B#v25#??,,1,6X#;13<0#;13?<Y,T,1+v21#4T,;#1T,<+v21#3T,1:+v21#4"%pstring.
Lemma bvlT3b_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlT3b] fx R M V bvlT3b_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlT3b] LibSegJb_bvlT3b.regs0 LibSegJb_bvlT3b.kn0 LibSegJb_bvlT3b.BR LibSegJb_bvlT3b.PSS LibSegJb_bvlT3b.NX0 LibSegJb_bvlT3b.F0 725952 LibSegJb_bvlT3b.seg_sound_ax fx R M V bvlT3b_conc_s. Qed.
Definition KS_bvlTbig_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlTbig.regs0 LibSegJb_bvlTbig.regs_out0).
Lemma KS_bvlTbig_0_ok : BG.kept_ok 60 LibSegJb_bvlTbig.regs0 LibSegJb_bvlTbig.regs_out0 KS_bvlTbig_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlTbig_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlTbig.regs0 LibSegJb_bvlTbig.regs_out1).
Lemma KS_bvlTbig_1_ok : BG.kept_ok 60 LibSegJb_bvlTbig.regs0 LibSegJb_bvlTbig.regs_out1 KS_bvlTbig_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlTbig_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v25p#2#40A#v26p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1;v26S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000B#v25#??B#4v26#??,,2,7X#;13<0#;1574Y,T,1++v21v26#1T,;#1T,<+v21v26T,1:++v21v26#1Cv26v23,4X#;13<0#;1574Y,1T,;#5Dv23v26"%pstring.
Lemma bvlTbig_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlTbig_0; KS_bvlTbig_1] fx R M V bvlTbig_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlTbig_0; KS_bvlTbig_1] LibSegJb_bvlTbig.regs0 LibSegJb_bvlTbig.kn0 LibSegJb_bvlTbig.BR LibSegJb_bvlTbig.PSS LibSegJb_bvlTbig.NX0 LibSegJb_bvlTbig.F0 725952 LibSegJb_bvlTbig.seg_sound_ax fx R M V bvlTbig_conc_s. Qed.
Definition KS_bvlL_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out0).
Lemma KS_bvlL_0_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out0 KS_bvlL_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out1).
Lemma KS_bvlL_1_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out1 KS_bvlL_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out2).
Lemma KS_bvlL_2_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out2 KS_bvlL_2 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out3).
Lemma KS_bvlL_3_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out3 KS_bvlL_3 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out4).
Lemma KS_bvlL_4_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out4 KS_bvlL_4 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out5).
Lemma KS_bvlL_5_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out5 KS_bvlL_5 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out6).
Lemma KS_bvlL_6_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out6 KS_bvlL_6 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out7).
Lemma KS_bvlL_7_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out7 KS_bvlL_7 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out8).
Lemma KS_bvlL_8_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out8 KS_bvlL_8 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out9).
Lemma KS_bvlL_9_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out9 KS_bvlL_9 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out10).
Lemma KS_bvlL_10_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out10 KS_bvlL_10 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_11 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out11).
Lemma KS_bvlL_11_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out11 KS_bvlL_11 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_12 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out12).
Lemma KS_bvlL_12_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out12 KS_bvlL_12 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlL_13 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out13).
Lemma KS_bvlL_13_ok : BG.kept_ok 60 LibSegJb_bvlL.regs0 LibSegJb_bvlL.regs_out13 KS_bvlL_13 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlL_conc_s := ",25A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v25p#2#40A#v27p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,;v27S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,19v25S,1:v22S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#1v23#4000000B#1+v21v23#800000000000B#v25#??B#v22#800000000000,,>,5X#;145<#;1574Y,T,;#6C&v27#??#90C%_v25#?0p#2#40#1,5X#;145<#;14:8Y,1W,;&v27#??D#90&v27#??C%_v25#?0p#2#40#1,6X#;145<#;1574Y,2T,;#6C#8?&v27#??C%_v25#?4p#2#40#1D#1%_v25#?0p#2#40,6X#;145<#;14:8Y,3W,;&v27#??D&v27#??#8?C%_v25#?4p#2#40#1D#1%_v25#?0p#2#40,5X#;145<#;1574Y,4T,;#6D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,6X#;145<#;14:8Y,5T,;#6Cv25#?5D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,6X#;145<#;1574Y,6T,;#6D#?5v25D#1%_v25#?4p#2#40D#1%_v25#?0p#2#40,5X#;145<#;1574Y,7T,;#6C&v27#??#:0C%_v25#>0p#2#40#1,5X#;145<#;14:8Y,8W,;&v27#??D#:0&v27#??C%_v25#>0p#2#40#1,6X#;145<#;1574Y,9T,;#6C#9?&v27#??C%_v25#>=p#2#40#1D#1%_v25#>0p#2#40,6X#;145<#;14:8Y,:W,;&v27#??D&v27#??#9?C%_v25#>=p#2#40#1D#1%_v25#>0p#2#40,5X#;145<#;1574Y,;T,;#6D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40,6X#;145<#;14:8Y,<T,;#6Cv25#?5D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40,6X#;145<#;1574Y,=T,;#6D#?5v25D#1%_v25#>=p#2#40D#1%_v25#>0p#2#40"%pstring.
Lemma bvlL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlL_0; KS_bvlL_1; KS_bvlL_2; KS_bvlL_3; KS_bvlL_4; KS_bvlL_5; KS_bvlL_6; KS_bvlL_7; KS_bvlL_8; KS_bvlL_9; KS_bvlL_10; KS_bvlL_11; KS_bvlL_12; KS_bvlL_13] fx R M V bvlL_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlL_0; KS_bvlL_1; KS_bvlL_2; KS_bvlL_3; KS_bvlL_4; KS_bvlL_5; KS_bvlL_6; KS_bvlL_7; KS_bvlL_8; KS_bvlL_9; KS_bvlL_10; KS_bvlL_11; KS_bvlL_12; KS_bvlL_13] LibSegJb_bvlL.regs0 LibSegJb_bvlL.kn0 LibSegJb_bvlL.BR LibSegJb_bvlL.PSS LibSegJb_bvlL.NX0 LibSegJb_bvlL.F0 726108 LibSegJb_bvlL.seg_sound_ax fx R M V bvlL_conc_s. Qed.
Definition KS_bvlB_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlB.regs0 LibSegJb_bvlB.regs_out0).
Lemma KS_bvlB_0_ok : BG.kept_ok 60 LibSegJb_bvlB.regs0 LibSegJb_bvlB.regs_out0 KS_bvlB_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlB_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlB.regs0 LibSegJb_bvlB.regs_out1).
Lemma KS_bvlB_1_ok : BG.kept_ok 60 LibSegJb_bvlB.regs0 LibSegJb_bvlB.regs_out1 KS_bvlB_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlB_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1:v21S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#v21#800000000000B#v23#800000000000B#+v21v23#800000000000,,2,5X#;14:8#;1574Y,T,:+v21v23T,;#C%_v21%+v21v23p#2#40p#2#40#1,4X#;14:8#;1278Y,1T,:v21D#1%_v21%+v21v23p#2#40p#2#40"%pstring.
Lemma bvlB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlB_0; KS_bvlB_1] fx R M V bvlB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlB_0; KS_bvlB_1] LibSegJb_bvlB.regs0 LibSegJb_bvlB.kn0 LibSegJb_bvlB.BR LibSegJb_bvlB.PSS LibSegJb_bvlB.NX0 LibSegJb_bvlB.F0 726184 LibSegJb_bvlB.seg_sound_ax fx R M V bvlB_conc_s. Qed.
Definition KS_bvlX : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlX.regs0 LibSegJb_bvlX.regs_out0).
Lemma KS_bvlX_ok : BG.kept_ok 60 LibSegJb_bvlX.regs0 LibSegJb_bvlX.regs_out0 KS_bvlX = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlX_conc_s := ",1>A#v2p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40A#v33p#2#40A#v34p#2#40S,2_v2#70B#7???7?801070v2#800000000000Hv2#10La_v2#8v28La_v2#10v29La_v2#18v2:La_v2#20v2;La_v2#28v2<La_v2#30v2=La_v2#38v2>La_v2#40v2?La_v2#48v30La_v2#50v31La_v2#58v32La_v2#60v33La_v2#68v34,,1,10X#;1574#;15:<Y,T,1v28T,2v2T,8v29T,9v2:T,12v2;T,13v2<T,14v2=T,15v2>T,16v2?T,17v30T,18v31T,19v32T,1:v33T,1;v34"%pstring.
Lemma bvlX_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlX] fx R M V bvlX_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlX] LibSegJb_bvlX.regs0 LibSegJb_bvlX.kn0 LibSegJb_bvlX.BR LibSegJb_bvlX.PSS LibSegJb_bvlX.NX0 LibSegJb_bvlX.F0 726388 LibSegJb_bvlX.seg_sound_ax fx R M V bvlX_conc_s. Qed.
End PMBVALP1.
