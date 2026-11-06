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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bvlF1Z LibSegJb_bvlF1P1 LibSegJb_bvlF1P2 LibSegJb_bvlF1P3 LibSegJb_bvlF1P4 LibSegJb_bvlF1P5 LibSegJb_bvlF1P6 LibSegJb_bvlF1P7 LibSegJb_bvlF2Z LibSegJb_bvlF2P1 LibSegJb_bvlF2P2 LibSegJb_bvlF2P3 LibSegJb_bvlF2P4 LibSegJb_bvlF2P5 LibSegJb_bvlF2P6 LibSegJb_bvlF2P7 LibSegJb_bvlF3Z LibSegJb_bvlF3P1 LibSegJb_bvlF3P2 LibSegJb_bvlF3P3 LibSegJb_bvlF3P4 LibSegJb_bvlF3P5 LibSegJb_bvlF3P6 LibSegJb_bvlF3P7 LibSegJb_bvlF4Z LibSegJb_bvlF4P1 LibSegJb_bvlF4P2 LibSegJb_bvlF4P3 LibSegJb_bvlF4P4 LibSegJb_bvlF4P5 LibSegJb_bvlF4P6 LibSegJb_bvlF4P7.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBVALP2.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bvlF1Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1Z.regs0 LibSegJb_bvlF1Z.regs_out0).
Lemma KS_bvlF1Z_0_ok : BG.kept_ok 60 LibSegJb_bvlF1Z.regs0 LibSegJb_bvlF1Z.regs_out0 KS_bvlF1Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF1Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1Z.regs0 LibSegJb_bvlF1Z.regs_out1).
Lemma KS_bvlF1Z_1_ok : BG.kept_ok 60 LibSegJb_bvlF1Z.regs0 LibSegJb_bvlF1Z.regs_out1 KS_bvlF1Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bvlF1Z_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Ka+/+v21#1#8#7???8000#1,,2,4X#;12:0#;138<Y,T,:+v21#1T,;+v21#1,3X#;12:0#;12<0Y,1T,;+v21#1"%pstring.
Lemma bvlF1Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlF1Z_0; KS_bvlF1Z_1] fx R M V bvlF1Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlF1Z_0; KS_bvlF1Z_1] LibSegJb_bvlF1Z.regs0 LibSegJb_bvlF1Z.kn0 LibSegJb_bvlF1Z.BR LibSegJb_bvlF1Z.PSS LibSegJb_bvlF1Z.NX0 LibSegJb_bvlF1Z.F0 725664 LibSegJb_bvlF1Z.seg_sound_ax fx R M V bvlF1Z_conc_s. Qed.
Definition KS_bvlF1P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P1.regs0 LibSegJb_bvlF1P1.regs_out0).
Lemma KS_bvlF1P1_0_ok : BG.kept_ok 60 LibSegJb_bvlF1P1.regs0 LibSegJb_bvlF1P1.regs_out0 KS_bvlF1P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF1P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P1.regs0 LibSegJb_bvlF1P1.regs_out1).
Lemma KS_bvlF1P1_1_ok : BG.kept_ok 60 LibSegJb_bvlF1P1.regs0 LibSegJb_bvlF1P1.regs_out1 KS_bvlF1P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF1P1_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#1B#&%+v21#1p#2#40#7#,,2,5X#;12:0#;138<Y,T,:+v21#1T,;+v21#1T,19#,4X#;12:0#;12<0Y,1T,;+v21#1T,19#"%pstring.
Lemma bvlF1P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF1P1_0; KS_bvlF1P1_1] fx R M V bvlF1P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF1P1_0; KS_bvlF1P1_1] LibSegJb_bvlF1P1.regs0 LibSegJb_bvlF1P1.kn0 LibSegJb_bvlF1P1.BR LibSegJb_bvlF1P1.PSS LibSegJb_bvlF1P1.NX0 LibSegJb_bvlF1P1.F0 725664 LibSegJb_bvlF1P1.seg_sound_ax fx R M V bvlF1P1_conc_s. Qed.
Definition KS_bvlF1P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P2.regs0 LibSegJb_bvlF1P2.regs_out0).
Lemma KS_bvlF1P2_0_ok : BG.kept_ok 60 LibSegJb_bvlF1P2.regs0 LibSegJb_bvlF1P2.regs_out0 KS_bvlF1P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF1P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P2.regs0 LibSegJb_bvlF1P2.regs_out1).
Lemma KS_bvlF1P2_1_ok : BG.kept_ok 60 LibSegJb_bvlF1P2.regs0 LibSegJb_bvlF1P2.regs_out1 KS_bvlF1P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF1P2_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#2B#&%+v21#1p#2#40#7#1,,2,5X#;12:0#;138<Y,T,:+v21#1T,;+v21#1W,19&%+v21#1p#2#40#7,4X#;12:0#;12<0Y,1T,;+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma bvlF1P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF1P2_0; KS_bvlF1P2_1] fx R M V bvlF1P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF1P2_0; KS_bvlF1P2_1] LibSegJb_bvlF1P2.regs0 LibSegJb_bvlF1P2.kn0 LibSegJb_bvlF1P2.BR LibSegJb_bvlF1P2.PSS LibSegJb_bvlF1P2.NX0 LibSegJb_bvlF1P2.F0 725664 LibSegJb_bvlF1P2.seg_sound_ax fx R M V bvlF1P2_conc_s. Qed.
Definition KS_bvlF1P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P3.regs0 LibSegJb_bvlF1P3.regs_out0).
Lemma KS_bvlF1P3_0_ok : BG.kept_ok 60 LibSegJb_bvlF1P3.regs0 LibSegJb_bvlF1P3.regs_out0 KS_bvlF1P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF1P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P3.regs0 LibSegJb_bvlF1P3.regs_out1).
Lemma KS_bvlF1P3_1_ok : BG.kept_ok 60 LibSegJb_bvlF1P3.regs0 LibSegJb_bvlF1P3.regs_out1 KS_bvlF1P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF1P3_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#3B#&%+v21#1p#2#40#7#2,,2,5X#;12:0#;138<Y,T,:+v21#1T,;+v21#1W,19&%+v21#1p#2#40#7,4X#;12:0#;12<0Y,1T,;+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma bvlF1P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF1P3_0; KS_bvlF1P3_1] fx R M V bvlF1P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF1P3_0; KS_bvlF1P3_1] LibSegJb_bvlF1P3.regs0 LibSegJb_bvlF1P3.kn0 LibSegJb_bvlF1P3.BR LibSegJb_bvlF1P3.PSS LibSegJb_bvlF1P3.NX0 LibSegJb_bvlF1P3.F0 725664 LibSegJb_bvlF1P3.seg_sound_ax fx R M V bvlF1P3_conc_s. Qed.
Definition KS_bvlF1P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P4.regs0 LibSegJb_bvlF1P4.regs_out0).
Lemma KS_bvlF1P4_0_ok : BG.kept_ok 60 LibSegJb_bvlF1P4.regs0 LibSegJb_bvlF1P4.regs_out0 KS_bvlF1P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF1P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P4.regs0 LibSegJb_bvlF1P4.regs_out1).
Lemma KS_bvlF1P4_1_ok : BG.kept_ok 60 LibSegJb_bvlF1P4.regs0 LibSegJb_bvlF1P4.regs_out1 KS_bvlF1P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF1P4_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#4B#&%+v21#1p#2#40#7#3,,2,5X#;12:0#;138<Y,T,:+v21#1T,;+v21#1W,19&%+v21#1p#2#40#7,4X#;12:0#;12<0Y,1T,;+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma bvlF1P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF1P4_0; KS_bvlF1P4_1] fx R M V bvlF1P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF1P4_0; KS_bvlF1P4_1] LibSegJb_bvlF1P4.regs0 LibSegJb_bvlF1P4.kn0 LibSegJb_bvlF1P4.BR LibSegJb_bvlF1P4.PSS LibSegJb_bvlF1P4.NX0 LibSegJb_bvlF1P4.F0 725664 LibSegJb_bvlF1P4.seg_sound_ax fx R M V bvlF1P4_conc_s. Qed.
Definition KS_bvlF1P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P5.regs0 LibSegJb_bvlF1P5.regs_out0).
Lemma KS_bvlF1P5_0_ok : BG.kept_ok 60 LibSegJb_bvlF1P5.regs0 LibSegJb_bvlF1P5.regs_out0 KS_bvlF1P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF1P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P5.regs0 LibSegJb_bvlF1P5.regs_out1).
Lemma KS_bvlF1P5_1_ok : BG.kept_ok 60 LibSegJb_bvlF1P5.regs0 LibSegJb_bvlF1P5.regs_out1 KS_bvlF1P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF1P5_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#5B#&%+v21#1p#2#40#7#4,,2,5X#;12:0#;138<Y,T,:+v21#1T,;+v21#1W,19&%+v21#1p#2#40#7,4X#;12:0#;12<0Y,1T,;+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma bvlF1P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF1P5_0; KS_bvlF1P5_1] fx R M V bvlF1P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF1P5_0; KS_bvlF1P5_1] LibSegJb_bvlF1P5.regs0 LibSegJb_bvlF1P5.kn0 LibSegJb_bvlF1P5.BR LibSegJb_bvlF1P5.PSS LibSegJb_bvlF1P5.NX0 LibSegJb_bvlF1P5.F0 725664 LibSegJb_bvlF1P5.seg_sound_ax fx R M V bvlF1P5_conc_s. Qed.
Definition KS_bvlF1P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P6.regs0 LibSegJb_bvlF1P6.regs_out0).
Lemma KS_bvlF1P6_0_ok : BG.kept_ok 60 LibSegJb_bvlF1P6.regs0 LibSegJb_bvlF1P6.regs_out0 KS_bvlF1P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF1P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P6.regs0 LibSegJb_bvlF1P6.regs_out1).
Lemma KS_bvlF1P6_1_ok : BG.kept_ok 60 LibSegJb_bvlF1P6.regs0 LibSegJb_bvlF1P6.regs_out1 KS_bvlF1P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF1P6_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#6B#&%+v21#1p#2#40#7#5,,2,5X#;12:0#;138<Y,T,:+v21#1T,;+v21#1W,19&%+v21#1p#2#40#7,4X#;12:0#;12<0Y,1T,;+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma bvlF1P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF1P6_0; KS_bvlF1P6_1] fx R M V bvlF1P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF1P6_0; KS_bvlF1P6_1] LibSegJb_bvlF1P6.regs0 LibSegJb_bvlF1P6.kn0 LibSegJb_bvlF1P6.BR LibSegJb_bvlF1P6.PSS LibSegJb_bvlF1P6.NX0 LibSegJb_bvlF1P6.F0 725664 LibSegJb_bvlF1P6.seg_sound_ax fx R M V bvlF1P6_conc_s. Qed.
Definition KS_bvlF1P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P7.regs0 LibSegJb_bvlF1P7.regs_out0).
Lemma KS_bvlF1P7_0_ok : BG.kept_ok 60 LibSegJb_bvlF1P7.regs0 LibSegJb_bvlF1P7.regs_out0 KS_bvlF1P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF1P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF1P7.regs0 LibSegJb_bvlF1P7.regs_out1).
Lemma KS_bvlF1P7_1_ok : BG.kept_ok 60 LibSegJb_bvlF1P7.regs0 LibSegJb_bvlF1P7.regs_out1 KS_bvlF1P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF1P7_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#1v24B#v24#??Na+/+v21#1#8#7???8000#7B#&%+v21#1p#2#40#7#6,,2,5X#;12:0#;138<Y,T,:+v21#1T,;+v21#1W,19&%+v21#1p#2#40#7,4X#;12:0#;12<0Y,1T,;+v21#1W,19&%+v21#1p#2#40#7"%pstring.
Lemma bvlF1P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF1P7_0; KS_bvlF1P7_1] fx R M V bvlF1P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF1P7_0; KS_bvlF1P7_1] LibSegJb_bvlF1P7.regs0 LibSegJb_bvlF1P7.kn0 LibSegJb_bvlF1P7.BR LibSegJb_bvlF1P7.PSS LibSegJb_bvlF1P7.NX0 LibSegJb_bvlF1P7.F0 725664 LibSegJb_bvlF1P7.seg_sound_ax fx R M V bvlF1P7_conc_s. Qed.
Definition KS_bvlF2Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2Z.regs0 LibSegJb_bvlF2Z.regs_out0).
Lemma KS_bvlF2Z_0_ok : BG.kept_ok 60 LibSegJb_bvlF2Z.regs0 LibSegJb_bvlF2Z.regs_out0 KS_bvlF2Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF2Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2Z.regs0 LibSegJb_bvlF2Z.regs_out1).
Lemma KS_bvlF2Z_1_ok : BG.kept_ok 60 LibSegJb_bvlF2Z.regs0 LibSegJb_bvlF2Z.regs_out1 KS_bvlF2Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF2Z_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Ka+/+v21#2#8#7???8000#1,,2,4X#;12<0#;138<Y,T,:+v21#2T,;+v21#2,3X#;12<0#;12>0Y,1T,;+v21#2"%pstring.
Lemma bvlF2Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlF2Z_0; KS_bvlF2Z_1] fx R M V bvlF2Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlF2Z_0; KS_bvlF2Z_1] LibSegJb_bvlF2Z.regs0 LibSegJb_bvlF2Z.kn0 LibSegJb_bvlF2Z.BR LibSegJb_bvlF2Z.PSS LibSegJb_bvlF2Z.NX0 LibSegJb_bvlF2Z.F0 725696 LibSegJb_bvlF2Z.seg_sound_ax fx R M V bvlF2Z_conc_s. Qed.
Definition KS_bvlF2P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P1.regs0 LibSegJb_bvlF2P1.regs_out0).
Lemma KS_bvlF2P1_0_ok : BG.kept_ok 60 LibSegJb_bvlF2P1.regs0 LibSegJb_bvlF2P1.regs_out0 KS_bvlF2P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF2P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P1.regs0 LibSegJb_bvlF2P1.regs_out1).
Lemma KS_bvlF2P1_1_ok : BG.kept_ok 60 LibSegJb_bvlF2P1.regs0 LibSegJb_bvlF2P1.regs_out1 KS_bvlF2P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF2P1_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#1B#&%+v21#2p#2#40#7#,,2,5X#;12<0#;138<Y,T,:+v21#2T,;+v21#2T,19#,4X#;12<0#;12>0Y,1T,;+v21#2T,19#"%pstring.
Lemma bvlF2P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF2P1_0; KS_bvlF2P1_1] fx R M V bvlF2P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF2P1_0; KS_bvlF2P1_1] LibSegJb_bvlF2P1.regs0 LibSegJb_bvlF2P1.kn0 LibSegJb_bvlF2P1.BR LibSegJb_bvlF2P1.PSS LibSegJb_bvlF2P1.NX0 LibSegJb_bvlF2P1.F0 725696 LibSegJb_bvlF2P1.seg_sound_ax fx R M V bvlF2P1_conc_s. Qed.
Definition KS_bvlF2P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P2.regs0 LibSegJb_bvlF2P2.regs_out0).
Lemma KS_bvlF2P2_0_ok : BG.kept_ok 60 LibSegJb_bvlF2P2.regs0 LibSegJb_bvlF2P2.regs_out0 KS_bvlF2P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF2P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P2.regs0 LibSegJb_bvlF2P2.regs_out1).
Lemma KS_bvlF2P2_1_ok : BG.kept_ok 60 LibSegJb_bvlF2P2.regs0 LibSegJb_bvlF2P2.regs_out1 KS_bvlF2P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF2P2_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#2B#&%+v21#2p#2#40#7#1,,2,5X#;12<0#;138<Y,T,:+v21#2T,;+v21#2W,19&%+v21#2p#2#40#7,4X#;12<0#;12>0Y,1T,;+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma bvlF2P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF2P2_0; KS_bvlF2P2_1] fx R M V bvlF2P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF2P2_0; KS_bvlF2P2_1] LibSegJb_bvlF2P2.regs0 LibSegJb_bvlF2P2.kn0 LibSegJb_bvlF2P2.BR LibSegJb_bvlF2P2.PSS LibSegJb_bvlF2P2.NX0 LibSegJb_bvlF2P2.F0 725696 LibSegJb_bvlF2P2.seg_sound_ax fx R M V bvlF2P2_conc_s. Qed.
Definition KS_bvlF2P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P3.regs0 LibSegJb_bvlF2P3.regs_out0).
Lemma KS_bvlF2P3_0_ok : BG.kept_ok 60 LibSegJb_bvlF2P3.regs0 LibSegJb_bvlF2P3.regs_out0 KS_bvlF2P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF2P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P3.regs0 LibSegJb_bvlF2P3.regs_out1).
Lemma KS_bvlF2P3_1_ok : BG.kept_ok 60 LibSegJb_bvlF2P3.regs0 LibSegJb_bvlF2P3.regs_out1 KS_bvlF2P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF2P3_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#3B#&%+v21#2p#2#40#7#2,,2,5X#;12<0#;138<Y,T,:+v21#2T,;+v21#2W,19&%+v21#2p#2#40#7,4X#;12<0#;12>0Y,1T,;+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma bvlF2P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF2P3_0; KS_bvlF2P3_1] fx R M V bvlF2P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF2P3_0; KS_bvlF2P3_1] LibSegJb_bvlF2P3.regs0 LibSegJb_bvlF2P3.kn0 LibSegJb_bvlF2P3.BR LibSegJb_bvlF2P3.PSS LibSegJb_bvlF2P3.NX0 LibSegJb_bvlF2P3.F0 725696 LibSegJb_bvlF2P3.seg_sound_ax fx R M V bvlF2P3_conc_s. Qed.
Definition KS_bvlF2P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P4.regs0 LibSegJb_bvlF2P4.regs_out0).
Lemma KS_bvlF2P4_0_ok : BG.kept_ok 60 LibSegJb_bvlF2P4.regs0 LibSegJb_bvlF2P4.regs_out0 KS_bvlF2P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF2P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P4.regs0 LibSegJb_bvlF2P4.regs_out1).
Lemma KS_bvlF2P4_1_ok : BG.kept_ok 60 LibSegJb_bvlF2P4.regs0 LibSegJb_bvlF2P4.regs_out1 KS_bvlF2P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF2P4_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#4B#&%+v21#2p#2#40#7#3,,2,5X#;12<0#;138<Y,T,:+v21#2T,;+v21#2W,19&%+v21#2p#2#40#7,4X#;12<0#;12>0Y,1T,;+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma bvlF2P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF2P4_0; KS_bvlF2P4_1] fx R M V bvlF2P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF2P4_0; KS_bvlF2P4_1] LibSegJb_bvlF2P4.regs0 LibSegJb_bvlF2P4.kn0 LibSegJb_bvlF2P4.BR LibSegJb_bvlF2P4.PSS LibSegJb_bvlF2P4.NX0 LibSegJb_bvlF2P4.F0 725696 LibSegJb_bvlF2P4.seg_sound_ax fx R M V bvlF2P4_conc_s. Qed.
Definition KS_bvlF2P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P5.regs0 LibSegJb_bvlF2P5.regs_out0).
Lemma KS_bvlF2P5_0_ok : BG.kept_ok 60 LibSegJb_bvlF2P5.regs0 LibSegJb_bvlF2P5.regs_out0 KS_bvlF2P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF2P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P5.regs0 LibSegJb_bvlF2P5.regs_out1).
Lemma KS_bvlF2P5_1_ok : BG.kept_ok 60 LibSegJb_bvlF2P5.regs0 LibSegJb_bvlF2P5.regs_out1 KS_bvlF2P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF2P5_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#5B#&%+v21#2p#2#40#7#4,,2,5X#;12<0#;138<Y,T,:+v21#2T,;+v21#2W,19&%+v21#2p#2#40#7,4X#;12<0#;12>0Y,1T,;+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma bvlF2P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF2P5_0; KS_bvlF2P5_1] fx R M V bvlF2P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF2P5_0; KS_bvlF2P5_1] LibSegJb_bvlF2P5.regs0 LibSegJb_bvlF2P5.kn0 LibSegJb_bvlF2P5.BR LibSegJb_bvlF2P5.PSS LibSegJb_bvlF2P5.NX0 LibSegJb_bvlF2P5.F0 725696 LibSegJb_bvlF2P5.seg_sound_ax fx R M V bvlF2P5_conc_s. Qed.
Definition KS_bvlF2P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P6.regs0 LibSegJb_bvlF2P6.regs_out0).
Lemma KS_bvlF2P6_0_ok : BG.kept_ok 60 LibSegJb_bvlF2P6.regs0 LibSegJb_bvlF2P6.regs_out0 KS_bvlF2P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF2P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P6.regs0 LibSegJb_bvlF2P6.regs_out1).
Lemma KS_bvlF2P6_1_ok : BG.kept_ok 60 LibSegJb_bvlF2P6.regs0 LibSegJb_bvlF2P6.regs_out1 KS_bvlF2P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF2P6_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#6B#&%+v21#2p#2#40#7#5,,2,5X#;12<0#;138<Y,T,:+v21#2T,;+v21#2W,19&%+v21#2p#2#40#7,4X#;12<0#;12>0Y,1T,;+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma bvlF2P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF2P6_0; KS_bvlF2P6_1] fx R M V bvlF2P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF2P6_0; KS_bvlF2P6_1] LibSegJb_bvlF2P6.regs0 LibSegJb_bvlF2P6.kn0 LibSegJb_bvlF2P6.BR LibSegJb_bvlF2P6.PSS LibSegJb_bvlF2P6.NX0 LibSegJb_bvlF2P6.F0 725696 LibSegJb_bvlF2P6.seg_sound_ax fx R M V bvlF2P6_conc_s. Qed.
Definition KS_bvlF2P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P7.regs0 LibSegJb_bvlF2P7.regs_out0).
Lemma KS_bvlF2P7_0_ok : BG.kept_ok 60 LibSegJb_bvlF2P7.regs0 LibSegJb_bvlF2P7.regs_out0 KS_bvlF2P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF2P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF2P7.regs0 LibSegJb_bvlF2P7.regs_out1).
Lemma KS_bvlF2P7_1_ok : BG.kept_ok 60 LibSegJb_bvlF2P7.regs0 LibSegJb_bvlF2P7.regs_out1 KS_bvlF2P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF2P7_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#2v24B#v24#??Na+/+v21#2#8#7???8000#7B#&%+v21#2p#2#40#7#6,,2,5X#;12<0#;138<Y,T,:+v21#2T,;+v21#2W,19&%+v21#2p#2#40#7,4X#;12<0#;12>0Y,1T,;+v21#2W,19&%+v21#2p#2#40#7"%pstring.
Lemma bvlF2P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF2P7_0; KS_bvlF2P7_1] fx R M V bvlF2P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF2P7_0; KS_bvlF2P7_1] LibSegJb_bvlF2P7.regs0 LibSegJb_bvlF2P7.kn0 LibSegJb_bvlF2P7.BR LibSegJb_bvlF2P7.PSS LibSegJb_bvlF2P7.NX0 LibSegJb_bvlF2P7.F0 725696 LibSegJb_bvlF2P7.seg_sound_ax fx R M V bvlF2P7_conc_s. Qed.
Definition KS_bvlF3Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3Z.regs0 LibSegJb_bvlF3Z.regs_out0).
Lemma KS_bvlF3Z_0_ok : BG.kept_ok 60 LibSegJb_bvlF3Z.regs0 LibSegJb_bvlF3Z.regs_out0 KS_bvlF3Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF3Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3Z.regs0 LibSegJb_bvlF3Z.regs_out1).
Lemma KS_bvlF3Z_1_ok : BG.kept_ok 60 LibSegJb_bvlF3Z.regs0 LibSegJb_bvlF3Z.regs_out1 KS_bvlF3Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF3Z_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Ka+/+v21#3#8#7???8000#1,,2,4X#;12>0#;138<Y,T,:+v21#3T,;+v21#3,3X#;12>0#;1300Y,1T,;+v21#3"%pstring.
Lemma bvlF3Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlF3Z_0; KS_bvlF3Z_1] fx R M V bvlF3Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlF3Z_0; KS_bvlF3Z_1] LibSegJb_bvlF3Z.regs0 LibSegJb_bvlF3Z.kn0 LibSegJb_bvlF3Z.BR LibSegJb_bvlF3Z.PSS LibSegJb_bvlF3Z.NX0 LibSegJb_bvlF3Z.F0 725728 LibSegJb_bvlF3Z.seg_sound_ax fx R M V bvlF3Z_conc_s. Qed.
Definition KS_bvlF3P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P1.regs0 LibSegJb_bvlF3P1.regs_out0).
Lemma KS_bvlF3P1_0_ok : BG.kept_ok 60 LibSegJb_bvlF3P1.regs0 LibSegJb_bvlF3P1.regs_out0 KS_bvlF3P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF3P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P1.regs0 LibSegJb_bvlF3P1.regs_out1).
Lemma KS_bvlF3P1_1_ok : BG.kept_ok 60 LibSegJb_bvlF3P1.regs0 LibSegJb_bvlF3P1.regs_out1 KS_bvlF3P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF3P1_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#1B#&%+v21#3p#2#40#7#,,2,5X#;12>0#;138<Y,T,:+v21#3T,;+v21#3T,19#,4X#;12>0#;1300Y,1T,;+v21#3T,19#"%pstring.
Lemma bvlF3P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF3P1_0; KS_bvlF3P1_1] fx R M V bvlF3P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF3P1_0; KS_bvlF3P1_1] LibSegJb_bvlF3P1.regs0 LibSegJb_bvlF3P1.kn0 LibSegJb_bvlF3P1.BR LibSegJb_bvlF3P1.PSS LibSegJb_bvlF3P1.NX0 LibSegJb_bvlF3P1.F0 725728 LibSegJb_bvlF3P1.seg_sound_ax fx R M V bvlF3P1_conc_s. Qed.
Definition KS_bvlF3P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P2.regs0 LibSegJb_bvlF3P2.regs_out0).
Lemma KS_bvlF3P2_0_ok : BG.kept_ok 60 LibSegJb_bvlF3P2.regs0 LibSegJb_bvlF3P2.regs_out0 KS_bvlF3P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF3P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P2.regs0 LibSegJb_bvlF3P2.regs_out1).
Lemma KS_bvlF3P2_1_ok : BG.kept_ok 60 LibSegJb_bvlF3P2.regs0 LibSegJb_bvlF3P2.regs_out1 KS_bvlF3P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF3P2_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#2B#&%+v21#3p#2#40#7#1,,2,5X#;12>0#;138<Y,T,:+v21#3T,;+v21#3W,19&%+v21#3p#2#40#7,4X#;12>0#;1300Y,1T,;+v21#3W,19&%+v21#3p#2#40#7"%pstring.
Lemma bvlF3P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF3P2_0; KS_bvlF3P2_1] fx R M V bvlF3P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF3P2_0; KS_bvlF3P2_1] LibSegJb_bvlF3P2.regs0 LibSegJb_bvlF3P2.kn0 LibSegJb_bvlF3P2.BR LibSegJb_bvlF3P2.PSS LibSegJb_bvlF3P2.NX0 LibSegJb_bvlF3P2.F0 725728 LibSegJb_bvlF3P2.seg_sound_ax fx R M V bvlF3P2_conc_s. Qed.
Definition KS_bvlF3P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P3.regs0 LibSegJb_bvlF3P3.regs_out0).
Lemma KS_bvlF3P3_0_ok : BG.kept_ok 60 LibSegJb_bvlF3P3.regs0 LibSegJb_bvlF3P3.regs_out0 KS_bvlF3P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF3P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P3.regs0 LibSegJb_bvlF3P3.regs_out1).
Lemma KS_bvlF3P3_1_ok : BG.kept_ok 60 LibSegJb_bvlF3P3.regs0 LibSegJb_bvlF3P3.regs_out1 KS_bvlF3P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF3P3_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#3B#&%+v21#3p#2#40#7#2,,2,5X#;12>0#;138<Y,T,:+v21#3T,;+v21#3W,19&%+v21#3p#2#40#7,4X#;12>0#;1300Y,1T,;+v21#3W,19&%+v21#3p#2#40#7"%pstring.
Lemma bvlF3P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF3P3_0; KS_bvlF3P3_1] fx R M V bvlF3P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF3P3_0; KS_bvlF3P3_1] LibSegJb_bvlF3P3.regs0 LibSegJb_bvlF3P3.kn0 LibSegJb_bvlF3P3.BR LibSegJb_bvlF3P3.PSS LibSegJb_bvlF3P3.NX0 LibSegJb_bvlF3P3.F0 725728 LibSegJb_bvlF3P3.seg_sound_ax fx R M V bvlF3P3_conc_s. Qed.
Definition KS_bvlF3P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P4.regs0 LibSegJb_bvlF3P4.regs_out0).
Lemma KS_bvlF3P4_0_ok : BG.kept_ok 60 LibSegJb_bvlF3P4.regs0 LibSegJb_bvlF3P4.regs_out0 KS_bvlF3P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF3P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P4.regs0 LibSegJb_bvlF3P4.regs_out1).
Lemma KS_bvlF3P4_1_ok : BG.kept_ok 60 LibSegJb_bvlF3P4.regs0 LibSegJb_bvlF3P4.regs_out1 KS_bvlF3P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF3P4_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#4B#&%+v21#3p#2#40#7#3,,2,5X#;12>0#;138<Y,T,:+v21#3T,;+v21#3W,19&%+v21#3p#2#40#7,4X#;12>0#;1300Y,1T,;+v21#3W,19&%+v21#3p#2#40#7"%pstring.
Lemma bvlF3P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF3P4_0; KS_bvlF3P4_1] fx R M V bvlF3P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF3P4_0; KS_bvlF3P4_1] LibSegJb_bvlF3P4.regs0 LibSegJb_bvlF3P4.kn0 LibSegJb_bvlF3P4.BR LibSegJb_bvlF3P4.PSS LibSegJb_bvlF3P4.NX0 LibSegJb_bvlF3P4.F0 725728 LibSegJb_bvlF3P4.seg_sound_ax fx R M V bvlF3P4_conc_s. Qed.
Definition KS_bvlF3P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P5.regs0 LibSegJb_bvlF3P5.regs_out0).
Lemma KS_bvlF3P5_0_ok : BG.kept_ok 60 LibSegJb_bvlF3P5.regs0 LibSegJb_bvlF3P5.regs_out0 KS_bvlF3P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF3P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P5.regs0 LibSegJb_bvlF3P5.regs_out1).
Lemma KS_bvlF3P5_1_ok : BG.kept_ok 60 LibSegJb_bvlF3P5.regs0 LibSegJb_bvlF3P5.regs_out1 KS_bvlF3P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF3P5_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#5B#&%+v21#3p#2#40#7#4,,2,5X#;12>0#;138<Y,T,:+v21#3T,;+v21#3W,19&%+v21#3p#2#40#7,4X#;12>0#;1300Y,1T,;+v21#3W,19&%+v21#3p#2#40#7"%pstring.
Lemma bvlF3P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF3P5_0; KS_bvlF3P5_1] fx R M V bvlF3P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF3P5_0; KS_bvlF3P5_1] LibSegJb_bvlF3P5.regs0 LibSegJb_bvlF3P5.kn0 LibSegJb_bvlF3P5.BR LibSegJb_bvlF3P5.PSS LibSegJb_bvlF3P5.NX0 LibSegJb_bvlF3P5.F0 725728 LibSegJb_bvlF3P5.seg_sound_ax fx R M V bvlF3P5_conc_s. Qed.
Definition KS_bvlF3P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P6.regs0 LibSegJb_bvlF3P6.regs_out0).
Lemma KS_bvlF3P6_0_ok : BG.kept_ok 60 LibSegJb_bvlF3P6.regs0 LibSegJb_bvlF3P6.regs_out0 KS_bvlF3P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF3P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P6.regs0 LibSegJb_bvlF3P6.regs_out1).
Lemma KS_bvlF3P6_1_ok : BG.kept_ok 60 LibSegJb_bvlF3P6.regs0 LibSegJb_bvlF3P6.regs_out1 KS_bvlF3P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF3P6_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#6B#&%+v21#3p#2#40#7#5,,2,5X#;12>0#;138<Y,T,:+v21#3T,;+v21#3W,19&%+v21#3p#2#40#7,4X#;12>0#;1300Y,1T,;+v21#3W,19&%+v21#3p#2#40#7"%pstring.
Lemma bvlF3P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF3P6_0; KS_bvlF3P6_1] fx R M V bvlF3P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF3P6_0; KS_bvlF3P6_1] LibSegJb_bvlF3P6.regs0 LibSegJb_bvlF3P6.kn0 LibSegJb_bvlF3P6.BR LibSegJb_bvlF3P6.PSS LibSegJb_bvlF3P6.NX0 LibSegJb_bvlF3P6.F0 725728 LibSegJb_bvlF3P6.seg_sound_ax fx R M V bvlF3P6_conc_s. Qed.
Definition KS_bvlF3P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P7.regs0 LibSegJb_bvlF3P7.regs_out0).
Lemma KS_bvlF3P7_0_ok : BG.kept_ok 60 LibSegJb_bvlF3P7.regs0 LibSegJb_bvlF3P7.regs_out0 KS_bvlF3P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF3P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF3P7.regs0 LibSegJb_bvlF3P7.regs_out1).
Lemma KS_bvlF3P7_1_ok : BG.kept_ok 60 LibSegJb_bvlF3P7.regs0 LibSegJb_bvlF3P7.regs_out1 KS_bvlF3P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF3P7_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#3v24B#v24#??Na+/+v21#3#8#7???8000#7B#&%+v21#3p#2#40#7#6,,2,5X#;12>0#;138<Y,T,:+v21#3T,;+v21#3W,19&%+v21#3p#2#40#7,4X#;12>0#;1300Y,1T,;+v21#3W,19&%+v21#3p#2#40#7"%pstring.
Lemma bvlF3P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF3P7_0; KS_bvlF3P7_1] fx R M V bvlF3P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF3P7_0; KS_bvlF3P7_1] LibSegJb_bvlF3P7.regs0 LibSegJb_bvlF3P7.kn0 LibSegJb_bvlF3P7.BR LibSegJb_bvlF3P7.PSS LibSegJb_bvlF3P7.NX0 LibSegJb_bvlF3P7.F0 725728 LibSegJb_bvlF3P7.seg_sound_ax fx R M V bvlF3P7_conc_s. Qed.
Definition KS_bvlF4Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4Z.regs0 LibSegJb_bvlF4Z.regs_out0).
Lemma KS_bvlF4Z_0_ok : BG.kept_ok 60 LibSegJb_bvlF4Z.regs0 LibSegJb_bvlF4Z.regs_out0 KS_bvlF4Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF4Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4Z.regs0 LibSegJb_bvlF4Z.regs_out1).
Lemma KS_bvlF4Z_1_ok : BG.kept_ok 60 LibSegJb_bvlF4Z.regs0 LibSegJb_bvlF4Z.regs_out1 KS_bvlF4Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF4Z_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Ka+/+v21#4#8#7???8000#1,,2,4X#;1300#;138<Y,T,:+v21#4T,;+v21#4,3X#;1300#;1320Y,1T,;+v21#4"%pstring.
Lemma bvlF4Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlF4Z_0; KS_bvlF4Z_1] fx R M V bvlF4Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlF4Z_0; KS_bvlF4Z_1] LibSegJb_bvlF4Z.regs0 LibSegJb_bvlF4Z.kn0 LibSegJb_bvlF4Z.BR LibSegJb_bvlF4Z.PSS LibSegJb_bvlF4Z.NX0 LibSegJb_bvlF4Z.F0 725760 LibSegJb_bvlF4Z.seg_sound_ax fx R M V bvlF4Z_conc_s. Qed.
Definition KS_bvlF4P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P1.regs0 LibSegJb_bvlF4P1.regs_out0).
Lemma KS_bvlF4P1_0_ok : BG.kept_ok 60 LibSegJb_bvlF4P1.regs0 LibSegJb_bvlF4P1.regs_out0 KS_bvlF4P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF4P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P1.regs0 LibSegJb_bvlF4P1.regs_out1).
Lemma KS_bvlF4P1_1_ok : BG.kept_ok 60 LibSegJb_bvlF4P1.regs0 LibSegJb_bvlF4P1.regs_out1 KS_bvlF4P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF4P1_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#1B#&%+v21#4p#2#40#7#,,2,5X#;1300#;138<Y,T,:+v21#4T,;+v21#4T,19#,4X#;1300#;1320Y,1T,;+v21#4T,19#"%pstring.
Lemma bvlF4P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF4P1_0; KS_bvlF4P1_1] fx R M V bvlF4P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF4P1_0; KS_bvlF4P1_1] LibSegJb_bvlF4P1.regs0 LibSegJb_bvlF4P1.kn0 LibSegJb_bvlF4P1.BR LibSegJb_bvlF4P1.PSS LibSegJb_bvlF4P1.NX0 LibSegJb_bvlF4P1.F0 725760 LibSegJb_bvlF4P1.seg_sound_ax fx R M V bvlF4P1_conc_s. Qed.
Definition KS_bvlF4P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P2.regs0 LibSegJb_bvlF4P2.regs_out0).
Lemma KS_bvlF4P2_0_ok : BG.kept_ok 60 LibSegJb_bvlF4P2.regs0 LibSegJb_bvlF4P2.regs_out0 KS_bvlF4P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF4P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P2.regs0 LibSegJb_bvlF4P2.regs_out1).
Lemma KS_bvlF4P2_1_ok : BG.kept_ok 60 LibSegJb_bvlF4P2.regs0 LibSegJb_bvlF4P2.regs_out1 KS_bvlF4P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF4P2_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#2B#&%+v21#4p#2#40#7#1,,2,5X#;1300#;138<Y,T,:+v21#4T,;+v21#4W,19&%+v21#4p#2#40#7,4X#;1300#;1320Y,1T,;+v21#4W,19&%+v21#4p#2#40#7"%pstring.
Lemma bvlF4P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF4P2_0; KS_bvlF4P2_1] fx R M V bvlF4P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF4P2_0; KS_bvlF4P2_1] LibSegJb_bvlF4P2.regs0 LibSegJb_bvlF4P2.kn0 LibSegJb_bvlF4P2.BR LibSegJb_bvlF4P2.PSS LibSegJb_bvlF4P2.NX0 LibSegJb_bvlF4P2.F0 725760 LibSegJb_bvlF4P2.seg_sound_ax fx R M V bvlF4P2_conc_s. Qed.
Definition KS_bvlF4P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P3.regs0 LibSegJb_bvlF4P3.regs_out0).
Lemma KS_bvlF4P3_0_ok : BG.kept_ok 60 LibSegJb_bvlF4P3.regs0 LibSegJb_bvlF4P3.regs_out0 KS_bvlF4P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF4P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P3.regs0 LibSegJb_bvlF4P3.regs_out1).
Lemma KS_bvlF4P3_1_ok : BG.kept_ok 60 LibSegJb_bvlF4P3.regs0 LibSegJb_bvlF4P3.regs_out1 KS_bvlF4P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF4P3_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#3B#&%+v21#4p#2#40#7#2,,2,5X#;1300#;138<Y,T,:+v21#4T,;+v21#4W,19&%+v21#4p#2#40#7,4X#;1300#;1320Y,1T,;+v21#4W,19&%+v21#4p#2#40#7"%pstring.
Lemma bvlF4P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF4P3_0; KS_bvlF4P3_1] fx R M V bvlF4P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF4P3_0; KS_bvlF4P3_1] LibSegJb_bvlF4P3.regs0 LibSegJb_bvlF4P3.kn0 LibSegJb_bvlF4P3.BR LibSegJb_bvlF4P3.PSS LibSegJb_bvlF4P3.NX0 LibSegJb_bvlF4P3.F0 725760 LibSegJb_bvlF4P3.seg_sound_ax fx R M V bvlF4P3_conc_s. Qed.
Definition KS_bvlF4P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P4.regs0 LibSegJb_bvlF4P4.regs_out0).
Lemma KS_bvlF4P4_0_ok : BG.kept_ok 60 LibSegJb_bvlF4P4.regs0 LibSegJb_bvlF4P4.regs_out0 KS_bvlF4P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF4P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P4.regs0 LibSegJb_bvlF4P4.regs_out1).
Lemma KS_bvlF4P4_1_ok : BG.kept_ok 60 LibSegJb_bvlF4P4.regs0 LibSegJb_bvlF4P4.regs_out1 KS_bvlF4P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF4P4_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#4B#&%+v21#4p#2#40#7#3,,2,5X#;1300#;138<Y,T,:+v21#4T,;+v21#4W,19&%+v21#4p#2#40#7,4X#;1300#;1320Y,1T,;+v21#4W,19&%+v21#4p#2#40#7"%pstring.
Lemma bvlF4P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF4P4_0; KS_bvlF4P4_1] fx R M V bvlF4P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF4P4_0; KS_bvlF4P4_1] LibSegJb_bvlF4P4.regs0 LibSegJb_bvlF4P4.kn0 LibSegJb_bvlF4P4.BR LibSegJb_bvlF4P4.PSS LibSegJb_bvlF4P4.NX0 LibSegJb_bvlF4P4.F0 725760 LibSegJb_bvlF4P4.seg_sound_ax fx R M V bvlF4P4_conc_s. Qed.
Definition KS_bvlF4P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P5.regs0 LibSegJb_bvlF4P5.regs_out0).
Lemma KS_bvlF4P5_0_ok : BG.kept_ok 60 LibSegJb_bvlF4P5.regs0 LibSegJb_bvlF4P5.regs_out0 KS_bvlF4P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF4P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P5.regs0 LibSegJb_bvlF4P5.regs_out1).
Lemma KS_bvlF4P5_1_ok : BG.kept_ok 60 LibSegJb_bvlF4P5.regs0 LibSegJb_bvlF4P5.regs_out1 KS_bvlF4P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF4P5_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#5B#&%+v21#4p#2#40#7#4,,2,5X#;1300#;138<Y,T,:+v21#4T,;+v21#4W,19&%+v21#4p#2#40#7,4X#;1300#;1320Y,1T,;+v21#4W,19&%+v21#4p#2#40#7"%pstring.
Lemma bvlF4P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF4P5_0; KS_bvlF4P5_1] fx R M V bvlF4P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF4P5_0; KS_bvlF4P5_1] LibSegJb_bvlF4P5.regs0 LibSegJb_bvlF4P5.kn0 LibSegJb_bvlF4P5.BR LibSegJb_bvlF4P5.PSS LibSegJb_bvlF4P5.NX0 LibSegJb_bvlF4P5.F0 725760 LibSegJb_bvlF4P5.seg_sound_ax fx R M V bvlF4P5_conc_s. Qed.
Definition KS_bvlF4P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P6.regs0 LibSegJb_bvlF4P6.regs_out0).
Lemma KS_bvlF4P6_0_ok : BG.kept_ok 60 LibSegJb_bvlF4P6.regs0 LibSegJb_bvlF4P6.regs_out0 KS_bvlF4P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF4P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P6.regs0 LibSegJb_bvlF4P6.regs_out1).
Lemma KS_bvlF4P6_1_ok : BG.kept_ok 60 LibSegJb_bvlF4P6.regs0 LibSegJb_bvlF4P6.regs_out1 KS_bvlF4P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF4P6_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#6B#&%+v21#4p#2#40#7#5,,2,5X#;1300#;138<Y,T,:+v21#4T,;+v21#4W,19&%+v21#4p#2#40#7,4X#;1300#;1320Y,1T,;+v21#4W,19&%+v21#4p#2#40#7"%pstring.
Lemma bvlF4P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF4P6_0; KS_bvlF4P6_1] fx R M V bvlF4P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF4P6_0; KS_bvlF4P6_1] LibSegJb_bvlF4P6.regs0 LibSegJb_bvlF4P6.kn0 LibSegJb_bvlF4P6.BR LibSegJb_bvlF4P6.PSS LibSegJb_bvlF4P6.NX0 LibSegJb_bvlF4P6.F0 725760 LibSegJb_bvlF4P6.seg_sound_ax fx R M V bvlF4P6_conc_s. Qed.
Definition KS_bvlF4P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P7.regs0 LibSegJb_bvlF4P7.regs_out0).
Lemma KS_bvlF4P7_0_ok : BG.kept_ok 60 LibSegJb_bvlF4P7.regs0 LibSegJb_bvlF4P7.regs_out0 KS_bvlF4P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF4P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF4P7.regs0 LibSegJb_bvlF4P7.regs_out1).
Lemma KS_bvlF4P7_1_ok : BG.kept_ok 60 LibSegJb_bvlF4P7.regs0 LibSegJb_bvlF4P7.regs_out1 KS_bvlF4P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF4P7_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#4v24B#v24#??Na+/+v21#4#8#7???8000#7B#&%+v21#4p#2#40#7#6,,2,5X#;1300#;138<Y,T,:+v21#4T,;+v21#4W,19&%+v21#4p#2#40#7,4X#;1300#;1320Y,1T,;+v21#4W,19&%+v21#4p#2#40#7"%pstring.
Lemma bvlF4P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF4P7_0; KS_bvlF4P7_1] fx R M V bvlF4P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF4P7_0; KS_bvlF4P7_1] LibSegJb_bvlF4P7.regs0 LibSegJb_bvlF4P7.kn0 LibSegJb_bvlF4P7.BR LibSegJb_bvlF4P7.PSS LibSegJb_bvlF4P7.NX0 LibSegJb_bvlF4P7.F0 725760 LibSegJb_bvlF4P7.seg_sound_ax fx R M V bvlF4P7_conc_s. Qed.
End PMBVALP2.
