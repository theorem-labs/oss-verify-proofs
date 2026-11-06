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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bvlF5Z LibSegJb_bvlF5P1 LibSegJb_bvlF5P2 LibSegJb_bvlF5P3 LibSegJb_bvlF5P4 LibSegJb_bvlF5P5 LibSegJb_bvlF5P6 LibSegJb_bvlF5P7 LibSegJb_bvlF6Z LibSegJb_bvlF6P1 LibSegJb_bvlF6P2 LibSegJb_bvlF6P3 LibSegJb_bvlF6P4 LibSegJb_bvlF6P5 LibSegJb_bvlF6P6 LibSegJb_bvlF6P7 LibSegJb_bvlF7Z LibSegJb_bvlF7P1 LibSegJb_bvlF7P2 LibSegJb_bvlF7P3 LibSegJb_bvlF7P4 LibSegJb_bvlF7P5 LibSegJb_bvlF7P6 LibSegJb_bvlF7P7.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBVALP3.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bvlF5Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5Z.regs0 LibSegJb_bvlF5Z.regs_out0).
Lemma KS_bvlF5Z_0_ok : BG.kept_ok 60 LibSegJb_bvlF5Z.regs0 LibSegJb_bvlF5Z.regs_out0 KS_bvlF5Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF5Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5Z.regs0 LibSegJb_bvlF5Z.regs_out1).
Lemma KS_bvlF5Z_1_ok : BG.kept_ok 60 LibSegJb_bvlF5Z.regs0 LibSegJb_bvlF5Z.regs_out1 KS_bvlF5Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bvlF5Z_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Ka+/+v21#5#8#7???8000#1,,2,4X#;1320#;138<Y,T,:+v21#5T,;+v21#5,3X#;1320#;1340Y,1T,;+v21#5"%pstring.
Lemma bvlF5Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlF5Z_0; KS_bvlF5Z_1] fx R M V bvlF5Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlF5Z_0; KS_bvlF5Z_1] LibSegJb_bvlF5Z.regs0 LibSegJb_bvlF5Z.kn0 LibSegJb_bvlF5Z.BR LibSegJb_bvlF5Z.PSS LibSegJb_bvlF5Z.NX0 LibSegJb_bvlF5Z.F0 725792 LibSegJb_bvlF5Z.seg_sound_ax fx R M V bvlF5Z_conc_s. Qed.
Definition KS_bvlF5P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P1.regs0 LibSegJb_bvlF5P1.regs_out0).
Lemma KS_bvlF5P1_0_ok : BG.kept_ok 60 LibSegJb_bvlF5P1.regs0 LibSegJb_bvlF5P1.regs_out0 KS_bvlF5P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF5P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P1.regs0 LibSegJb_bvlF5P1.regs_out1).
Lemma KS_bvlF5P1_1_ok : BG.kept_ok 60 LibSegJb_bvlF5P1.regs0 LibSegJb_bvlF5P1.regs_out1 KS_bvlF5P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF5P1_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#1B#&%+v21#5p#2#40#7#,,2,5X#;1320#;138<Y,T,:+v21#5T,;+v21#5T,19#,4X#;1320#;1340Y,1T,;+v21#5T,19#"%pstring.
Lemma bvlF5P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF5P1_0; KS_bvlF5P1_1] fx R M V bvlF5P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF5P1_0; KS_bvlF5P1_1] LibSegJb_bvlF5P1.regs0 LibSegJb_bvlF5P1.kn0 LibSegJb_bvlF5P1.BR LibSegJb_bvlF5P1.PSS LibSegJb_bvlF5P1.NX0 LibSegJb_bvlF5P1.F0 725792 LibSegJb_bvlF5P1.seg_sound_ax fx R M V bvlF5P1_conc_s. Qed.
Definition KS_bvlF5P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P2.regs0 LibSegJb_bvlF5P2.regs_out0).
Lemma KS_bvlF5P2_0_ok : BG.kept_ok 60 LibSegJb_bvlF5P2.regs0 LibSegJb_bvlF5P2.regs_out0 KS_bvlF5P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF5P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P2.regs0 LibSegJb_bvlF5P2.regs_out1).
Lemma KS_bvlF5P2_1_ok : BG.kept_ok 60 LibSegJb_bvlF5P2.regs0 LibSegJb_bvlF5P2.regs_out1 KS_bvlF5P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF5P2_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#2B#&%+v21#5p#2#40#7#1,,2,5X#;1320#;138<Y,T,:+v21#5T,;+v21#5W,19&%+v21#5p#2#40#7,4X#;1320#;1340Y,1T,;+v21#5W,19&%+v21#5p#2#40#7"%pstring.
Lemma bvlF5P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF5P2_0; KS_bvlF5P2_1] fx R M V bvlF5P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF5P2_0; KS_bvlF5P2_1] LibSegJb_bvlF5P2.regs0 LibSegJb_bvlF5P2.kn0 LibSegJb_bvlF5P2.BR LibSegJb_bvlF5P2.PSS LibSegJb_bvlF5P2.NX0 LibSegJb_bvlF5P2.F0 725792 LibSegJb_bvlF5P2.seg_sound_ax fx R M V bvlF5P2_conc_s. Qed.
Definition KS_bvlF5P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P3.regs0 LibSegJb_bvlF5P3.regs_out0).
Lemma KS_bvlF5P3_0_ok : BG.kept_ok 60 LibSegJb_bvlF5P3.regs0 LibSegJb_bvlF5P3.regs_out0 KS_bvlF5P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF5P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P3.regs0 LibSegJb_bvlF5P3.regs_out1).
Lemma KS_bvlF5P3_1_ok : BG.kept_ok 60 LibSegJb_bvlF5P3.regs0 LibSegJb_bvlF5P3.regs_out1 KS_bvlF5P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF5P3_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#3B#&%+v21#5p#2#40#7#2,,2,5X#;1320#;138<Y,T,:+v21#5T,;+v21#5W,19&%+v21#5p#2#40#7,4X#;1320#;1340Y,1T,;+v21#5W,19&%+v21#5p#2#40#7"%pstring.
Lemma bvlF5P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF5P3_0; KS_bvlF5P3_1] fx R M V bvlF5P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF5P3_0; KS_bvlF5P3_1] LibSegJb_bvlF5P3.regs0 LibSegJb_bvlF5P3.kn0 LibSegJb_bvlF5P3.BR LibSegJb_bvlF5P3.PSS LibSegJb_bvlF5P3.NX0 LibSegJb_bvlF5P3.F0 725792 LibSegJb_bvlF5P3.seg_sound_ax fx R M V bvlF5P3_conc_s. Qed.
Definition KS_bvlF5P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P4.regs0 LibSegJb_bvlF5P4.regs_out0).
Lemma KS_bvlF5P4_0_ok : BG.kept_ok 60 LibSegJb_bvlF5P4.regs0 LibSegJb_bvlF5P4.regs_out0 KS_bvlF5P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF5P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P4.regs0 LibSegJb_bvlF5P4.regs_out1).
Lemma KS_bvlF5P4_1_ok : BG.kept_ok 60 LibSegJb_bvlF5P4.regs0 LibSegJb_bvlF5P4.regs_out1 KS_bvlF5P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF5P4_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#4B#&%+v21#5p#2#40#7#3,,2,5X#;1320#;138<Y,T,:+v21#5T,;+v21#5W,19&%+v21#5p#2#40#7,4X#;1320#;1340Y,1T,;+v21#5W,19&%+v21#5p#2#40#7"%pstring.
Lemma bvlF5P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF5P4_0; KS_bvlF5P4_1] fx R M V bvlF5P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF5P4_0; KS_bvlF5P4_1] LibSegJb_bvlF5P4.regs0 LibSegJb_bvlF5P4.kn0 LibSegJb_bvlF5P4.BR LibSegJb_bvlF5P4.PSS LibSegJb_bvlF5P4.NX0 LibSegJb_bvlF5P4.F0 725792 LibSegJb_bvlF5P4.seg_sound_ax fx R M V bvlF5P4_conc_s. Qed.
Definition KS_bvlF5P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P5.regs0 LibSegJb_bvlF5P5.regs_out0).
Lemma KS_bvlF5P5_0_ok : BG.kept_ok 60 LibSegJb_bvlF5P5.regs0 LibSegJb_bvlF5P5.regs_out0 KS_bvlF5P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF5P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P5.regs0 LibSegJb_bvlF5P5.regs_out1).
Lemma KS_bvlF5P5_1_ok : BG.kept_ok 60 LibSegJb_bvlF5P5.regs0 LibSegJb_bvlF5P5.regs_out1 KS_bvlF5P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF5P5_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#5B#&%+v21#5p#2#40#7#4,,2,5X#;1320#;138<Y,T,:+v21#5T,;+v21#5W,19&%+v21#5p#2#40#7,4X#;1320#;1340Y,1T,;+v21#5W,19&%+v21#5p#2#40#7"%pstring.
Lemma bvlF5P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF5P5_0; KS_bvlF5P5_1] fx R M V bvlF5P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF5P5_0; KS_bvlF5P5_1] LibSegJb_bvlF5P5.regs0 LibSegJb_bvlF5P5.kn0 LibSegJb_bvlF5P5.BR LibSegJb_bvlF5P5.PSS LibSegJb_bvlF5P5.NX0 LibSegJb_bvlF5P5.F0 725792 LibSegJb_bvlF5P5.seg_sound_ax fx R M V bvlF5P5_conc_s. Qed.
Definition KS_bvlF5P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P6.regs0 LibSegJb_bvlF5P6.regs_out0).
Lemma KS_bvlF5P6_0_ok : BG.kept_ok 60 LibSegJb_bvlF5P6.regs0 LibSegJb_bvlF5P6.regs_out0 KS_bvlF5P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF5P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P6.regs0 LibSegJb_bvlF5P6.regs_out1).
Lemma KS_bvlF5P6_1_ok : BG.kept_ok 60 LibSegJb_bvlF5P6.regs0 LibSegJb_bvlF5P6.regs_out1 KS_bvlF5P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF5P6_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#6B#&%+v21#5p#2#40#7#5,,2,5X#;1320#;138<Y,T,:+v21#5T,;+v21#5W,19&%+v21#5p#2#40#7,4X#;1320#;1340Y,1T,;+v21#5W,19&%+v21#5p#2#40#7"%pstring.
Lemma bvlF5P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF5P6_0; KS_bvlF5P6_1] fx R M V bvlF5P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF5P6_0; KS_bvlF5P6_1] LibSegJb_bvlF5P6.regs0 LibSegJb_bvlF5P6.kn0 LibSegJb_bvlF5P6.BR LibSegJb_bvlF5P6.PSS LibSegJb_bvlF5P6.NX0 LibSegJb_bvlF5P6.F0 725792 LibSegJb_bvlF5P6.seg_sound_ax fx R M V bvlF5P6_conc_s. Qed.
Definition KS_bvlF5P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P7.regs0 LibSegJb_bvlF5P7.regs_out0).
Lemma KS_bvlF5P7_0_ok : BG.kept_ok 60 LibSegJb_bvlF5P7.regs0 LibSegJb_bvlF5P7.regs_out0 KS_bvlF5P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF5P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF5P7.regs0 LibSegJb_bvlF5P7.regs_out1).
Lemma KS_bvlF5P7_1_ok : BG.kept_ok 60 LibSegJb_bvlF5P7.regs0 LibSegJb_bvlF5P7.regs_out1 KS_bvlF5P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF5P7_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#5v24B#v24#??Na+/+v21#5#8#7???8000#7B#&%+v21#5p#2#40#7#6,,2,5X#;1320#;138<Y,T,:+v21#5T,;+v21#5W,19&%+v21#5p#2#40#7,4X#;1320#;1340Y,1T,;+v21#5W,19&%+v21#5p#2#40#7"%pstring.
Lemma bvlF5P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF5P7_0; KS_bvlF5P7_1] fx R M V bvlF5P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF5P7_0; KS_bvlF5P7_1] LibSegJb_bvlF5P7.regs0 LibSegJb_bvlF5P7.kn0 LibSegJb_bvlF5P7.BR LibSegJb_bvlF5P7.PSS LibSegJb_bvlF5P7.NX0 LibSegJb_bvlF5P7.F0 725792 LibSegJb_bvlF5P7.seg_sound_ax fx R M V bvlF5P7_conc_s. Qed.
Definition KS_bvlF6Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6Z.regs0 LibSegJb_bvlF6Z.regs_out0).
Lemma KS_bvlF6Z_0_ok : BG.kept_ok 60 LibSegJb_bvlF6Z.regs0 LibSegJb_bvlF6Z.regs_out0 KS_bvlF6Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF6Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6Z.regs0 LibSegJb_bvlF6Z.regs_out1).
Lemma KS_bvlF6Z_1_ok : BG.kept_ok 60 LibSegJb_bvlF6Z.regs0 LibSegJb_bvlF6Z.regs_out1 KS_bvlF6Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF6Z_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Ka+/+v21#6#8#7???8000#1,,2,4X#;1340#;138<Y,T,:+v21#6T,;+v21#6,3X#;1340#;1360Y,1T,;+v21#6"%pstring.
Lemma bvlF6Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlF6Z_0; KS_bvlF6Z_1] fx R M V bvlF6Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlF6Z_0; KS_bvlF6Z_1] LibSegJb_bvlF6Z.regs0 LibSegJb_bvlF6Z.kn0 LibSegJb_bvlF6Z.BR LibSegJb_bvlF6Z.PSS LibSegJb_bvlF6Z.NX0 LibSegJb_bvlF6Z.F0 725824 LibSegJb_bvlF6Z.seg_sound_ax fx R M V bvlF6Z_conc_s. Qed.
Definition KS_bvlF6P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P1.regs0 LibSegJb_bvlF6P1.regs_out0).
Lemma KS_bvlF6P1_0_ok : BG.kept_ok 60 LibSegJb_bvlF6P1.regs0 LibSegJb_bvlF6P1.regs_out0 KS_bvlF6P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF6P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P1.regs0 LibSegJb_bvlF6P1.regs_out1).
Lemma KS_bvlF6P1_1_ok : BG.kept_ok 60 LibSegJb_bvlF6P1.regs0 LibSegJb_bvlF6P1.regs_out1 KS_bvlF6P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF6P1_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#1B#&%+v21#6p#2#40#7#,,2,5X#;1340#;138<Y,T,:+v21#6T,;+v21#6T,19#,4X#;1340#;1360Y,1T,;+v21#6T,19#"%pstring.
Lemma bvlF6P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF6P1_0; KS_bvlF6P1_1] fx R M V bvlF6P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF6P1_0; KS_bvlF6P1_1] LibSegJb_bvlF6P1.regs0 LibSegJb_bvlF6P1.kn0 LibSegJb_bvlF6P1.BR LibSegJb_bvlF6P1.PSS LibSegJb_bvlF6P1.NX0 LibSegJb_bvlF6P1.F0 725824 LibSegJb_bvlF6P1.seg_sound_ax fx R M V bvlF6P1_conc_s. Qed.
Definition KS_bvlF6P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P2.regs0 LibSegJb_bvlF6P2.regs_out0).
Lemma KS_bvlF6P2_0_ok : BG.kept_ok 60 LibSegJb_bvlF6P2.regs0 LibSegJb_bvlF6P2.regs_out0 KS_bvlF6P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF6P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P2.regs0 LibSegJb_bvlF6P2.regs_out1).
Lemma KS_bvlF6P2_1_ok : BG.kept_ok 60 LibSegJb_bvlF6P2.regs0 LibSegJb_bvlF6P2.regs_out1 KS_bvlF6P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF6P2_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#2B#&%+v21#6p#2#40#7#1,,2,5X#;1340#;138<Y,T,:+v21#6T,;+v21#6W,19&%+v21#6p#2#40#7,4X#;1340#;1360Y,1T,;+v21#6W,19&%+v21#6p#2#40#7"%pstring.
Lemma bvlF6P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF6P2_0; KS_bvlF6P2_1] fx R M V bvlF6P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF6P2_0; KS_bvlF6P2_1] LibSegJb_bvlF6P2.regs0 LibSegJb_bvlF6P2.kn0 LibSegJb_bvlF6P2.BR LibSegJb_bvlF6P2.PSS LibSegJb_bvlF6P2.NX0 LibSegJb_bvlF6P2.F0 725824 LibSegJb_bvlF6P2.seg_sound_ax fx R M V bvlF6P2_conc_s. Qed.
Definition KS_bvlF6P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P3.regs0 LibSegJb_bvlF6P3.regs_out0).
Lemma KS_bvlF6P3_0_ok : BG.kept_ok 60 LibSegJb_bvlF6P3.regs0 LibSegJb_bvlF6P3.regs_out0 KS_bvlF6P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF6P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P3.regs0 LibSegJb_bvlF6P3.regs_out1).
Lemma KS_bvlF6P3_1_ok : BG.kept_ok 60 LibSegJb_bvlF6P3.regs0 LibSegJb_bvlF6P3.regs_out1 KS_bvlF6P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF6P3_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#3B#&%+v21#6p#2#40#7#2,,2,5X#;1340#;138<Y,T,:+v21#6T,;+v21#6W,19&%+v21#6p#2#40#7,4X#;1340#;1360Y,1T,;+v21#6W,19&%+v21#6p#2#40#7"%pstring.
Lemma bvlF6P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF6P3_0; KS_bvlF6P3_1] fx R M V bvlF6P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF6P3_0; KS_bvlF6P3_1] LibSegJb_bvlF6P3.regs0 LibSegJb_bvlF6P3.kn0 LibSegJb_bvlF6P3.BR LibSegJb_bvlF6P3.PSS LibSegJb_bvlF6P3.NX0 LibSegJb_bvlF6P3.F0 725824 LibSegJb_bvlF6P3.seg_sound_ax fx R M V bvlF6P3_conc_s. Qed.
Definition KS_bvlF6P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P4.regs0 LibSegJb_bvlF6P4.regs_out0).
Lemma KS_bvlF6P4_0_ok : BG.kept_ok 60 LibSegJb_bvlF6P4.regs0 LibSegJb_bvlF6P4.regs_out0 KS_bvlF6P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF6P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P4.regs0 LibSegJb_bvlF6P4.regs_out1).
Lemma KS_bvlF6P4_1_ok : BG.kept_ok 60 LibSegJb_bvlF6P4.regs0 LibSegJb_bvlF6P4.regs_out1 KS_bvlF6P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF6P4_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#4B#&%+v21#6p#2#40#7#3,,2,5X#;1340#;138<Y,T,:+v21#6T,;+v21#6W,19&%+v21#6p#2#40#7,4X#;1340#;1360Y,1T,;+v21#6W,19&%+v21#6p#2#40#7"%pstring.
Lemma bvlF6P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF6P4_0; KS_bvlF6P4_1] fx R M V bvlF6P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF6P4_0; KS_bvlF6P4_1] LibSegJb_bvlF6P4.regs0 LibSegJb_bvlF6P4.kn0 LibSegJb_bvlF6P4.BR LibSegJb_bvlF6P4.PSS LibSegJb_bvlF6P4.NX0 LibSegJb_bvlF6P4.F0 725824 LibSegJb_bvlF6P4.seg_sound_ax fx R M V bvlF6P4_conc_s. Qed.
Definition KS_bvlF6P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P5.regs0 LibSegJb_bvlF6P5.regs_out0).
Lemma KS_bvlF6P5_0_ok : BG.kept_ok 60 LibSegJb_bvlF6P5.regs0 LibSegJb_bvlF6P5.regs_out0 KS_bvlF6P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF6P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P5.regs0 LibSegJb_bvlF6P5.regs_out1).
Lemma KS_bvlF6P5_1_ok : BG.kept_ok 60 LibSegJb_bvlF6P5.regs0 LibSegJb_bvlF6P5.regs_out1 KS_bvlF6P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF6P5_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#5B#&%+v21#6p#2#40#7#4,,2,5X#;1340#;138<Y,T,:+v21#6T,;+v21#6W,19&%+v21#6p#2#40#7,4X#;1340#;1360Y,1T,;+v21#6W,19&%+v21#6p#2#40#7"%pstring.
Lemma bvlF6P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF6P5_0; KS_bvlF6P5_1] fx R M V bvlF6P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF6P5_0; KS_bvlF6P5_1] LibSegJb_bvlF6P5.regs0 LibSegJb_bvlF6P5.kn0 LibSegJb_bvlF6P5.BR LibSegJb_bvlF6P5.PSS LibSegJb_bvlF6P5.NX0 LibSegJb_bvlF6P5.F0 725824 LibSegJb_bvlF6P5.seg_sound_ax fx R M V bvlF6P5_conc_s. Qed.
Definition KS_bvlF6P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P6.regs0 LibSegJb_bvlF6P6.regs_out0).
Lemma KS_bvlF6P6_0_ok : BG.kept_ok 60 LibSegJb_bvlF6P6.regs0 LibSegJb_bvlF6P6.regs_out0 KS_bvlF6P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF6P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P6.regs0 LibSegJb_bvlF6P6.regs_out1).
Lemma KS_bvlF6P6_1_ok : BG.kept_ok 60 LibSegJb_bvlF6P6.regs0 LibSegJb_bvlF6P6.regs_out1 KS_bvlF6P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF6P6_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#6B#&%+v21#6p#2#40#7#5,,2,5X#;1340#;138<Y,T,:+v21#6T,;+v21#6W,19&%+v21#6p#2#40#7,4X#;1340#;1360Y,1T,;+v21#6W,19&%+v21#6p#2#40#7"%pstring.
Lemma bvlF6P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF6P6_0; KS_bvlF6P6_1] fx R M V bvlF6P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF6P6_0; KS_bvlF6P6_1] LibSegJb_bvlF6P6.regs0 LibSegJb_bvlF6P6.kn0 LibSegJb_bvlF6P6.BR LibSegJb_bvlF6P6.PSS LibSegJb_bvlF6P6.NX0 LibSegJb_bvlF6P6.F0 725824 LibSegJb_bvlF6P6.seg_sound_ax fx R M V bvlF6P6_conc_s. Qed.
Definition KS_bvlF6P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P7.regs0 LibSegJb_bvlF6P7.regs_out0).
Lemma KS_bvlF6P7_0_ok : BG.kept_ok 60 LibSegJb_bvlF6P7.regs0 LibSegJb_bvlF6P7.regs_out0 KS_bvlF6P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF6P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF6P7.regs0 LibSegJb_bvlF6P7.regs_out1).
Lemma KS_bvlF6P7_1_ok : BG.kept_ok 60 LibSegJb_bvlF6P7.regs0 LibSegJb_bvlF6P7.regs_out1 KS_bvlF6P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF6P7_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#6v24B#v24#??Na+/+v21#6#8#7???8000#7B#&%+v21#6p#2#40#7#6,,2,5X#;1340#;138<Y,T,:+v21#6T,;+v21#6W,19&%+v21#6p#2#40#7,4X#;1340#;1360Y,1T,;+v21#6W,19&%+v21#6p#2#40#7"%pstring.
Lemma bvlF6P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF6P7_0; KS_bvlF6P7_1] fx R M V bvlF6P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF6P7_0; KS_bvlF6P7_1] LibSegJb_bvlF6P7.regs0 LibSegJb_bvlF6P7.kn0 LibSegJb_bvlF6P7.BR LibSegJb_bvlF6P7.PSS LibSegJb_bvlF6P7.NX0 LibSegJb_bvlF6P7.F0 725824 LibSegJb_bvlF6P7.seg_sound_ax fx R M V bvlF6P7_conc_s. Qed.
Definition KS_bvlF7Z_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7Z.regs0 LibSegJb_bvlF7Z.regs_out0).
Lemma KS_bvlF7Z_0_ok : BG.kept_ok 60 LibSegJb_bvlF7Z.regs0 LibSegJb_bvlF7Z.regs_out0 KS_bvlF7Z_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF7Z_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7Z.regs0 LibSegJb_bvlF7Z.regs_out1).
Lemma KS_bvlF7Z_1_ok : BG.kept_ok 60 LibSegJb_bvlF7Z.regs0 LibSegJb_bvlF7Z.regs_out1 KS_bvlF7Z_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF7Z_conc_s := ",21A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Ka+/+v21#7#8#7???8000#1,,2,4X#;1360#;138<Y,T,:+v21#7T,;+v21#7,4X#;1360#;14:8Y,1T,;+v21#7T,1:+v21#8"%pstring.
Lemma bvlF7Z_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvlF7Z_0; KS_bvlF7Z_1] fx R M V bvlF7Z_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvlF7Z_0; KS_bvlF7Z_1] LibSegJb_bvlF7Z.regs0 LibSegJb_bvlF7Z.kn0 LibSegJb_bvlF7Z.BR LibSegJb_bvlF7Z.PSS LibSegJb_bvlF7Z.NX0 LibSegJb_bvlF7Z.F0 725856 LibSegJb_bvlF7Z.seg_sound_ax fx R M V bvlF7Z_conc_s. Qed.
Definition KS_bvlF7P1_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P1.regs0 LibSegJb_bvlF7P1.regs_out0).
Lemma KS_bvlF7P1_0_ok : BG.kept_ok 60 LibSegJb_bvlF7P1.regs0 LibSegJb_bvlF7P1.regs_out0 KS_bvlF7P1_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF7P1_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P1.regs0 LibSegJb_bvlF7P1.regs_out1).
Lemma KS_bvlF7P1_1_ok : BG.kept_ok 60 LibSegJb_bvlF7P1.regs0 LibSegJb_bvlF7P1.regs_out1 KS_bvlF7P1_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF7P1_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#1B#&%+v21#7p#2#40#7#,,2,5X#;1360#;138<Y,T,:+v21#7T,;+v21#7T,19#,5X#;1360#;14:8Y,1T,;+v21#7T,19#T,1:+v21#8"%pstring.
Lemma bvlF7P1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF7P1_0; KS_bvlF7P1_1] fx R M V bvlF7P1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF7P1_0; KS_bvlF7P1_1] LibSegJb_bvlF7P1.regs0 LibSegJb_bvlF7P1.kn0 LibSegJb_bvlF7P1.BR LibSegJb_bvlF7P1.PSS LibSegJb_bvlF7P1.NX0 LibSegJb_bvlF7P1.F0 725856 LibSegJb_bvlF7P1.seg_sound_ax fx R M V bvlF7P1_conc_s. Qed.
Definition KS_bvlF7P2_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P2.regs0 LibSegJb_bvlF7P2.regs_out0).
Lemma KS_bvlF7P2_0_ok : BG.kept_ok 60 LibSegJb_bvlF7P2.regs0 LibSegJb_bvlF7P2.regs_out0 KS_bvlF7P2_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF7P2_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P2.regs0 LibSegJb_bvlF7P2.regs_out1).
Lemma KS_bvlF7P2_1_ok : BG.kept_ok 60 LibSegJb_bvlF7P2.regs0 LibSegJb_bvlF7P2.regs_out1 KS_bvlF7P2_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF7P2_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#2B#&%+v21#7p#2#40#7#1,,2,5X#;1360#;138<Y,T,:+v21#7T,;+v21#7W,19&%+v21#7p#2#40#7,5X#;1360#;14:8Y,1T,;+v21#7W,19&%+v21#7p#2#40#7T,1:+v21#8"%pstring.
Lemma bvlF7P2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF7P2_0; KS_bvlF7P2_1] fx R M V bvlF7P2_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF7P2_0; KS_bvlF7P2_1] LibSegJb_bvlF7P2.regs0 LibSegJb_bvlF7P2.kn0 LibSegJb_bvlF7P2.BR LibSegJb_bvlF7P2.PSS LibSegJb_bvlF7P2.NX0 LibSegJb_bvlF7P2.F0 725856 LibSegJb_bvlF7P2.seg_sound_ax fx R M V bvlF7P2_conc_s. Qed.
Definition KS_bvlF7P3_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P3.regs0 LibSegJb_bvlF7P3.regs_out0).
Lemma KS_bvlF7P3_0_ok : BG.kept_ok 60 LibSegJb_bvlF7P3.regs0 LibSegJb_bvlF7P3.regs_out0 KS_bvlF7P3_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF7P3_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P3.regs0 LibSegJb_bvlF7P3.regs_out1).
Lemma KS_bvlF7P3_1_ok : BG.kept_ok 60 LibSegJb_bvlF7P3.regs0 LibSegJb_bvlF7P3.regs_out1 KS_bvlF7P3_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF7P3_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#3B#&%+v21#7p#2#40#7#2,,2,5X#;1360#;138<Y,T,:+v21#7T,;+v21#7W,19&%+v21#7p#2#40#7,5X#;1360#;14:8Y,1T,;+v21#7W,19&%+v21#7p#2#40#7T,1:+v21#8"%pstring.
Lemma bvlF7P3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF7P3_0; KS_bvlF7P3_1] fx R M V bvlF7P3_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF7P3_0; KS_bvlF7P3_1] LibSegJb_bvlF7P3.regs0 LibSegJb_bvlF7P3.kn0 LibSegJb_bvlF7P3.BR LibSegJb_bvlF7P3.PSS LibSegJb_bvlF7P3.NX0 LibSegJb_bvlF7P3.F0 725856 LibSegJb_bvlF7P3.seg_sound_ax fx R M V bvlF7P3_conc_s. Qed.
Definition KS_bvlF7P4_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P4.regs0 LibSegJb_bvlF7P4.regs_out0).
Lemma KS_bvlF7P4_0_ok : BG.kept_ok 60 LibSegJb_bvlF7P4.regs0 LibSegJb_bvlF7P4.regs_out0 KS_bvlF7P4_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF7P4_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P4.regs0 LibSegJb_bvlF7P4.regs_out1).
Lemma KS_bvlF7P4_1_ok : BG.kept_ok 60 LibSegJb_bvlF7P4.regs0 LibSegJb_bvlF7P4.regs_out1 KS_bvlF7P4_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF7P4_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#4B#&%+v21#7p#2#40#7#3,,2,5X#;1360#;138<Y,T,:+v21#7T,;+v21#7W,19&%+v21#7p#2#40#7,5X#;1360#;14:8Y,1T,;+v21#7W,19&%+v21#7p#2#40#7T,1:+v21#8"%pstring.
Lemma bvlF7P4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF7P4_0; KS_bvlF7P4_1] fx R M V bvlF7P4_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF7P4_0; KS_bvlF7P4_1] LibSegJb_bvlF7P4.regs0 LibSegJb_bvlF7P4.kn0 LibSegJb_bvlF7P4.BR LibSegJb_bvlF7P4.PSS LibSegJb_bvlF7P4.NX0 LibSegJb_bvlF7P4.F0 725856 LibSegJb_bvlF7P4.seg_sound_ax fx R M V bvlF7P4_conc_s. Qed.
Definition KS_bvlF7P5_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P5.regs0 LibSegJb_bvlF7P5.regs_out0).
Lemma KS_bvlF7P5_0_ok : BG.kept_ok 60 LibSegJb_bvlF7P5.regs0 LibSegJb_bvlF7P5.regs_out0 KS_bvlF7P5_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF7P5_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P5.regs0 LibSegJb_bvlF7P5.regs_out1).
Lemma KS_bvlF7P5_1_ok : BG.kept_ok 60 LibSegJb_bvlF7P5.regs0 LibSegJb_bvlF7P5.regs_out1 KS_bvlF7P5_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF7P5_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#5B#&%+v21#7p#2#40#7#4,,2,5X#;1360#;138<Y,T,:+v21#7T,;+v21#7W,19&%+v21#7p#2#40#7,5X#;1360#;14:8Y,1T,;+v21#7W,19&%+v21#7p#2#40#7T,1:+v21#8"%pstring.
Lemma bvlF7P5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF7P5_0; KS_bvlF7P5_1] fx R M V bvlF7P5_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF7P5_0; KS_bvlF7P5_1] LibSegJb_bvlF7P5.regs0 LibSegJb_bvlF7P5.kn0 LibSegJb_bvlF7P5.BR LibSegJb_bvlF7P5.PSS LibSegJb_bvlF7P5.NX0 LibSegJb_bvlF7P5.F0 725856 LibSegJb_bvlF7P5.seg_sound_ax fx R M V bvlF7P5_conc_s. Qed.
Definition KS_bvlF7P6_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P6.regs0 LibSegJb_bvlF7P6.regs_out0).
Lemma KS_bvlF7P6_0_ok : BG.kept_ok 60 LibSegJb_bvlF7P6.regs0 LibSegJb_bvlF7P6.regs_out0 KS_bvlF7P6_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF7P6_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P6.regs0 LibSegJb_bvlF7P6.regs_out1).
Lemma KS_bvlF7P6_1_ok : BG.kept_ok 60 LibSegJb_bvlF7P6.regs0 LibSegJb_bvlF7P6.regs_out1 KS_bvlF7P6_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF7P6_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#6B#&%+v21#7p#2#40#7#5,,2,5X#;1360#;138<Y,T,:+v21#7T,;+v21#7W,19&%+v21#7p#2#40#7,5X#;1360#;14:8Y,1T,;+v21#7W,19&%+v21#7p#2#40#7T,1:+v21#8"%pstring.
Lemma bvlF7P6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF7P6_0; KS_bvlF7P6_1] fx R M V bvlF7P6_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF7P6_0; KS_bvlF7P6_1] LibSegJb_bvlF7P6.regs0 LibSegJb_bvlF7P6.kn0 LibSegJb_bvlF7P6.BR LibSegJb_bvlF7P6.PSS LibSegJb_bvlF7P6.NX0 LibSegJb_bvlF7P6.F0 725856 LibSegJb_bvlF7P6.seg_sound_ax fx R M V bvlF7P6_conc_s. Qed.
Definition KS_bvlF7P7_0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P7.regs0 LibSegJb_bvlF7P7.regs_out0).
Lemma KS_bvlF7P7_0_ok : BG.kept_ok 60 LibSegJb_bvlF7P7.regs0 LibSegJb_bvlF7P7.regs_out0 KS_bvlF7P7_0 = true. Proof. vm_compute. reflexivity. Qed.
Definition KS_bvlF7P7_1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvlF7P7.regs0 LibSegJb_bvlF7P7.regs_out1).
Lemma KS_bvlF7P7_1_ok : BG.kept_ok 60 LibSegJb_bvlF7P7.regs0 LibSegJb_bvlF7P7.regs_out1 KS_bvlF7P7_1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvlF7P7_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v23p#2#40A#v24p#2#40S,2_v2#70S,5#?5S,6#2S,7-41S,8#9?S,9#?0S,:v21S,=+v21v23S,>#8S,?-1S,10#1S,11-3>S,12#2325=S,13-2325>S,14#7???8000S,15#90S,16#?4S,17#8?S,18#3S,1<#>?S,1=#>0S,1>#:0S,1?#>=B#1v21#800000000000B#8v23#4000000B#1+v21v23#800000000000Na+v21#7v24B#v24#??Na+/+v21#7#8#7???8000#7B#&%+v21#7p#2#40#7#6,,2,5X#;1360#;138<Y,T,:+v21#7T,;+v21#7W,19&%+v21#7p#2#40#7,5X#;1360#;14:8Y,1T,;+v21#7W,19&%+v21#7p#2#40#7T,1:+v21#8"%pstring.
Lemma bvlF7P7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvlF7P7_0; KS_bvlF7P7_1] fx R M V bvlF7P7_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvlF7P7_0; KS_bvlF7P7_1] LibSegJb_bvlF7P7.regs0 LibSegJb_bvlF7P7.kn0 LibSegJb_bvlF7P7.BR LibSegJb_bvlF7P7.PSS LibSegJb_bvlF7P7.NX0 LibSegJb_bvlF7P7.F0 725856 LibSegJb_bvlF7P7.seg_sound_ax fx R M V bvlF7P7_conc_s. Qed.
End PMBVALP3.
