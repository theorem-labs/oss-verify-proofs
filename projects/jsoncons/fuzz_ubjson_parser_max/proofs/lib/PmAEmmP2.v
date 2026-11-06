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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_aemS0 LibSegJa_aemS1 LibSegJa_aemS2 LibSegJa_aemS3 LibSegJa_aemS4 LibSegJa_aemS5 LibSegJa_aemS6 LibSegJa_aemS7 LibSegJa_aemS8 LibSegJa_aemS9 LibSegJa_aemS10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAEMP2.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aemS0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS0.regs0 LibSegJa_aemS0.regs_out0).
Lemma KS_aemS0_ok : BG.kept_ok 60 LibSegJa_aemS0.regs0 LibSegJa_aemS0.regs_out0 KS_aemS0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aemS0_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#20La+v21#10+v24#20B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#2T,9v21T,:#40T,;#2T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#20T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS0] fx R M V aemS0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS0] LibSegJa_aemS0.regs0 LibSegJa_aemS0.kn0 LibSegJa_aemS0.BR LibSegJa_aemS0.PSS LibSegJa_aemS0.NX0 LibSegJa_aemS0.F0 728260 LibSegJa_aemS0.seg_sound_ax fx R M V aemS0_conc_s. Qed.
Definition KS_aemS1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS1.regs0 LibSegJa_aemS1.regs_out0).
Lemma KS_aemS1_ok : BG.kept_ok 60 LibSegJa_aemS1.regs0 LibSegJa_aemS1.regs_out0 KS_aemS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aemS1_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#40La+v21#10+v24#40B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#4T,9v21T,:#80T,;#4T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#40T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS1] fx R M V aemS1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS1] LibSegJa_aemS1.regs0 LibSegJa_aemS1.kn0 LibSegJa_aemS1.BR LibSegJa_aemS1.PSS LibSegJa_aemS1.NX0 LibSegJa_aemS1.F0 728260 LibSegJa_aemS1.seg_sound_ax fx R M V aemS1_conc_s. Qed.
Definition KS_aemS2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS2.regs0 LibSegJa_aemS2.regs_out0).
Lemma KS_aemS2_ok : BG.kept_ok 60 LibSegJa_aemS2.regs0 LibSegJa_aemS2.regs_out0 KS_aemS2 = true. Proof. vm_compute. reflexivity. Qed.
Definition aemS2_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#80La+v21#10+v24#80B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#8T,9v21T,:#100T,;#8T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#80T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS2] fx R M V aemS2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS2] LibSegJa_aemS2.regs0 LibSegJa_aemS2.kn0 LibSegJa_aemS2.BR LibSegJa_aemS2.PSS LibSegJa_aemS2.NX0 LibSegJa_aemS2.F0 728260 LibSegJa_aemS2.seg_sound_ax fx R M V aemS2_conc_s. Qed.
Definition KS_aemS3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS3.regs0 LibSegJa_aemS3.regs_out0).
Lemma KS_aemS3_ok : BG.kept_ok 60 LibSegJa_aemS3.regs0 LibSegJa_aemS3.regs_out0 KS_aemS3 = true. Proof. vm_compute. reflexivity. Qed.
Definition aemS3_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#100La+v21#10+v24#100B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#10T,9v21T,:#200T,;#10T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#100T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS3] fx R M V aemS3_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS3] LibSegJa_aemS3.regs0 LibSegJa_aemS3.kn0 LibSegJa_aemS3.BR LibSegJa_aemS3.PSS LibSegJa_aemS3.NX0 LibSegJa_aemS3.F0 728260 LibSegJa_aemS3.seg_sound_ax fx R M V aemS3_conc_s. Qed.
Definition KS_aemS4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS4.regs0 LibSegJa_aemS4.regs_out0).
Lemma KS_aemS4_ok : BG.kept_ok 60 LibSegJa_aemS4.regs0 LibSegJa_aemS4.regs_out0 KS_aemS4 = true. Proof. vm_compute. reflexivity. Qed.
Definition aemS4_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#200La+v21#10+v24#200B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#20T,9v21T,:#400T,;#20T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#200T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS4] fx R M V aemS4_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS4] LibSegJa_aemS4.regs0 LibSegJa_aemS4.kn0 LibSegJa_aemS4.BR LibSegJa_aemS4.PSS LibSegJa_aemS4.NX0 LibSegJa_aemS4.F0 728260 LibSegJa_aemS4.seg_sound_ax fx R M V aemS4_conc_s. Qed.
Definition KS_aemS5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS5.regs0 LibSegJa_aemS5.regs_out0).
Lemma KS_aemS5_ok : BG.kept_ok 60 LibSegJa_aemS5.regs0 LibSegJa_aemS5.regs_out0 KS_aemS5 = true. Proof. vm_compute. reflexivity. Qed.
Definition aemS5_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#400La+v21#10+v24#400B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#40T,9v21T,:#800T,;#40T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#400T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS5] fx R M V aemS5_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS5] LibSegJa_aemS5.regs0 LibSegJa_aemS5.kn0 LibSegJa_aemS5.BR LibSegJa_aemS5.PSS LibSegJa_aemS5.NX0 LibSegJa_aemS5.F0 728260 LibSegJa_aemS5.seg_sound_ax fx R M V aemS5_conc_s. Qed.
Definition KS_aemS6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS6.regs0 LibSegJa_aemS6.regs_out0).
Lemma KS_aemS6_ok : BG.kept_ok 60 LibSegJa_aemS6.regs0 LibSegJa_aemS6.regs_out0 KS_aemS6 = true. Proof. vm_compute. reflexivity. Qed.
Definition aemS6_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#800La+v21#10+v24#800B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#80T,9v21T,:#1000T,;#80T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#800T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS6] fx R M V aemS6_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS6] LibSegJa_aemS6.regs0 LibSegJa_aemS6.kn0 LibSegJa_aemS6.BR LibSegJa_aemS6.PSS LibSegJa_aemS6.NX0 LibSegJa_aemS6.F0 728260 LibSegJa_aemS6.seg_sound_ax fx R M V aemS6_conc_s. Qed.
Definition KS_aemS7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS7.regs0 LibSegJa_aemS7.regs_out0).
Lemma KS_aemS7_ok : BG.kept_ok 60 LibSegJa_aemS7.regs0 LibSegJa_aemS7.regs_out0 KS_aemS7 = true. Proof. vm_compute. reflexivity. Qed.
Definition aemS7_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#1000La+v21#10+v24#1000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#100T,9v21T,:#2000T,;#100T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#1000T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS7] fx R M V aemS7_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS7] LibSegJa_aemS7.regs0 LibSegJa_aemS7.kn0 LibSegJa_aemS7.BR LibSegJa_aemS7.PSS LibSegJa_aemS7.NX0 LibSegJa_aemS7.F0 728260 LibSegJa_aemS7.seg_sound_ax fx R M V aemS7_conc_s. Qed.
Definition KS_aemS8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS8.regs0 LibSegJa_aemS8.regs_out0).
Lemma KS_aemS8_ok : BG.kept_ok 60 LibSegJa_aemS8.regs0 LibSegJa_aemS8.regs_out0 KS_aemS8 = true. Proof. vm_compute. reflexivity. Qed.
Definition aemS8_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#2000La+v21#10+v24#2000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#200T,9v21T,:#4000T,;#200T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#2000T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS8] fx R M V aemS8_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS8] LibSegJa_aemS8.regs0 LibSegJa_aemS8.kn0 LibSegJa_aemS8.BR LibSegJa_aemS8.PSS LibSegJa_aemS8.NX0 LibSegJa_aemS8.F0 728260 LibSegJa_aemS8.seg_sound_ax fx R M V aemS8_conc_s. Qed.
Definition KS_aemS9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS9.regs0 LibSegJa_aemS9.regs_out0).
Lemma KS_aemS9_ok : BG.kept_ok 60 LibSegJa_aemS9.regs0 LibSegJa_aemS9.regs_out0 KS_aemS9 = true. Proof. vm_compute. reflexivity. Qed.
Definition aemS9_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#4000La+v21#10+v24#4000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#400T,9v21T,:#8000T,;#400T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#4000T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS9] fx R M V aemS9_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS9] LibSegJa_aemS9.regs0 LibSegJa_aemS9.kn0 LibSegJa_aemS9.BR LibSegJa_aemS9.PSS LibSegJa_aemS9.NX0 LibSegJa_aemS9.F0 728260 LibSegJa_aemS9.seg_sound_ax fx R M V aemS9_conc_s. Qed.
Definition KS_aemS10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aemS10.regs0 LibSegJa_aemS10.regs_out0).
Lemma KS_aemS10_ok : BG.kept_ok 60 LibSegJa_aemS10.regs0 LibSegJa_aemS10.regs_out0 KS_aemS10 = true. Proof. vm_compute. reflexivity. Qed.
Definition aemS10_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#8000La+v21#10+v24#8000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#;1<<4#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#800T,9v21T,:#10000T,;#800T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#8000T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#;1>34Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aemS10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aemS10] fx R M V aemS10_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aemS10] LibSegJa_aemS10.regs0 LibSegJa_aemS10.kn0 LibSegJa_aemS10.BR LibSegJa_aemS10.PSS LibSegJa_aemS10.NX0 LibSegJa_aemS10.F0 728260 LibSegJa_aemS10.seg_sound_ax fx R M V aemS10_conc_s. Qed.
End PMAEMP2.
