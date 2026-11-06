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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_aebS0 LibSegJa_aebS1 LibSegJa_aebS2 LibSegJa_aebS3 LibSegJa_aebS4 LibSegJa_aebS5 LibSegJa_aebS6 LibSegJa_aebS7 LibSegJa_aebS8 LibSegJa_aebS9 LibSegJa_aebS10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAEBP2.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aebS0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS0.regs0 LibSegJa_aebS0.regs_out0).
Lemma KS_aebS0_ok : BG.kept_ok 60 LibSegJa_aebS0.regs0 LibSegJa_aebS0.regs_out0 KS_aebS0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aebS0_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#20La+v21#10+v24#20B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#2T,9v21T,:#40T,;#2T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#20T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS0] fx R M V aebS0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS0] LibSegJa_aebS0.regs0 LibSegJa_aebS0.kn0 LibSegJa_aebS0.BR LibSegJa_aebS0.PSS LibSegJa_aebS0.NX0 LibSegJa_aebS0.F0 701968 LibSegJa_aebS0.seg_sound_ax fx R M V aebS0_conc_s. Qed.
Definition KS_aebS1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS1.regs0 LibSegJa_aebS1.regs_out0).
Lemma KS_aebS1_ok : BG.kept_ok 60 LibSegJa_aebS1.regs0 LibSegJa_aebS1.regs_out0 KS_aebS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aebS1_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#40La+v21#10+v24#40B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#4T,9v21T,:#80T,;#4T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#40T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS1] fx R M V aebS1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS1] LibSegJa_aebS1.regs0 LibSegJa_aebS1.kn0 LibSegJa_aebS1.BR LibSegJa_aebS1.PSS LibSegJa_aebS1.NX0 LibSegJa_aebS1.F0 701968 LibSegJa_aebS1.seg_sound_ax fx R M V aebS1_conc_s. Qed.
Definition KS_aebS2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS2.regs0 LibSegJa_aebS2.regs_out0).
Lemma KS_aebS2_ok : BG.kept_ok 60 LibSegJa_aebS2.regs0 LibSegJa_aebS2.regs_out0 KS_aebS2 = true. Proof. vm_compute. reflexivity. Qed.
Definition aebS2_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#80La+v21#10+v24#80B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#8T,9v21T,:#100T,;#8T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#80T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS2] fx R M V aebS2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS2] LibSegJa_aebS2.regs0 LibSegJa_aebS2.kn0 LibSegJa_aebS2.BR LibSegJa_aebS2.PSS LibSegJa_aebS2.NX0 LibSegJa_aebS2.F0 701968 LibSegJa_aebS2.seg_sound_ax fx R M V aebS2_conc_s. Qed.
Definition KS_aebS3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS3.regs0 LibSegJa_aebS3.regs_out0).
Lemma KS_aebS3_ok : BG.kept_ok 60 LibSegJa_aebS3.regs0 LibSegJa_aebS3.regs_out0 KS_aebS3 = true. Proof. vm_compute. reflexivity. Qed.
Definition aebS3_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#100La+v21#10+v24#100B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#10T,9v21T,:#200T,;#10T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#100T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS3] fx R M V aebS3_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS3] LibSegJa_aebS3.regs0 LibSegJa_aebS3.kn0 LibSegJa_aebS3.BR LibSegJa_aebS3.PSS LibSegJa_aebS3.NX0 LibSegJa_aebS3.F0 701968 LibSegJa_aebS3.seg_sound_ax fx R M V aebS3_conc_s. Qed.
Definition KS_aebS4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS4.regs0 LibSegJa_aebS4.regs_out0).
Lemma KS_aebS4_ok : BG.kept_ok 60 LibSegJa_aebS4.regs0 LibSegJa_aebS4.regs_out0 KS_aebS4 = true. Proof. vm_compute. reflexivity. Qed.
Definition aebS4_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#200La+v21#10+v24#200B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#20T,9v21T,:#400T,;#20T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#200T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS4] fx R M V aebS4_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS4] LibSegJa_aebS4.regs0 LibSegJa_aebS4.kn0 LibSegJa_aebS4.BR LibSegJa_aebS4.PSS LibSegJa_aebS4.NX0 LibSegJa_aebS4.F0 701968 LibSegJa_aebS4.seg_sound_ax fx R M V aebS4_conc_s. Qed.
Definition KS_aebS5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS5.regs0 LibSegJa_aebS5.regs_out0).
Lemma KS_aebS5_ok : BG.kept_ok 60 LibSegJa_aebS5.regs0 LibSegJa_aebS5.regs_out0 KS_aebS5 = true. Proof. vm_compute. reflexivity. Qed.
Definition aebS5_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#400La+v21#10+v24#400B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#40T,9v21T,:#800T,;#40T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#400T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS5] fx R M V aebS5_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS5] LibSegJa_aebS5.regs0 LibSegJa_aebS5.kn0 LibSegJa_aebS5.BR LibSegJa_aebS5.PSS LibSegJa_aebS5.NX0 LibSegJa_aebS5.F0 701968 LibSegJa_aebS5.seg_sound_ax fx R M V aebS5_conc_s. Qed.
Definition KS_aebS6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS6.regs0 LibSegJa_aebS6.regs_out0).
Lemma KS_aebS6_ok : BG.kept_ok 60 LibSegJa_aebS6.regs0 LibSegJa_aebS6.regs_out0 KS_aebS6 = true. Proof. vm_compute. reflexivity. Qed.
Definition aebS6_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#800La+v21#10+v24#800B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#80T,9v21T,:#1000T,;#80T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#800T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS6] fx R M V aebS6_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS6] LibSegJa_aebS6.regs0 LibSegJa_aebS6.kn0 LibSegJa_aebS6.BR LibSegJa_aebS6.PSS LibSegJa_aebS6.NX0 LibSegJa_aebS6.F0 701968 LibSegJa_aebS6.seg_sound_ax fx R M V aebS6_conc_s. Qed.
Definition KS_aebS7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS7.regs0 LibSegJa_aebS7.regs_out0).
Lemma KS_aebS7_ok : BG.kept_ok 60 LibSegJa_aebS7.regs0 LibSegJa_aebS7.regs_out0 KS_aebS7 = true. Proof. vm_compute. reflexivity. Qed.
Definition aebS7_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#1000La+v21#10+v24#1000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#100T,9v21T,:#2000T,;#100T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#1000T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS7] fx R M V aebS7_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS7] LibSegJa_aebS7.regs0 LibSegJa_aebS7.kn0 LibSegJa_aebS7.BR LibSegJa_aebS7.PSS LibSegJa_aebS7.NX0 LibSegJa_aebS7.F0 701968 LibSegJa_aebS7.seg_sound_ax fx R M V aebS7_conc_s. Qed.
Definition KS_aebS8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS8.regs0 LibSegJa_aebS8.regs_out0).
Lemma KS_aebS8_ok : BG.kept_ok 60 LibSegJa_aebS8.regs0 LibSegJa_aebS8.regs_out0 KS_aebS8 = true. Proof. vm_compute. reflexivity. Qed.
Definition aebS8_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#2000La+v21#10+v24#2000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#200T,9v21T,:#4000T,;#200T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#2000T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS8] fx R M V aebS8_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS8] LibSegJa_aebS8.regs0 LibSegJa_aebS8.kn0 LibSegJa_aebS8.BR LibSegJa_aebS8.PSS LibSegJa_aebS8.NX0 LibSegJa_aebS8.F0 701968 LibSegJa_aebS8.seg_sound_ax fx R M V aebS8_conc_s. Qed.
Definition KS_aebS9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS9.regs0 LibSegJa_aebS9.regs_out0).
Lemma KS_aebS9_ok : BG.kept_ok 60 LibSegJa_aebS9.regs0 LibSegJa_aebS9.regs_out0 KS_aebS9 = true. Proof. vm_compute. reflexivity. Qed.
Definition aebS9_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#4000La+v21#10+v24#4000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#400T,9v21T,:#8000T,;#400T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#4000T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS9] fx R M V aebS9_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS9] LibSegJa_aebS9.regs0 LibSegJa_aebS9.kn0 LibSegJa_aebS9.BR LibSegJa_aebS9.PSS LibSegJa_aebS9.NX0 LibSegJa_aebS9.F0 701968 LibSegJa_aebS9.seg_sound_ax fx R M V aebS9_conc_s. Qed.
Definition KS_aebS10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aebS10.regs0 LibSegJa_aebS10.regs_out0).
Lemma KS_aebS10_ok : BG.kept_ok 60 LibSegJa_aebS10.regs0 LibSegJa_aebS10.regs_out0 KS_aebS10 = true. Proof. vm_compute. reflexivity. Qed.
Definition aebS10_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40S,2v2S,:v21S,;v22S,<v23B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#8000La+v21#10+v24#8000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1:X#:;610#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#800T,9v21T,:#10000T,;#800T,<^#7#?????????????>0T,=#T,12v23T,13v22T,14#8000T,15+/+v21#8#8#7???8000T,16#7???8000Lb_v2#80+v21#8Lb_v2#78#:;780Lb_v2#48v21Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aebS10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aebS10] fx R M V aebS10_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aebS10] LibSegJa_aebS10.regs0 LibSegJa_aebS10.kn0 LibSegJa_aebS10.BR LibSegJa_aebS10.PSS LibSegJa_aebS10.NX0 LibSegJa_aebS10.F0 701968 LibSegJa_aebS10.seg_sound_ax fx R M V aebS10_conc_s. Qed.
End PMAEBP2.
