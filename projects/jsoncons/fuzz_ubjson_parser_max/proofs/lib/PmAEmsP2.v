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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_aesS0 LibSegJa_aesS1 LibSegJa_aesS2 LibSegJa_aesS3 LibSegJa_aesS4 LibSegJa_aesS5 LibSegJa_aesS6 LibSegJa_aesS7 LibSegJa_aesS8 LibSegJa_aesS9 LibSegJa_aesS10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAESP2.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aesS0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS0.regs0 LibSegJa_aesS0.regs_out0).
Lemma KS_aesS0_ok : BG.kept_ok 60 LibSegJa_aesS0.regs0 LibSegJa_aesS0.regs_out0 KS_aesS0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aesS0_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#20La+v21#10+v24#20B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#2T,9v34T,:#40T,;#2T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#20T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS0] fx R M V aesS0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS0] LibSegJa_aesS0.regs0 LibSegJa_aesS0.kn0 LibSegJa_aesS0.BR LibSegJa_aesS0.PSS LibSegJa_aesS0.NX0 LibSegJa_aesS0.F0 727328 LibSegJa_aesS0.seg_sound_ax fx R M V aesS0_conc_s. Qed.
Definition KS_aesS1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS1.regs0 LibSegJa_aesS1.regs_out0).
Lemma KS_aesS1_ok : BG.kept_ok 60 LibSegJa_aesS1.regs0 LibSegJa_aesS1.regs_out0 KS_aesS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aesS1_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#40La+v21#10+v24#40B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#4T,9v34T,:#80T,;#4T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#40T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS1] fx R M V aesS1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS1] LibSegJa_aesS1.regs0 LibSegJa_aesS1.kn0 LibSegJa_aesS1.BR LibSegJa_aesS1.PSS LibSegJa_aesS1.NX0 LibSegJa_aesS1.F0 727328 LibSegJa_aesS1.seg_sound_ax fx R M V aesS1_conc_s. Qed.
Definition KS_aesS2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS2.regs0 LibSegJa_aesS2.regs_out0).
Lemma KS_aesS2_ok : BG.kept_ok 60 LibSegJa_aesS2.regs0 LibSegJa_aesS2.regs_out0 KS_aesS2 = true. Proof. vm_compute. reflexivity. Qed.
Definition aesS2_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#80La+v21#10+v24#80B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#8T,9v34T,:#100T,;#8T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#80T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS2] fx R M V aesS2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS2] LibSegJa_aesS2.regs0 LibSegJa_aesS2.kn0 LibSegJa_aesS2.BR LibSegJa_aesS2.PSS LibSegJa_aesS2.NX0 LibSegJa_aesS2.F0 727328 LibSegJa_aesS2.seg_sound_ax fx R M V aesS2_conc_s. Qed.
Definition KS_aesS3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS3.regs0 LibSegJa_aesS3.regs_out0).
Lemma KS_aesS3_ok : BG.kept_ok 60 LibSegJa_aesS3.regs0 LibSegJa_aesS3.regs_out0 KS_aesS3 = true. Proof. vm_compute. reflexivity. Qed.
Definition aesS3_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#100La+v21#10+v24#100B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#10T,9v34T,:#200T,;#10T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#100T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS3] fx R M V aesS3_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS3] LibSegJa_aesS3.regs0 LibSegJa_aesS3.kn0 LibSegJa_aesS3.BR LibSegJa_aesS3.PSS LibSegJa_aesS3.NX0 LibSegJa_aesS3.F0 727328 LibSegJa_aesS3.seg_sound_ax fx R M V aesS3_conc_s. Qed.
Definition KS_aesS4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS4.regs0 LibSegJa_aesS4.regs_out0).
Lemma KS_aesS4_ok : BG.kept_ok 60 LibSegJa_aesS4.regs0 LibSegJa_aesS4.regs_out0 KS_aesS4 = true. Proof. vm_compute. reflexivity. Qed.
Definition aesS4_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#200La+v21#10+v24#200B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#20T,9v34T,:#400T,;#20T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#200T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS4] fx R M V aesS4_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS4] LibSegJa_aesS4.regs0 LibSegJa_aesS4.kn0 LibSegJa_aesS4.BR LibSegJa_aesS4.PSS LibSegJa_aesS4.NX0 LibSegJa_aesS4.F0 727328 LibSegJa_aesS4.seg_sound_ax fx R M V aesS4_conc_s. Qed.
Definition KS_aesS5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS5.regs0 LibSegJa_aesS5.regs_out0).
Lemma KS_aesS5_ok : BG.kept_ok 60 LibSegJa_aesS5.regs0 LibSegJa_aesS5.regs_out0 KS_aesS5 = true. Proof. vm_compute. reflexivity. Qed.
Definition aesS5_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#400La+v21#10+v24#400B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#40T,9v34T,:#800T,;#40T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#400T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS5] fx R M V aesS5_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS5] LibSegJa_aesS5.regs0 LibSegJa_aesS5.kn0 LibSegJa_aesS5.BR LibSegJa_aesS5.PSS LibSegJa_aesS5.NX0 LibSegJa_aesS5.F0 727328 LibSegJa_aesS5.seg_sound_ax fx R M V aesS5_conc_s. Qed.
Definition KS_aesS6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS6.regs0 LibSegJa_aesS6.regs_out0).
Lemma KS_aesS6_ok : BG.kept_ok 60 LibSegJa_aesS6.regs0 LibSegJa_aesS6.regs_out0 KS_aesS6 = true. Proof. vm_compute. reflexivity. Qed.
Definition aesS6_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#800La+v21#10+v24#800B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#80T,9v34T,:#1000T,;#80T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#800T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS6] fx R M V aesS6_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS6] LibSegJa_aesS6.regs0 LibSegJa_aesS6.kn0 LibSegJa_aesS6.BR LibSegJa_aesS6.PSS LibSegJa_aesS6.NX0 LibSegJa_aesS6.F0 727328 LibSegJa_aesS6.seg_sound_ax fx R M V aesS6_conc_s. Qed.
Definition KS_aesS7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS7.regs0 LibSegJa_aesS7.regs_out0).
Lemma KS_aesS7_ok : BG.kept_ok 60 LibSegJa_aesS7.regs0 LibSegJa_aesS7.regs_out0 KS_aesS7 = true. Proof. vm_compute. reflexivity. Qed.
Definition aesS7_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#1000La+v21#10+v24#1000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#100T,9v34T,:#2000T,;#100T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#1000T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS7] fx R M V aesS7_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS7] LibSegJa_aesS7.regs0 LibSegJa_aesS7.kn0 LibSegJa_aesS7.BR LibSegJa_aesS7.PSS LibSegJa_aesS7.NX0 LibSegJa_aesS7.F0 727328 LibSegJa_aesS7.seg_sound_ax fx R M V aesS7_conc_s. Qed.
Definition KS_aesS8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS8.regs0 LibSegJa_aesS8.regs_out0).
Lemma KS_aesS8_ok : BG.kept_ok 60 LibSegJa_aesS8.regs0 LibSegJa_aesS8.regs_out0 KS_aesS8 = true. Proof. vm_compute. reflexivity. Qed.
Definition aesS8_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#2000La+v21#10+v24#2000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#200T,9v34T,:#4000T,;#200T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#2000T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS8] fx R M V aesS8_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS8] LibSegJa_aesS8.regs0 LibSegJa_aesS8.kn0 LibSegJa_aesS8.BR LibSegJa_aesS8.PSS LibSegJa_aesS8.NX0 LibSegJa_aesS8.F0 727328 LibSegJa_aesS8.seg_sound_ax fx R M V aesS8_conc_s. Qed.
Definition KS_aesS9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS9.regs0 LibSegJa_aesS9.regs_out0).
Lemma KS_aesS9_ok : BG.kept_ok 60 LibSegJa_aesS9.regs0 LibSegJa_aesS9.regs_out0 KS_aesS9 = true. Proof. vm_compute. reflexivity. Qed.
Definition aesS9_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#4000La+v21#10+v24#4000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#400T,9v34T,:#8000T,;#400T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#4000T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS9] fx R M V aesS9_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS9] LibSegJa_aesS9.regs0 LibSegJa_aesS9.kn0 LibSegJa_aesS9.BR LibSegJa_aesS9.PSS LibSegJa_aesS9.NX0 LibSegJa_aesS9.F0 727328 LibSegJa_aesS9.seg_sound_ax fx R M V aesS9_conc_s. Qed.
Definition KS_aesS10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aesS10.regs0 LibSegJa_aesS10.regs_out0).
Lemma KS_aesS10_ok : BG.kept_ok 60 LibSegJa_aesS10.regs0 LibSegJa_aesS10.regs_out0 KS_aesS10 = true. Proof. vm_compute. reflexivity. Qed.
Definition aesS10_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#8000La+v21#10+v24#8000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#;1920#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#800T,9v34T,:#10000T,;#800T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#8000T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#;1::<Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aesS10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aesS10] fx R M V aesS10_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aesS10] LibSegJa_aesS10.regs0 LibSegJa_aesS10.kn0 LibSegJa_aesS10.BR LibSegJa_aesS10.PSS LibSegJa_aesS10.NX0 LibSegJa_aesS10.F0 727328 LibSegJa_aesS10.seg_sound_ax fx R M V aesS10_conc_s. Qed.
End PMAESP2.
