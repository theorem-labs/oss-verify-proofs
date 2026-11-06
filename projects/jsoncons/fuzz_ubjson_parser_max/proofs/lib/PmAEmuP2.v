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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_aeuS0 LibSegJa_aeuS1 LibSegJa_aeuS2 LibSegJa_aeuS3 LibSegJa_aeuS4 LibSegJa_aeuS5 LibSegJa_aeuS6 LibSegJa_aeuS7 LibSegJa_aeuS8 LibSegJa_aeuS9 LibSegJa_aeuS10.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAEUP2.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aeuS0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS0.regs0 LibSegJa_aeuS0.regs_out0).
Lemma KS_aeuS0_ok : BG.kept_ok 60 LibSegJa_aeuS0.regs0 LibSegJa_aeuS0.regs_out0 KS_aeuS0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aeuS0_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#20La+v21#10+v24#20B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#2T,9v34T,:#40T,;#2T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#20T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS0] fx R M V aeuS0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS0] LibSegJa_aeuS0.regs0 LibSegJa_aeuS0.kn0 LibSegJa_aeuS0.BR LibSegJa_aeuS0.PSS LibSegJa_aeuS0.NX0 LibSegJa_aeuS0.F0 708008 LibSegJa_aeuS0.seg_sound_ax fx R M V aeuS0_conc_s. Qed.
Definition KS_aeuS1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS1.regs0 LibSegJa_aeuS1.regs_out0).
Lemma KS_aeuS1_ok : BG.kept_ok 60 LibSegJa_aeuS1.regs0 LibSegJa_aeuS1.regs_out0 KS_aeuS1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aeuS1_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#40La+v21#10+v24#40B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#4T,9v34T,:#80T,;#4T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#40T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS1] fx R M V aeuS1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS1] LibSegJa_aeuS1.regs0 LibSegJa_aeuS1.kn0 LibSegJa_aeuS1.BR LibSegJa_aeuS1.PSS LibSegJa_aeuS1.NX0 LibSegJa_aeuS1.F0 708008 LibSegJa_aeuS1.seg_sound_ax fx R M V aeuS1_conc_s. Qed.
Definition KS_aeuS2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS2.regs0 LibSegJa_aeuS2.regs_out0).
Lemma KS_aeuS2_ok : BG.kept_ok 60 LibSegJa_aeuS2.regs0 LibSegJa_aeuS2.regs_out0 KS_aeuS2 = true. Proof. vm_compute. reflexivity. Qed.
Definition aeuS2_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#80La+v21#10+v24#80B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#8T,9v34T,:#100T,;#8T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#80T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS2] fx R M V aeuS2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS2] LibSegJa_aeuS2.regs0 LibSegJa_aeuS2.kn0 LibSegJa_aeuS2.BR LibSegJa_aeuS2.PSS LibSegJa_aeuS2.NX0 LibSegJa_aeuS2.F0 708008 LibSegJa_aeuS2.seg_sound_ax fx R M V aeuS2_conc_s. Qed.
Definition KS_aeuS3 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS3.regs0 LibSegJa_aeuS3.regs_out0).
Lemma KS_aeuS3_ok : BG.kept_ok 60 LibSegJa_aeuS3.regs0 LibSegJa_aeuS3.regs_out0 KS_aeuS3 = true. Proof. vm_compute. reflexivity. Qed.
Definition aeuS3_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#100La+v21#10+v24#100B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#10T,9v34T,:#200T,;#10T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#100T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS3_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS3] fx R M V aeuS3_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS3] LibSegJa_aeuS3.regs0 LibSegJa_aeuS3.kn0 LibSegJa_aeuS3.BR LibSegJa_aeuS3.PSS LibSegJa_aeuS3.NX0 LibSegJa_aeuS3.F0 708008 LibSegJa_aeuS3.seg_sound_ax fx R M V aeuS3_conc_s. Qed.
Definition KS_aeuS4 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS4.regs0 LibSegJa_aeuS4.regs_out0).
Lemma KS_aeuS4_ok : BG.kept_ok 60 LibSegJa_aeuS4.regs0 LibSegJa_aeuS4.regs_out0 KS_aeuS4 = true. Proof. vm_compute. reflexivity. Qed.
Definition aeuS4_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#200La+v21#10+v24#200B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#20T,9v34T,:#400T,;#20T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#200T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS4_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS4] fx R M V aeuS4_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS4] LibSegJa_aeuS4.regs0 LibSegJa_aeuS4.kn0 LibSegJa_aeuS4.BR LibSegJa_aeuS4.PSS LibSegJa_aeuS4.NX0 LibSegJa_aeuS4.F0 708008 LibSegJa_aeuS4.seg_sound_ax fx R M V aeuS4_conc_s. Qed.
Definition KS_aeuS5 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS5.regs0 LibSegJa_aeuS5.regs_out0).
Lemma KS_aeuS5_ok : BG.kept_ok 60 LibSegJa_aeuS5.regs0 LibSegJa_aeuS5.regs_out0 KS_aeuS5 = true. Proof. vm_compute. reflexivity. Qed.
Definition aeuS5_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#400La+v21#10+v24#400B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#40T,9v34T,:#800T,;#40T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#400T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS5_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS5] fx R M V aeuS5_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS5] LibSegJa_aeuS5.regs0 LibSegJa_aeuS5.kn0 LibSegJa_aeuS5.BR LibSegJa_aeuS5.PSS LibSegJa_aeuS5.NX0 LibSegJa_aeuS5.F0 708008 LibSegJa_aeuS5.seg_sound_ax fx R M V aeuS5_conc_s. Qed.
Definition KS_aeuS6 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS6.regs0 LibSegJa_aeuS6.regs_out0).
Lemma KS_aeuS6_ok : BG.kept_ok 60 LibSegJa_aeuS6.regs0 LibSegJa_aeuS6.regs_out0 KS_aeuS6 = true. Proof. vm_compute. reflexivity. Qed.
Definition aeuS6_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#800La+v21#10+v24#800B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#80T,9v34T,:#1000T,;#80T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#800T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS6_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS6] fx R M V aeuS6_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS6] LibSegJa_aeuS6.regs0 LibSegJa_aeuS6.kn0 LibSegJa_aeuS6.BR LibSegJa_aeuS6.PSS LibSegJa_aeuS6.NX0 LibSegJa_aeuS6.F0 708008 LibSegJa_aeuS6.seg_sound_ax fx R M V aeuS6_conc_s. Qed.
Definition KS_aeuS7 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS7.regs0 LibSegJa_aeuS7.regs_out0).
Lemma KS_aeuS7_ok : BG.kept_ok 60 LibSegJa_aeuS7.regs0 LibSegJa_aeuS7.regs_out0 KS_aeuS7 = true. Proof. vm_compute. reflexivity. Qed.
Definition aeuS7_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#1000La+v21#10+v24#1000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#100T,9v34T,:#2000T,;#100T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#1000T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS7_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS7] fx R M V aeuS7_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS7] LibSegJa_aeuS7.regs0 LibSegJa_aeuS7.kn0 LibSegJa_aeuS7.BR LibSegJa_aeuS7.PSS LibSegJa_aeuS7.NX0 LibSegJa_aeuS7.F0 708008 LibSegJa_aeuS7.seg_sound_ax fx R M V aeuS7_conc_s. Qed.
Definition KS_aeuS8 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS8.regs0 LibSegJa_aeuS8.regs_out0).
Lemma KS_aeuS8_ok : BG.kept_ok 60 LibSegJa_aeuS8.regs0 LibSegJa_aeuS8.regs_out0 KS_aeuS8 = true. Proof. vm_compute. reflexivity. Qed.
Definition aeuS8_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#2000La+v21#10+v24#2000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#200T,9v34T,:#4000T,;#200T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#2000T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS8_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS8] fx R M V aeuS8_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS8] LibSegJa_aeuS8.regs0 LibSegJa_aeuS8.kn0 LibSegJa_aeuS8.BR LibSegJa_aeuS8.PSS LibSegJa_aeuS8.NX0 LibSegJa_aeuS8.F0 708008 LibSegJa_aeuS8.seg_sound_ax fx R M V aeuS8_conc_s. Qed.
Definition KS_aeuS9 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS9.regs0 LibSegJa_aeuS9.regs_out0).
Lemma KS_aeuS9_ok : BG.kept_ok 60 LibSegJa_aeuS9.regs0 LibSegJa_aeuS9.regs_out0 KS_aeuS9 = true. Proof. vm_compute. reflexivity. Qed.
Definition aeuS9_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#4000La+v21#10+v24#4000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#400T,9v34T,:#8000T,;#400T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#4000T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS9_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS9] fx R M V aeuS9_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS9] LibSegJa_aeuS9.regs0 LibSegJa_aeuS9.kn0 LibSegJa_aeuS9.BR LibSegJa_aeuS9.PSS LibSegJa_aeuS9.NX0 LibSegJa_aeuS9.F0 708008 LibSegJa_aeuS9.seg_sound_ax fx R M V aeuS9_conc_s. Qed.
Definition KS_aeuS10 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJa_aeuS10.regs0 LibSegJa_aeuS10.regs_out0).
Lemma KS_aeuS10_ok : BG.kept_ok 60 LibSegJa_aeuS10.regs0 LibSegJa_aeuS10.regs_out0 KS_aeuS10 = true. Proof. vm_compute. reflexivity. Qed.
Definition aeuS10_conc_s := ",1=A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v34p#2#40S,2v2S,:v21S,;v22S,<v23S,=v34B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000Ka+/v2#8#7???7>00#200O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#691000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#681000v21#18Lav21v24La+v21#8+v24#8000La+v21#10+v24#8000B#1000v24#7?????????>0Hv24#10,1_v2#80#80,1,1<X#:<=:8#12;3>4Y,T,1#:;>=<T,2_v2#80T,8#800T,9v34T,:#10000T,;#800T,<^#7#?????????????>0T,=#T,12v21T,13v23T,14v22T,15#8000T,16+/+v21#8#8#7???8000T,17#7???8000Lb_v2#80+v21#8Lb_v2#78#:<?34Lb_v2#50v21Lb_v2#48r17Lb_v2#40r16Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeuS10_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeuS10] fx R M V aeuS10_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeuS10] LibSegJa_aeuS10.regs0 LibSegJa_aeuS10.kn0 LibSegJa_aeuS10.BR LibSegJa_aeuS10.PSS LibSegJa_aeuS10.NX0 LibSegJa_aeuS10.F0 708008 LibSegJa_aeuS10.seg_sound_ax fx R M V aeuS10_conc_s. Qed.
End PMAEUP2.
