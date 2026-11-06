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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bvcA0 LibSegJb_bvcAn LibSegJb_bvcL1 LibSegJb_bvcL2c LibSegJb_bvcL2x LibSegJb_bvcZ1 LibSegJb_bvcZ2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBVCP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bvcA0 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvcA0.regs0 LibSegJb_bvcA0.regs_out0).
Lemma KS_bvcA0_ok : BG.kept_ok 60 LibSegJb_bvcA0.regs0 LibSegJb_bvcA0.regs_out0 KS_bvcA0 = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bvcA0_conc_s := ",17A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v29p#2#40S,2v2S,:v21B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8v24La+v21#10v29B#1000v24#7?????????>0Hv24#10,1_v2#10#10,1,8X#::?04#::?60Y,T,2_v2#10T,;+v21#8T,<+/+v21#8#8#7???8000T,=v24T,>v24Lb_v2#8r1"%pstring.
Lemma bvcA0_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvcA0] fx R M V bvcA0_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvcA0] LibSegJb_bvcA0.regs0 LibSegJb_bvcA0.kn0 LibSegJb_bvcA0.BR LibSegJb_bvcA0.PSS LibSegJb_bvcA0.NX0 LibSegJb_bvcA0.F0 700164 LibSegJb_bvcA0.seg_sound_ax fx R M V bvcA0_conc_s. Qed.
Definition KS_bvcAn : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvcAn.regs0 LibSegJb_bvcAn.regs_out0).
Lemma KS_bvcAn_ok : BG.kept_ok 60 LibSegJb_bvcAn.regs0 LibSegJb_bvcAn.regs_out0 KS_bvcAn = true. Proof. vm_compute. reflexivity. Qed.
Definition bvcAn_conc_s := ",19A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40A#v29p#2#40S,2v2S,:v21B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18Lav21v24La+v21#8+v24v25La+v21#10v29B#1000v24#7?????????>0Hv24#10B#20v25#10000,1_v2#10#10,1,:X#::?04#::?50Y,T,2_v2#10T,;+v21#8T,<+/+v21#8#8#7???8000T,=v24T,>+v24v25T,?#20T,10+v24v25Lb_v2#8r1"%pstring.
Lemma bvcAn_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvcAn] fx R M V bvcAn_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvcAn] LibSegJb_bvcAn.regs0 LibSegJb_bvcAn.kn0 LibSegJb_bvcAn.BR LibSegJb_bvcAn.PSS LibSegJb_bvcAn.NX0 LibSegJb_bvcAn.F0 700164 LibSegJb_bvcAn.seg_sound_ax fx R M V bvcAn_conc_s. Qed.
Definition KS_bvcL1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvcL1.regs0 LibSegJb_bvcL1.regs_out0).
Lemma KS_bvcL1_ok : BG.kept_ok 60 LibSegJb_bvcL1.regs0 LibSegJb_bvcL1.regs_out0 KS_bvcL1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvcL1_conc_s := ",8A#v2p#2#40A#v24p#2#40A#v2=p#2#40S,2v2S,?#20S,10+v24v2=B#1000v24#7?????????>0B#20v2=#10000,,1,3X#::?50#::?5<Y,T,10_+v24v2=#20"%pstring.
Lemma bvcL1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvcL1] fx R M V bvcL1_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvcL1] LibSegJb_bvcL1.regs0 LibSegJb_bvcL1.kn0 LibSegJb_bvcL1.BR LibSegJb_bvcL1.PSS LibSegJb_bvcL1.NX0 LibSegJb_bvcL1.F0 700240 LibSegJb_bvcL1.seg_sound_ax fx R M V bvcL1_conc_s. Qed.
Definition KS_bvcL2c : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvcL2c.regs0 LibSegJb_bvcL2c.regs_out0).
Lemma KS_bvcL2c_ok : BG.kept_ok 60 LibSegJb_bvcL2c.regs0 LibSegJb_bvcL2c.regs_out0 KS_bvcL2c = true. Proof. vm_compute. reflexivity. Qed.
Definition bvcL2c_conc_s := ",8A#v2p#2#40A#v24p#2#40A#v2=p#2#40S,2v2S,=v24S,10+v24v2=B#1000v24#7?????????>0B#20v2=#10000,,1,2X#::?5<#::?50Y,"%pstring.
Lemma bvcL2c_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvcL2c] fx R M V bvcL2c_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvcL2c] LibSegJb_bvcL2c.regs0 LibSegJb_bvcL2c.kn0 LibSegJb_bvcL2c.BR LibSegJb_bvcL2c.PSS LibSegJb_bvcL2c.NX0 LibSegJb_bvcL2c.F0 700252 LibSegJb_bvcL2c.seg_sound_ax fx R M V bvcL2c_conc_s. Qed.
Definition KS_bvcL2x : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvcL2x.regs0 LibSegJb_bvcL2x.regs_out0).
Lemma KS_bvcL2x_ok : BG.kept_ok 60 LibSegJb_bvcL2x.regs0 LibSegJb_bvcL2x.regs_out0 KS_bvcL2x = true. Proof. vm_compute. reflexivity. Qed.
Definition bvcL2x_conc_s := ",6A#v2p#2#40A#v24p#2#40S,2v2S,=v24S,10v24B#1000v24#7?????????>0,,1,2X#::?5<#::?60Y,"%pstring.
Lemma bvcL2x_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bvcL2x] fx R M V bvcL2x_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bvcL2x] LibSegJb_bvcL2x.regs0 LibSegJb_bvcL2x.kn0 LibSegJb_bvcL2x.BR LibSegJb_bvcL2x.PSS LibSegJb_bvcL2x.NX0 LibSegJb_bvcL2x.F0 700252 LibSegJb_bvcL2x.seg_sound_ax fx R M V bvcL2x_conc_s. Qed.
Definition KS_bvcZ1 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvcZ1.regs0 LibSegJb_bvcZ1.regs_out0).
Lemma KS_bvcZ1_ok : BG.kept_ok 60 LibSegJb_bvcZ1.regs0 LibSegJb_bvcZ1.regs_out0 KS_bvcZ1 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvcZ1_conc_s := ",11A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#10S,:v21S,<+/+v21#8#8#7???8000S,=v24S,>+v24v25B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18B#1000v24#7?????????>0B#v25#10000,,1,4X#::?60#::?6<Y,T,;v25T,<#"%pstring.
Lemma bvcZ1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvcZ1] fx R M V bvcZ1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvcZ1] LibSegJb_bvcZ1.regs0 LibSegJb_bvcZ1.kn0 LibSegJb_bvcZ1.BR LibSegJb_bvcZ1.PSS LibSegJb_bvcZ1.NX0 LibSegJb_bvcZ1.F0 700256 LibSegJb_bvcZ1.seg_sound_ax fx R M V bvcZ1_conc_s. Qed.
Definition KS_bvcZ2 : list nat := Eval vm_compute in (BG.kept_list 60 LibSegJb_bvcZ2.regs0 LibSegJb_bvcZ2.regs_out0).
Lemma KS_bvcZ2_ok : BG.kept_ok 60 LibSegJb_bvcZ2.regs0 LibSegJb_bvcZ2.regs_out0 KS_bvcZ2 = true. Proof. vm_compute. reflexivity. Qed.
Definition bvcZ2_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v24p#2#40A#v2;p#2#40S,2_v2#10S,:v21S,=v24B#7???7?802000v2#800000000000Hv2#10I_v2#1000#1000B#693000v21#7?????????=?Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#1000#1000v21#18P#10000#683000v21#18I+v21#8#8La_v2#8v2;B#1000v24#7?????????>0,1+v21#8#8,1,5X#::?70#:;054Y,T,1v2;T,2v2Lb+v21#8v24"%pstring.
Lemma bvcZ2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bvcZ2] fx R M V bvcZ2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bvcZ2] LibSegJb_bvcZ2.regs0 LibSegJb_bvcZ2.kn0 LibSegJb_bvcZ2.BR LibSegJb_bvcZ2.PSS LibSegJb_bvcZ2.NX0 LibSegJb_bvcZ2.F0 700272 LibSegJb_bvcZ2.seg_sound_ax fx R M V bvcZ2_conc_s. Qed.
End PMBVCP.
