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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_avdA LibSegJa_avdB LibSegJa_avdC LibSegJa_avdD.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAVDP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_avdA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_avdA.regs0 LibSegJa_avdA.regs_out0).
Lemma KS_avdA_ok : BG.kept_ok 48 LibSegJa_avdA.regs0 LibSegJa_avdA.regs_out0 KS_avdA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition avdA_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40S,2v2O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#691000r:#7??????????8Hr:#8P#7???7000#100000001000r:#8Ka+/r:#8#7???8000#1P_v2#20#20r:#8Lar:v21B#691000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#20#20v21#18Pr:#8v21#18Lav21v22B#1000v22#800000000000Hv22#10La+v21#8v24B#_v24v22#10000H_v24v22#20I+v21#8#8,2_v2#20#20+v21#8#8,1,?X#::5;4#::624Y,T,2_v2#20U,8,:T,9#7???8000T,:v21T,;+*-1v22v24T,<v22T,=#T,12+/r:#8#7???8000Lb+v21#8v22Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma avdA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avdA] fx R M V avdA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avdA] LibSegJa_avdA.regs0 LibSegJa_avdA.kn0 LibSegJa_avdA.BR LibSegJa_avdA.PSS LibSegJa_avdA.NX0 LibSegJa_avdA.F0 697780 LibSegJa_avdA.seg_sound_ax fx R M V avdA_conc_s. Qed.
Definition KS_avdB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_avdB.regs0 LibSegJa_avdB.regs_out0).
Lemma KS_avdB_ok : BG.kept_ok 48 LibSegJa_avdB.regs0 LibSegJa_avdB.regs_out0 KS_avdB = true. Proof. vm_compute. reflexivity. Qed.
Definition avdB_conc_s := ",5A#v2p#2#40S,2_v2#20B#7???7?801020v2#800000000000Hv2#10I_v2#20#20,,1,3X#::628#::778Y,T,1#::62<"%pstring.
Lemma avdB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_avdB] fx R M V avdB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_avdB] LibSegJa_avdB.regs0 LibSegJa_avdB.kn0 LibSegJa_avdB.BR LibSegJa_avdB.PSS LibSegJa_avdB.NX0 LibSegJa_avdB.F0 697896 LibSegJa_avdB.seg_sound_ax fx R M V avdB_conc_s. Qed.
Definition KS_avdC : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_avdC.regs0 LibSegJa_avdC.regs_out0).
Lemma KS_avdC_ok : BG.kept_ok 48 LibSegJa_avdC.regs0 LibSegJa_avdC.regs_out0 KS_avdC = true. Proof. vm_compute. reflexivity. Qed.
Definition avdC_conc_s := ",10A#v2p#2#40A#v21p#2#40A#v28p#2#40S,2_v2#20S,8v28S,9#7???8000S,12+/v28#8#7???8000B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#691000v28#7??????????8Hv28#8P#7???7000#100000001000v28#8Ka+/v28#8#7???8000#1P_v2#20#20v28#8Lav28v21,,1,4X#::62<#::6=8Y,T,1#::63<T,:v21"%pstring.
Lemma avdC_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avdC] fx R M V avdC_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avdC] LibSegJa_avdC.regs0 LibSegJa_avdC.kn0 LibSegJa_avdC.BR LibSegJa_avdC.PSS LibSegJa_avdC.NX0 LibSegJa_avdC.F0 697900 LibSegJa_avdC.seg_sound_ax fx R M V avdC_conc_s. Qed.
Definition KS_avdD : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_avdD.regs0 LibSegJa_avdD.regs_out0).
Lemma KS_avdD_ok : BG.kept_ok 48 LibSegJa_avdD.regs0 LibSegJa_avdD.regs_out0 KS_avdD = true. Proof. vm_compute. reflexivity. Qed.
Definition avdD_conc_s := ",22A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#20S,8v28S,9#7???8000S,12+/v28#8#7???8000B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#691000v28#7??????????8Hv28#8P#7???7000#100000001000v28#8Ka+/v28#8#7???8000#1P_v2#20#20v28#8Lav28v21B#691000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3P_v2#20#20v21#18Pv28#8v21#18Lav21v22La+v21#10v23La_v2#8v26La_v2#10v27La_v2#18v29La_v2#20v2:,,1,:X#::63<#<>:58Y,T,1v26T,2v2T,8v27T,9v29T,:v22T,;+*-1v22v23T,<#T,12v2:"%pstring.
Lemma avdD_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_avdD] fx R M V avdD_conc_s).
Proof. r1pf L5KA.zeros_at [KS_avdD] LibSegJa_avdD.regs0 LibSegJa_avdD.kn0 LibSegJa_avdD.BR LibSegJa_avdD.PSS LibSegJa_avdD.NX0 LibSegJa_avdD.F0 697916 LibSegJa_avdD.seg_sound_ax fx R M V avdD_conc_s. Qed.
End PMAVDP.
