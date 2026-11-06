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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_brsS LibSegJb_brsL LibSegJb_brsM LibSegJb_brsZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBRSP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_brsS : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_brsS.regs0 LibSegJb_brsS.regs_out0).
Lemma KS_brsS_ok : BG.kept_ok 48 LibSegJb_brsS.regs0 LibSegJb_brsS.regs_out0 KS_brsS = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition brsS_conc_s := ",17A#v2p#2#40A#v21p#2#40S,2v2O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000r:#7????????>80Hr:#8P#7???7000#100000001000r:#180Ka+/r:#8#7???8001#1Ka+/r:#8#7???802:#6Ka+/+r:#9#8#7???8000#1Ka+/+r:#<#8#7???8000#1Ka+/+r:#151#8#7???8000#1P_v2#50#50r:#180Na+r:#150v21B#v21#??Fv21#fI+r:#8#2I+r:#150#2,3_v2#38#38+r:#8#2+r:#150#2,1,16X#:<>2<#::?04Y,T,1#:<?2<T,2_v2#50U,8,:T,:+r:#168T,;#T,<+/+r:#150#8#7???8000T,=#T,12+r:#168T,13#7???8000Nb+r:#150#Nb+r:#151#Nb+r:#9#Nb+r:#8#1Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma brsS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_brsS] fx R M V brsS_conc_s).
Proof. r1pf L5KA.zeros_at [KS_brsS] LibSegJb_brsS.regs0 LibSegJb_brsS.kn0 LibSegJb_brsS.BR LibSegJb_brsS.PSS LibSegJb_brsS.NX0 LibSegJb_brsS.F0 708140 LibSegJb_brsS.seg_sound_ax fx R M V brsS_conc_s. Qed.
Definition KS_brsL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_brsL.regs0 LibSegJb_brsL.regs_out0).
Lemma KS_brsL_ok : BG.kept_ok 48 LibSegJb_brsL.regs0 LibSegJb_brsL.regs_out0 KS_brsL = true. Proof. vm_compute. reflexivity. Qed.
Definition brsL_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v25p#2#40S,2v2O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000r:#7????????>80Hr:#8P#7???7000#100000001000r:#180Ka+/r:#8#7???8001#1Ka+/r:#8#7???802:#6Ka+/+r:#9#8#7???8000#1Ka+/+r:#<#8#7???8000#1Ka+/+r:#151#8#7???8000#1P_v2#50#50r:#180Na+r:#150v21B#v21#??Fv21#tLa+r:#160v25B#1000v25#7??????????8Hv25#8P#7???7000#100000001000v25#1Ka+/v25#8#7???8000#1Iv25#1P_v2#50#50v25#1Pv25#1r:#180I+r:#8#2I+r:#158#8,4_v2#38#38+r:#8#2+v25##1+r:#158#8,1,15X#:<>2<#::?04Y,T,1#:<?2<T,2_v2#50U,8,:T,:+r:#168T,;+r:#158T,<+/+r:#150#8#7???8000T,12+r:#168T,13#7???8000Lb+r:#158#Nbv25#Nb+r:#9#Nb+r:#8#1Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma brsL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_brsL] fx R M V brsL_conc_s).
Proof. r1pf L5KA.zeros_at [KS_brsL] LibSegJb_brsL.regs0 LibSegJb_brsL.kn0 LibSegJb_brsL.BR LibSegJb_brsL.PSS LibSegJb_brsL.NX0 LibSegJb_brsL.F0 708140 LibSegJb_brsL.seg_sound_ax fx R M V brsL_conc_s. Qed.
Definition KS_brsM : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_brsM.regs0 LibSegJb_brsM.regs_out0).
Lemma KS_brsM_ok : BG.kept_ok 48 LibSegJb_brsM.regs0 LibSegJb_brsM.regs_out0 KS_brsM = true. Proof. vm_compute. reflexivity. Qed.
Definition brsM_conc_s := ",15A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v28p#2#40S,2_v2#50S,8v28S,12+v28#168S,13#7???8000B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v28#7????????>80Hv28#8P#7???7000#100000001000v28#180P_v2#50#50v28#180Ka+/v28#8#7???802>#2La+v28#170v22La+v28#178v23B#1000v22#7?????????>0B#1020v23#800000000000B#20_v23v22#10000,1_v2#41#9,1,=X#:<?2<#:==40Y,T,1#:<?80T,9+v28#170T,:+v28#168T,;_v2#3<T,<_v2#40T,=_v2#41T,14+/+v28#170#8#7???8000T,15v22Nb_v2#41#Mb_v2#40#Mb_v2#3<#"%pstring.
Lemma brsM_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_brsM] fx R M V brsM_conc_s).
Proof. r1pf L5KA.zeros_at [KS_brsM] LibSegJb_brsM.regs0 LibSegJb_brsM.kn0 LibSegJb_brsM.BR LibSegJb_brsM.PSS LibSegJb_brsM.NX0 LibSegJb_brsM.F0 708396 LibSegJb_brsM.seg_sound_ax fx R M V brsM_conc_s. Qed.
Definition KS_brsZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJb_brsZ.regs0 LibSegJb_brsZ.regs_out0).
Lemma KS_brsZ_ok : BG.kept_ok 48 LibSegJb_brsZ.regs0 LibSegJb_brsZ.regs_out0 KS_brsZ = true. Proof. vm_compute. reflexivity. Qed.
Definition brsZ_conc_s := ",25A#v2p#2#40A#v22p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40A#v2<p#2#40A#v2>p#2#40S,2_v2#50S,8v28S,9+v28#170S,12+v28#168S,13#7???8000S,14+/+v28#170#8#7???8000S,15v22B#7???7?801050v2#800000000000Hv2#10I_v2#50#50B#693000v28#7????????>80Hv28#8P#7???7000#100000001000v28#180P_v2#50#50v28#180Ka+/v28#8#7???802>#1Ka+/+v28#<#8#7???8000#1B#1000v22#7?????????>0Hv22#10I+v28#170#8I+v28#<#4La_v2#8v26La_v2#10v27La_v2#18v29La_v2#20v2:La_v2#28v2;La_v2#30v2<La_v2#38v2>,2+v28#170#8+v28#<#4,1,>X#:<?80#:=004Y,T,1v26T,2v2T,8v27T,9v29T,:+v28#<T,;#T,12v2:T,13v2;T,14v2<T,15v2>Mb+v28#<#Lb+v28#170+v22#20"%pstring.
Lemma brsZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_brsZ] fx R M V brsZ_conc_s).
Proof. r1pf L5KA.zeros_at [KS_brsZ] LibSegJb_brsZ.regs0 LibSegJb_brsZ.kn0 LibSegJb_brsZ.BR LibSegJb_brsZ.PSS LibSegJb_brsZ.NX0 LibSegJb_brsZ.F0 708480 LibSegJb_brsZ.seg_sound_ax fx R M V brsZ_conc_s. Qed.
End PMBRSP.
