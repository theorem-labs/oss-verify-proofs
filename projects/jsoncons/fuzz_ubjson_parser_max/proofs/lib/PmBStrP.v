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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_ascZ LibSegJb_ascS LibSegJb_ascH23 LibSegJb_ascHg LibSegJb_ascN LibSegJb_ascTS LibSegJb_ascTH.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBSTP.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_ascZ : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJb_ascZ.regs0 LibSegJb_ascZ.regs_out0).
Lemma KS_ascZ_ok : BG.kept_ok 52 LibSegJb_ascZ.regs0 LibSegJb_ascZ.regs_out0 KS_ascZ = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition ascZ_conc_s := ",12A#v2p#2#40A#v21p#2#40S,2v2S,:v21S,<#B#7???7?801040v2#800000000000Hv2#10I_v2#40#40O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#1000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3Iv21#18P_v2#40#40v21#18Ka+/+v21#1#8#7???8000#1,2_v2#40#40+v21##2,1,6X#:832<#:8454Y,T,:+v21#1T,;#Nb+v21#1#Nbv21#"%pstring.
Lemma ascZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ascZ] fx R M V ascZ_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ascZ] LibSegJb_ascZ.regs0 LibSegJb_ascZ.kn0 LibSegJb_ascZ.BR LibSegJb_ascZ.PSS LibSegJb_ascZ.NX0 LibSegJb_ascZ.F0 688940 LibSegJb_ascZ.seg_sound_ax fx R M V ascZ_conc_s. Qed.
Definition KS_ascS : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJb_ascS.regs0 LibSegJb_ascS.regs_out0).
Lemma KS_ascS_ok : BG.kept_ok 52 LibSegJb_ascS.regs0 LibSegJb_ascS.regs_out0 KS_ascS = true. Proof. vm_compute. reflexivity. Qed.
Definition ascS_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v21S,;v23S,<v22B#7???7?801040v2#800000000000Hv2#10I_v2#40#40O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#1000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3Iv21#18P_v2#40#40v21#18B#1v22#16,2_v2#40#40+v21##1,1,12X#:832<#77<>8Y,T,1#:8414T,2_v2#40T,8v22T,9v23T,:+v21#1T,12v21T,13+v21#1T,15#7???8000Nbv21*#2v22Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ascS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ascS] fx R M V ascS_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ascS] LibSegJb_ascS.regs0 LibSegJb_ascS.kn0 LibSegJb_ascS.BR LibSegJb_ascS.PSS LibSegJb_ascS.NX0 LibSegJb_ascS.F0 688940 LibSegJb_ascS.seg_sound_ax fx R M V ascS_conc_s. Qed.
Definition KS_ascH23 : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJb_ascH23.regs0 LibSegJb_ascH23.regs_out0).
Lemma KS_ascH23_ok : BG.kept_ok 52 LibSegJb_ascH23.regs0 LibSegJb_ascH23.regs_out0 KS_ascH23 = true. Proof. vm_compute. reflexivity. Qed.
Definition ascH23_conc_s := ",13A#v2p#2#40A#v21p#2#40A#v23p#2#40S,2v2S,:v21S,;v23S,<#17B#7???7?801040v2#800000000000Hv2#10I_v2#40#40O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#1000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3Iv21#18P_v2#40#40v21#18,1_v2#40#40,1,12X#:832<#12=21<Y,T,1#:83;8T,2_v2#40T,8#17T,9v23T,:#1:T,;^#?#??????????????8T,12v21T,14#1:T,15#7???8000Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ascH23_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ascH23] fx R M V ascH23_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ascH23] LibSegJb_ascH23.regs0 LibSegJb_ascH23.kn0 LibSegJb_ascH23.BR LibSegJb_ascH23.PSS LibSegJb_ascH23.NX0 LibSegJb_ascH23.F0 688940 LibSegJb_ascH23.seg_sound_ax fx R M V ascH23_conc_s. Qed.
Definition KS_ascHg : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJb_ascHg.regs0 LibSegJb_ascHg.regs_out0).
Lemma KS_ascHg_ok : BG.kept_ok 52 LibSegJb_ascHg.regs0 LibSegJb_ascHg.regs_out0 KS_ascHg = true. Proof. vm_compute. reflexivity. Qed.
Definition ascHg_conc_s := ",16A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40S,2v2S,:v21S,;v23S,<v22B#7???7?801040v2#800000000000Hv2#10I_v2#40#40O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#1000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3Iv21#18P_v2#40#40v21#18B#18v22#3??????B#18|v22#7#4000007,1_v2#40#40,1,12X#:832<#12=21<Y,T,1#:83;8T,2_v2#40T,8v22T,9v23T,:+*#8/v22#8#8T,;^#?#??????????????8T,12v21T,14+*#8/v22#8#8T,15#7???8000Lb_v2#38r15Lb_v2#30r14Lb_v2#28r13Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma ascHg_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ascHg] fx R M V ascHg_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ascHg] LibSegJb_ascHg.regs0 LibSegJb_ascHg.kn0 LibSegJb_ascHg.BR LibSegJb_ascHg.PSS LibSegJb_ascHg.NX0 LibSegJb_ascHg.F0 688940 LibSegJb_ascHg.seg_sound_ax fx R M V ascHg_conc_s. Qed.
Definition KS_ascN : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJb_ascN.regs0 LibSegJb_ascN.regs_out0).
Lemma KS_ascN_ok : BG.kept_ok 52 LibSegJb_ascN.regs0 LibSegJb_ascN.regs_out0 KS_ascN = true. Proof. vm_compute. reflexivity. Qed.
Definition ascN_conc_s := ",1;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40S,2_v2#40S,8v22S,9v23S,:v24S,12v21S,14v25S,15#7???8000B#7???7?801040v2#800000000000Hv2#10I_v2#40#40O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#1000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3Iv21#18P_v2#40#40v21#18B#17v22#3??????B#1:v25#4000008,1+v21##18,1,:X#:83;8#77<>8Y,T,1#:8414T,;v23T,<v22T,13v24T,14+v25#1Lb+v21#8v22Lbv21+v25#1Lb+v21#10v24"%pstring.
Lemma ascN_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ascN] fx R M V ascN_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ascN] LibSegJb_ascN.regs0 LibSegJb_ascN.kn0 LibSegJb_ascN.BR LibSegJb_ascN.PSS LibSegJb_ascN.NX0 LibSegJb_ascN.F0 689080 LibSegJb_ascN.seg_sound_ax fx R M V ascN_conc_s. Qed.
Definition KS_ascTS : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJb_ascTS.regs0 LibSegJb_ascTS.regs_out0).
Lemma KS_ascTS_ok : BG.kept_ok 52 LibSegJb_ascTS.regs0 LibSegJb_ascTS.regs_out0 KS_ascTS = true. Proof. vm_compute. reflexivity. Qed.
Definition ascTS_conc_s := ",23A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40S,2_v2#40S,8v22S,13+v21#1S,15#7???8000B#7???7?801040v2#800000000000Hv2#10I_v2#40#40O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#1000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3Iv21#18P_v2#40#40v21#18La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32B#1v22#16Ka+/++v21v22#1#8#7???8000#1,1++v21#1##17,1,=X#:8414#:8454Y,T,1v2<T,2v2T,8v2=T,9v2>T,:++v21v22#1T,;#T,12v2?T,13v30T,14v31T,15v32Nb++v21v22#1#"%pstring.
Lemma ascTS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ascTS] fx R M V ascTS_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ascTS] LibSegJb_ascTS.regs0 LibSegJb_ascTS.kn0 LibSegJb_ascTS.BR LibSegJb_ascTS.PSS LibSegJb_ascTS.NX0 LibSegJb_ascTS.F0 689172 LibSegJb_ascTS.seg_sound_ax fx R M V ascTS_conc_s. Qed.
Definition KS_ascTH : list nat := Eval vm_compute in (BG.kept_list 52 LibSegJb_ascTH.regs0 LibSegJb_ascTH.regs_out0).
Lemma KS_ascTH_ok : BG.kept_ok 52 LibSegJb_ascTH.regs0 LibSegJb_ascTH.regs_out0 KS_ascTH = true. Proof. vm_compute. reflexivity. Qed.
Definition ascTH_conc_s := ",32A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40A#v2?p#2#40A#v30p#2#40A#v31p#2#40A#v32p#2#40S,2_v2#40S,8v22S,13v24S,15#7???8000B#7???7?801040v2#800000000000Hv2#10I_v2#40#40O#12=000#136000La#13<:38#7???8000Ma#13<:40#1B#1000v21#7?????????>8Hv21#8P#7???7000#100000001000v21#18Ka+/v21#8#7???8000#3Iv21#18P_v2#40#40v21#18La_v2#8v2<La_v2#10v2=La_v2#18v2>La_v2#20v2?La_v2#28v30La_v2#30v31La_v2#38v32B#1000v24#7?????7???>6Hv24#10P#7???7000#100000001000v24v25Ka+/v24#8#7???8000v26Iv24v25P_v2#40#40v24v25Pv21#18v24v25B#17v22#3??????B#1:v25#4000008B#3v26#800001Ka+/+v22v24#8#7???8000#1I+v22v24#1P_v2#40#40+v22v24#1P#7???7000#100000001000+v22v24#1,1++v22v24##1,1,=X#:8414#:8454Y,T,1v2<T,2v2T,8v2=T,9v2>T,:+v22v24T,;#T,12v2?T,13v30T,14v31T,15v32Nb+v22v24#"%pstring.
Lemma ascTH_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_ascTH] fx R M V ascTH_conc_s).
Proof. r1pf L5KA.zeros_at [KS_ascTH] LibSegJb_ascTH.regs0 LibSegJb_ascTH.kn0 LibSegJb_ascTH.BR LibSegJb_ascTH.PSS LibSegJb_ascTH.NX0 LibSegJb_ascTH.F0 689172 LibSegJb_ascTH.seg_sound_ax fx R M V ascTH_conc_s. Qed.
End PMBSTP.
