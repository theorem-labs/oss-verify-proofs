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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_aerA LibSegJa_aerB1 LibSegJa_aerB2.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAERP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aerA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aerA.regs0 LibSegJa_aerA.regs_out0).
Lemma KS_aerA_ok : BG.kept_ok 48 LibSegJa_aerA.regs0 LibSegJa_aerA.regs_out0 KS_aerA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aerA_conc_s := ",14A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;v22B#7???7?801080v2#800000000000Hv2#10I_v2#80#80O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#1000v21#7??????????0Hv21#8P#7???7000#100000001000v21#10Ka+/v21#8#7???8000#2Iv21#10P_v2#80#80v21#10B#1v22#40Na#66=380#1,2_v2#20#20+v21##10,1,5X#:>974#:>:00Y,T,;#Lb+v21#8#136=70Lbv21v22"%pstring.
Lemma aerA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aerA] fx R M V aerA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aerA] LibSegJa_aerA.regs0 LibSegJa_aerA.kn0 LibSegJa_aerA.BR LibSegJa_aerA.PSS LibSegJa_aerA.NX0 LibSegJa_aerA.F0 715124 LibSegJa_aerA.seg_sound_ax fx R M V aerA_conc_s. Qed.
Definition KS_aerB1 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aerB1.regs0 LibSegJa_aerB1.regs_out0).
Lemma KS_aerB1_ok : BG.kept_ok 48 LibSegJa_aerB1.regs0 LibSegJa_aerB1.regs_out0 KS_aerB1 = true. Proof. vm_compute. reflexivity. Qed.
Definition aerB1_conc_s := ",15A#v2p#2#40A#v21p#2#40A#v22p#2#40S,2v2S,:v21S,;v22B#7???7?801080v2#800000000000Hv2#10I_v2#80#80O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#1000v21#7??????????0Hv21#8P#7???7000#100000001000v21#10Ka+/v21#8#7???8000#2Iv21#10P_v2#80#80v21#10B#1v22#40O#66=380#66=382I#66=380#2,2_v2#20#20+##66=380#2,1,?X#:>974#6=0<0Y,T,1#:>:34T,2_v2#20T,8v21T,9v22T,:#=01=0T,;#136=70T,<#134448T,12#7???8000Nb#66=381#2Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aerB1_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aerB1] fx R M V aerB1_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aerB1] LibSegJa_aerB1.regs0 LibSegJa_aerB1.kn0 LibSegJa_aerB1.BR LibSegJa_aerB1.PSS LibSegJa_aerB1.NX0 LibSegJa_aerB1.F0 715124 LibSegJa_aerB1.seg_sound_ax fx R M V aerB1_conc_s. Qed.
Definition KS_aerB2 : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aerB2.regs0 LibSegJa_aerB2.regs_out0).
Lemma KS_aerB2_ok : BG.kept_ok 48 LibSegJa_aerB2.regs0 LibSegJa_aerB2.regs_out0 KS_aerB2 = true. Proof. vm_compute. reflexivity. Qed.
Definition aerB2_conc_s := ",1>A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v2;p#2#40A#v2<p#2#40A#v2=p#2#40A#v2>p#2#40S,2_v2#20S,8v21S,9v22S,12#7???8000B#7???7?801080v2#800000000000Hv2#10I_v2#80#80O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#1000v21#7??????????0Hv21#8P#7???7000#100000001000v21#10Ka+/v21#8#7???8000#2Iv21#10P_v2#80#80v21#10B#1v22#40I#66=380#2P#10000#681000v21#10La_v2#8v2;La_v2#10v2<La_v2#18v2=La_v2#20v2>,2+v21##10+##66=380#2,1,=X#:>:34#:>:00Y,T,1v2;T,2v2T,8v2<T,9v2=T,:v21T,;#T,12v2>Lb+v21#8#136=70Lbv21v22Nb#66=381#1Nb#66=380#1"%pstring.
Lemma aerB2_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aerB2] fx R M V aerB2_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aerB2] LibSegJa_aerB2.regs0 LibSegJa_aerB2.kn0 LibSegJa_aerB2.BR LibSegJa_aerB2.PSS LibSegJa_aerB2.NX0 LibSegJa_aerB2.F0 715316 LibSegJa_aerB2.seg_sound_ax fx R M V aerB2_conc_s. Qed.
End PMAERP.
