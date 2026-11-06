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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_aeaA LibSegJa_aeaB LibSegJa_aeoA LibSegJa_aeoB.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMAENP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_aeaA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aeaA.regs0 LibSegJa_aeaA.regs_out0).
Lemma KS_aeaA_ok : BG.kept_ok 48 LibSegJa_aeaA.regs0 LibSegJa_aeaA.regs_out0 KS_aeaA = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition aeaA_conc_s := ",2;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#20#20v24#180B#691000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#20#20v25#8Lav25#12<940Ka#8001=92;#1Ma+v24#<v21Na+v24#10#Ma+v24#14#La+v24#168v22La+v24#170+v22v23B#1v21#400B#1000v22#7???????0000B#40v23#8020Hv23#20Pv24#180v25#8,3_v2#20#20+v24#8#1+v24#<#4,1,14X#:=424#:=54<Y,T,1#:=49<T,2_v2#20T,5#T,8v24T,9#7???8000T,:+v22v23T,;v23T,<+v24#168T,=_+v22v23#20T,>+v24#170T,?+/+v24#170#8#7???8000T,10v22T,11/v23#20Nb+v24#8#1Mb+v24#<_v21#1Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeaA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeaA] fx R M V aeaA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeaA] LibSegJa_aeaA.regs0 LibSegJa_aeaA.kn0 LibSegJa_aeaA.BR LibSegJa_aeaA.PSS LibSegJa_aeaA.NX0 LibSegJa_aeaA.F0 709668 LibSegJa_aeaA.seg_sound_ax fx R M V aeaA_conc_s. Qed.
Definition KS_aeaB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aeaB.regs0 LibSegJa_aeaB.regs_out0).
Lemma KS_aeaB_ok : BG.kept_ok 48 LibSegJa_aeaB.regs0 LibSegJa_aeaB.regs_out0 KS_aeaB = true. Proof. vm_compute. reflexivity. Qed.
Definition aeaB_conc_s := ",18A#v2p#2#40A#v24p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,9#7???8000S,;v27S,<+v24#168S,=v28S,>+v24#170B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#691000v24#7????????>80Hv24#8P_v2#20#20v24#180La_v2#8v29La_v2#10v2:La_v2#18v2;I+v24#170#8,1+v24#170#8,1,8X#:=550#::778Y,T,1v29T,2v2T,8v2:T,9v2;T,:+v24#168Lb+v24#170v28"%pstring.
Lemma aeaB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aeaB] fx R M V aeaB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aeaB] LibSegJa_aeaB.regs0 LibSegJa_aeaB.kn0 LibSegJa_aeaB.BR LibSegJa_aeaB.PSS LibSegJa_aeaB.NX0 LibSegJa_aeaB.F0 709968 LibSegJa_aeaB.seg_sound_ax fx R M V aeaB_conc_s. Qed.
Definition KS_aeoA : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aeoA.regs0 LibSegJa_aeoA.regs_out0).
Lemma KS_aeoA_ok : BG.kept_ok 48 LibSegJa_aeoA.regs0 LibSegJa_aeoA.regs_out0 KS_aeoA = true. Proof. vm_compute. reflexivity. Qed.
Definition aeoA_conc_s := ",2;A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v26p#2#40S,2v2S,:v24S,;v25S,<v26O#10000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#691000v24#7????????>80Hv24#8P#7???7000#100000001000v24#180Ka+/v24#8#7???8000#3Ka+/+v24#20#8#7???8000#2<Ka+/+v24#14#8#7???8000#1Iv24#180P_v2#20#20v24#180B#691000v25#7??????????8Hv25#8P#7???7000#100000001000v25#8Ka+/v25#8#7???8000#1Iv25#8P_v2#20#20v25#8Lav25#12<940Ka#8001=932#1Ma+v24#<v21Na+v24#10#Ma+v24#14#La+v24#168v22La+v24#170+v22v23B#1v21#400B#1000v22#7???????0000B#40v23#8020Hv23#20Pv24#180v25#8,3_v2#20#20+v24#8#1+v24#<#4,1,14X#:>?;0#:?0=8Y,T,1#:?028T,2_v2#20T,5#T,8v24T,9#7???8000T,:+v22v23T,;v23T,<+v24#168T,=_+v22v23#20T,>+v24#170T,?+/+v24#170#8#7???8000T,10v22T,11/v23#20Nb+v24#8#1Mb+v24#<_v21#1Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1"%pstring.
Lemma aeoA_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_aeoA] fx R M V aeoA_conc_s).
Proof. r1pf L5KA.zeros_at [KS_aeoA] LibSegJa_aeoA.regs0 LibSegJa_aeoA.kn0 LibSegJa_aeoA.BR LibSegJa_aeoA.PSS LibSegJa_aeoA.NX0 LibSegJa_aeoA.F0 716720 LibSegJa_aeoA.seg_sound_ax fx R M V aeoA_conc_s. Qed.
Definition KS_aeoB : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_aeoB.regs0 LibSegJa_aeoB.regs_out0).
Lemma KS_aeoB_ok : BG.kept_ok 48 LibSegJa_aeoB.regs0 LibSegJa_aeoB.regs_out0 KS_aeoB = true. Proof. vm_compute. reflexivity. Qed.
Definition aeoB_conc_s := ",18A#v2p#2#40A#v24p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40A#v2;p#2#40S,2_v2#20S,8v24S,9#7???8000S,;v27S,<+v24#168S,=v28S,>+v24#170B#7???7?801020v2#800000000000Hv2#10I_v2#20#20B#691000v24#7????????>80Hv24#8P_v2#20#20v24#180La_v2#8v29La_v2#10v2:La_v2#18v2;I+v24#170#8,1+v24#170#8,1,8X#:?0=<#::778Y,T,1v29T,2v2T,8v2:T,9v2;T,:+v24#168Lb+v24#170v28"%pstring.
Lemma aeoB_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_aeoB] fx R M V aeoB_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_aeoB] LibSegJa_aeoB.regs0 LibSegJa_aeoB.kn0 LibSegJa_aeoB.BR LibSegJa_aeoB.PSS LibSegJa_aeoB.NX0 LibSegJa_aeoB.F0 717020 LibSegJa_aeoB.seg_sound_ax fx R M V aeoB_conc_s. Qed.
End PMAENP.
