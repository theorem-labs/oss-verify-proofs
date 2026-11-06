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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJa_arsS LibSegJa_arsL LibSegJa_arsT LibSegJa_arsM LibSegJa_arsZ.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMARSP.
Abbreviation RSEGS := Asan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_arsS : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arsS.regs0 LibSegJa_arsS.regs_out0).
Lemma KS_arsS_ok : BG.kept_ok 48 LibSegJa_arsS.regs0 LibSegJa_arsS.regs_out0 KS_arsS = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition arsS_conc_s := ",20A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40S,2v2O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000r:#7????????>80Hr:#8P#7???7000#100000001000r:#180Ka+/r:#8#7???8001#1Ka+/r:#8#7???802:#6Ka+/+r:#9#8#7???8000#1Ka+/+r:#<#8#7???8000#1Ka+/+r:#151#8#7???8000#1P_v2#30#30r:#180Na+r:#150v21B#v21#??Fv21#fLa+r:#168v22B#1000v22#800000000000Hv22#10La+r:#170v24B#_v24v22#10000H_v24v22#20I+r:#8#2I+r:#150#2I+r:#170#8,4_v2#20#20+r:#8#2+r:#150#2+r:#170#8,1,13X#:;?84#:<09<Y,T,2_v2#30U,8,:T,9+r:#168T,:+*-1v22v24T,;#T,<v22T,=#T,12#7???8000Nb+r:#150#Nb+r:#151#Nb+r:#9#Nb+r:#8#1Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+r:#170v24"%pstring.
Lemma arsS_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arsS] fx R M V arsS_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arsS] LibSegJa_arsS.regs0 LibSegJa_arsS.kn0 LibSegJa_arsS.BR LibSegJa_arsS.PSS LibSegJa_arsS.NX0 LibSegJa_arsS.F0 704388 LibSegJa_arsS.seg_sound_ax fx R M V arsS_conc_s. Qed.
Definition KS_arsL : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arsL.regs0 LibSegJa_arsL.regs_out0).
Lemma KS_arsL_ok : BG.kept_ok 48 LibSegJa_arsL.regs0 LibSegJa_arsL.regs_out0 KS_arsL = true. Proof. vm_compute. reflexivity. Qed.
Definition arsL_conc_s := ",29A#v2p#2#40A#v21p#2#40A#v22p#2#40A#v24p#2#40A#v25p#2#40S,2v2O#12<000#134000La#13:<?8#7???8000Ma#13:=00#1B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000r:#7????????>80Hr:#8P#7???7000#100000001000r:#180Ka+/r:#8#7???8001#1Ka+/r:#8#7???802:#6Ka+/+r:#9#8#7???8000#1Ka+/+r:#<#8#7???8000#1Ka+/+r:#151#8#7???8000#1P_v2#30#30r:#180Na+r:#150v21B#v21#??Fv21#tLa+r:#160v25B#1000v25#7??????????8Hv25#8P#7???7000#100000001000v25#1Ka+/v25#8#7???8000#1Iv25#1P_v2#30#30v25#1Pv25#1r:#180La+r:#168v22B#1000v22#800000000000Hv22#10La+r:#170v24B#_v24v22#10000H_v24v22#20I+r:#8#2I+r:#158#8I+r:#170#8,5_v2#20#20+r:#8#2+v25##1+r:#158#8+r:#170#8,1,12X#:;?84#:<09<Y,T,2_v2#30U,8,:T,9+r:#168T,:+*-1v22v24T,;#T,<v22T,12#7???8000Lb+r:#158#Nbv25#Nb+r:#9#Nb+r:#8#1Lb_v2#20r12Lb_v2#18r9Lb_v2#10r8Lb_v2#8r1Lb+r:#170v24"%pstring.
Lemma arsL_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arsL] fx R M V arsL_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arsL] LibSegJa_arsL.regs0 LibSegJa_arsL.kn0 LibSegJa_arsL.BR LibSegJa_arsL.PSS LibSegJa_arsL.NX0 LibSegJa_arsL.F0 704388 LibSegJa_arsL.seg_sound_ax fx R M V arsL_conc_s. Qed.
Definition KS_arsT : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arsT.regs0 LibSegJa_arsT.regs_out0).
Lemma KS_arsT_ok : BG.kept_ok 48 LibSegJa_arsT.regs0 LibSegJa_arsT.regs_out0 KS_arsT = true. Proof. vm_compute. reflexivity. Qed.
Definition arsT_conc_s := ",=A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28S,9+v28#168S,12#7???8000B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v28#7????????>80Hv28#8P_v2#30#30v28#180I+v28#170#8,1+v28#170#8,1,5X#:<0:0#::778Y,T,1#:<0:<T,:+v28#168Lb+v28#170r<"%pstring.
Lemma arsT_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arsT] fx R M V arsT_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arsT] LibSegJa_arsT.regs0 LibSegJa_arsT.kn0 LibSegJa_arsT.BR LibSegJa_arsT.PSS LibSegJa_arsT.NX0 LibSegJa_arsT.F0 704672 LibSegJa_arsT.seg_sound_ax fx R M V arsT_conc_s. Qed.
Definition KS_arsM : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arsM.regs0 LibSegJa_arsM.regs_out0).
Lemma KS_arsM_ok : BG.kept_ok 48 LibSegJa_arsM.regs0 LibSegJa_arsM.regs_out0 KS_arsM = true. Proof. vm_compute. reflexivity. Qed.
Definition arsM_conc_s := ",9A#v2p#2#40A#v28p#2#40S,2_v2#30S,8v28S,9+v28#168S,12#7???8000B#7???7?801030v2#800000000000Hv2#10I_v2#30#30,1_v2#29#9,1,:X#:<0:<#:<=:8Y,T,1#:<0<<T,:+v28#168T,;_v2#24T,<_v2#28T,=_v2#29Nb_v2#29#Mb_v2#28#Mb_v2#24#"%pstring.
Lemma arsM_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_arsM] fx R M V arsM_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_arsM] LibSegJa_arsM.regs0 LibSegJa_arsM.kn0 LibSegJa_arsM.BR LibSegJa_arsM.PSS LibSegJa_arsM.NX0 LibSegJa_arsM.F0 704684 LibSegJa_arsM.seg_sound_ax fx R M V arsM_conc_s. Qed.
Definition KS_arsZ : list nat := Eval vm_compute in (BG.kept_list 48 LibSegJa_arsZ.regs0 LibSegJa_arsZ.regs_out0).
Lemma KS_arsZ_ok : BG.kept_ok 48 LibSegJa_arsZ.regs0 LibSegJa_arsZ.regs_out0 KS_arsZ = true. Proof. vm_compute. reflexivity. Qed.
Definition arsZ_conc_s := ",16A#v2p#2#40A#v26p#2#40A#v27p#2#40A#v28p#2#40A#v29p#2#40A#v2:p#2#40S,2_v2#30S,8v28S,9+v28#168S,12#7???8000B#7???7?801030v2#800000000000Hv2#10I_v2#30#30B#691000v28#7????????>80Hv28#8P_v2#30#30v28#180Ka+/+v28#<#8#7???8000#1La_v2#8v26La_v2#10v27La_v2#18v29La_v2#20v2:I+v28#<#4,1+v28#<#4,1,:X#:<0<<#:<0?8Y,T,1v26T,2v2T,8v27T,9v29T,:+v28#<T,;#T,12v2:Mb+v28#<#"%pstring.
Lemma arsZ_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_arsZ] fx R M V arsZ_conc_s).
Proof. r1pf L5KA.zeros_at [KS_arsZ] LibSegJa_arsZ.regs0 LibSegJa_arsZ.kn0 LibSegJa_arsZ.BR LibSegJa_arsZ.PSS LibSegJa_arsZ.NX0 LibSegJa_arsZ.F0 704716 LibSegJa_arsZ.seg_sound_ax fx R M V arsZ_conc_s. Qed.
End PMARSP.
