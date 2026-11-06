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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.seg Require LibSegJb_bsrXge LibSegJb_bsrXlt LibSegJb_bsrR.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PConc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Module PMBSRP3.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).
Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom AsanUbsan.M.loaded_segments)) (only parsing).
Definition aligned (a m : Z) : Prop := a mod m = 0.
Definition srl_range (a c lo hi : Z) : Prop := lo <= a / c <= hi.
Import PConc.
Definition KS_bsrXge : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bsrXge.regs0 LibSegJb_bsrXge.regs_out0).
Lemma KS_bsrXge_ok : BG.kept_ok 80 LibSegJb_bsrXge.regs0 LibSegJb_bsrXge.regs_out0 KS_bsrXge = true. Proof. vm_compute. reflexivity. Qed.
Local Ltac r1mk za ks fx R M V s := PStmt.mk RSEGS aligned srl_range za ks fx R M V s.
Local Ltac r1pf za ks r0 k0 br pss nx f0 pc seg fx R M V s :=
PConcR.PR.solve2 RSEGS aligned srl_range za ks r0 k0 br pss nx f0 pc seg fx R M V s.
Definition bsrXge_conc_s := ",53A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v2=p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40S,2v32S,8v2S,9v32S,:#4000S,12+/+v24#120#8#7???8000S,13v24S,14#S,16+v24#?0S,17+v24#120S,18+/+v24#?0#8#7???8000S,19+/v2?#8#7???8000S,1:v2?S,1;#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????60Hv32#20Iv32#38La+v32#18v25B#1000v25#7???????<000La+v32#8+v2?#20La+v32#10v2?La+v32#30v2?B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#38v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v23La+v24#120#B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#38v2?#80Pv32#38v30#1Pv2?#80#10000#126000La+v2?#20#4000B#693000v2=#7????????>?0Hv2=#8P#7???7000#100000001000v2=#110Ka+/v2=#8#7???8000#22Iv2=#110Pv24#128v2=#110Pv32#38v2=#110La+v24#?0v2=La+v24#?8+v2=#10Lav2=#132010La+v2=#10#131?20Ma+v2=#98#Ma+v2=#9<#La+v2=#:0+v2=#10Ka#8001>3??#1Ka#8001>3><#1Pv2=#110v2?#80Pv2=#110v30#1P+/v2?#8#7???8000#10+/v2=#8#7???8000#22P+/v2?#8#7???8000#10#8001>3??#1P+/v2?#8#7???8000#10#8001>3><#1,1+v24#100#28,1,9X#;0:7<#;0;3<Y,T,:+v24#100T,12#4000T,16#4000Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v23Lb+v24#120#"%pstring.
Lemma bsrXge_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsrXge] fx R M V bsrXge_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsrXge] LibSegJb_bsrXge.regs0 LibSegJb_bsrXge.kn0 LibSegJb_bsrXge.BR LibSegJb_bsrXge.PSS LibSegJb_bsrXge.NX0 LibSegJb_bsrXge.F0 723580 LibSegJb_bsrXge.seg_sound_ax fx R M V bsrXge_conc_s. Qed.
Definition KS_bsrXlt : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bsrXlt.regs0 LibSegJb_bsrXlt.regs_out0).
Lemma KS_bsrXlt_ok : BG.kept_ok 80 LibSegJb_bsrXlt.regs0 LibSegJb_bsrXlt.regs_out0 KS_bsrXlt = true. Proof. vm_compute. reflexivity. Qed.
Definition bsrXlt_conc_s := ",55A#v2p#2#40A#v22p#2#40A#v23p#2#40A#v24p#2#40A#v25p#2#40A#v2=p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40A#v33p#2#40S,2v32S,8v2S,9v32S,:v33S,12+/+v24#120#8#7???8000S,13v24S,14#S,16+v24#?0S,17+v24#120S,18+/+v24#?0#8#7???8000S,19+/v2?#8#7???8000S,1:v2?S,1;#7???8000O#10000#136000La#13<:38#7???8000Ma#13<:40#1B#7???7?801000v32#7?????????60Hv32#20Iv32#38La+v32#18v25B#1000v25#7???????<000La+v32#8+v2?#20La+v32#10v2?La+v32#30v2?B#693000v24#7????????>=8Hv24#8P#7???7000#100000001000v24#128Ka+/+v24#8#8#7???8000#24Iv24#128Pv32#38v24#128La+v24#108v22La+v24#110#4000Ja+v24#100#8La+v24#118v23La+v24#120#B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#38v2?#80Pv32#38v30#1Pv2?#80#10000#126000La+v2?#20#4000B#693000v2=#7????????>?0Hv2=#8P#7???7000#100000001000v2=#110Ka+/v2=#8#7???8000#22Iv2=#110Pv24#128v2=#110Pv32#38v2=#110La+v24#?0v2=La+v24#?8+v2=#10Lav2=#132010La+v2=#10#131?20Ma+v2=#98#Ma+v2=#9<#La+v2=#:0+v2=#10Ka#8001>3??#1Ka#8001>3><#1Pv2=#110v2?#80Pv2=#110v30#1P+/v2?#8#7???8000#10+/v2=#8#7???8000#22P+/v2?#8#7???8000#10#8001>3??#1P+/v2?#8#7???8000#10#8001>3><#1B#v33#3???,2+v24#100#28+v2=#98#4,1,=X#;0:7<#;0;3<Y,T,1#;0:?<T,:+v24#100T,<#T,=#T,12v33T,16v33Mb+v2=#98#2Lb+v24#108v22Lb+v24#110#4000Lb+v24#118v23Lb+v24#120#"%pstring.
Lemma bsrXlt_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5KA.zeros_at [KS_bsrXlt] fx R M V bsrXlt_conc_s).
Proof. r1pf L5KA.zeros_at [KS_bsrXlt] LibSegJb_bsrXlt.regs0 LibSegJb_bsrXlt.kn0 LibSegJb_bsrXlt.BR LibSegJb_bsrXlt.PSS LibSegJb_bsrXlt.NX0 LibSegJb_bsrXlt.F0 723580 LibSegJb_bsrXlt.seg_sound_ax fx R M V bsrXlt_conc_s. Qed.
Definition KS_bsrR : list nat := Eval vm_compute in (BG.kept_list 80 LibSegJb_bsrR.regs0 LibSegJb_bsrR.regs_out0).
Lemma KS_bsrR_ok : BG.kept_ok 80 LibSegJb_bsrR.regs0 LibSegJb_bsrR.regs_out0 KS_bsrR = true. Proof. vm_compute. reflexivity. Qed.
Definition bsrR_conc_s := ",41A#v2p#2#40A#v24p#2#40A#v29p#2#40A#v2?p#2#40A#v30p#2#40A#v32p#2#40A#v40p#2#40A#v41p#2#40A#v42p#2#40A#v43p#2#40A#v44p#2#40A#v45p#2#40A#v46p#2#40A#v47p#2#40A#v48p#2#40A#v49p#2#40A#v4:p#2#40A#v4;p#2#40A#v4<p#2#40S,2v32S,8v2S,9v32S,16v29S,19+/v2?#8#7???8000S,1:v2?B#7???7?8010:0v2#800000000000Hv2#10I_v2#:0#:0B#7???7?801000v32#7?????????60Hv32#20Iv32#38La+v32#10v2?B#693000v2?#7?????????80Hv2?#20Jav2?#80Iv2?#80P#7???7000#100000001000v2?#80I+/v2?#8#7???8000#10La+v2?#78v30B#1000v30#7???????????Iv30#1P#7???7000#100000001000v30#1Pv2?#80v30#1Pv24#128v2?#80Pv24#128v30#1P+/v24#8#7???8000#25+/v2?#8#7???8000#10Pv32#38v2?#80Pv32#38v30#1Pv2?#80#10000#126000La_v2#8v40La_v2#10v41La_v2#18v42La_v2#20v43La_v2#28v44La_v2#30v45La_v2#38v46La_v2#40v47La_v2#48v48La_v2#50v49La_v2#58v4:La_v2#60v4;La_v2#68v4<P_v2#68#68v2?#80P_v2#68#68v30#1P_v2#68#68+/v2?#8#7???8000#10,3+v2?##8++/v2?#8#7???8000##10+v30##1,1,25X#;0;3<#;0<10Y,T,1v40T,2v2T,8v41T,9v42T,:v29T,;v2?T,12v43T,13v44T,14v45T,15v46T,16v47T,17v48T,18v49T,19v4:T,1:v4;T,1;v4<Nbv30#Nb+/v2?#8#7???800;#?5Nb+/v2?#8#7???800:#?5Nb+/v2?#8#7???8009#?5Nb+/v2?#8#7???8008#?5Nb+/v2?#8#7???800?#?5Nb+/v2?#8#7???800>#?5Nb+/v2?#8#7???800=#?5Nb+/v2?#8#7???800<#?5Nb+/v2?#8#7???8003#?5Nb+/v2?#8#7???8002#?5Nb+/v2?#8#7???8001#?5Nb+/v2?#8#7???8000#?5Nb+/v2?#8#7???8007#?5Nb+/v2?#8#7???8006#?5Nb+/v2?#8#7???8005#?5Nb+/v2?#8#7???8004#?5Lbv2?#45>0360>Jb+v2?#8#78"%pstring.
Lemma bsrR_conc (fx : FPState) (R : PStmt.RTY) (M : PStmt.MTY) (V : PStmt.VTY) :
ltac:(r1mk L5.defined [KS_bsrR] fx R M V bsrR_conc_s).
Proof. r1pf PConcR.PR.zeros_r [KS_bsrR] LibSegJb_bsrR.regs0 LibSegJb_bsrR.kn0 LibSegJb_bsrR.BR LibSegJb_bsrR.PSS LibSegJb_bsrR.NX0 LibSegJb_bsrR.F0 723772 LibSegJb_bsrR.seg_sound_ax fx R M V bsrR_conc_s. Qed.
End PMBSRP3.
