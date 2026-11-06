(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PmModel PmStatics PmSpecs
     PeCLayout PeCLayoutS PeCSink PeCModel PeCSpecs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeCSpecsS () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout8pa_rw_loC13~~~K46Stdlib9micromega7EnvRing5PExpr01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout9pa_canaryC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout?pa_errcat_guardC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout?pa_syscat_guardC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout:pa_glocaleC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout9pa_atexitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout=pa_need_locksC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout>pa_locale_lockC13~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2or00C47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout;pa_loc_footC13~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2or01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PmStatics4PMST8addrs_wf01C13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCLayoutS7CADDR_SC13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSS.
Abbreviation RSEGS := Plain.M.loaded_segments.
Abbreviation AD := PeCLayoutS.CADDR_S.
Abbreviation EE := PeCLayoutS.EADDR_S.

Lemma addrs_wf_S : PMST.addrs_wf AD.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCSpecsS ()) [] "h07__arithh14__ffh28__varmaph35__with46__sat0h56__sat1h61Hh72ivh82Hap;1p;2p;3p;4p;6p;;p;7g0000j14Tg000Uj1>Tg0013j15Tg001Xj2oTg002@j2CTg002\j2^Tg0039j3[Tg003]j1XTg004=j1VTg004]j1PTg005;j1NTg005Yj1nTg006Dj1aTg006bj3_Tg007Ej2]Tg007gj2ITg008Aj2\Tg008mj38Tg009Gj3ZTg009fj4YTg00:Xj27Tg00;4j1WTg00<@j2GTg00<cj1UTg00>0j1OTg00?Cj1QTg00@Vj1RTg00Adj1STg00C1j1TTg00DBj1mTg00ETj2lTg00F4j4MTg00FTR0j2@Tg00Fnj6KTg00GJj1iTg00HYj3hTg00I0j2BTg00IMj2<Tg00Ihj3gTg00JBj3JTg00Jej4bTg00K@j4cTg00KZj2dTg00L4l;`Tg00MHj4ATg00N3j7DTg00NWj7LTg00O;j3jTg00OXj3kTf0R1#4#4p=1g00P5R2/71p=E%41#4#4#>p=9g00PSR3/G1p=2%51#5p=;%51#4p=6%41#5p=3f6R4g00Q1R5g00QPR6P6g00R0R7f5R8P5P6P6P7P3f4R9g00RPR:f3R;CAg00S7R<FDf2R=P5P6P6P7P3f1R>g00SWP1CAP<FDFLp=:1C>1,<=p=H172=1C>1'<p=0%41#>p=FAj331p=?Ak331p==P=P5P6P6P7P3P>P:P1CAP<FDp=fP9P5P6P6P7P;P5P6P6P7P3P=P:P>CAP<FDP1FLp=eg00T>R<g00UKR:#4R6#>R5%56R?#1R@#4RA#>RB'oRC1C25%EB1^5BRD,C2[[RE%E5RFg00V0RGA[5B>UW8RB%ED\G^8FRFg00VLRG#XRH%VGRG%P3RI%N3RJ%n3RKPK%16#1R6#1#1#1#1#9RL#2%;?#1#6#6#3#3#3#9R?#2RMPKPM%25%aA5_3RAF:1]K7R7P1P=g00W8R5g00WXRM'I1\1==85MdAZ32>CYRMb1b2b317L??H?DP1b0b4b5%W<R?,7L?H?DePCPEPBPFPHPGPIPJPKPK1G32R2%5:R:#6#6#;#1R?#5RL#3R5#3#6#9RN#2ROPKPOPAF:P7PMb1b2b3A0NNDP1b0b4b5%U<RN?0NDePCPEPBPFPHPGPIPJPKPKP2%1:#6R:#3RN#4#;#1#6#1#9RO#2RPPKPPPAF:P7PMb1b2b3A0OODP1b0b4b5%O<RO?0ODePCPEPBPFPHPGPIPJPKPKP2%5NRN#4RO#1#3#;#1RP#4#FRQ#2RRPKPRPAF:P7PMb1b2b3A0QQDP1b0b4b5%Q<RQ?0QDePCPEPBPFPHPGPIPJPKPKP2%5O#1#6#3#9RO#2RQPKPQPAF:P7PMb1b2b3A0OODP1b0b4b5%R<RR?0RDePCPEPBPFPHPGPIPJPKPKP2%4?#3#1#3#9R?#2RSPKPSPAF:P7PMb1b2b3A0??DP1b0b4b5%S<R??0?DePCPEPBPFPHPGPIPJPKPKP2%55#3#1#;#>R5#2R?PKP?PAF:P7PMb1b2b3A055DP1b0b4b5%T<R5?05DePCPEPBPFPHPGPIPJPKPKP2%;L#3#3#9RL#2R5PKP5PAF:P7PMb1b2b3A0LLDP1b0b4b5%m<RL?0LDe1l33RLP3P3%5P#FRP%;N#;#3#6#9RNCMR5=8L1P3P3%5:#1#;R:#3#6#;#9R?%6:#3#6#9R:CMRS=8L1g00X8RT'@'@RUP0A8L5>A8LS>/@T%?=%==;0DP1A8L5=PLP5%?1RV%=1RW;0DX7LRXPCPEPBPFPHPGPIPJPKPKP2%2PRYPK%2NRZPAF:P7PMb1b2b3A0PNDP1b0b4b5%?5R[%=5R\;0DeP;P1EKW6P1O1A8LS=/@TP0A8LS;PT%?9%=9;0DP1A8LS9PLPSPXPCPEPBPFPHPGPIPJPKPKP2%2?PK%2:PAF:P7PMb1b2b3A0?:DP1b0b4b5%?S%=S;0DeP8P1EKW6P1O1PT%?4%=4;0DP1n010000000X6TP1O1n200100000021100010000W6P1O1n200100000021100011000W6W7%i<9hL1R<%?>%=>;0D[^7LePL%>6R6,BORD,7V%5@#>R@,BORO/7W'<,<UX7LP5A8L55RUA8LS5/@TRT'@RS17[D17O\'<R\1IL59gUTPHPGPIPJPKPKPY%269J3Q%2@9J3Q=fKZDeP7PMb1b2b317PD17ON'<P1b0P\eCb1<S\eCc1BR6,7V1BR@/7W'<,<<X7L,dLeM;`o"). Qed.

Section Names.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Variable P : PESK.sink_policy.
Definition make_ec_spec : Prop := PECS.make_ec_spec RSEGS AD EE L HI.
Definition rtv_spec : Prop := PECS.rtv_spec RSEGS AD EE L HI P.
Definition read_value_spec : Prop := PECS.read_value_spec RSEGS AD EE L HI P.
Definition read_key_spec : Prop := PECS.read_key_spec RSEGS AD EE L HI P.
Definition begin_array_spec : Prop := PECS.begin_array_spec RSEGS AD EE L HI P.
Definition begin_object_spec : Prop := PECS.begin_object_spec RSEGS AD EE L HI P.
Definition end_array_spec : Prop := PECS.end_array_spec RSEGS AD EE L HI P.
Definition end_object_spec : Prop := PECS.end_object_spec RSEGS AD EE L HI P.
Definition get_length_spec : Prop := PECS.get_length_spec RSEGS AD EE L HI P.
Definition parse_spec : Prop := PECS.parse_spec RSEGS AD EE L HI P.
Definition reader_read_spec : Prop := PECS.reader_read_spec RSEGS AD EE L HI P.
Definition v_null_spec : Prop := PECS.v_null_spec RSEGS AD EE L HI P.
Definition v_bool_spec : Prop := PECS.v_bool_spec RSEGS AD EE L HI P.
Definition v_uint64_spec : Prop := PECS.v_uint64_spec RSEGS AD EE L HI P.
Definition v_int64_spec : Prop := PECS.v_int64_spec RSEGS AD EE L HI P.
Definition v_double_spec : Prop := PECS.v_double_spec RSEGS AD EE L HI P.
Definition v_begin_arr_spec : Prop := PECS.v_begin_arr_spec RSEGS AD EE L HI P.
Definition v_begin_obj_spec : Prop := PECS.v_begin_obj_spec RSEGS AD EE L HI P.
Definition v_begin_arr_len_spec : Prop := PECS.v_begin_arr_len_spec RSEGS AD EE L HI P.
Definition v_begin_obj_len_spec : Prop := PECS.v_begin_obj_len_spec RSEGS AD EE L HI P.
Definition v_end_arr_spec : Prop := PECS.v_end_arr_spec RSEGS AD EE L HI P.
Definition v_end_obj_spec : Prop := PECS.v_end_obj_spec RSEGS AD EE L HI P.
Definition v_key_spec : Prop := PECS.v_key_spec RSEGS AD EE L HI P.
Definition v_string_spec : Prop := PECS.v_string_spec RSEGS AD EE L HI P.
Definition v_flush_spec : Prop := PECS.v_flush_spec RSEGS AD EE L HI P.
Definition put_length_spec : Prop := PECS.put_length_spec RSEGS AD EE L HI P.
Definition evec_alloc_spec : Prop := PECS.evec_alloc_spec RSEGS AD EE L HI.
Definition evec_sbdtor_spec : Prop := PECS.evec_sbdtor_spec RSEGS AD EE L HI.
Definition peek_spec : Prop := PECS.peek_spec RSEGS AD L HI.
Definition ignore_spec : Prop := PECS.ignore_spec RSEGS AD L HI.
Definition src_read_spec : Prop := PECS.src_read_spec RSEGS AD L HI.
Definition fill_buffer_spec : Prop := PECS.fill_buffer_spec RSEGS AD L HI.
Definition read_span_spec : Prop := PECS.read_span_spec RSEGS AD L HI.
Definition str_ctor_c_spec : Prop := PECS.str_ctor_c_spec RSEGS AD L HI.
Definition iss_ctor_c_spec : Prop := PECS.iss_ctor_c_spec RSEGS AD L HI.
Definition pay_in (Q : list byte -> Prop) : Prop := PECS.pay_in P Q.
Definition pay_out (Q : list byte -> Prop) : Prop := PECS.pay_out P Q.
End Names.
End PECSS.
