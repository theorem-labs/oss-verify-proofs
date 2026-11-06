(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk AsanAcct HeapIface HeapIfaceA HeapIfaceAEx L5Defs L5Core L5DefsA L5CoreA PmLayout PmLayoutA PmModel PmStatics PmStaticsA
     PmSpecs PmSpecsA PmSpecsAX PeCLayout PeCLayoutB PeCSink PeCModel PeCSpecs PeCSinkA PeCModelA PeCStaticsA PeCSpecsA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeCSpecsAb () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout8pa_rw_loC13~~~K46Stdlib9micromega7EnvRing5PExpr01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout9pa_canaryC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout?pa_errcat_guardC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout?pa_syscat_guardC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout:pa_glocaleC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout9pa_atexitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout=pa_need_locksC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout>pa_locale_lockC13~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2or00C47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout;pa_loc_footC13~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2or01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PmStatics4PMST8addrs_wf01C13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCLayoutB7CADDR_BC13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PECSB.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeCLayoutB.CADDR_B.
Abbreviation AAD := PeCLayoutB.CAADDR_B.
Abbreviation EE := PeCLayoutB.EADDR_B.

Lemma addrs_wf_B : PMST.addrs_wf AD.
Proof.
ltac2:(KReplay.run1 (kr_t_PeCSpecsAb ()) [] "h07__arithh14__ffh28__varmaph35__with46__sat0h56__sat1h61Hh72ivh82Hap;1p;2p;3p;4p;6p;;p;7g0000j11Tg000Uj1<Tg0013j15Tg001Xj2pTg002@j2DTg002\j2^Tg0039j3[Tg003]j1XTg004=j1VTg004]j1UTg005;j1OTg005Yj1oTg006Dj1bTg006bj3`Tg007Ej2]Tg007gj2JTg008Aj2\Tg008mj37Tg009Gj3ZTg009fj4YTg00:Xj26Tg00;4j1WTg00<@j2HTg00<cj1TTg00>0j1PTg00?Cj1QTg00@Vj1RTg00Adj1STg00C1j1nTg00DBj1mTg00ETj2lTg00F4j4MTg00FTR0j2?Tg00Fnj6LTg00GJj1jTg00HYj3iTg00I0j2CTg00IMj2:Tg00Ihj3hTg00JBj3KTg00Jej4dTg00K@j4eTg00KZj2aTg00L4l;fTg00MHj4ETg00N3j7BTg00NWj7NTg00O;j3kTg00OXj3_Tf0R1#1#1p=4g00P5R2/61p=F%11#1#1#1p=@%11#1#1#<p=8g00PSR3/H1p=2%51#5p=3%51#1p=;f6R4g00Q1R5g00QPR6P6g00R0R7f5R8P5P6P6P7P3f4R9g00RPR:f3R;CEg00S7R<FBf2R=P5P6P6P7P3f1R>g00SWP1CEP<FBFNp=91D>1,:=p=I%11#5p=A162=1D>1':p=0%11#<p=GAk331p=>A_331p==P=P5P6P6P7P3P>P:P1CEP<FBp=gP9P5P6P6P7P;P5P6P6P7P3P=P:P>CEP<FBP1FNp=cg00T>R<g00UKR:#1R6#<R5%56#4R?#1R@#<RA'pRB1D25%FA1^5ARC,D2[[RD%F5REg00V0RFA[5A>UW8RA%FC\F^8EREg00VLRF#XRG%VFRF%U3RH%O3RI%o3RJPJ%16R6#1#4RK#@#@#8RL#2%56#3#3#;#@#@#8R6#2RMPJPM%25%b@5`3R@F91]J7R7P1P=g00W8R5g00WXRM'J1\1==75MdAZ32>CYRMb1b2b316L6?I6CP1b0b4b5%W<R6,6L?I6CePBPDPAPEPGPFPHPIPJPJ1H32R2%;:R:#5#4#3#A#4R6#4#3#;RL#4#8R5#2RNPJPNP@F9P7PMb1b2b3A055CP1b0b4b5%T<R5?05CePBPDPAPEPGPFPHPIPJPJP2%1:#3#3#4R:#1R5#1#3#3#@#8RN#2ROPJPOP@F9P7PMb1b2b3A0NNCP1b0b4b5%P<RN?0NCePBPDPAPEPGPFPHPIPJPJP2%;5R5#A#;#3#4RN#1#GRO#2RPPJPPP@F9P7PMb1b2b3A0OOCP1b0b4b5%Q<RO?0OCePBPDPAPEPGPFPHPIPJPJP2%55#3#4#A#8R5#2ROPJPOP@F9P7PMb1b2b3A055CP1b0b4b5%R<RP?0PCePBPDPAPEPGPFPHPIPJPJP2%;L#8RL#2RQPJPQP@F9P7PMb1b2b3A0LLCP1b0b4b5%S<RL?0LCePBPDPAPEPGPFPHPIPJPJP2%56#4R6#4#A#4#3#<RL#2RQPJPQP@F9P7PMb1b2b3A0LLCP1b0b4b5%n<RL?0LCePBPDPAPEPGPFPHPIPJPJP2%56#3#;#8R6#2RLPJPLP@F9P7PMb1b2b3A066CP1b0b4b5%m<R6?06Ce1l33R6P3P3%5N#GRN%5:R:#1#4#A#3#;#8RLCMRQ=761P3P3%5:#@R:#4#3#8RR%3:#;#8R:CMRS=761g00X8RT'?'?RUP0A76Q>A76S>/?T%>=%==;0CP1A76Q=P6PQ%>1RV%=1RW;0CX76RXPBPDPAPEPGPFPHPIPJPJP2%2NRYPJ%2LRZP@F9P7PMb1b2b3A0NLCP1b0b4b5%>QR[%=QR\;0CeP;P1ELW6P1O1A76S=/?TP0A76S;PT%>9%=9;0CP1A76S9P6PSPXPBPDPAPEPGPFPHPIPJPJP2%2RPJ%2:P@F9P7PMb1b2b3A0R:CP1b0b4b5%>S%=S;0CeP8P1ELW6P1O1PT%>4%=4;0CP1n010000000X6TP1O1n200100000021100010000W6P1O1n200100000021100011000W6W7%j<9i61R<%>>%=>;0C[^76eP6%<KRK,C5RC,6V%5?#<R?,C5R5/6W':,:UX76PQA76QQRUA76SQ/?TRT'?RS16[C165\':R\1J6Q9hUTPGPFPHPIPJPJPY%2K9K3O%2?9K3O=gJZDcP7PMb1b2b316NC165L':P1b0P\eCd1:S\eCe1CPK,6V1CP?/6W':,:<X76,a6eM;fo"). Qed.

Section Names.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable P : PESKA.sink_policyA.
Definition make_ec_spec : Prop := @PECSPA.make_ec_spec SCFG_P RSEGS AD AAD EE L ar HI.
Definition rtv_spec : Prop := @PECSPA.rtv_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition read_value_spec : Prop := @PECSPA.read_value_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition read_key_spec : Prop := @PECSPA.read_key_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition begin_array_spec : Prop := @PECSPA.begin_array_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition begin_object_spec : Prop := @PECSPA.begin_object_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition end_array_spec : Prop := @PECSPA.end_array_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition end_object_spec : Prop := @PECSPA.end_object_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition get_length_spec : Prop := @PECSPA.get_length_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition parse_spec : Prop := @PECSPA.parse_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition reader_read_spec : Prop := @PECSPA.reader_read_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_null_spec : Prop := @PECSPA.v_null_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_bool_spec : Prop := @PECSPA.v_bool_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_uint64_spec : Prop := @PECSPA.v_uint64_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_int64_spec : Prop := @PECSPA.v_int64_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_double_spec : Prop := @PECSPA.v_double_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_begin_arr_spec : Prop := @PECSPA.v_begin_arr_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_begin_obj_spec : Prop := @PECSPA.v_begin_obj_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_begin_arr_len_spec : Prop := @PECSPA.v_begin_arr_len_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_begin_obj_len_spec : Prop := @PECSPA.v_begin_obj_len_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_end_arr_spec : Prop := @PECSPA.v_end_arr_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_end_obj_spec : Prop := @PECSPA.v_end_obj_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_key_spec : Prop := @PECSPA.v_key_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_string_spec : Prop := @PECSPA.v_string_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition v_flush_spec : Prop := @PECSPA.v_flush_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition put_length_spec : Prop := @PECSPA.put_length_spec SCFG_P RSEGS AD AAD EE L ar HI P.
Definition evec_alloc_spec : Prop := @PECSPA.evec_alloc_spec SCFG_P RSEGS AD EE L ar HI.
Definition evec_sbdtor_spec : Prop := @PECSPA.evec_sbdtor_spec SCFG_P RSEGS AD EE L ar HI.
Definition peek_spec : Prop := @PECSPA.peek_spec SCFG_P RSEGS AD L ar HI.
Definition ignore_spec : Prop := @PECSPA.ignore_spec SCFG_P RSEGS AD L ar HI.
Definition src_read_spec : Prop := @PECSPA.src_read_spec SCFG_P RSEGS AD L ar HI 32.
Definition fill_buffer_spec : Prop := @PECSPA.fill_buffer_spec SCFG_P RSEGS AD L ar HI.
Definition read_span_spec : Prop := @PECSPA.read_span_spec SCFG_P RSEGS AD L ar HI.
Definition str_ctor_c_spec : Prop := @PECSPA.str_ctor_c_spec SCFG_P RSEGS AD L ar HI.
Definition iss_ctor_c_spec : Prop := @PECSPA.iss_ctor_c_spec SCFG_P RSEGS AD L ar HI.
Definition reset_spec : Prop := @PECSPA.reset_spec SCFG_P RSEGS AD L ar HI.
Definition reader_ctor_spec : Prop := @PECSPA.reader_ctor_spec SCFG_P RSEGS AD L ar HI.
Definition pay_in (Q : list byte -> Prop) : Prop := @PECSPA.pay_in P Q.
Definition pay_out (Q : list byte -> Prop) : Prop := @PECSPA.pay_out P Q.
(* [comment removed for export] *)
Definition push_mi_spec : Prop := @PMSAX.push_mi_spec SCFG_P RSEGS AD AAD L ar HI.
Definition push_miu_spec : Prop := @PMSAX.push_miu_spec SCFG_P RSEGS AD AAD L ar HI.
Definition push_ms_spec : Prop := @PMSAX.push_ms_spec SCFG_P RSEGS AD AAD L ar HI.
Definition push_msu_spec : Prop := @PMSAX.push_msu_spec SCFG_P RSEGS AD AAD L ar HI.
Definition ann_shrink_spec : Prop := @PMSAX.ann_shrink_spec SCFG_P RSEGS AD AAD L ar HI.
Definition ann_delete_spec : Prop := @PMSAX.ann_delete_spec SCFG_P RSEGS AD AAD L ar HI.
End Names.
End PECSB.
