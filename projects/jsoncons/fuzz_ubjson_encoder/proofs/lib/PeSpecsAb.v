(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs PmLayout PmLayoutA PmModel PmStatics PmStaticsA
     HeapIfaceAEx L5DefsAB0 PmSpecsA PnLayout PeLayoutA PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeSpecsAb () := "C46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout8pa_rw_loC13~~~K46Stdlib9micromega7EnvRing5PExpr01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout9pa_canaryC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout?pa_errcat_guardC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout?pa_syscat_guardC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout:pa_glocaleC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout9pa_atexitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout=pa_need_locksC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout>pa_locale_lockC13~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2or00C47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout;pa_loc_footC13~~~C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2or01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PmStatics4PMST8addrs_wf01C13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeLayoutA6ADDR_BC13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PnLayout3PNL<pn_inf_guardC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PnLayout3PNL<pn_nan_guardC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PnLayout3PNL:pn_inf_objC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PnLayout3PNL:pn_nan_objC13~~~C47Corelib4Init5Logic3notK89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PnStatics4PNST8addrs_wf01C13~~~K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeLayoutA7NADDR_BC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeSpecsAb3PMB:addrs_wf_AC13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMB.
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Abbreviation AD := PeLayoutA.ADDR_B.
Abbreviation AAD := PeLayoutA.AADDR_B.
Abbreviation AN := PeLayoutA.NADDR_B.
(* [comment removed for export] *)
Definition EXT : HAJ.ext_consts := HAJ.EXTC (paa_annotate AAD) 2304 (paa_cxa_atexit_icpt AAD) 1024 (pa_atexit AD) (paa_atexit_f0 AAD) (paa_atexit_a0 AAD)
  (PNL.pn_drv_call AN) (PNL.pn_drv_guard AN) (* [comment removed for export] *) (paa_at_cxa_atexit AAD) (pa_need_locks AD) 0x5f494 16.
(* [comment removed for export] *)
Definition SM_PC (k : Z) : Z := nth (Z.to_nat k) [0x5ec3c; 0x5edb0; 0x5ef40; 0x5f0dc; 0x5f288; 0x5f288] 0.

(* [comment removed for export] *)
Record layout (L : asan_layout) (C : asan_statics_cells) : Prop := LAY {
  ly_as0 : L5A.as0_layout L C;            (* [comment removed for export] *)
  ly_tp : hl_tp L = pa_tp AD;
  ly_sm : forall k, In k [0; 1; 2; 3; 5] -> hl_stack_malloc L k = SM_PC k;
  ly_cost : hl_k_per_malloc L = 8 /\ hl_b_lin L = 3 /\ hl_b_overhead L = 2 ^ 21;
  ly_static : forall a, PNST.dep AD AN a -> ~ hl_rt_static L a;      (* [comment removed for export] *)
  ly_static_data : forall a, 0x141fe8 <= a < 0x142a10 -> ~ hl_rt_static L a;   (* [comment removed for export] *)
  ly_ro : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x13f000;
  ly_cxa_cells : In (0x13f878, 8, 0x11e9c4) (asc_cells C) /\ In (pa_tp AD + 16, 4, 0) (asc_cells C)
      (* [comment removed for export] *);
  ly_ctr_static : forall a, hl_tp L + 16 <= a < hl_tp L + 20 -> hl_rt_static L a;
  ly_errno_cw : forall a, pa_tp AD - 164 <= a < pa_tp AD - 160 -> ~ hl_rt_static L a
      (* [comment removed for export] *)
}.

Lemma addrs_wf_A : PMST.addrs_wf AD.
Proof.
ltac2:(KReplay.run1 (kr_t_PeSpecsAb ()) [] "h07__arithh14__ffh28__varmaph35__with46__sat0h56__sat1h61Hh72ivh82Hap;1p;2p;3p;4p;6p;;p;7p-1g0000R0p4p710p8g000Gj11Tg000lj1<Tg001Jj15Tg001oj2pTg002Wj2DTg0033j2^Tg003Pj3[Tg0044j1XTg004Tj1VTg0054j1UTg005Rj1OTg0060j1oTg006[j1bTg0079j3`Tg007\j2]Tg008>j2JTg008Xj2\Tg009Dj37Tg009^j3ZTg00:=j4YTg00:oj26Tg00;Kj1WTg00<Wj2HTg00=:j1TTg00>Gj1PTg00?Zj1QTg00@mj1RTg00B;j1STg00CHj1nTg00DYj1mTg00Ekj2lTg00FKj4MTg00FkR1j2?Tg00GEj6LTg00Gaj1jTP0j3iTg00I0j2CTg00IMj2:Tg00Ihj3hTg00JBj3KTg00Jej4dTg00K@j4eTg00KZj2aTg00L4l;fTg00MHj4ETg00N3j7BTg00NWj7NTg00O;j3kTg00OXj3_Tf0R0#1#1p=4g00P5R2/60p=F%10#1#1#1p=@%10#1#1#<p=8g00PSR3/H0p=2%50#5p=3%50#1p=;f6R4g00Q1R5g00QPR6P6g00R0R7f5R8P5P6P6P7P3f4R9g00RPR:f3R;CEg00S7R<FBf2R=P5P6P6P7P3f1R>g00SWP0CEP<FBFNp=91D>0,:=p=I%10#5p=A162=1D>0':p=0%10#<p=GAk330p=>A_330p==P=P5P6P6P7P3P>P:P0CEP<FBp=gP9P5P6P6P7P;P5P6P6P7P3P=P:P>CEP<FBP0FNp=cg00T>R<g00UIR:#1R6#<R5%56#4R?#1R@#<RA'pRB1D25%FA1^5ARC,D2[[RD%F5REg00UnRFA[5A>UW8RA%FC\F^8EREg00VJRF#XRG%VFRF%U3RH%O3RI%o3RJPJ%16R6#1#4RK#@#@#8RL#2%56#3#3#;#@#@#8R6#2RMPJPM%25%b@5`3R@F91]J7R7P0P=g00W6R5g00WVRM'J1\0==75MdAZ32>CYRMb1b2b316L6?I6CP0b0b4b5%W<R6,6L?I6CePBPDPAPEPGPFPHPIPJPJ1H32R2%;:R:#5#4#3#A#4R6#4#3#;RL#4#8R5#2RNPJPNP@F9P7PMb1b2b3A055CP0b0b4b5%T<R5?05CePBPDPAPEPGPFPHPIPJPJP2%1:#3#3#4R:#1R5#1#3#3#@#8RN#2ROPJPOP@F9P7PMb1b2b3A0NNCP0b0b4b5%P<RN?0NCePBPDPAPEPGPFPHPIPJPJP2%;5R5#A#;#3#4RN#1#GRO#2RPPJPPP@F9P7PMb1b2b3A0OOCP0b0b4b5%Q<RO?0OCePBPDPAPEPGPFPHPIPJPJP2%55#3#4#A#8R5#2ROPJPOP@F9P7PMb1b2b3A055CP0b0b4b5%R<RP?0PCePBPDPAPEPGPFPHPIPJPJP2%;L#8RL#2RQPJPQP@F9P7PMb1b2b3A0LLCP0b0b4b5%S<RL?0LCePBPDPAPEPGPFPHPIPJPJP2%56#4R6#4#A#4#3#<RL#2RQPJPQP@F9P7PMb1b2b3A0LLCP0b0b4b5%n<RL?0LCePBPDPAPEPGPFPHPIPJPJP2%56#3#;#8R6#2RLPJPLP@F9P7PMb1b2b3A066CP0b0b4b5%m<R6?06Ce1l33R6P3P3%5N#GRN%5:R:#1#4#A#3#;#8RLCMRQ=760P3P3%5:#@R:#4#3#8RR%3:#;#8R:CMRS=760g00X6RT'?'?RUP1A76Q>A76S>/?T%>=%==;0CP0A76Q=P6PQ%>0RV%=0RW;0CX76RXPBPDPAPEPGPFPHPIPJPJP2%2NRYPJ%2LRZP@F9P7PMb1b2b3A0NLCP0b0b4b5%>QR[%=QR\;0CeP;P0ELW6P0O1A76S=/?TP1A76S;PT%>9%=9;0CP0A76S9P6PSPXPBPDPAPEPGPFPHPIPJPJP2%2RPJ%2:P@F9P7PMb1b2b3A0R:CP0b0b4b5%>S%=S;0CeP8P0ELW6P0O1PT%>4%=4;0CP0n010000000X6TP0O1n200100000021100010000W6P0O1n200100000021100011000W6W7%j<9i60R<%>>%=>;0C[^76eP6%<KRK,C5RC,6V%5?#<R?,C5R5/6W':,:UX76PQA76QQRUA76SQ/?TRT'?RS16NC165L':RL1J6Q9hUTPGPFPHPIPJPJPY%2K9K3O%2?9K3O=gJZDcP7PMb1b2b3PLP0b0Cd16[C165\':,:SeCe1CPK,6V1CP?/6W':,:<X76,a6eM;fo"). Qed.
Lemma addrs_wf_B : PNST.addrs_wf AD AN.
Proof.
ltac2:(KReplay.run1 (kr_t_PeSpecsAb ()) [] "h07__arithh14__ffh28__varmaph35__with42ivh53Hinh61Hh72Hah86__sat0h96__sat1p;1p;2p;3p;4p;7p;6p;8g000Gj17Tg000lj15Tg001oj2gTg002Wj2?Tg0033j2XTg003Pj3UTg0044j1QTg004Tj1MTg0054j1KTg005Rj1JTg0060j1fTg00<Wj2ITg00MHj4ETg006[j1\Tg0079j3[Tg00NWj7ZTg007\j2YTg008>j2WTg008Xj2VTg009Dj33Tg009^j3TTg00:=j4STg00:oj2FTg00IMj21Tg00XSj1PTg00Ygj1OTg00[;j1LTg00\Mj1NTg00]_j1CTg00Ekj2RTg001Jj1;Tg00FKj4GTg00FkR0j2DTg00GEj6HTg00Jej4=Tg00>Gj1eTg00B;j1dTg00?Zj1_Tg00Gaj1^Tg0000j3`Tg00^8j8]Tg00N3j7aTg00O;j3bTg00_Lj6cTf0R1#;#7p=4%71#7p=0g00P5R2/F1p=8f1R3g00Q1R4g00QPR5P5g00R0R6P1g00S7Fap=:g00PSR7/I1p=>%;1#;p=6%71#;p=<A3731p=BAb771p=9A3731#Cp=2P7P3g00`0P1CEp=AP3P4P5P5P6P1Ecp=@g00T>R8g00`WR9g00acg00UIR:#7R;#5R<%4;#0R;#5R='g1?2<%8=1X<=R>,?2R?[[%8<R@g00UnRAAU<=3UW7%8>\A^7@g00VJR@#QRA%M@R@%K7R=%J7RB%f7RCP4P5P5P6P71I72R5g00RPP5CE,:CP7P5g00SW%><%\;5[7CE,:CFZ1YC6R6P1f2R;g00W6R<g00WVR4'W1V1;=3<4dAT723CSR4b1b2b31F22/1?P1b0b8b9R?%P9R<#81?<>'1eP?%O9RD#81?D>'1eP?%L9RE#81?E>'1eP?%N9R9#81?9>'1e%4:R:#7#6#6#0R>#7R?#<#6#4#0#0#0#5RF%4:#<#4#4#0#<#6#<#0#0#5R:'BRG#C%4?#<#4#6#0R?#0#5RH/B:RI#CRJA372:R2#CRK1R77RLP7P7%4?#5R?%;>R>#0#0#6#6#0#0#5CGRM=3L1P7P7%;>#0#0R>#7#<#4#0#5R7%;>#6#0#0#5CGR>=3L1g00X6RN'D'DRO%93RP/2:[]4RQ,1KRR,1KRS,1KRT'1RU'1PAP@P=PB%>F%>:RF'A,:C,@CP6P4b1b2b3PN\GP1b0PJPUPAP@P=PB%>H/AF,:C,@CP6P4b1b2b3PN\IP1b0PKPTPAP@P=PB1A5F,:C,@CP6P4b1b2b3PN\2P1b0R2PKPSP2PKPRP2PKPQP2P0A3LM3A3L>3/DN%9;/2:P1A3LM;PLPM%91/2:X4LR3PAP@P=PB%>?/AF,:C,@CP6P4b1b2b31B?:PN[P1b0%9M/2:ef3RMP1EHW6P1O1A3L>;/DNP0A3L>MPNf4RM#9/2:P1A3L>MPLP>P3PAP@P=PB%>7/AF,:C,@CP6P4b1b2b31B7:PN[P1b0%9>/2:ef5P1EHW6P1O1PNf6#9/2:P1n010000000X5NP1O1n200100000021100010000W5P1O1n200100000021100011000X5OX4LC=C=C=C=C=C=%e8%d8RO'2%_8/2O12<O12DO12EO129O%^89`L112PO[^4L'1'1'1'1'1'1eG]o"). Qed.

Section Names.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Definition opnew_spec := @PMSPA.opnew_spec SCFG_P RSEGS AD L ar HI.
Definition opdel_spec := @PMSPA.opdel_spec SCFG_P RSEGS AD L ar HI.
Definition opdel_sized_spec := @PMSPA.opdel_sized_spec SCFG_P RSEGS AD L ar HI.
Definition str_ctor_spec := @PMSPA.str_ctor_spec SCFG_P RSEGS AD L ar HI.
Definition locale_ctor_spec := @PMSPA.locale_ctor_spec SCFG_P RSEGS AD L ar HI.
Definition locale_dtor_spec := @PMSPA.locale_dtor_spec SCFG_P RSEGS AD L ar HI.
Definition iss_ctor_spec := @PMSPA.iss_ctor_spec SCFG_P RSEGS AD L ar HI.
Definition reader_ctor_spec := @PMSPA.reader_ctor_spec SCFG_P RSEGS AD L ar HI.
Definition syscat_spec := @PMSPA.syscat_spec SCFG_P RSEGS AD L ar HI.
Definition reset_spec := @PMSPA.reset_spec SCFG_P RSEGS AD L ar HI.
Definition make_ec_spec := @PMSPA.make_ec_spec SCFG_P RSEGS AD AAD L ar HI.
Definition src_dtor_spec := @PMSPA.src_dtor_spec SCFG_P RSEGS AD L ar HI.
Definition ios_dtor_spec := @PMSPA.ios_dtor_spec SCFG_P RSEGS AD L ar HI.
Definition rtv_spec := @PMSPA.rtv_spec SCFG_P RSEGS AD AAD L ar HI.
Definition read_value_spec := @PMSPA.read_value_spec SCFG_P RSEGS AD AAD L ar HI.
Definition read_key_spec := @PMSPA.read_key_spec SCFG_P RSEGS AD AAD L ar HI.
Definition begin_array_spec := @PMSPA.begin_array_spec SCFG_P RSEGS AD AAD L ar HI.
Definition begin_object_spec := @PMSPA.begin_object_spec SCFG_P RSEGS AD AAD L ar HI.
Definition end_array_spec := @PMSPA.end_array_spec SCFG_P RSEGS AD AAD L ar HI.
Definition end_object_spec := @PMSPA.end_object_spec SCFG_P RSEGS AD AAD L ar HI.
Definition get_length_spec := @PMSPA.get_length_spec SCFG_P RSEGS AD AAD L ar HI.
Definition read_span_spec := @PMSPA.read_span_spec SCFG_P RSEGS AD L ar HI.
Definition parse_spec := @PMSPA.parse_spec SCFG_P RSEGS AD AAD L ar HI.
Definition validate_spec := @PMSPA.validate_spec SCFG_P RSEGS AD L ar HI.
Definition is_base10_spec := @PMSPA.is_base10_spec SCFG_P RSEGS AD L ar HI.
Definition str_resize_spec := @PMSPA.str_resize_spec SCFG_P RSEGS AD L ar HI.
Definition xsgetn_spec := @PMSPA.xsgetn_spec SCFG_P RSEGS AD L ar HI.
Definition fill_buffer_spec := @PMSPA.fill_buffer_spec SCFG_P RSEGS AD L ar HI.
Definition peek_spec := @PMSPA.peek_spec SCFG_P RSEGS AD L ar HI.
Definition ignore_spec := @PMSPA.ignore_spec SCFG_P RSEGS AD L ar HI.
Definition src_read_spec := @PMSPA.src_read_spec SCFG_P RSEGS AD L ar HI.
Definition fill_buffer_tb_spec := @PMSPA.fill_buffer_tb_spec SCFG_P RSEGS AD L ar HI.
Definition srd_read_spec := @PMSPA.srd_read_spec SCFG_P RSEGS AD L ar HI.
Definition reader_read_spec := @PMSPA.reader_read_spec SCFG_P RSEGS AD AAD L ar HI.
Definition vec_dtor_spec := @PMSPA.vec_dtor_spec SCFG_P RSEGS AD L ar HI.
End Names.
End PMB.
