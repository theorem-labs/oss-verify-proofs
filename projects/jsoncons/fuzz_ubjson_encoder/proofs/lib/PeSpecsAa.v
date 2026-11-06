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
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk HeapIface HeapIfaceA L5Defs PmLayout PmLayoutA PmModel PmStatics PmStaticsA
     HeapIfaceAEx L5DefsA PmSpecsA PnLayout PeLayoutA PnStatics.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeSpecsAa () := "C46Stdlib5Lists4List2InK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout8pa_rw_loC13~~~K46Stdlib9micromega7EnvRing5PExpr01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout9pa_canaryC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout?pa_errcat_guardC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout?pa_syscat_guardC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout:pa_glocaleC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout9pa_atexitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout=pa_need_locksC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout>pa_locale_lockC13~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2or00C47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout;pa_loc_footC13~~~C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2or01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PmStatics4PMST8addrs_wf01C13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeLayoutA6ADDR_AC13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PnLayout3PNL<pn_inf_guardC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PnLayout3PNL<pn_nan_guardC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PnLayout3PNL:pn_inf_objC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PnLayout3PNL:pn_nan_objC13~~~C47Corelib4Init5Logic3notK89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PnStatics4PNST8addrs_wf01C13~~~K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega=RingMicromega3Op201C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeLayoutA7NADDR_AC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeSpecsAa3PMA:addrs_wf_AC13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMA.
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeLayoutA.ADDR_A.
Abbreviation AAD := PeLayoutA.AADDR_A.
Abbreviation AN := PeLayoutA.NADDR_A.
(* [comment removed for export] *)
Definition EXT : HAJ.ext_consts := HAJ.EXTC (paa_annotate AAD) 2304 (paa_cxa_atexit_icpt AAD) 1024 (pa_atexit AD) (paa_atexit_f0 AAD) (paa_atexit_a0 AAD)
  (PNL.pn_drv_call AN) (PNL.pn_drv_guard AN) (* [comment removed for export] *) (paa_at_cxa_atexit AAD) (pa_need_locks AD) 0x5ec6c 16.
(* [comment removed for export] *)
Definition SM_PC (k : Z) : Z := nth (Z.to_nat k) [0x5e414; 0x5e588; 0x5e718; 0x5e8b4; 0x5ea60; 0x5ea60] 0.

(* [comment removed for export] *)
Record layout (L : asan_layout) (C : asan_statics_cells) : Prop := LAY {
  ly_as0 : L5A.as0_layout L C;            (* [comment removed for export] *)
  ly_tp : hl_tp L = pa_tp AD;
  ly_sm : forall k, In k [0; 1; 2; 3; 5] -> hl_stack_malloc L k = SM_PC k;
  ly_cost : hl_k_per_malloc L = 8 /\ hl_b_lin L = 3 /\ hl_b_overhead L = 2 ^ 21;
  ly_static : forall a, PNST.dep AD AN a -> ~ hl_rt_static L a;      (* [comment removed for export] *)
  ly_static_data : forall a, 0x13d8d8 <= a < 0x13e340 -> ~ hl_rt_static L a;   (* [comment removed for export] *)
  ly_ro : forall a, hl_rt_ro L a -> 0x10000 <= a < 0x13a000;
  ly_cxa_cells : In (0x13b168, 8, 0x11a21c) (asc_cells C) /\ In (pa_tp AD + 16, 4, 0) (asc_cells C)
      (* [comment removed for export] *);
  ly_ctr_static : forall a, hl_tp L + 16 <= a < hl_tp L + 20 -> hl_rt_static L a;
  ly_errno_cw : forall a, pa_tp AD - 164 <= a < pa_tp AD - 160 -> ~ hl_rt_static L a
      (* [comment removed for export] *)
}.

Lemma addrs_wf_A : PMST.addrs_wf AD.
Proof.
ltac2:(KReplay.run1 (kr_t_PeSpecsAa ()) [] "h07__arithh14__ffh28__varmaph35__with46__sat0h56__sat1h61Hh72ivh82Hap;1p;2p;3p;4p;6p;;p;7p-1g0000R0p4p710p8g000Gj11Tg000lj1=Tg001Jj14Tg001oj2pTg002Wj2DTg0033j2^Tg003Pj3[Tg0044j1XTg004Tj1VTg0054j1UTg005Rj1OTg0060j1oTg006[j1bTg0079j3`Tg007\j2]Tg008>j2JTg008Xj2\Tg009Dj37Tg009^j3ZTg00:=j4YTg00:oj26Tg00;Kj1WTg00<Wj2HTg00=:j1TTg00>Gj1PTg00?Zj1QTg00@mj1RTg00B;j1STg00CHj1nTg00DYj1mTg00Ekj2lTg00FKj4MTg00FkR1j2@Tg00GEj6LTg00Gaj1jTP0j3iTg00I0j2CTg00IMj2;Tg00Ihj3hTg00JBj3KTg00Jej4dTg00K@j4eTg00KZj2aTg00L4l;fTg00MHj4ETg00N3j7BTg00NWj7NTg00O;j3kTg00OXj3_Tf0R0#1#1p=5g00P5R2/60p=F%10#1#1#1p=A%10#1#1#=p=8g00PSR3/H0p=2%40#4p=9%10#4p=<f6R4g00Q1R5g00QPR6P6g00R0R7f5R8P5P6P6P7P3f4R9g00RPR:f3R;CEg00S7R<FBf2R=P5P6P6P7P3f1R>g00SWP0CEP<FBFNp=:1D>0,;=p=I%40#1p=3162=1D>0';p=0%10#=p=GAk330p=?A_330p=>P=P5P6P6P7P3P>P:P0CEP<FBp=gP9P5P6P6P7P;P5P6P6P7P3P=P:P>CEP<FBP0FNp=cg00T>R<g00UIR:#1R6#=R5%46#5R?#1R@#=RA'pRB1D25%FA1^5ARC,D2[[RD%F5REg00UnRFA[5A>UW8RA%FC\F^8EREg00VJRF#XRG%VFRF%U3RH%O3RI%o3RJPJ%16R6#1#5RK#A#A#8RL#2%46#9#<#5#A#A#8R6#2RMPJPM%25%b@5`3R@F:1]J7R7P0P=g00W6R5g00WVRM'J1\0==75MdAZ32>CYRMb1b2b316L6?I6CP0b0b4b5%W<R6,6L?I6CePBPDPAPEPGPFPHPIPJPJ1H32R2%3:R:#4#5#3#3#9R6#<#<#3RL#5#8R5#2RNPJPNP@F:P7PMb1b2b3A055CP0b0b4b5%T<R5?05CePBPDPAPEPGPFPHPIPJPJP2%1:#9#3#3R:#1R5#1RN#1RO#1#<#A#8RP#2RQPJPQP@F:P7PMb1b2b3A0PPCP0b0b4b5%P<RP?0PCePBPDPAPEPGPFPHPIPJPJP2%3O#3#9#5RO#1#GRP#2RQPJPQP@F:P7PMb1b2b3A0PPCP0b0b4b5%Q<RP?0PCePBPDPAPEPGPFPHPIPJPJP2%3N#<#5#<#8RN#2RPPJPPP@F:P7PMb1b2b3A0NNCP0b0b4b5%R<RQ?0QCePBPDPAPEPGPFPHPIPJPJP2%3L#8RL#2RRPJPRP@F:P7PMb1b2b3A0LLCP0b0b4b5%S<RL?0LCePBPDPAPEPGPFPHPIPJPJP2%46#<R6#5#<#5#9#=RL#2RRPJPRP@F:P7PMb1b2b3A0LLCP0b0b4b5%n<RL?0LCePBPDPAPEPGPFPHPIPJPJP2%46#9#3#8R6#2RLPJPLP@F:P7PMb1b2b3A066CP0b0b4b5%m<R6?06Ce1l33R6P3P3%4O#GRO%45#5#9#9#3#8R5CMRL=760P3P3%3:#5#3R:#5#9#8RR%9:#3#8R:CMRS=760g00X6RT'@'@RUP1A76L>A76S>/@T%?=%>=;0CP0A76L=P6PL%?0RV%>0RW;0CX76RXPBPDPAPEPGPFPHPIPJPJP2%2ORYPJ%25RZP@F:P7PMb1b2b3A0O5CP0b0b4b5%?LR[%>LR\;0CeP;P0ELW6P0O1A76S=/@TP1A76S;PT%?9%>9;0CP0A76S9P6PSPXPBPDPAPEPGPFPHPIPJPJP2%2RPJ%2:P@F:P7PMb1b2b3A0R:CP0b0b4b5%?S%>S;0CeP8P0ELW6P0O1PT%?4%>4;0CP0n010000000X6TP0O1n200100000021100010000W6P0O1n200100000021100011000W6W7%j<9i60R<%?>%>>;0C[^76eP6%=KRK,CNRC,6V%4?#=R?,CNRN/6W';,;UX76PLA76LLRUA76SL/@TRT'@RS16OC16N5';R51J6L9hUTPGPFPHPIPJPJPY%2K9K3P%2?9K3P=gJZDcP7PMb1b2b3P5P0b0Cd16[C16N\';,;SeCe1CQK,6V1CQ?/6W';,;<X76,a6eM;fo"). Qed.
Lemma addrs_wf_B : PNST.addrs_wf AD AN.
Proof.
ltac2:(KReplay.run1 (kr_t_PeSpecsAa ()) [] "h07__arithh14__ffh28__varmaph35__with42ivh53Hinh61Hh72Hah86__sat0h96__sat1p;1p;2p;3p;4p;7p;6p;8g000Gj16Tg000lj15Tg001oj2gTg002Wj2>Tg0033j2XTg003Pj3UTg0044j1QTg004Tj1MTg0054j1KTg005Rj1JTg0060j1fTg00<Wj2ITg00MHj4ETg006[j1\Tg0079j3[Tg00NWj7ZTg007\j2YTg008>j2WTg008Xj2VTg009Dj34Tg009^j3TTg00:=j4STg00:oj2FTg00IMj20Tg00XSj1PTg00Ygj1OTg00[;j1LTg00\Mj1NTg00]_j1CTg00Ekj2RTg00FKj4GTg001Jj1ATg00FkR0j2DTg00GEj6HTg00Jej4=Tg00>Gj1eTg00B;j1dTg00?Zj1_Tg00Gaj1^Tg0000j3`Tg00^8j8]Tg00N3j7aTg00O;j3bTg00_Lj6cTf0R1#A#6p=2%61#6p=1g00P5R2/F1p=7f1R3g00Q1R4g00QPR5P5g00R0R6P1g00S7Fap=9g00PSR7/I1p=<%A1#Ap=:%61#Ap=;A4731p=BAb771p=8A4731#Cp=3P7P3g00`0P1CEp=@P3P4P5P5P6P1Ecp=?g00T>R8g00`WR9g00acg00UIR:#6R;#5R<%2;#1R;#5R='g1>2<%7=1X<=R>,>2R?[[%7<R@g00UnRAAU<=3UW7%7>\A^7@g00VJR@#QRA%M@R@%K7R=%J7RB%f7RCP4P5P5P6P71I72R5g00RPP5CE,9CP7P5g00SW%<<%\;5[7CE,9CFZ1YC6R6P1f2R;g00W6R<g00WVR4'W1V1;=4<4dAT723CSR4b1b2b31F22/0?P1b0b8b9R?%P9R<#71><>'0eP?%O9RD#71>D>'0eP?%L9RE#71>E>'0eP?%N9R9#71>9>'0e%2:R:#6#:#2#2R>#6R?#1RF#1#2#1#1#1#5RG%2:#;#;#;#2#2#:#;#1#1#5R:'BRH#C%2F#2#:#1RF#1#5RI/B:RJ#CRKA472:R2#CRL1R77RMP7P7%2F#5RF%2?#;#:#:#1#1#5CGR?=4M1P7P7%2>#1#2R>#6#;#2#1#5R7%A>#:#1#1#5CGR>=4M1g00X6RN'D'DRO%83RP/3:[]4RQ,0LRR,0LRS,0LRT'0RU'0PAP@P=PB%<G%<:RG'@,9C,?CP6P4b1b2b3PN\HP1b0PKPUPAP@P=PB%<I/@G,9C,?CP6P4b1b2b3PN\JP1b0PLPTPAP@P=PB1@5G,9C,?CP6P4b1b2b3PN\2P1b0R2PLPSP2PLPRP2PLPQP2P0A4M?3A4M>3/DN%8;/3:P1A4M?;PMP?%81/3:X4MR3PAP@P=PB%<F/@G,9C,?CP6P4b1b2b31BF:PN[P1b0%8?/3:ef3R?P1EHW6P1O1A4M>;/DNP0A4M>?PNf4R?#8/3:P1A4M>?PMP>P3PAP@P=PB%<7/@G,9C,?CP6P4b1b2b31B7:PN[P1b0%8>/3:ef5P1EHW6P1O1PNf6#8/3:P1n010000000X5NP1O1n200100000021100010000W5P1O1n200100000021100011000X5OX4MC=C=C=C=C=C=%e8%d8RO'3%_8/3O13<O13DO13EO139O%^89`M113PO[^4M'0'0'0'0'0'0eG]o"). Qed.

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
End PMA.
