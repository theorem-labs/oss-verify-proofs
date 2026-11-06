(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec StoreOk HeapIface L5Defs L5Core PmLayout PeLayoutU PmModel PmStatics PmSpecs PmSpecsX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeSpecsU () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout8pa_rw_loC13~~~K46Stdlib9micromega7EnvRing5PExpr01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout9pa_canaryC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout?pa_errcat_guardC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout?pa_syscat_guardC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout:pa_glocaleC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout9pa_atexitC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout=pa_need_locksC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout>pa_locale_lockC13~~~I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01I47Corelib4Init5Logic2or00C47Corelib4Init5Logic6eq_indC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout;pa_loc_footC13~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic3and00K47Corelib4Init5Logic2or01K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01I47Corelib4Init5Logic2ex00K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PmStatics4PMST8addrs_wf01C13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeLayoutU6ADDR_UC13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PMU.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation AD := PeLayoutU.ADDR_U.

(* [comment removed for export] *)
Record layout (L : heap_layout) : Prop := LAY {
  ly_segs : hl_segs L = RSEGS;
  ly_tp : hl_tp L = pa_tp AD;
  ly_img_lo : hl_img_lo L = 0x10000;
  ly_img_hi : hl_img_hi L = 0xee000;
  ly_stack : hl_stack L = 8224;
  ly_ro : forall a, hl_alloc_ro L a -> (hl_img_lo L <= a < hl_img_hi L) \/ hl_sptop L <= a;
  ly_errno : hl_errno L = 0xccb1c;
  ly_static : forall a, hl_alloc_static L a -> 0xecfc8 <= a < 0xed370;        (* [comment removed for export] *)
  ly_kpm : 0 <= hl_k_per_malloc L <= 8;
  ly_bov : 0 <= hl_b_overhead L <= 6350523;
  ly_malloc : hl_malloc L = 0x9f958;                                          (* [comment removed for export] *)
  ly_free : hl_free L = 0x9f818;
  ly_ro_foot : forall a, hl_alloc_ro L a -> ~ (0xbb028 <= a < 0xece28)                 (* [comment removed for export] *)
}.

Lemma addrs_wf_U : PMST.addrs_wf AD.
Proof.
ltac2:(KReplay.run1 (kr_t_PeSpecsU ()) [] "h07__arithh14__ffh28__varmaph35__with46__sat0h56__sat1h61Hh72ivh82Hap;1p;2p;3p;4p;6p;;p;7g0000j11Tg000Uj1>Tg0013j13Tg001Xj2pTg002@j2DTg002\j2^Tg0039j3\Tg003]j1YTg004=j1WTg004]j1UTg005;j1OTg005Yj1oTg006Dj1`Tg006bj3_Tg007Ej2]Tg007gj2JTg008Aj2[Tg008mj37Tg009Gj3ZTg009fj4XTg00:Xj25Tg00;4j1VTg00<@j2HTg00<cj1TTg00>0j1PTg00?Cj1QTg00@Vj1RTg00Adj1STg00C1j1nTg00DBj1mTg00ETj2lTg00F4j4MTg00FTR0j2@Tg00Fnj6LTg00GJj1iTg00HYj3hTg00I0j2CTg00IMj2;Tg00Ihj3gTg00JBj3KTg00Jej4dTg00K@j4eTg00KZj2bTg00L4l;aTg00MHj4BTg00N3j7ETg00NWj7NTg00O;j3jTg00OXj3kTf0R1#1#1p=?g00P5R2/51p=F%11#1#1#1p=A%11#1#1#>p=:g00PSR3/H1p=2%31#3p=8%11#3p=4%31#1p=6f6R4g00Q1R5g00QPR6P6g00R0R7f5R8P5P6P6P7P3f4R9g00RPR:f3R;CBg00S7R<FEf2R=P5P6P6P7P3f1R>g00SWP1CBP<FEFNp=91D>1,;=p=I152=1D>1';p=0%11#>p=GAj331p==Ak331p=<P=P5P6P6P7P3P>P:P1CBP<FEp=fP9P5P6P6P7P;P5P6P6P7P3P=P:P>CBP<FEP1FNp=cg00T>R<g00UIR:#1R6#>R5%36R?#?R@#1RA#>RB'pRC1D25%FB1^5BRD,D2[[RE%F5RFg00UnRGA\5B>UW8RB%FD\G^8FRFg00VJRG#YRH%WGRG%U3RI%O3RJ%o3RKPK%A6R6#A#A#:RL#2%8?#4#6#A#4#4#:R?#2RMPKPM%25%`A5_3RAF91]K7R7P1P=g00W6R5g00WVRM'J1[1==75MdAZ32>CXRMb1b2b315L??I?DP1b0b4b5%V<R?,5L?I?DePCPEPBPFPHPGPIPJPKPK1H32R2%3:R:#6#8#?#8R?#3RL#?R5#4#6#:RN#2ROPKPOPAF9P7PMb1b2b3A0NNDP1b0b4b5%T<RN?0NDePCPEPBPFPHPGPIPJPKPKP2%1:#4R:#1#8RN#1RO#1RP#1#8#6#?#:RQ#2RRPKPRPAF9P7PMb1b2b3A0QQDP1b0b4b5%P<RQ?0QDePCPEPBPFPHPGPIPJPKPKP2%8P#8#8#?RP#1#GRQ#2RRPKPRPAF9P7PMb1b2b3A0QQDP1b0b4b5%Q<RQ?0QDePCPEPBPFPHPGPIPJPKPKP2%6O#8#6#4#:RO#2RQPKPQPAF9P7PMb1b2b3A0OODP1b0b4b5%R<RR?0RDePCPEPBPFPHPGPIPJPKPKP2%1?#A#4#:R?#2RSPKPSPAF9P7PMb1b2b3A0??DP1b0b4b5%S<R??0?DePCPEPBPFPHPGPIPJPKPKP2%35#4#?#8#>R5#2R?PKP?PAF9P7PMb1b2b3A055DP1b0b4b5%n<R5?05DePCPEPBPFPHPGPIPJPKPKP2%6L#4#4#:RL#2R5PKP5PAF9P7PMb1b2b3A0LLDP1b0b4b5%m<RL?0LDe1l33RLP3P3%3P#GRP%3N#4#6#4#6#:RNCMR5=7L1P3P3%3:#A#6R:#1#6#8#:R?%3:#4#6#:R:CMRS=7L1g00X6RT'@'@RUP0A7L5>A7LS>/@T%==%<=;0DP1A7L5=PLP5%=1RV%<1RW;0DX7LRXPCPEPBPFPHPGPIPJPKPKP2%2PRYPK%2NRZPAF9P7PMb1b2b3A0PNDP1b0b4b5%=5R[%<5R\;0DeP;P1ELW6P1O1A7LS=/@TP0A7LS;PT%=9%<9;0DP1A7LS9PLPSPXPCPEPBPFPHPGPIPJPKPKP2%2?PK%2:PAF9P7PMb1b2b3A0?:DP1b0b4b5%=S%<S;0DeP8P1ELW6P1O1PT%=4%<4;0DP1n010000000X6TP1O1n200100000021100010000W6P1O1n200100000021100011000W6W7%i<9hL1R<%=>%<>;0D[^7LePL%>6R6,CORD,5V%3@#>R@,CORO/5W';,;UX7LP5A7L55RUA7LS5/@TRT'@RS15PD15ON';RN1JL59gUTPHPGPIPJPKPKPY%269K3Q%2@9K3Q=fKZDcP7PMb1b2b3PNP1b0Cd15[D15O\';,;SeCe1CR6,5V1CR@/5W';,;<X7L,bLeM;ao"). Qed.

Section Names.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Definition opnew_spec := PMSP.opnew_spec RSEGS AD L HI.
Definition opdel_spec := PMSP.opdel_spec RSEGS AD L HI.
Definition opdel_sized_spec := PMSP.opdel_sized_spec RSEGS AD L HI.
Definition str_ctor_spec := PMSP.str_ctor_spec RSEGS AD L HI.
Definition locale_ctor_spec := PMSP.locale_ctor_spec RSEGS AD L HI.
Definition locale_dtor_spec := PMSP.locale_dtor_spec RSEGS AD L.
Definition iss_ctor_spec := PMSP.iss_ctor_spec RSEGS AD L HI.
Definition reader_ctor_spec := PMSP.reader_ctor_spec RSEGS AD L HI.
Definition syscat_spec := PMSP.syscat_spec RSEGS AD L HI.
Definition reset_spec := PMSP.reset_spec RSEGS AD L HI.
Definition make_ec_spec := PMSP.make_ec_spec RSEGS AD L HI.
Definition src_dtor_spec := PMSP.src_dtor_spec RSEGS AD L HI.
Definition ios_dtor_spec := PMSP.ios_dtor_spec RSEGS AD L HI.
Definition rtv_spec := PMSP.rtv_spec RSEGS AD L HI.
Definition read_value_spec := PMSP.read_value_spec RSEGS AD L HI.
Definition read_key_spec := PMSP.read_key_spec RSEGS AD L HI.
Definition begin_array_spec := PMSP.begin_array_spec RSEGS AD L HI.
Definition begin_object_spec := PMSP.begin_object_spec RSEGS AD L HI.
Definition end_array_spec := PMSP.end_array_spec RSEGS AD L HI.
Definition end_object_spec := PMSP.end_object_spec RSEGS AD L HI.
Definition get_length_spec := PMSP.get_length_spec RSEGS AD L HI.
Definition read_span_spec := PMSP.read_span_spec RSEGS AD L HI.
Definition parse_spec := PMSP.parse_spec RSEGS AD L HI.
Definition peek_spec := PMSP.peek_spec RSEGS AD L HI.
Definition ignore_spec := PMSP.ignore_spec RSEGS AD L HI.
Definition src_read_spec := PMSP.src_read_spec RSEGS AD L HI.
Definition fill_buffer_spec := PMSP.fill_buffer_spec RSEGS AD L HI.
Definition validate_spec := PMSP.validate_spec RSEGS AD L.
Definition is_base10_spec := PMSP.is_base10_spec RSEGS AD L.
Definition str_resize_spec := PMSP.str_resize_spec RSEGS AD L HI.
Definition reader_read_spec := PMSX.reader_read_spec RSEGS AD L HI.
Definition vec_dtor_spec := PMSX.vec_dtor_spec RSEGS AD L HI.
End Names.
End PMU.
