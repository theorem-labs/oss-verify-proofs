(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core
     PmLayout PmModel PmStatics PmSpecs PeHeapR PeHeapS PeCSink.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Heap Require Export HeIface.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_PeHeapP () := "C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapS4PEHS;opnewS_specC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK4SP_SC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK7sp_modeC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_vmmapsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface7hi_heapC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP8model_okC13~~~K47Corelib4Init9Datatypes4list01K47Corelib7Numbers7BinNums1Z02K45stdpp9bitvector;definitions2bv01C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK6sp_cszC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55ra_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout5pa_tpC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface8hl_sptopC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C3stkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface>regs_preservedC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C;fresh_blockC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Core3L5C5hpresC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface<model_but_vmC13~~~K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z3subC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK6sp_capC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PmSpecs4PMSP3cfgC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout8pa_opnewC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeIface4fitsC13~~~C56Stdlib6ZArith6BinInt1Z7sub_0_rC47Corelib4Init5Logic8eq_ind_rc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapP4PEHP;opnewP_specC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec4getrC13~~~I47Corelib4Init5Logic2eq00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK47Corelib4Init9Datatypes4prod01I47Corelib7Numbers7BinNums1Z00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PropExec7FPState00C13~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface6creditC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapS4PEHS9OPNEW_SCRC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs2L55rangeC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapS4PEHS>opdelS_spec_atC13~~~C46Stdlib5Lists4List2InC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9HeapIface9lb_removeC13~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z7add_0_rc89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapP4PEHP>opdelP_spec_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapS4PEHS9OPDEL_SCRC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PmLayout8pa_opdelC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapP4PEHP>opdelP_of_S_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapS4PEHS;opnewF_specC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK4SP_TC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeIface6debitRC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapR4PMSR>opdelR_spec_atC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeIface7refundRC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapR4PMSR9OPDEL_SCRC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapP4PEHP>opdelP_of_R_atC13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PEHP.
Section Specs.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable segs : list Segment.
Variable A : pm_addrs.
Variable L : heap_layout.
Variable HI : heap_iface.

(* [comment removed for export] *)
Definition opnewP_spec (P : PESK.sink_policy) (NMAX : Z) : Prop :=
  PESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 n -> 0 < n <= NMAX -> 1 <= fst cr /\ PESK.sp_csz P n <= snd cr ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp PEHS.OPNEW_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B : Z),
        getr R' 10%bv = Z_to_bv 64 B -> regs_preserved R R' ->
        L5C.fresh_block L LB M' B n ->
        L5C.hpres L LB sp PEHS.OPNEW_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI ((B, n) :: LB) (fst cr - 1, snd cr - PESK.sp_csz P n) M' (m_vmmaps model') ->
        PESK.sp_cap P n ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R (pa_opnew A) M model) K.

(* [comment removed for export] *)
Definition opdelP_spec_at (P : PESK.sink_policy) (pc : Z) : Prop :=
  PESK.sp_mode P ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (B n sp r : Z),
    hi_heap HI LB cr M (m_vmmaps model) -> PMSP.model_ok model -> K [] ->
    In (B, n) LB -> getr R 10%bv = Z_to_bv 64 B ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 (pa_tp A) -> L5C.stk (hl_sptop L) M sp PEHS.OPDEL_SCR ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model),
        regs_preserved R R' ->
        L5C.hpres L (lb_remove B LB) sp PEHS.OPDEL_SCR [] M M' ->
        model_but_vm model model' -> hi_heap HI (lb_remove B LB) (fst cr + 1, snd cr + PESK.sp_csz P n) M' (m_vmmaps model') ->
        srealizes segs SCFG (PMSP.cfg segs R' r M' model') K) ->
    srealizes segs SCFG (PMSP.cfg segs R pc M model) K.
Definition opdelP_spec (P : PESK.sink_policy) : Prop := opdelP_spec_at P (pa_opdel A).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma opnewP_of_S (lim NMAX : Z) : PEHS.opnewS_spec segs A L HI lim NMAX -> opnewP_spec (PESK.SP_S lim) NMAX.
Proof.
ltac2:(KReplay.run1 (kr_t_PeHeapP ()) ["Specs"] "h01Bh12M'h22R'h33fx'h46model'h54NMAXh63limh74CONTh82FBh93FITh:1Hh;2H1h<3H10h=4H10'h>2H2h?2H4h@2HHhA3HH'hB2HMhC2HPhD2HchE2HnhF1KhG2K0hH2LBhI1MhJ2MBhK3MOKhL3OPNhM1RhN2RAhO2RPhP3STKhQ2_HhR2crhS2fxhT5modelhU1nhV1rhW2sphX1zp;8p;2p;1p;5p;3p;4p;7p;6g0000j8aTg001Cj22Tg002Oj1STg003^j17Tg004Cj1`Tg004hj1ETg005Fj1JTg005ij2RTg006Uj1QTg0077j2NTg007Wj1MTg0087j1ATg008nj5:Tg00::j1_Tg00;Jj1KTg00;jj1=Tg00<Hj3<Tg00<kj29Tg00=Qj2TTg00=mj26Tg00>IR0j2ITg00>dj28Tg00@2j1HTg00A<j1PTg00BEj1OTg00CRj4GTg00D[j2?Tg00Enj5>Tg00G?j7@Tg00HJj2BTg00I[j3;Tg00J;j21Tg00JXj2FTg00Kfj1LTg00Llj6CTg00N7j5DTg00OCj1^Tg00POj2]Tg00Q[j1\Tg00R<j6WTg00RZj2XTg00Smj2YTg00U5j3VTg00UOj3ZTg00Ulj3[Tg00VIj4UTf3R1f2R2f1R3'Yf0R43Vp=3g00ViR5?Z54p=4A[554p=5P5P5P3P4CUp=0p,6SCFG_PR6p,3bmKR7p,4segsR8p,1AR9p,1LR:p,2HIR;P3P4Ga1272R<#Sg00WGR=g00XTR>#7R?#`R@#ERA%7?RB#7RC#7#7#7#ERD#JRE'RRF%EC#J#Q\ERCg00Y9RGg00Yo1N55RH#Mg00[7P;f4RIP1f7RJf6RK#ARLD:%_JPJg00\B#KO1PEf;RM%7@#=g00]8R@5<ARNf5RO,9DC3g00]TRP/TKf@RQ,6K'I%=>R>f8RR#4'6fBRS,27/8J%5R'6'IP0f9R0#4,6>fCRT,27/8R%50'6PEf?RUA<A>@RV19DJC3%HRPEfARW%=?=<A@R?f:RX,9DRYC3PEPS%=B=<A@R@%P9,9DRAC3%O:RBPSf<RZg00^2R[CGPEP1PN19D4C3RNfJR\/?IP:fGR]PIP2fER^D>P:fHR_P^P[g00_C#KR`fKRaPOF@1BaOP;10O_=;H\fIRb#4/1>%5bfS,27/8_'1'0PJPLD:fT,27/FbP7P8%L6R6P8PMPXP_P0PRECfMRcDD[[[[[[[^05^4G^1C^2F^3=P7P8P6P8fFRdP^%^9fDR9PTECPSDD[[[[[[P4%4M,6>127d/8M%5Z'6PEPSPVPYC3%HMPEP9P?f=R?,9DC3PEP^P@PAC3PBP^PUP[CG1?cIP:P\PIP2P_D>P:PaP_P[P`fNRBPOF@1BBOP;10Oa=;HcfLRA#4/1>%5AfV,27/8a'1'0PJPLD:fW,27/FAP7P8P6P8PMPXPaP0PRECfPR8DD[[[[[[\N^05^4G^1C^2F^3=PaP\PbP_P]PdP^P9PTPSPWPQPUf>P?PZPMPJPOPIP1P2P31?BIP:PaPIP2PbD>P:PAPbP[P`fOR`POF@1B`OP;10OA=;HB%4c/1>%5c'0PJPLD:fX/]cPZPMPXP0PRPJPKPOPIP1P2P5%5`R2P;10R`fQ5;H%48/1>/04PX%A0D:XX5P3112P%\2EWP;10JB=;H8%4`/1>fY,27/8B,12'0P0%ARD:eP4O<W9WAWJWCW8WOX=NX05X4GX1CX2FX3=OGW7WPW?W>WNW;WQWDP3P4O2n2001000010121000000W:WEW<WGWKW@XV5XW5XU5WRWHWFWTWIWMWSWB1X<3eWLX55X65P3P4O2X55X65o"). Qed.

Lemma opdelP_of_S_at (lim pc : Z) : PEHS.opdelS_spec_at segs A L HI pc -> opdelP_spec_at (PESK.SP_S lim) pc.
Proof.
ltac2:(KReplay.run1 (kr_t_PeHeapP ()) ["Specs"] "h02M'h12R'h23fx'h33limh46model'h52pch61Bh74CONTh82H1h93H10h:2H2h;2H4h<2HHh=3HH'h>3HINh?2HMh@2HPhA1KhB2K0hC2LBhD1MhE2MBhF3MOKhG3OPDhH1RhI2RAhJ2RPhK3STKhL2crhM2fxhN5modelhO1nhP1rhQ2sphR1zp;7p;2p;1p;5p;3p;4p;6g00`Mj7ZTg001Cj2>Tg002Oj1OTg003^j10Tg004Cj1YTg004hj1=Tg005Fj1CTg005ij2NTg006Uj1JTg0077j2HTg007Wj1GTg0087j19Tg008nj54Tg00::j1XTg00;Jj1DTg00acj3RTg00;jj18Tg00<Hj36Tg00Smj2:Tg00<kj2;Tg00U5j37Tg00@2j1MTg00A<j1LTg00BEj1KTg00CRj4ITg00D[j2@Tg00b:j22Tg00G?j7ATg00HJj2BTg00cHj21Tg00>dj2?Tg00Kfj1FTg00Llj6PTg00N7j5QTg00cej1ETg00R<j6STg00dFj2TTg00VIj4WTg00UOj3VTg00Ulj3UTg00ViR0P0f1R1f0R2CWp=3AV002p=5AU002p=<p,6SCFG_PR3p,3bmKR4p,4segsR5p,1AR6p,1LR7p,2HIR8P2FZf2R9,>4R:#Og00WGR;g00XTR<#0R=#YR>#=R?%0=R@#0RA#0#0#0#=RB#CRC'NRD%=A#C#J\CRAg00Y9REg00Yo1H00RF#Gg00[7P8f5RGf4RHf8RIf7RJ#9D4%XIPIg00\B#DO1f6RK/3G=RFIf=RF%0>#8g00]8R>56?':1;BJ57Cf>RL%8<R<=6?>':1;BG57C%MKf@RM%8==6?>':1;BI57CfAR=%8@=6?>':%L6,;B57C%K7P=f:RCg00e\RBCIfGR6/@9P7fBR>fDR?'2PMPBg00_C#DR@P6P9FA1B69P8fFRN,2?fERO#5/1<%<OfO,>4fCRP'?'1'3PHf3RQ#9RRD4P4P5%F3P5PJPKP>PGPHEPfHR5DQ[[[[^4E^0A^1D^2;P6PNPOP?PPP>P=PMf?PLPFf<f;PCf9PIPJPKPGPHPQP9P11@59P712POP=PBP@P5P9FA1B59P812O6%5N/1<%<N'3PHPRD4PIPJPKPGPHPQP9P1P0%<6R9P8fI,26%55/1</32PK%9GD4XR0P2g00]T,19%E9ESP812N5%56/1<fQ,>4/?O,19'3PG%9HD4eO8W=WEW@WJX4EX0AX1DX2;OGW7WKW;W:WIW8W9W>WBWFW<XP0XQ0XO0X60WLWCWAWNWDWHWMW?1T:1eWGX50X30P1P2O2X50X30o"). Qed.
Lemma opdelP_of_S (lim : Z) : PEHS.opdelS_spec segs A L HI -> opdelP_spec (PESK.SP_S lim).
Proof.
ltac2:(KReplay.run1 (kr_t_PeHeapP ()) ["Specs"] "h03limp;1p;2g00fmj11Tg00h9j20Tg00ViR0f0R1p,1A#1'0X00P1O1W0o"). Qed.

(* [comment removed for export] *)
Lemma opnewP_of_F (lim zmax hb NMAX : Z) : PEHS.opnewF_spec segs A L HI lim NMAX -> opnewP_spec (PESK.SP_T zmax hb) NMAX.
Proof.
ltac2:(KReplay.run1 (kr_t_PeHeapP ()) ["Specs"] "h01Bh12M'h24NMAXh32R'h42_Hh53fx'h62hbh73limh86model'h94zmaxh:4CONTh;2FBh<2H1h=3H10h>4H10'h?2H2h@2H4hA2HHhB3HH'hC2HPhD2HchE2HnhF1KhG2K0hH2LBhI1MhJ2MBhK3MOKhL3OPNhM1RhN2RAhO2RPhP3STKhQ2crhR2fxhS5modelhT1nhU1rhV2spp;8p;2p;1p;5p;3p;4p;7p;6g00iOj8\Tg00jbj24Tg002Oj1QTg003^j10Tg004Cj1[Tg004hj18Tg005Fj1CTg005ij2PTg006Uj1OTg0077j2LTg007Wj1ITg0087j1HTg008nj5:Tg00::j1ZTg00;Jj1FTg00;jj16Tg00<Hj35Tg00Smj21Tg00<kj22Tg00U5j33Tg00=Qj2RTg00=mj27Tg00>Ij2ATg00UOj3@Tg00>dj2<Tg00Ulj3?Tg00@2j1NTg00A<j1MTg00BEj1KTg00CRj4JTg00D[j2>Tg00Enj5=Tg00G?j7DTg00HJj2;Tg00I[j3ETg00J;j2BTg00JXj2GTg00Kfj1STg00Llj6TTg00N7j5YTg00knj2XTg00POj2VTg00RZj2UTg00VIj4WTg00ViR0P0f1R1f0R2CWp=9p,6SCFG_PR3p,3bmKR4p,4segsR5p,1AR6p,1LR7p,2HIR8f3R9P2G\f2R:,49R;#Qg00WGR<g00XTR=#0R>#[R?#8R@%0>RA#0RB#0#0#0#8RC#CRD'PRE%8B#C#O\DRBg00Y9RFg00Yo1L00RG#Ig00[7P8f4RHP9f7RIf6RJ#HRKD:%ZIPIg00\B#FO1f;RL%0?#6g00]8R?55@RM'1f5RN,2C53Dg00]T/RJf@RO,7J'A%6=R=f8RP9@00'7fCRQfBRR'4/<IA?00P'7'Af>RSA5@=?'112CJ53D%NI%6>=5@?,1Of9R>,2C53DfART%6A=5@?'1%M6,2C53D%K7PTPLg00^2R6CJ119M12C253DRDfIRC/>HP7fFPHP:fDRMD=P7fGR@PMP6g00_C#FRAfJRUPNFD1;UNP819N@=EGCfHRV9@00/B=A?00VfSR=fR'4/<@'B'9PIPKD:fT/4=/GVP4P5%S3P5PLf:R5P@P>PPETfLDY[[[[[[[^00^8F^1B^3E^5<P@fER3PMPQPRPTPOf?PSf=f<RSPLP5P>PPPIPJPNPHP9P:P11>UHP7P@PHP:P3D=P7PVP3P6PAfKRAPNFD1;ANP819NV=EGU1XCVPIPKD:fV/VCPSPLP5P>PPPIPJPNPHP9P:P1P?O<W4WBWJWCW;WOX>DX00X8FX1BX3EX5<OFW:WPW@W?WNW<WDWEW=WGWKWAXU0XV0XT0WQWHWFWSWIWMWRW41U;1eWLX20X60X90X70P9P:P1P2O4X20X60X90X70o"). Qed.

Lemma opdelP_of_R_at (zmax hb pc : Z) : PMSR.opdelR_spec_at segs A L HI pc -> opdelP_spec_at (PESK.SP_T zmax hb) pc.
Proof.
ltac2:(KReplay.run1 (kr_t_PeHeapP ()) ["Specs"] "h02M'h12R'h23fx'h32hbh46model'h52pch64zmaxh71Bh84CONTh92H1h:3H10h;2H2h<2H4h=2HHh>3HH'h?3HINh@2HPhA1KhB2K0hC2LBhD1MhE2MBhF3MOKhG3OPDhH1RhI2RAhJ2RPhK3STKhL2_HhM2crhN2fxhO5modelhP1nhQ1rhR2spp;7p;2p;1p;5p;4p;3p;6g00m<j7VTg00jbj2ATg002Oj1NTg003^j10Tg004Cj1UTg004hj17Tg005Fj1=Tg005ij2MTg006Uj1HTg0077j2FTg007Wj1ETg0087j1>Tg008nj58Tg00::j1TTg00;Jj1@Tg00VIj4?Tg00acj3RTg00;jj16Tg00<Hj33Tg00Smj25Tg00<kj22Tg00U5j34Tg00@2j1LTg00A<j1KTg00BEj1ITg00CRj4GTg00D[j2:Tg00b:j21Tg00G?j79Tg00HJj2;Tg00UOj3JTg00cHj2<Tg00Ulj3DTg00>dj2OTg00Kfj1CTg00Llj6PTg00N7j5QTg00nRj2BTg00dFj2STg00ViR0p,6SCFG_PR1p,3bmKR2p,4segsR3p,1AR4p,1LR5p,2HIR6f0R7FVf3R8f2R9'AR:#Ng00WGR;g00XTR<#0R=#UR>#7R?%0=R@#0RA#0#0#0#7RB#=RC'MRD%7A#=#H\CRAg00Y9REg00Yo1F00RF#Eg00[7P6f5RGf4RHf8RIf7RJ#>D8%TIPIg00\B#@O1P0P0f6RKPGC?=RFIf=RF%0>#6g00]8R>53?'512BJ54Cf>RL%6<R<=3?>'512BG54C%LKf@RM%6==3?>'512BI54CfAR=%6@=3?>'5%K4,2B54C%I5P=f:RCg00e\RBCGfGR4/:9P5fBR>fDR?'1PMPBg00_C#@RBP4P9F91;49P6fFR@,1?P0P0fERN9J00/<<AD00NfPfO'AfCR<'O'<C?PH%>8ROD8P2P3%C1P3PJPKP>PGPHEPfHR3DQ[[[[^4E^0A^1D^2;P4PNP?P<P>P=PMf?PLPFf<f;PCf9PIPJPKPGPHP8P9f1RC1:39P511<NP=g00oaPBP3P9F91;39P611N41B@?PHPOD8PIPJPKPGPHP8P9PCP7O8W>WEW@WJX4EX0AX1DX2;OFW8WKW<W;WIW9W:W?WBWFW=XQ0XR0XP0X70WMWCWAWOWDWHWNWL1S:CeWGX50X30X60P9PCP7O3X50X30W6o"). Qed.
Lemma opdelP_of_R (zmax hb : Z) : PMSR.opdelR_spec segs A L HI -> opdelP_spec (PESK.SP_T zmax hb).
Proof.
ltac2:(KReplay.run1 (kr_t_PeHeapP ()) ["Specs"] "h02hbh14zmaxp;1p;3g00fmj11Tg0112j30Tg00ViR0f1R1f0R2p,1A#130X00X10P1P2O2X00W1o"). Qed.
End Specs.
End PEHP.
