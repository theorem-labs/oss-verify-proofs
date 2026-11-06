(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import StartupTac ArgvEnv RefLayout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib U1BootDefs U1Boot U1StartInit_defs U1CxxTable U1Start.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_U1CxxLink () := "C59OSSVerify5KrLib3Drv7RunsLib;runs_equivFC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib3Drv7RunsLib:runs_equivC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib>runs_equivF_eqC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib3Drv@U1StartInit_defs9init_runsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv:U1CxxTable5D_CXXC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib3Drv7Overlay7runs_okC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C59OSSVerify5KrLib3Drv6U1Boot2D8C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib@runs_equiv_soundC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Drv7U1Start7D_main1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay:apply_runsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00c59OSSVerify5KrLib3Drv9U1CxxLink<init_runs_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv9U1CxxLink8D_CXX_okC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv9U1CxxLink;d_cxx_equivC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C59OSSVerify5KrLib3Drv7Overlay;lookup_byteC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib3Drv7RunsLib?apply_runs_pinsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv9U1CxxLink=D_main1_tableC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib3Drv7RunsLib4pinsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib3Drv7RunsLib:runs_clearC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3addC49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z4of_NC46Stdlib9micromega;ZifyClasses6eq_iffC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses9and_morphK46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega;ZifyClasses;rew_iff_revC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions=Z_to_bv_smallC49OSSVerify5KrLib8PropExec7rdn_extC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLibDrdn_apply_runs_clearC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_transK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib4Init9Datatypes3nat00I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib3Drv7RunsLibCapply_runs_clear_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7Overlay;lookup_runsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Drv9U1CxxLink<D_main1_pinsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Drv7RunsLib;rdn_of_pinsC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma d_cxx_equiv : runs_equiv init_runs D_CXX = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1CxxLink ()) [] "h01bp;2p;3p;6g0000j25Tg000lj30Tg001Fj22Tg001`j21Tg002[j24Tg003Zj63Tg0046R0g004VR1g005YR2'5R3f0g006RR4500X001204A0034d11121412E3o"). Qed.

Lemma init_runs_ok : runs_ok init_runs = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1CxxLink ()) [] "p;2p;1p;3g001Fj22Tg0072j11Tg000lj30Tg0046R0g006RR1'2g004V#1=001do"). Qed.

Lemma D_CXX_ok : runs_ok D_CXX = true.
Proof.
ltac2:(KReplay.run1 (kr_t_U1CxxLink ()) [] "p;2p;1p;3g001Fj22Tg0072j11Tg000lj30Tg0046R0g006RR1'2g005Y#1=001do"). Qed.

Lemma D_main1_table : forall sp0 av ev hw tid rdraw (a : word),
  D_main1 sp0 av ev hw tid rdraw a = apply_runs D_CXX (D8 sp0 av ev hw tid rdraw) a.
Proof.
ltac2:(KReplay.run1 (kr_t_U1CxxLink ()) [] "h01ah12avh22evh32hwh45rdrawh53sp0h63tidp;1p;6p;7p;3g007jj10Tg008Oj13Tg008mj12Tg009Pj11Tg00:0j69Tg00:bj78Tg00;cj17Tg00<Ej74Tg00==j35Tg000lj36Tg00>8#0#0#0R0#0#0#0#3#2R1%30#2R0#1#1R2g00>]g004Vg005YR3f6R4f5R5f4R6f3R7f2R8f1R9E9R:f0R;g00?]g00@\g00AWF8%70P4P5P6P7P8P9P;F4A53:;36eX01W4X61X31X22W1W5o"). Qed.

Lemma D_main1_pins : forall sp0 av ev hw tid rdraw, pins D_CXX (D_main1 sp0 av ev hw tid rdraw).
Proof.
ltac2:(KReplay.run1 (kr_t_U1CxxLink ()) [] "h02Hlh12Hyh22avh31bh42evh52hwh61oh75rdrawh83sp0h93tidh:1yp;1p;2p;3p;6p;7g007jj10Tg008Oj18Tg008mj12Tg009Pj11Tg00BUj2ETg00C1j17Tg00COj2<Tg00Clj2;Tg00DHj2:Tg00;cj16Tg00Dcj29Tg00E_j24Tg000lj35Tg00:0j6DTg00FAj23Tg00==j3CTg00Fgj7=Tg00<Ej7>j6ATg00Ggj7?Tg00Hgj6@Tg00IEj2BTg00>8#0R0#0#0R1#0#0#0R2#8R3#2R4%81R1#2R5#1#1R6g00>]g00J:R7g00JXf1R8'E%70%72'<,;8':%67g005YR2f2R0'9147835%65R9f9R:f8R;f7R<f6R=f5R>f4R?EDR@f3RA,33R35C2f0RB131A,45559X69P2P@g00@\PAP0P8PBF=P:P;P<P=P>P?P3F>P:P;P<P=P>P?P3F?E@W0W1X37W:P>P?PAP0P8PBEA,B2eW7X94X54X46W2W8o"). Qed.

Lemma D_main1_clear : forall segs sp0 av ev hw tid rdraw lo n,
  runs_clear D_CXX lo n = true -> 0 <= lo < 2 ^ 64 -> lo + Z.of_nat n <= 2 ^ 64 ->
  rdn segs (D_main1 sp0 av ev hw tid rdraw) (Z_to_bv 64 lo) n = rdn segs (D8 sp0 av ev hw tid rdraw) (Z_to_bv 64 lo) n.
Proof.
ltac2:(KReplay.run1 (kr_t_U1CxxLink ()) [] "h04__x1h11xh22Hah37__arithh44__ffh56__sat1h66__sat2h78__varmaph85__with94__x2h:4cstrh;1nh<2Hch=3Hloh>2Hnh?2_Hh@2avhA2evhB2hwhC2lohD1mhE5rdrawhF4segshG3sp0hH3tidhI1yhJ1zp;1p;3p;2p;6p;4p;<p;7p;9p;8p;Bg009Pj17Tg007jj15Tg008Oj1ATg008mj1>Tg00K6j3oTg000lj3FTg00C1j1BTg00COR0j29Tg00ClR1j20Tg00DHj23Tg00L1j18Tg00LQj26Tg00BUj24Tg00;cj1lTg00<Ej6^Tg00FAj2ETg00Lnj4;Tg00:0j6WTg00==j2VTg00M_j1TTg00NDj2RTg00Nlj3QTg00OPj1PTg00P0j2DTg00PNj1OTg00Plj4NTg00QJj1MTg00Qhj1LTg00RSj2?Tg00S6j3KTg00SYj2@Tg00T<j3JTg00T_j4:Tg00UJj1ITg00Ulj2HTg001Fj22Tg00VNj2STg00W:j3nTg00WYj4mTg00XKj2=Tg00Y5R2j1GTg00YSj3kTg00Z9j1eTg00ZWj4]Tg00[:l<ZTg00[_j6YTg00\Hj7_Tg00\lj4XTg00]Wj1`Tg00^@j3aTg00Hgj6bTg00Ggj7cTg00^lj7dTg00_al9UTg00`fj6fTg00aDj7gTg00ahj8hTg00bLl<iTg00c1lBjTg00JXR3f0R4'4p=1f1R5g00cWR6g00d6R7P7g00dVR8P4g00e6Fgp=<f3R9P6P7P7P8f2R:P5P4Ghp=Cg00eVR;g00J:R<P<P<P2P2f5R2f4R=P9P:P5P4M<ip=\P<P<P<P<P<P<P0P4P5P:P0P9P=P2f6R0f7R>f8R?f9R@MBjp=[g00f4#7g00>8RA#5RB#5#5RC#5#5#5RD#ARE#>RF%AC#>#7RC#7RGg00>]g00g3g0046RHg005YRI?o54g006RRJ3F%1:%BBRK%BDRD'9RL,0:'3%8:,69/4L%lCf;RCf:RMP@P?P>P0P2E^RN1EE=ROP9C;PCPMP@P?P>P0P2EWR0,VIRPPOP9C;PCP0POP9C;PCP9PNPPPOP<P=%8=RP,64/4LXJ<%T9RN%89#1RQ1RKDRR103K%1D103L[[RS%1KRTg00gRRUAQKD5UW2RV%1L\U^2TRTg00gnRU#PRW%7URUP<1D<:P5%O<CN%M<RX%L<RYP<1?<ARA1?<B5K<g00hZRB1@<K=J<ERZC:,<YR[%I7R\P[CC1HY8R[P4P:12HJ1S4:=FHJdAn<35CmRJb4b7b8X0<X9<1645/4L165:/4L[^0<^9<P4%8>P?P=O3b3b5b6b:1=EO%1=RO%GERH,9KR],0=R^'310=LR_,3OPOP^POP_p-0/2O9kOOP<P<P1P4X1<R_P11054#eXI<X1<P=P=12<=P]PLP_P_P_P<P<g00iA1954C],2<XD<X;<PKPK12<KPHPDP_P_%G4,2<X1;PEPD12<DE\M:[M<ZEYPNPQPRPSPVPTPWPU1D<5PXPYPYP6P7P7P8P<1@<3PBPAC:,<YP<PAg00iePZC:,<YF_RYP\PYCCP[PJb4b7b8X0<%14104L'3%15105L'3[^0<P4P?P2O2b3b5b6b:CX%`E,0=,3Oe9aE=Eb1EE2,=ER21=E4RE'4162P,0E'3f<PCPMP@P?P>P5FcW?X1FFdPCPIP0P=P9g00@\P:P5P4M9UEfW>W=W<W;XC<WEXHFXBFXAGW@WGWFo"). Qed.

Lemma D_main1_clear_at : forall sp0 av ev hw tid rdraw lo n (x : Z),
  runs_clear D_CXX lo n = true -> 0 <= x < 2 ^ 64 -> lo <= x < lo + Z.of_nat n ->
  D_main1 sp0 av ev hw tid rdraw (Z_to_bv 64 x) = D8 sp0 av ev hw tid rdraw (Z_to_bv 64 x).
Proof.
ltac2:(KReplay.run1 (kr_t_U1CxxLink ()) [] "h02avh12evh22hwh32loh41nh51oh65rdrawh73sp0h83tidh91xp;1p;3p;2p;6p;7p;9g007jj10Tg008Oj19Tg008mj15Tg009Pj17Tg00K6j3ETg000lj34Tg00BUj28Tg00C1j12Tg00COj2<Tg00Clj26Tg00DHj21Tg00L1j1;Tg00LQj2:Tg00;cj1DTg00:0j6Cj7?Tg00FAj23Tg00==j3@Tg00jLl9>Tg00<Ej7=Tg00Ggj7ATg00Hgj6BTg00>8#0R0#0#0R1#0#0#0R2#9R3#5R4%91#5R1#7#7R5g00>]g00J:R6g00g3g0046g005YR7f2R8f1R93Eg006R34g00JX/89%20%22'<,69'1f4R2/88f3R0#;,:2,68'1%D1R1f;R:f:R;f9R<f8R=f7R>f6R?ECR@1330RA5@7f0RBf<P:P;P<P=P>1332F?541X51P7P@f5P2P0g00@\P8P9PBM9>P:P;P<P=P>P?PAF=P:P;P<P=P>P?PAFAEBUUUX96W4W3W6X84X24X15W0W7o"). Qed.

Lemma D_main1_hit : forall segs sp0 av ev hw tid rdraw (x : Z) n zs,
  0 <= x -> x + Z.of_nat n <= 2 ^ 64 -> lookup_runs D_CXX x n = Some zs ->
  rdn segs (D_main1 sp0 av ev hw tid rdraw) (Z_to_bv 64 x) n = Some (map (Z_to_bv 8) zs).
Proof.
ltac2:(KReplay.run1 (kr_t_U1CxxLink ()) [] "h02avh12evh22hwh31nh45rdrawh54segsh63sp0h73tidh81xh92zsp;1p;2p;3p;6p;:g009Pj11Tg007jj10Tg008Oj12Tg008mj14Tg00BUj25Tg00L1j1<Tg00LQj2;Tg00C1j13Tg00COj28Tg00;cj17Tg00kPj36Tg00E_j29Tg000lj3:Tg00<Ej6?Tg00lLj6>Tg00mKl:=Tg00f4#1g00>8#0R0#0#0R1#0#0#0R2#2#4R3%21#4#1#1R1g00>]g00J:R4g00g3%14R4g00JXf2R5'5f3R6%<5';%30%32'8'5%74g005YR2f4R0;6619453:f<P2f;R2f:R4f9R7f8R8f7R9f6R:E?P0f5P6P2P4P7P8P9P:E>P5f1f0M:=UUUW9W3W8W4X73X23X11W0W6W5o"). Qed.
