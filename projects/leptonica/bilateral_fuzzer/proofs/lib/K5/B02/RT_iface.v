(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require Import Prelim StrFun Canon Stdio.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Spec Require PrintfFormats.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow IcptSpec.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_iface () := "C46Stdlib5Lists4List2hdI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00c69OSSVerify5KrLib2K53B028RT_iface9sec_bytesC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z8ltb_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3ltbI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3addK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes8list_indK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init5Logic8eq_ind_rC46Stdlib5Lists4List6filterI47Corelib4Init5Logic3and00C46Stdlib5Lists4List?Forall_cons_iffC47Corelib4Init9Datatypes3sndI46Stdlib5Lists4List6Exists00C46Stdlib5Lists4List:fold_rightI46Stdlib5Lists4List5NoDup00C46Stdlib5Lists4List4inclc69OSSVerify5KrLib2K53B028RT_iface@sec_bytes_nonnegC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List5in_eqC46Stdlib5Lists4List8in_splitI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List2InC47Corelib4Init5Logic3notC46Stdlib5Lists4List>NoDup_cons_iffC46Stdlib5Lists4List7in_consC46Stdlib5Lists4List9in_app_orI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C46Stdlib5Lists4List9in_or_appC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic6eq_indK47Corelib4Init5Logic2or02c69OSSVerify5KrLib2K53B028RT_iface=sec_bytes_appC1?~~~~~~~~~~~~~~~C35stdpp4base6FilterC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic8eq_transC4ELinuxProcessSemantics?LinuxProcessSem2Fs2Fsc69OSSVerify5KrLib2K53B028RT_iface3rtsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c69OSSVerify5KrLib2K53B028RT_iface8rt_afterC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_iface3ARTC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_iface:rt_after_fC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2K53Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib5Frame3stkC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2K53B028RT_iface6rt_sig00C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_iface;live_removeC1?~~~~~~~~~~~~~~~C45stdpp;list_basics4list;list_filterC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC46Stdlib4Bool4Bool7Is_trueC35stdpp9decidable;Is_true_decC35stdpp4base6filterC35stdpp4base6decideI47Corelib4Init6Specif7sumbool00K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5State5m_fdsC4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsc69OSSVerify5KrLib2K53B028RT_iface4PMfdC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028RT_iface9fdfs_onlyC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State7FdEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00".
Import ListNotations.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition SEGTOP_A : Z := 0x66f000.
(* [comment removed for export] *)
Definition USTACK_TOP : Z := 0x800000000000.
Definition STACK_WIN : Z := 0x800000.
(* [comment removed for export] *)
Definition RT_STACK : Z := 0x10000.
(* [comment removed for export] *)
Definition LIVE_MAX : Z := 8192.
Definition FRAMES_MAX : nat := 16.
(* [comment removed for export] *)
Definition SEC_BYTES : Z := 0x80000000.
Fixpoint sec_bytes (l : list (Z * Z)) : Z :=
  match l with [] => 0 | (p, n) :: l' => (if 64512 <? n then n else 0) + sec_bytes l' end.

Lemma sec_bytes_nonneg : forall l, 0 <= sec_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "p'0h04__x1h11lh27__arithh34__ffh48__varmaph55__with61Hh74__x2h82IHh91ah:1bi001bh;2b0h<1nh=1pi011pi021zp;2p;1p;3p;4p;5p;7p;8p-1R0p10000p4p710p8P0p1000Gp4p710p8P0p1000hR1p4p710p8P0P1p4p7210p8P0p1001Ep4p710p8g001bR0j2ZTg002Bj1DTg002bj12Tg003`j1FTg004@j1RTg004^j1OTg005<j1MTg005gj2?Tg006Jj2HTg006lj2GTg007Fj2YTg0082j3UTg008Lj3TTg008kj4QTg009]j24Tg00:9j3:Tg00:Yj16Tg00;>j1NTg00;\j2LTg00<>j27Tg00<Zj2ATg00=7R1j3KTg00=[j28Tg00>8j1@Tg00>Wj29Tg00?@j3=Tg00?ij2JTg00@Uj2>Tg00A3j4ITg00AQj2BTg00B4j4CTg00B_j1PTg00CAj1;Tg00Cfj3ETg00DIj4STg00Dij5XTg00EKj7WTg00Eoj8VTg00FSR2f0R3'4p=0g00G1R4f1R5g00GOP3CCp=5P5g00H6R6g00HUR7P7g00I5R8P3g00IUFWp=1%;3#;p=3f3R9P6P7P7P8f2R6P5P3GVp=<1Z44R:#DR;P:%23#0R<X1;g00J5R=#FR>%D=R?%R4R@%O4RA%M4RB1?42RC/5C'11HB8R8P3P6g00JaRDg00KARE'G1Y36=UDEdAT425CQREb3b4b51422P3b2%F:#2#0eP0P4P4A::65#2#0\<^1;P3g00KaR0#6#6#6#6#6#3#3#3#3#3#NRF/L617F6146F1AF63K1AF9PDP1f4R1,7F141FPDP4P5f6RDP2n0100000020000f5R1#2'8#0P517F1g00LFRG#@RH#@,94194H194G5=45=4g00Le'J=:=>P?P41>46P5P@CIPAPBP41?4Fg00MQ1B40R@CC,1B%P7R7PB%;0,B4R0,5C,1BP7AE4@0,5C,1BC<C<P8PEb3b4b5X04X7417F3%061869#0[[^04^74P3%2DRDf7P5P1O4b2W6P3O1141FP>P?1>45PAPB15C@,1BP7AE4C@,5C,1BC<P8PEb3b4b5X04%031825#0[^04P3PDP1O2b2W6P3O1n200210000000021100010000b;b:P4P4P9P6CS=::5#2#0eX8<X1;X<4X=4P5P3O2n2001101000121102102X9:P3DXW1o"). Qed.
Lemma sec_bytes_cons_small : forall p n l, n <= 64512 -> sec_bytes ((p, n) :: l) = sec_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "p'0h04__x1h12H0h27__arithh34__ffh48__varmaph55__with64__x2h71Hh81bi001bh92b0h:1lh;1nh<1pp;2p;1p;3p;4p;7p;8g001bj2STg002Bj1@Tg00:Yj11Tg00;>j1RTg009]j27Tg00;\j2GTg00<>j25Tg00<Zj2>Tg00=7R0j3DTg002bj16Tg00=[j29Tg0082j30Tg003`j1QTg00@Uj2?Tg004@j1PTg00A3j4MTg004^j1LTg005<j1KTg005gj2=Tg00AQj2<Tg00B4j43Tg00B_j1FTg00CAj18Tg00Cfj3:Tg006Jj2ETg006lj2HTg007Fj2ITg008Lj3JTg008kj4CTg00DIj4BTg00:9j3NTg00EKj7ATg00Eoj8OTf0R1#8#8p=2f1R2g00H6R3g00HUR4P4g00I5R5P1g00IUFAp=4f3R6P3P4P4P5f2R3P2P1GOp=;g00G1R71S77R8#@g00KaR9#1#1#1#1#1#2#2#2#2#2#RR:,72R;1G:315:3173:1>:33D1>:6g00JaR<P0f4R0,5:170:P<P7P2f6R0g00FSR=n0100000020000f5R>#6R?'9=07?P215:>g00J5R?#QR@%@?R?P71?73P2%P7CM%L7RA%K7RBP71=7:RCg00MQ1<79RDC3,4B%F4R4PBP7PDg00GOPCC3,4BP4P7%89,<7R99:7Dg00N8R4P9C3,4BC;C;1EB5R5P1P3g00KAR9,H<1I13=0<9dAJ7=2CCR9b3b4b5X07X6715:11936=076\;[^07^67P1%60R0f7P2P>O4b2W1P1O117>:P@P?1?72PAP71=7==:7DP4PDC3,4BP5P9b3b4b5X0719=1=071^07P1P0O1b2W1P1O1n200210000000021100010000b9b8P7P7P6P3CB=N82#6%62507eW7W:X;7W<o"). Qed.
Lemma sec_bytes_cons_big : forall p n l, 64512 < n -> sec_bytes ((p, n) :: l) = n + sec_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "p'0h04__x1h14__x2h22H0h37__arithh44__ffh58__varmaph65__with71Hh81bi001bh92b0h:1lh;1nh<1pp;2p;1p;3p;4p;7p;8g001bj2STg002Bj1?Tg00:Yj13Tg00;>j1RTg00<>j26Tg00;\j2FTg009]j24Tg00<Zj2;Tg00=7R0j3CTg002bj18Tg00=[j20Tg0082j31Tg003`j1QTg00@Uj2PTg004@j1NTg00A3j4MTg004^j1LTg005<j1KTg00AQj2=Tg00CAj19Tg00Cfj3:Tg00B4j45Tg006Jj2ETg006lj2DTg007Fj2GTg008Lj3HTg008kj4ITg005gj2<Tg00B_j1JTg00DIj4BTg00:9j3ATg00EKj7@Tg00Eoj8OTf0R1#9#9p=2f1R2g00H6R3g00HUR4P4g00I5R5P1g00IUF@p=7f3R6P3P4P4P5f2R3P2P1GOp=>g00G1R71S77R8#?g00KaR9#3#3#3#3#3#2#2#2#2#2#RR:/621F:316:3R;143:1;:33C1;:6g00JaR<P0f4R0,6:140:P<P7P2f6R0g00FSR=n0100000020000f5R>#8R?'0100?517P216:>g00J5R?#QR@%??R?P71P73P2%N7CMRA%L7RB%K7RCP71=79RD%99,=7R95:7REg00N8RFPEC5'71EC5R5P1P3g00KARE,D<1G13=1<EdAH7=2CIREb4b5b6X07X171012R<=17<^07^17P1%80R0f7R<O2b3W2P1O114>:P@P?PAPBPCP7P9g00GO1<7:RBC5,7C%J4R4PCP7PBg00MQP9C5,7CP4P71<7==:7DPFA:79DC5,7CC>C>P5PEb4b5b6X07X17142:10=31063517\;[^07^17P1P<P0P2P>O4b3W2P1O1n200210000000021000011000b9b8P7P7P6P3CB=A82#8%82,03517eW7W:X;7W<o"). Qed.
Lemma sec_bytes_cons_le : forall p n l, 0 <= n -> sec_bytes ((p, n) :: l) <= n + sec_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "p'0h04__x1h14__x2h22H0h37__arithh44__ffh58__varmaph65__with71Hh81bi001bh92b0h:1lh;1nh<1pp;2p;1p;3p;4p;8p;7g001bj2STg002Bj1<Tg009]j20Tg00:Yj12Tg00;>j1MTg00;\j2ETg00<>j27Tg00<Zj2;Tg00=7R0j3ATg002bj14Tg00=[j21Tg003`j1=Tg00@Uj2RTg004@j1QTg00A3j4PTg004^j1LTg005<j1KTg00AQj2:Tg00CAj18Tg00Cfj36Tg006Jj2DTg006lj2CTg007Fj2BTg0082j3FTg008Lj3GTg008kj4HTg005gj2ITg00B_j1JTg00Eoj8@Tg00DIj4?Tg00:9j3NTg00B4j4>Tg00EKj7OTf0R1#8#8p=3g00G1R2f1R3g00GOP1C>p=5P3g00H6R4g00HUR5P5g00I5R6P1g00IUFOp=91S22R7#<g00FSR8/03R9g00KaR:#2#2#2#2#2#3#3#3#3#3#MR;f2R<'E17;<10<;1;;<3Af3R=,;;g00JaR>P0f4R0,7;100;P>P2P3f6R0P8n0100000020000f5R?#4R@'1110@'0P317;?g00J5R@#=RA%<@R@P21R2<P3%Q2CPRB%L2RC%K2RD1:2:RE%8:,:2R:562RF/5F'91DD6RFP1P<g00KARG,C>1B1<=F>GdAG283CHRGb4b5b6X02X121113R>/0>^02^12P1%40R0f7R>O2b3W2P1O110?;PAP@PBPCPDP4P5P5P61I28R6/5:,9D%J5A626EA62:E'5,9DG@PFPGb4b5b6X02X12118311<3'0\9^02^12P1P>P0P?O3b3W2P1O1n200210000000021000010000b9b8P2P2P=P<C?=N73#4%43,1<'0eW7W:X;2X<2o"). Qed.
Lemma sec_bytes_app : forall l1 l2, sec_bytes (l1 ++ l2) = sec_bytes l1 + sec_bytes l2.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "p'0h04__x1h12l2h22l1h37__arithh44__ffh58__varmaph65__with74__x2h84__x3h92IHh:1ah;1lh<1nh=1pi001ph>1zi011zp;2p;1p;3p;4p;6p;5p;7g001bR0j2OTg002Bj1?Tg001Ej33Tg002bj11Tg00=[j20Tg003`j1;Tg00@Uj29Tg004^j1CTg005<j1BTg00AQj27Tg005gj2@Tg00Cfj35Tg00B4j4>Tg006Jj2NTg006lj2MTg007Fj2LTg0082j3<Tg008Lj3HTg008kj4GTg00:9j3:Tg00:Yj16Tg00;>j1DTg00<Zj2ETg00A3j4FTg00CAj18Tg00N_j6ITg00DIj4JTg00Dij5KTg00EKj7ATg00G1R1f1R2f0R33<p=2P2g00H6g00HUR4P4g00I5R4P3g00IUFAp==%83#8p=41O11R5#?R6P5A3523#1%12R7%13R8'0'2^16R9X26g00J5R:#;R;%?:R:1912%C1R<%B1R=P1g00KaR>,71R?g00N8R@g00FSRA,@1=51?C>'=1N=4R4P3f2RBg00JaRCg00KARD'M1L3B=<CDdAH1A2CGRDb4b5b6X0110A3,23^01P3P7O1b3%;5RE=353#1%1E/08'2eX16P0P1P1f3R0=:5BRE=353#1%1E/08'2^16\9^;6P3P1%1B/08PCP1%6>RC#6#6#6#6#4#4#4#4#4#Df4RE'EPEPAn0100000020000RA/03%10RF,0A/07'2X>1P;P:P1191BP21910CFP<P1%8>,71R>171CRC551951?P@A51?>=51CC>,==P4PDb4b5b6X01X71X81102B,031032/0B'2^01^71^81P3P7PFPAO3b3A35B3#1P2P3O1EIP1P1PEP0CJ=:5BRB=353#1%1B/08'2eX16X99X26X<1X=1P2P3O2n2001100000121101101X:5P3DKW2o"). Qed.
Lemma sec_bytes_filter_le : forall (f : Z * Z -> bool) l, sec_bytes (List.filter f l) <= sec_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "p'0h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61Hh74__x3h81lh91bi001bh:2b0h;2IHh<1ah=1fh>1nh?1pi011pi021zp;2p;1p;3p;4p;5p;7p;8g001bR0j2]Tg002Bj1GTg00O=j34Tg002bj11Tg003`j1FTg004@j1STg004^j1RTg005<j1PTg005gj2CTg006Jj2LTg006lj2KTg007Fj2\Tg0082j3WTg008Lj3VTg008kj4UTg009]j20Tg00:9j39Tg00:Yj17Tg00;>j1QTg00<Zj2DTg00=[j22Tg00;\j2OTg00<>j2;Tg00=7R1j3NTg00@Uj2@Tg00A3j4BTg00CAj1<Tg00AQj2=Tg00B_j1MTg00Cfj3:Tg00>8j1HTg00>Wj2>Tg00?@j3ETg00?ij2TTg00B4j4JTg00Dij5ZTg00EKj7ITg00DIj4XTg00Eoj8YTf1R2#1f0R3'0p=3f2R4g00H6R5g00HUR6P6g00I5R7g00G1R8P2g00GOP3CJg00IUR9FIp=5P8P8P2P3CXp=?%<3#<p=6A4423#1p=Af3R:P5P6P6P7P4P2P3GYp=8P2P5P6P6P7P3P9FIp=[1]88R9g00JaR5[%G9R;P9A4943%13R<'3X8;g00J5R=#FR>%G=R?%S8R@%R8RA%P8RBg00FSRC,C8RD;5D1LB7R7P3P4g00KARE,K51\34=W5EdAV8C2CUREb3b4b510CCP3b2%F9RF9492%1F'3eP0P8P8f4R0=493/3<f5RFA9942RG549%1G'3[^8;P3f7RG=493/3<f8R<1?:4RHO1P5P5P5P;P31?F0f:=49:RI599PIn0100000020000P5P8g00KaRI#7RJ#7#7#7#7#6#6#6#6#6#QRK/D0RLP0PCn0100000020000%1:'2'3P31OK:RM1;K:10:K1DK:RN3NROPLP5P11;KFRP10FKRFP5P8P2PGPCn0100000020000RQf=f6RR5A9RS'2%1R,2QRQ'0P21;KRRTP>P?P81@84RUP21@8:CBRVPAPB%<I,=8RW1=8JRJ55B%M6R61=8IRI=:8WA:8IJ55BC8P7PEb3b4b5X08X18X7810241224122:'0[^08^18^78P3%1GRXf>=A9GRGP<PRO4b2W6P3O110RKRYP>P?P8PUP2P@CBR@PAPBA5BIWRUP6A:8DIA:8DWRD55BC8P7PEb3b4b5X08X181032RZ12C212C4R['0[^08^18P3PXPGPRO3R\b2W6P3O1n200210000000021000010000b:b91?0:f9=494R]599P5P8PNP:PCn0100000020000%14'2RC'3ePMPOPLP5P1PPPF10SQP2g00LFRQ#HRS#H,>81>8S1>8Q5E85E8g00Le'T=9=>P?PVPAPBP81C8Kg00MQPWCJ,[BP6PBA5BIJP6A:8WJ95BIC8C8P7PEb3b4b5X08X18X781;K2102:12:0,04[[^08^18^78P3PXP<PGP2PRO5b2X6TP3O1P>P?P@PAPBPUP6A5BIDC8P7PEb3b4b5X08X18102[\Z^08^18P\b2X6YP3O1n200210000000021100010000b:b913]Cen0110000020101b9A99H2RH949<%1H'3eW;X8;X>8X?8P2P3O2n2001101000121102102X<9P3DZW8W=o"). Qed.
(* [comment removed for export] *)
Lemma sec_bytes_small : forall l, Forall (fun e => snd e <= 64512) l -> sec_bytes l = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "p'0h01lh11Hh21ah31Ah41Ph57__arithh64__ffh78__varmaph85__with94__x1h:2H0h;2H1h<2H2h=2IHh>1bi001bh?2b0h@1ehA1nhB1pi011phC1zi021zp;2p;1p;3p;4p;6p;5p;7p;8g001bR0j2[Tg002Bj1?Tg00:Yj18Tg00;>j1VTg009]j22Tg000Gj30Tg002bj14Tg003`j1BTg006lj2ETg00:9j33Tg00OXR1j2=Tg00P3j4WTg00<Zj2>Tg00=[j26Tg00;\j2UTg00<>j2;Tg00=7R2j3RTg00@Uj2QTg004^j1NTg005<j1MTg005gj2CTg00AQj2LTg00B4j49Tg00B_j1KTg00Cfj3@Tg006Jj2JTg007Fj2ITg0082j3DTg008Lj3HTg008kj4OTg004@j1PTg00N_j6GTg00Dij5STg00PWj3TTg00CAj1FTg00DIj4ZTg00EKj7YTg00Eoj8XTg00G1R3f0R47T3p=<%F4#Fp=7g00FSR59D34p=1P3P3f1R6P4CZp=5P6g00H6R7g00HUR8P8g00I5R9P4g00IUFYp=:f3R:P7P8P8P9f2R7P6P4GXp=A1[33R;#?R<P;%<4g00KaR=#8#8#8#8#8#7#7#7#7#7#VR>'2X@;R?=0;4%46#1[R@X0<%B;RA90;?1E35%4A#1eW1P0P3P3A3;7690;?A3;:7#4#1[\@^0<P415:7=3;690;?g00Q4p4p710R0p-0\4RA%?7RBP1A3:6490:7P:P7O1f4RC?0:6'=[RDP7P6O1A0:74'=A3C7690C:RE[PCP:O1f5RF?0C7'=\EP:P7P6P4CWP6n2001000000120000000W0X26W4W3PD^0B^26^4A^30P4P;P?15FCR0P:P6O5%<0/2>A0;?:'=P1f6R1/5F#</2>A0;?Cg00JaR0P31>>1P1P5n0100000020000%4F'6#1P4f8RFf7RA'5#</2>A0;?AP3P5P0P3f:R?,>>RBP?P5n0100000020000/64#1XC3f9R?,U>1;>?12?>1>>?3RPBP0P2f;R2,;>122>P0P3P6f=P5n0100000020000/65#1P6f<R2,;>g00J5RB#BR?%?BRB1Q36%N3RD%M3REP31C3>RGg00MQ1L3=R=C9,:E%K8R8PEP3P=g00GOPGC9,:EP8P31C35R89@3=g00N8R=P8C9,:ECACA1JE9R9P4P7g00KARG,E01I47=D0GdAH356CORGb6b7b8X931;>4126>1675#1[[^93P4f>P6P1O3b5W1P4O1122>P?PB%P3PDP3A@388P=P8C9,:EP9PGb6b7b81655#1P4b5W1P4O1n200210000000021100010000b?b>%4FPAP4O1EGW<W;P6P4O2n2001000000121000000b1b:15C:=3;7#4#1eW1X=@X0<XA3XB3P6P4O2n2001101000121102102X2;P4DSW0o"). Qed.
(* [comment removed for export] *)
Lemma sec_bytes_le_sum : forall l, Forall (fun e => 0 <= snd e) l -> sec_bytes l <= fold_right (fun e acc => snd e + acc) 0 l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "p'0h01lh11Hh24__x1h34__x2h44__x3h52H0h67__arithh74__ffh88__varmaph95__with:1ah;1Ah<1Ph=1eh>2H1h?2H2h@2IHhA3acchB1bi001bhC2b0hD1nhE1pi011pi021zp;2p;1p;3p;4p;5p;7p;8g001bR0j2aTg002Bj1BTg009]j20Tg000Gj31Tg002bj13Tg00=[j22Tg003`j1FTg004@j1OTg004^j1LTg005<j1JTg005gj2ITg006Jj2YTg006lj2XTg007Fj2VTg0082j3UTg008Lj3TTg008kj4STg00:9j36Tg00OXR1j2=Tg00P3j4QTg00:Yj1;Tg00;>j1PTg00<Zj2<Tg00;\j2NTg00<>j2?Tg00=7R2j3KTg00@Uj2ETg00A3j4MTg00CAj1@Tg00AQj2CTg00B_j1RTg00Cfj3>Tg00>8j1GTg00>Wj2DTg00?@j3HTg00?ij2`Tg00Dij5_Tg00PWj3^Tg00QQj5]Tg00B4j4ZTg00EKj7[Tg00DIj4\Tg00Eoj8WTg00G1R3f0R47^3p=5P3f2R5f1R6g00FSR7P4D]p=4P3P6g00GOP4CZp=8P6g00H6R8g00HUR9P9g00I5R:P4g00IUF[p=9P3P3P6P4C\p=7%@4#@p=:f3R;P8P9P9P:P5P6P4GWp=A1a33R8#BR<P8%54,07X=8R==184%36%56/24XA3X=8R>=486'0[R?X0<%F8R@918=g00J5RA#FRB%BARC%O3%L3RD%J3RE1I37RF/8F'91YE:R:P4P5g00JaRGg00KARH'X1V45=UGHdAT376CSRHb7b8b91077P4b6%3@A48>@'0eW1P0P3P3A6856918=A68;5R0#3A48>0'0[\?^0<P417;5=686918=g00Q4p4p710R0p-0\4R@%B5RIP1A6;6491;5P;P5O1f4RJ?1;6'=[RKP5P6O1A1;54'=A6J5691J;RL[PJP;O1f5RM?1J5'=\LP;P5P6P4CQP6n2001000000120000000W0X:6W<W;PK^0I^:6^<@^;0P4P8P=17MJR0P;P6O5%50,07A18=;'=P1f6R1/7M#5,07A18=JPGP3g00KaR0#;R@#;#;#;#;#:#:#:#:#:#PRI/<1P1P7n0100000020000%3M'2f7RK/71#5A48>M'2'0P4f8R1/7K#5,07A18=KPKP4O1%31R=A48>1R1'0f:RL,NI1?IL10LI1<IL3Kf;,<IPGP2f<R2,?I102IPGP3P6f>R2P7n0100000020000f=RN#3'2A48>N,22'0P61?INPBPCP31E35P61E3;CMROPDPE%@0,C3RP1C3@R@'8,9E%R9R91C30R0=>3PA>30@'8,9ECAP:PHb7b8b9X23X33X4310651265126;'0[^23^33^43P4A48>2RQ%32R2f?RRPMO4b6W5P4O110NIg00LFRN#GRS#G,D31D3S1D3N5H35H3g00Le'`=6ABPCPOPDPE180@,9EP9PE18FP,9EP9A>3F0A>3P@'8,9ECACAP:PHb7b8b9X23X33X4310451075127512;J'0[[^23^33^43P4PQPRP2PMPKO5b6W5P4O1n200210000000021000010000bCbBb1PGP3f9RG,<IPGP7n0100000020000/2=17LG#5/21'0eW?W>P6P4O2n2001000000121000000b1b517J;=685R5#3A48>5'0eW1X@?X0<XD3XE3P6P4O2n2001101000121102102X:8P4D_W0o"). Qed.
(* [comment removed for export] *)
Lemma sec_bytes_sub : forall l L, List.NoDup l -> incl l L -> sec_bytes l <= sec_bytes L.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "p'0h03INCh12NDh21Yh31lh42l2h51Hh61Lh72Hyh82l1h91Ah:1Xh;4__x1h<4__x2h=4__x3h>4__x4h?1ah@1yhA1zi001zhB2IHhC4INC'hD2NIhE7__arithhF4__ffhG8__varmaphH5__withI1ehJ1ni011nhK1pi021phL1xi031xi042p0p;2p;1p;3p;4p;5p;7p;6p;8g001bR0j2hTg002Bj1DTg00R0R1j25Tg00RLj39Tg002bj11Tg009]j22Tg003`j1HTg00Rej1ZTg00:9j37Tg00:Yj1>Tg00;>j1NTg00<Zj2;Tg00=[j24Tg00Sjj3^Tg00TDj4\Tg001Ej33Tg0082j3:Tg00TaR2j2ATg00U;j30Tg00URj1<Tg00OXR3j2@Tg00Ukj3YTg00VNj5XTg00Vjj5WTg00WHR4j2VTg00Wbj3UTg00X<j5GTg00XZj2TTg00Y9j7Qj6OTg00YUj3PTg00Yoj2ETg00@Uj2ITg004@j1RTg00A3j4FTg004^j1MTg005<j1STg00CAj1CTg00AQj2BTg00Cfj3?Tg00B4j4LTg00B_j1gTg00Eoj8fTg006Jj2eTg006lj2dTg007Fj2]Tg008Lj3_Tg008kj4`Tg00N_j6aj7bTg00Dij5cTg00DIj4JTg00EKj7[Tf0R5#C#Cp==f3R6g00G1R7P7f2R8f1R9CJ;75p=6P7P7P9P5CJp=8P9g00H6R:g00HUR;P;g00I5R<P5g00IUF[p=K1h77R=#DR>P=15=9A9=89%16%18R?'2[[^6>R@X3>%H=RA,5=A9=A9%Z8%1A/2?eW0W1X6>A7=68,5=f4RA=7=6=9=9P0P7P7f5RB97=5,5=f6RC97=9=9=AP0P7P7P7P8g00JaR0P7g00KaRD#>RE#>#>#>#>#=#=#=#=#=#NRF/;5P5g00FSRGn0100000020000f9RH#1'4n2001104000120102101%1B'2]0]1PBP=P9P5f8RIC6,5=P=P8P9PHC6f7RJ59=P=1868RKPIP5PKf:RL9^=KO2C\P=PBPAP5C693=99:>LX4>,A>X8>,A>P2P>f;RKP=PCPBP5C693=95:>X4>,A>X8>P0P71;FAPAPGn0100000020000f<RM#1RN'4%1LRO'2P5f=RPP=PIPJP5C693=95:>X4>,A>P2P>f>R2P=PHPIP5C693=85:>X4>P0P71;FIPIPGn0100000020000f@RQ#1RR'4%12RS'2P5P=PKPLP5C693=A9:>QP>18MKRT=7=993=BRUP=PPPMfDRVC6=9=5P0P71;FPPPPGn0100000020000fERW#1'4%19'2]0X6>fCRX97=T=9=UP1p4p710R1%D9RUP3A7895,58A0689#<1569'@[RTA0895#<1585'@A7689,56RY[A0A68#<15A8'@\YAY895P9n2001000000120000000W3X?5W9PT^3U^?5^91P5P=182PR1PWPMO4A0=1W#<15=W'@P3f?R3/82fFR150=#<15=1P0P71;F3P3PGn0100000020000fGRU#1'4P=PQP3PBC693=H#1'2P5fART/8QfHRY50=#<fIRZ,5=fKR[90=5PIP9P=18WVR\P9fLR]P5DXO2A7=\LR\93=2R^90=9P=P3P=P1PWPKC6RKP8P5DWA0=83A0=8K'VP4A0=6QP=PUP1PMC690=6A3=TP90=AP5A0=ATP=fBR_P2PBA0=B_A0=B2R`;U5DGW2P5O1P=PYPUPPC690=AP418ZY=:=BP`A3=X390=CP5fJRX/8Z=:=CP=18[XRZfS90=5A3=1_90=9]7X@=fR90=Z18][A3=WT50=PLP5O1'TW7PJP5PCFQW2P5O1A0=C3P=PVPQPJA0=JVA0=JQ;P5DGW2P5O1n200100000021000010000W5P5O1n200100000021000010000b2b2W7X@=A3=MI99=XRMePMPXA3=PHRPP9P5O3%1[%1P'2P7%1\,4SP0P71;FWPWPGn0100000020000fM#1RW'4RP/25XA7P7A3=2L#112W5XA7P514SORS1E2LEO%1]/2Sg00J5RS#H%DSP7P71I7AP8%R7CFP91I76CF%M7%S7RSP:P;P;P<P7%CDR:,B7R]g00GORL1B7ERE%C:,B7R:5?7CL,KS%g;P71B7DRD=?7]PLA?7D:9?7ECL,KSGf1eS<P5P8g00KARS,d01]58=:0SdA_7G9C`bFbGbHX;7X<7X=7X>71486,291498149A,46'2[^;7^<7^=7^>7P5PNPRfN#1P0P71;F1P1PGn0100000020000P9O5bE%13%1K'4,2Peb:%1^1E2\Eab:bCW1WDP9P5O2n2001000000121000000b1b5W0PTP5PHFbW5X4>P9P5O2n2001000000121103000W5X8>P9P5O2n2001000000121103000bIW0W1XJ7XK7P9P5O2n2001102000121100100P9P5O2A7=BA#1/2?eW0W1X6>XB@X3>XL=P5DcW3o"). Qed.
(* [comment removed for export] *)
Definition mcost (n : Z) : Z := if n <=? 64512 then 0 else 2 * n + 16384.

(* [comment removed for export] *)
Definition e_malloc : Z := 0x67d44.        (* [comment removed for export] *)
Definition e_free : Z := 0x67d40.          (* [comment removed for export] *)
Definition e_strdup : Z := 0x4bf34.        (* [comment removed for export] *)
Definition e_strndup : Z := 0x4beac.       (* [comment removed for export] *)
Definition e_strlen : Z := 0x56b64.        (* [comment removed for export] *)
Definition e_strnlen : Z := 0x56b68.       (* [comment removed for export] *)
Definition e_strncmp : Z := 0x4beb4.       (* [comment removed for export] *)
Definition e_memchr : Z := 0x56b7c.        (* [comment removed for export] *)
Definition e_memset : Z := 0x66524.        (* [comment removed for export] *)
Definition e_memcpy : Z := 0x6652c.        (* [comment removed for export] *)
Definition e_asan_memcpy : Z := 0x66530.   (* [comment removed for export] *)
Definition e_asan_memset : Z := 0x669cc.   (* [comment removed for export] *)
Definition e_read : Z := 0x56b84.          (* [comment removed for export] *)
Definition e_fwrite : Z := 0x56b88.        (* [comment removed for export] *)
Definition e_vprintf : Z := 0x56b98.       (* [comment removed for export] *)
Definition e_vfprintf : Z := 0x56b9c.      (* [comment removed for export] *)
Definition e_vsnprintf : Z := 0x56ba0.     (* [comment removed for export] *)
Definition e_fprintf : Z := 0x56ba4.       (* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_stack_malloc (k : nat) : Z :=
  match k with 0%nat => 0x51614 | 1%nat => 0x51788 | _ => 0x51c60 end.
(* [comment removed for export] *)
Definition set_shadow_vals : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 0xf1; 0xf2; 0xf3; 0xf5; 0xf8].
Definition e_set_shadow (v : Z) : Z :=
  match v with
  | 0 => 0x69f6c | 1 => 0x69f84 | 2 => 0x69f9c | 3 => 0x69fb4 | 4 => 0x69fcc | 5 => 0x69fe4 | 6 => 0x69ffc
  | 7 => 0x6a014 | 241 => 0x6a02c | 242 => 0x6a044 | 243 => 0x6a05c | 245 => 0x6a074 | _ => 0x6a08c
  end.

(* [comment removed for export] *)
Definition fs_size (k : nat) : Z := Z.shiftl 64 (Z.of_nat k).

(* [comment removed for export] *)
Definition ALLOC_RAS : list Z :=
  (* [comment removed for export] *)
  [0x960c8; 0x9611c; 0x96140; 0x96270; 0x963a8; 0x9643c; 0x99c2c; 0xa4b30; 0xa4b80; 0xa2d34; 0xa2d3c].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record rt_sig : Type := mkRTS {
  rts : Type;
  ART : rts -> mem -> Prop;               (* [comment removed for export] *)
  ARTM : rts -> Model -> Prop;            (* [comment removed for export] *)
  rt_live : rts -> list (Z * Z);          (* [comment removed for export] *)
  rt_frames : rts -> list (Z * nat);      (* [comment removed for export] *)
  rt_allow : rts -> list (Z * Z);         (* [comment removed for export] *)
  rt_sp0 : rts -> Z;                      (* [comment removed for export] *)
  rt_credit : rts -> Z                    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition fdfs_only (PMc : Model -> Prop) : Prop :=
  forall mo mo', m_fds mo' = m_fds mo -> m_fs mo' = m_fs mo -> PMc mo -> PMc mo'.

(* [comment removed for export] *)
Definition frmW (Pm : machine_state -> Prop) : machine_state -> Prop := fun ms => Pm ms /\ FP.frm0 (ms_fcsr ms).

(* [comment removed for export] *)
Definition ASTA (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop) (Pm : machine_state -> Prop) : config -> Prop :=
  AST SEGTOP_A (rt_allow RT Σ) (frmW Pm) (fun mo => ARTM RT Σ mo /\ PMc mo).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CLIENT_STATIC : list (Z * Z) := [ (0x10ef50, 0x116718) (* [comment removed for export] *) ;
                                              (0x63c3d0, 0x64c3d0) (* [comment removed for export] *) ;
                                              (0x64c3d0, 0x66e828) (* [comment removed for export] *) ].
(* [comment removed for export] *)
Definition RT_STATIC : list (Z * Z) :=
  [(* [comment removed for export] *)
   (0x10f184, 0x10f1a0); (0x10f1a8, 0x10f1c0); (0x10f1c8, 0x10f1e0); (0x10f1e8, 0x10f200); (0x10f204, 0x10f220); (0x10f224, 0x10f240); (* [comment removed for export] *)
   (0x64cef0, 0x64cef8); (0x64cf40, 0x64cf60); (0x64cf68, 0x64cf78); (0x66e2f0, 0x66e2f8);
   (* [comment removed for export] *)
   (0x66d208, 0x66d210)].

Definition in_ranges (l : list (Z * Z)) (a : Z) : Prop := exists lo hi, In (lo, hi) l /\ lo <= a < hi.
Definition client_static (a : Z) : Prop := in_ranges CLIENT_STATIC a /\ ~ in_ranges RT_STATIC a.

Definition in_live (live : list (Z * Z)) (a : Z) : Prop := exists p n, In (p, n) live /\ p <= a < p + n.
(* [comment removed for export] *)
Definition in_fframe (frames : list (Z * nat)) (a : Z) : Prop :=
  exists f k, In (f, k) frames /\ f <= a < f + fs_size k - 8.
(* [comment removed for export] *)
Definition in_fframe_shadow (frames : list (Z * nat)) (a : Z) : Prop :=
  exists f k, In (f, k) frames /\ shad f <= a < shad (f + fs_size k).

Definition aclient (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (a : Z) : Prop :=
  (sp <= a < USTACK_TOP) \/ client_static a \/ in_live live a \/ in_fframe frames a \/ in_fframe_shadow frames a.

(* [comment removed for export] *)
Definition rt_pres (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (m m' : mem) : Prop :=
  forall a : word, aclient live frames sp (bv_unsigned a) -> m' a = m a.
(* [comment removed for export] *)
Definition rt_pres_ex (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (d n : Z) (m m' : mem) : Prop :=
  forall a : word, aclient live frames sp (bv_unsigned a) -> ~ (d <= bv_unsigned a < d + n) -> m' a = m a.

(* [comment removed for export] *)
Definition rng_class (RT : rt_sig) (Σ : rts RT) (s n : Z) : Prop :=
  (exists p k, In (p, k) (rt_live RT Σ) /\ p <= s /\ s + n <= p + k)
  \/ (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= s /\ s + n <= f + fs_size k - 8)
  \/ (rt_sp0 RT Σ - STACK_WIN + 64 <= s /\ s + n <= USTACK_TOP - 16)
  \/ (0x10000 <= s /\ s + n <= SEGTOP_A).

(* [comment removed for export] *)
Definition call_ok (RT : rt_sig) (Σ : rts RT) (m : mem) (sp : word) (lo : Z) : Prop :=
  stk asegs m lo (bv_unsigned sp) /\ rt_sp0 RT Σ - STACK_WIN <= lo /\ lo + RT_STACK <= bv_unsigned sp
  /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0.

(* [comment removed for export] *)
Definition unwind_ok (ra s0 sp : word) : Prop :=
  In (bv_unsigned ra) ALLOC_RAS
  /\ (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition entry_st (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (pc : Z) (m : mem) : machine_state :=
  MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom asegs).

(* [comment removed for export] *)
Definition ret_st (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (m' : mem) (ms : machine_state) : Prop :=
  exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32),
    ms = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 v a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (ret_pc ra) fc' None m' (seg_rom asegs).

(* [comment removed for export] *)
Definition rt_after (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
  ART RT Σ' m' /\ mem_inv asegs m' /\ wmono asegs m m' /\ stk asegs m' lo sp.

(* [comment removed for export] *)
Definition rt_after_f (RT : rt_sig) (Σ' : rts RT) (sp lo : Z) (m m' : mem) : Prop :=
  ART RT Σ' m' /\ mem_inv asegs m' /\ stk asegs m' lo sp.

Lemma rt_after_f_of : forall RT Σ' sp lo m m', rt_after RT Σ' sp lo m m' -> rt_after_f RT Σ' sp lo m m'.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "h01Hh12H1h22H2h32H4h42RTh52_Hh62loh71mh82m'h92sph:3Σ'p;1p;6p;3p;2p;4p-1p100[1p4p710p8p100[Ep4p70p100\5p4p710R0p8p100\Sp4p70P0p8g00]Aj1>Tg00CAj13Tg00^9j18Tg00^Wj17Tg00_:j1=Tg00_\j6:Tg00`Yj35Tg00aQj24Tg00OXR0j20Tg00bHj66Tg00cGj49Tg00cbj3<Tg00dYj4;Tg00eNR1f1R2f0R33<p=2P1f2R4P2P3C;p=1g00fF%>3g00G1R5g00Ka#3#3#3R6#3#3#3#8#7%86#7#=[R6f5R7f4R8f3R9P4P2P3E:P0f6R:?57214121242A1298'0'0f7R;P:P7P8P9P4E6P3f8R4?5;914181278A18:;'0'0P0141712:7A17;4'0f;R8f:R9f9R<P4P;P:E6P3141;12<4A1498'0P0129<f<R091<8f?R4f>R;f=R:P0P8P9E6P31208A10;4fBfA;5:141:R1f@91:4R:'0P<P1P:P7P3C9C9W3W5P2P3O2n2001000000120000000W0W2P2P3O2n2001000000120000000W0W1P2P3O2n2001000000120000000W0X86W7X65W9W:W4o"). Qed.

(* [comment removed for export] *)
Definition icpt_post (RT : rt_sig) (Σ : rts RT) (PMc : Model -> Prop)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v : word) (lo d n : Z) (m : mem) (Q : mem -> Prop) : config -> Prop :=
  ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
                    /\ rt_after RT Σ (bv_unsigned sp) lo m m'
                    /\ rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) d n m m' /\ Q m').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Contracts.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition malloc_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (n lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (p : Z),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' p n /\ acc asegs m' p n) c
    /\ rt_live RT Σ' = (p, n) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ - mcost n /\ 0 < p /\ p mod 16 = 0 /\ p + n < USTACK_TOP.

Definition malloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 0x64cf48 ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  (64512 < n -> sec_bytes (rt_live RT Σ) + n <= SEC_BYTES) (* [comment removed for export] *) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_malloc m)))
            (malloc_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

(* [comment removed for export] *)
Definition live_remove (p : Z) (live : list (Z * Z)) : list (Z * Z) := filter (fun e => negb (fst e =? p)) live.
(* [comment removed for export] *)
Lemma sec_bytes_live_remove : forall p l, sec_bytes (live_remove p l) <= sec_bytes l.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) ["Contracts"] "p'0h04__x1h14__x2h27__arithh34__ffh48__varmaph55__with61eh71lh81xh91Eh:1Hh;4__x3h<1bi001bh=2b0h>2IHh?1Nh@1ahA1nhB1pi011phC1qi021zp;2p;1p;3p;4p;6p;5p;7p;8g001bR0j2hTg002Bj1RTg00gCj21Tg002bj13Tg003`j1MTg004@j1\Tg004^j1ZTg005<j1YTg005gj2KTg006Jj2UTg006lj2HTg007Fj2gTg0082j35Tg008Lj3eTg008kj4`Tg009]j22Tg00hCj1]Tg000hj3[Tg00hhj29Tg00iEj17Tg00icj18Tg00j>j1;Tg00j\j6<j3XTg00:9j30Tg00URj1ETg00k0j2DTg00Rej1WTg00:Yj1>Tg00;>j1VTg00<Zj2JTg00=[j26Tg00;\j2TTg00<>j2BTg00=7R1j3STg00>8j1ITg00>Wj2CTg00?@j3QTg00?ij2fTg00@Uj2OTg00A3j4PTg00CAj1FTg00AQj2GTg00B4j4NTg00B_j1_Tg00Cfj3?Tg00N_j6^Tg00Dij5aTg00EKj7LTg00DIj4bTg00Eoj8cTf1R2#3f0R3'2p=4f2R4g00H6R5g00HUR6P6g00I5R7g00G1R8P2g00GOP3CNg00IUR9FLp=:P8P8P2P3Cbp==%F3#Fp=AP2P5P6P6P7P3P9FLp=df3R9P5P6P6P7P4P2P3Gcp=@1h88R5#RR:P51143%33R;'4X7:g00J5R<#MR=%R<R>%\8R?%Z8R@%Y8RAg00FSRB,K8RC;:C1UA7R7P3P4g00JaRDg00KARE'H1g34=5DEdAe8B2C`RFb3b4b512BBP3b2P5P:%]5RGA[883RH/94#7RI#8X65%;IX85%M5RIE<%3IRJ'4e112I/4JeP0P8P8f4R0/13/4;f5RJA0542RI'1%3I'4[^7:P3f7RI/13/4;f8RK,99RLPDPDg00kDRM%73RN#8RO%EOP:%;N,DOf6RO/=JRNP5P:AX5:GRPf<RQ,9H#7RR#8X65%;RX85P0E<RR505PRn200100000021000010000PDP:P3P5P:PGf;RR,9H#7RS#8X65RT%;SX85RSP9E<RU1=J0RV=05Un010000002000055:P3P5P:PGf:RU,9H#7RW#8X65%;WX85P4E<RW,H:PM%7ERE#8RX%EXP:%;E,DXP5P:PPPTPSP9E<RS905VRTPSn200100000021000010000=5:We1=09RP=05WRW,H:PMg00kd#7RM#8RX%EXP:%;M,DXPTPSn200100000021000010000=5:Wen0110001020001b<P5P:PGf9RW,9H#7RH#8X65RS%;HX85RH1=94RT=052RXE<PDP:PLP5P:PGPSPHP2E<RHA05THn010000002000055:e11KXPDP:PL11K2RLA05TLn010000002000055:RLePLP:PDP:190W11W4RLA05PLn0100000020000A05V9#3RL,2;X7:%W4%34,2B19JUR;PDPD1=IORT=05J,1QPDP:P311QJRQA05TQRTn010000002000055:PDP:P2f=/1ORX1=KI=05Xn0100000020000PDP8g00KaRX#>RH#>#>#>#>#A#A#A#A#A#VRS/JIRGPIPBn0100000020000%3O'6'4]9P3A05N0,1RRI11R0RM55:1TSORE1BSO12OS1JSORY3SRZPGPDP11BSKR[12KSRKf@/1W#3R\PDP8P2PUPBn0100000020000R]%3W'6R^'2P21BSWR_g00LFR`#IRa#I,C81C8a1C8`5Q85Q8g00Le'f=0<=P>P81O84R<P21O89CPR`P@PAP81K8Sg00MQ%FX,G8RaCN,dA%_6R6PA1G8XRX1G8HRH5:AP6A?8aH9:AXC@C@P7PFb3b4b5X08X18X;81BS212291690,24[[^08^18^;8P3%3UR0PRfA/1U#3RbP2PWO5b2W:P3O112WSRSP=P>P8P<P2P?CPR?P@PAA:AXaR<P6A?8CaRc9:AXC@P7PFb3b4b5X08X181232Rd16B4Re,22[^08^18P3P0PbPWO3Rfb2W:P3O1n200210000000021100010000b=b<PDP8PYPOPBn0100000020000%3J'6RJ,4QeW9A05NM95:IPEPZPGPDP1P[PK16]\/2^P2P=P>P`P@PAA:AaHP6A?8XaA?8XH5:AC@P7PFb3b4b5X08X18X;8122416241629'2[^08^18^;8P3P0PbPRPWO4b2X:_P3O1P=P>P?P@PAP<P6A?8CX=:AcC@P7PFb3b4b5X08X1816B2/2e\d^08^18Pfb2X:SP3O1n200210000000021000010000b=b<14TJeW9n0110000020101P4O1b<PDP:P;11U9RUA05VUn0100000020000/4Leb?A05P4,1WP3E^b9W>X7:XA8XC8P2P3O2n2001101000121102102X@5P3DaW7XB8o"). Qed.

(* [comment removed for export] *)
Definition free_post (Σ : rts RT) (PMc : Model -> Prop) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (p lo : Z) (m : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (v : word),
    ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ') (rt_frames RT Σ) (bv_unsigned sp) m m') c
    /\ rt_live RT Σ' = live_remove p (rt_live RT Σ) /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
    /\ rt_credit RT Σ' = rt_credit RT Σ.

Definition free_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 0x64cf48 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

(* [comment removed for export] *)
Definition free_null_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x64cf48 ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (fun c => exists v, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo 0 0 m (fun _ => True) c).

(* [comment removed for export] *)
Definition strdup_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s : Z) (str : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> tp = Z_to_bv 64 0x64cf48 ->
  bytes_at asegs m s (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 < 2^27 ->
  rng_class RT Σ s (Z.of_nat (length str) + 1) -> acc asegs m s (Z.of_nat (length str) + 1) ->
  ((forall i, 0 <= i < Z.of_nat (length str) + 1 -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (s + i))
   \/ (0x10000 <= s /\ s + Z.of_nat (length str) + 1 <= 0x107000) (* [comment removed for export] *)) ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (Z.of_nat (length str) + 1) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strdup m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ bytes_at asegs m' p (str ++ [Z_to_bv 8 0]) /\ wr_at asegs m' p (Z.of_nat (length str) + 1)
         /\ acc asegs m' p (Z.of_nat (length str) + 1)) c
       /\ rt_live RT Σ' = (p, Z.of_nat (length str) + 1) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (Z.of_nat (length str) + 1)
       /\ 0 < p /\ p + Z.of_nat (length str) + 1 < USTACK_TOP).

(* [comment removed for export] *)
Definition strndup_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s k : Z) (buf : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 k -> tp = Z_to_bv 64 0x64cf48 ->
  0 <= k < 2^27 -> bytes_at asegs m s buf -> strnlen_known k buf ->
  (exists p0 n0, In (p0, n0) (rt_live RT Σ) /\ p0 <= s /\ s + Z.of_nat (length buf) <= p0 + n0) ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (k + 1) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_ok ra s0 sp ->
  let cl := strnlen_res k buf in
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strndup m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ bytes_at asegs m' p (firstn (Z.to_nat cl) buf ++ [Z_to_bv 8 0]) /\ wr_at asegs m' p (cl + 1)
         /\ acc asegs m' p (cl + 1)) c
       /\ rt_live RT Σ' = (p, cl + 1) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ
       /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (cl + 1)
       /\ 0 < p /\ p + cl + 1 < USTACK_TOP).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition checked_src (Σ : rts RT) (m : mem) (sp : word) (lo s n : Z) : Prop :=
  (0 < n -> acc asegs m s n /\ rng_class RT Σ s n) /\ (s + n <= lo \/ bv_unsigned sp <= s).
(* [comment removed for export] *)
Definition checked_dst (Σ : rts RT) (m : mem) (sp : word) (d n : Z) : Prop :=
  (0 < n -> acc asegs m d n /\ rng_class RT Σ d n)
  /\ (forall i, 0 <= i < n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (d + i)) /\ wr_at asegs m d n.

(* [comment removed for export] *)
Definition memcpy_icontract (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d s : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  0 <= d <= 2^47 -> 0 <= s <= 2^47 -> Z.of_nat (length bs) < 2^40 -> bytes_at asegs m s bs ->
  checked_src Σ m sp lo s (Z.of_nat (length bs)) -> checked_dst Σ m sp d (Z.of_nat (length bs)) ->
  (d + Z.of_nat (length bs) <= s \/ s + Z.of_nat (length bs) <= d) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d (Z.of_nat (length bs)) m
               (fun m' => bytes_at asegs m' d bs)).

(* [comment removed for export] *)
Definition memset_icontract (entry : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d n : Z) (c : byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (bv_unsigned c) -> a2 = Z_to_bv 64 n ->
  0 <= d <= 2^47 -> 0 <= n < 2^40 -> checked_dst Σ m sp d n ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc entry m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 d) lo d n m
               (fun m' => bytes_at asegs m' d (repeat c (Z.to_nat n)))).

(* [comment removed for export] *)
Definition memchr_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s cz n : Z) (buf : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 cz -> a2 = Z_to_bv 64 n ->
  0 < s <= 2^47 -> 0 <= cz < 256 -> 0 <= n < 2^40 -> bytes_at asegs m s buf -> memchr_ok s cz n buf ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) (* [comment removed for export] *) ->
  checked_src Σ m sp lo s (memchr_chk cz n buf) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_memchr m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (memchr_res s cz n buf)) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strlen_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s : Z) (str slack : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s ->
  bytes_at asegs m s (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) < 2^40 ->
  (- (s + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) ->
  0 < s <= 2^47 -> (s + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= s) ->
  checked_src Σ m sp lo s (Z.of_nat (length str) + 1) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strlen m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.of_nat (length str))) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strnlen_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (s n : Z) (buf : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
  0 < s <= 2^47 -> 0 <= n < 2^40 -> bytes_at asegs m s buf -> strnlen_ok s n buf ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) (* [comment removed for export] *) ->
  checked_src Σ m sp lo s (strnlen_chk n buf) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strnlen m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strnlen_res n buf)) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
Definition strncmp_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p1 p2 n : Z) (b1 b2 : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 n ->
  0 < n < 2^31 -> bytes_at asegs m p1 b1 -> bytes_at asegs m p2 b2 -> strncmp_ok n b1 b2 ->
  checked_src Σ m sp lo p1 (strncmp_sz n b1 b2) -> checked_src Σ m sp lo p2 (strncmp_sz n b1 b2) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_strncmp m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (strncmp_res n b1 b2)) lo 0 0 m
               (fun _ => True)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_malloc_contract (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> (k = 0 \/ k = 1 \/ k = 6)%nat -> tp = Z_to_bv 64 0x64cf48 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8)) c
       /\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP).

(* [comment removed for export] *)
Definition set_shadow_contract (v : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d n : Z) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> In v set_shadow_vals -> a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 n ->
  0 <= n < 2^20 -> (forall i, 0 <= i < n -> in_fframe_shadow (rt_frames RT Σ) (d + i)) -> wr_at asegs m d n ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_set_shadow v) m)))
    (fun c => exists v0, icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v0 lo d n m
               (fun m' => bytes_at asegs m' d (repeat (Z_to_bv 8 v) (Z.to_nat n))) c).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition client_consts (m : mem) : Prop :=
  ro_cells asegs m g_GOT_shadow_offset_cell [C8 (Z_to_bv 64 g_shadow_memory_dynamic_address)]
  /\ ro_cells asegs m g_shadow_memory_dynamic_address [C8 (Z_to_bv 64 SHB)]
  /\ ro_cells asegs m g_GOT_detect_uar [C8 (Z_to_bv 64 g_detect_stack_use_after_return)]
  /\ ro_cells asegs m g_detect_stack_use_after_return [C4 (Z_to_bv 64 1)].

(* [comment removed for export] *)
Definition ACC_LITS : list (Z * Z) :=
  [(0x25200, 14); (0x25220, 10); (0x25240, 16); (0x25260, 29); (0x25360, 39); (0x253c0, 16); (0x253e0, 18); (0x25420, 19); (0x254c0, 12); (0x254e0, 24); (0x256c0, 11); (0x25860, 16); (0x25880, 12); (0x25900, 13); (0x25960, 12); (0x259c0, 17); (0x25a80, 10); (0x2aaa0, 13); (0x25be0, 15); (0x25c00, 22); (0x25c80, 11); (0x25ee0, 16); (0x26140, 14); (0x26be0, 15); (0x26c00, 19); (0x26c40, 15); (0x26c60, 17); (0x26ca0, 23); (0x27000, 22); (0x27040, 15); (0x27400, 17); (0x274c0, 15); (0x274e0, 29); (0x27520, 11); (0x27540, 14); (0x275a0, 17); (0x27760, 22); (0x277a0, 20); (0x277e0, 37); (0x28a60, 19); (0x28aa0, 8); (0x28ac0, 16); (0x2aa60, 28); (0x2aac0, 21); (0x29bc0, 13); (0x29be0, 17); (0x29c20, 25); (0x29cc0, 18); (0x29d00, 14); (0x29d20, 15); (0x29d40, 15); (0x29d60, 16); (0x29d80, 22); (0x29e40, 14); (0x29e60, 18); (0x29ea0, 25); (0x24680, 17); (0x25460, 47); (0x25520, 48); (0x25580, 52); (0x255e0, 53); (0x25660, 37); (0x26b80, 37); (0x26160, 27); (0x26ce0, 37); (0x26d40, 47); (0x26da0, 46); (0x26e00, 31); (0x26e40, 51); (0x26ea0, 56); (0x26f00, 58); (0x26f60, 77); (0x29c60, 35); (0x29dc0, 84); (0x261a0, 132);
   (* [comment removed for export] *)
   (0x248c0, 21); (0x24900, 11); (0x24920, 37); (0x24980, 12); (0x249a0, 17); (0x249e0, 17); (0x24a20, 11); (0x24a40, 16); (0x24a60, 14); (0x24a80, 17); (0x24c20, 13); (0x24c40, 11); (0x24c60, 16); (0x24c80, 33); (0x24ce0, 15); (0x24d00, 19); (0x24d40, 21); (0x24d80, 18); (0x24dc0, 16); (0x24de0, 15); (0x24e00, 20); (0x24e40, 16); (0x24e60, 24); (0x24ea0, 17); (0x24f20, 37); (0x24fa0, 19); (0x24fe0, 11); (0x25040, 12); (0x252a0, 17); (0x252e0, 18); (0x25780, 17); (0x25aa0, 18); (0x25ca0, 15); (0x25cc0, 15); (0x25f80, 17); (0x26320, 14); (0x26340, 20); (0x26380, 23); (0x263c0, 21); (0x26400, 17); (0x26440, 16); (0x26460, 17); (0x264a0, 18); (0x264e0, 17); (0x26520, 17); (0x26560, 24); (0x265a0, 20); (0x265e0, 21); (0x26620, 19); (0x26660, 16); (0x26680, 13); (0x266a0, 17); (0x266e0, 19); (0x26720, 15); (0x26740, 39); (0x275e0, 29); (0x27620, 21); (0x27660, 19); (0x276a0, 13); (0x276c0, 31); (0x27700, 33); (0x28b20, 17); (0x28b60, 12); (0x28b80, 17); (0x28bc0, 31); (0x2a600, 17); (0x2a660, 14); (0x2a680, 19); (0x2a740, 16); (0x2a7a0, 20); (0x2a7e0, 16); (0x2a8e0, 13); (0x2a9c0, 13); (0x2a9e0, 19); (0x2ab00, 18); (0x2ab40, 77); (0x2abc0, 13); (0x2abe0, 19); (0x2ac20, 25); (0x2ac60, 29); (0x2aca0, 17); (0x2ace0, 20); (0x2ad20, 13); (0x2ad40, 17); (0x2ad80, 18); (0x2adc0, 16); (0x2ade0, 23); (0x2ae20, 22); (0x2ae60, 18); (0x2aea0, 24); (0x2aee0, 86); (0x2af60, 23); (0x2afa0, 14); (0x2afc0, 23); (0x2b000, 22); (0x2b040, 20); (0x2b080, 19); (0x2b0c0, 16); (0x2b0e0, 13); (0x2b100, 14); (0x2b120, 16); (0x2b140, 15); (0x2b160, 15); (0x2b180, 24); (0x2b1c0, 14); (0x25320, 24); (0x25a20, 10); (0x25a40, 17); (0x256e0, 8); (0x257c0, 16); (0x25820, 15); (0x25840, 15); (0x26b40, 12); (0x26b60, 13); (0x26fe0, 16); (0x2ab40, 77); (0x2aee0, 86); (0x28ce0, 132); (0x28da0, 132)].

Record art_facts : Prop := mkAF {
  af_client_consts : forall Σ m, ART RT Σ m -> client_consts m;
  (* [comment removed for export] *)
  af_frame : forall Σ (m m' : mem) (sp : Z), ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= sp ->
    (forall a : word, ~ aclient (rt_live RT Σ) (rt_frames RT Σ) sp (bv_unsigned a) -> m' a = m a) ->
    wmono asegs m m' -> ART RT Σ m';
  (* [comment removed for export] *)
  af_with_fds : forall Σ mo fds, ARTM RT Σ mo -> ARTM RT Σ (with_fds fds mo);
  af_mat_stable : forall Σ, mat_stable (ARTM RT Σ);
  (* [comment removed for export] *)
  af_acc_live : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> wr_at asegs m p n /\ acc asegs m p n;
  (* [comment removed for export] *)
  af_live_slack : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
    exists slack, bytes_at asegs m (p + n) slack /\ (- (p + n)) mod 8 <= Z.of_nat (length slack)
      /\ p + n + Z.of_nat (length slack) <= rt_sp0 RT Σ - STACK_WIN;
  (* [comment removed for export] *)
  af_acc_stack : forall Σ m a n, ART RT Σ m -> rt_sp0 RT Σ - STACK_WIN <= a -> a + n <= USTACK_TOP -> acc asegs m a n;
  (* [comment removed for export] *)
  af_acc_static : forall Σ m a n, ART RT Σ m -> 0 <= a ->
    (forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x10f580 <= a + i < 0x1166c0)) -> acc asegs m a n;
  (* [comment removed for export] *)
  af_live_range : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) ->
    0 < p /\ p + n <= rt_sp0 RT Σ - STACK_WIN /\ (p + n <= 0x10000 \/ SEGTOP_A <= p);
  af_live_disj : forall Σ m p1 n1 p2 n2 l1 l2, ART RT Σ m -> rt_live RT Σ = l1 ++ (p1, n1) :: l2 -> In (p2, n2) (l1 ++ l2) ->
    p1 + n1 <= p2 \/ p2 + n2 <= p1;
  af_frames_range : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
    0 < f /\ f + fs_size k <= rt_sp0 RT Σ - STACK_WIN /\ (f + fs_size k <= 0x10000 \/ SEGTOP_A <= f)
    /\ forall p n, In (p, n) (rt_live RT Σ) -> f + fs_size k <= p \/ p + n <= f;
  af_sp0_range : forall Σ m, ART RT Σ m -> SEGTOP_A + STACK_WIN <= rt_sp0 RT Σ <= USTACK_TOP;
  (* [comment removed for export] *)
  af_sp0_win : forall Σ m, ART RT Σ m -> 0x7fff80000000 <= rt_sp0 RT Σ;
  (* [comment removed for export] *)
  af_frame_release : forall Σ (m : mem) f k fr, ART RT Σ m -> rt_frames RT Σ = (f, k) :: fr ->
    exists (Σ' : rts RT) (fl : Z), rw_cells asegs m fl [C1 (Z_to_bv 8 1)]
      /\ ~ aclient (rt_live RT Σ) (rt_frames RT Σ) USTACK_TOP fl
      (* [comment removed for export] *)
      /\ 0 < fl /\ fl + 1 <= rt_sp0 RT Σ - STACK_WIN
      (* [comment removed for export] *)
      /\ ro_cells asegs m (f + fs_size k - 8) [C8 (Z_to_bv 64 fl)]
      /\ forall m', munch [(fl, fl + 1)] m m' -> wmono asegs m m' -> rw_cells asegs m' fl [C1 (Z_to_bv 8 0)] ->
           ART RT Σ' m' /\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
           /\ rt_credit RT Σ' = rt_credit RT Σ /\ rt_allow RT Σ' = rt_allow RT Σ /\ (forall mo, ARTM RT Σ mo -> ARTM RT Σ' mo);
  (* [comment removed for export] *)
  af_frames_align : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f mod 64 = 0 /\ SEGTOP_A <= f;
  af_frames_disj : forall Σ m f1 k1 f2 k2 l1 l2, ART RT Σ m -> rt_frames RT Σ = l1 ++ (f1, k1) :: l2 -> In (f2, k2) (l1 ++ l2) ->
    f1 + fs_size k1 <= f2 \/ f2 + fs_size k2 <= f1;
  af_fshadow_apart : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) ->
    (forall p n, In (p, n) (rt_live RT Σ) -> p + n <= shad f \/ shad (f + fs_size k) <= p)
    /\ (forall f' k', In (f', k') (rt_frames RT Σ) -> f' + fs_size k' <= shad f \/ shad (f + fs_size k) <= f');
  (* [comment removed for export] *)
  af_got_lib : forall Σ m, ART RT Σ m ->
    ro_cells asegs m 0x10b7d8 [C8 (Z_to_bv 64 0x10f180)] /\ ro_cells asegs m 0x10b838 [C8 (Z_to_bv 64 0x66cf88)];
  (* [comment removed for export] *)
  af_acc_lits : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) ACC_LITS;
  (* [comment removed for export] *)
  af_frames_hi : forall Σ m f k, ART RT Σ m -> In (f, k) (rt_frames RT Σ) -> f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f;
  (* [comment removed for export] *)
  af_live_align : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p mod 16 = 0
}.

Record rt_contracts : Prop := mkRTC {
  rc_malloc : malloc_contract;
  rc_free : free_contract;
  rc_free_null : free_null_contract;
  rc_memcpy : memcpy_icontract e_memcpy;
  rc_asan_memcpy : memcpy_icontract e_asan_memcpy;
  rc_memset : memset_icontract e_memset;
  rc_asan_memset : memset_icontract e_asan_memset;
  rc_memchr : memchr_icontract;
  rc_strlen : strlen_icontract;
  rc_strnlen : strnlen_icontract;
  rc_stack_malloc_0 : stack_malloc_contract 0;
  rc_stack_malloc_1 : stack_malloc_contract 1;
  rc_stack_malloc_6 : stack_malloc_contract 6;
  rc_set_shadow : forall v, In v set_shadow_vals -> set_shadow_contract v;
  rc_facts : art_facts
}.

End Contracts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition PMfd (F0 : list (word * FdEntry)) (fs0 : Fs) : Model -> Prop := fun mo => m_fds mo = F0 /\ m_fs mo = fs0.

Lemma PMfd_fdfs_only : forall F0 fs0, fdfs_only (PMfd F0 fs0).
Proof.
ltac2:(KReplay.run1 (kr_t_RT_iface ()) [] "h02E1h12E2h22F0h31Hh42H1h52H2h63fs0h72moh83mo'p;1p;2p;3p;6p;4g00CAj12Tg00^9j1<Tg00^Wj17Tg001bj26Tg002Bj1;Tg00lDj11Tg0082j30Tg00m8j13Tg00mkj34j29Tg00\5j65Tg00cGj48Tg00ndj1:Tg00Ka#2#2#2#2#2#2#<#7g00ob'6#;R0g00\SR1g010ZR2f0R3#1f1R4#1500%34f2#3501f5R5f4R6f334g00OX%16f6R7500%36=015f7R8?476P3%17f8R6500%38R9=016%18R8f:R:500f9R;9019P0P8%16P:P7P4E5P1P9%36P;P5P3E5C8W5W4P4P3O2n2001000000120000000W3W1W0X82W71943#:eW6W2o"). Qed.

(* [comment removed for export] *)
Definition rt_pres_fp (live : list (Z * Z)) (frames : list (Z * nat)) (sp : Z) (W : list (Z * Z)) (m m' : mem) : Prop :=
  forall a : word, aclient live frames sp (bv_unsigned a) -> outside W (bv_unsigned a) -> m' a = m a.

(* [comment removed for export] *)
Definition errno_cell (tp : word) : Z := bv_unsigned tp - 164.

(* [comment removed for export] *)
Definition FMT_usage : Z := 0x16729.          (* [comment removed for export] *)
Definition FMT_cannot_open : Z := 0x201ea.    (* [comment removed for export] *)
Definition FMT_read_error : Z := 0x201ff.     (* [comment removed for export] *)
Definition FMT_too_big : Z := 0x1b4c4.        (* [comment removed for export] *)
Definition FMT_emit : Z := 0x15265.           (* [comment removed for export] *)
(* [comment removed for export] *)
Definition STDERR_FILE : Z := 0x10f288.

(* [comment removed for export] *)
Inductive fp_case : Type :=
| FPusage (argv0 : Z) (s : list byte)       (* [comment removed for export] *)
| FPcannot_open (path : Z) (s : list byte)  (* [comment removed for export] *)
| FPread_error (path : Z) (s : list byte)   (* [comment removed for export] *)
| FPtoo_big.                                (* [comment removed for export] *)

Definition fp_fmt (c : fp_case) : Z :=
  match c with FPusage _ _ => FMT_usage | FPcannot_open _ _ => FMT_cannot_open
             | FPread_error _ _ => FMT_read_error | FPtoo_big => FMT_too_big end.
Definition fp_arg (c : fp_case) : Z :=
  match c with FPusage a _ | FPcannot_open a _ | FPread_error a _ => a | FPtoo_big => 67108864 end.
(* [comment removed for export] *)
Definition fp_str (c : fp_case) : option (Z * list byte) :=
  match c with FPusage a s | FPcannot_open a s | FPread_error a s => Some (a, s) | FPtoo_big => None end.
(* [comment removed for export] *)
Definition fp_msg (c : fp_case) : list Z :=
  match c with
  | FPusage _ s => msg_usage (map bv_unsigned s)
  | FPcannot_open _ s => msg_cannot_open (map bv_unsigned s)
  | FPread_error _ s => msg_read_error (map bv_unsigned s)
  | FPtoo_big => msg_too_big
  end.

(* [comment removed for export] *)
Definition so_lines (k : nat) : stdout_st := mkStdout true (zeros_out k) false false.

(* [comment removed for export] *)
Definition io_ssp (m : mem) : Prop :=
  exists g : word, ro_cells asegs m 0x10b838 [C8 (Z_to_bv 64 0x66cf88)] /\ ro_cells asegs m 0x66cf88 [C8 g].

Section IO.
Variable RT : rt_sig.
(* [comment removed for export] *)
Variable OUT_rep : stdout_st -> mem -> Prop.
Variable ERR_rep : mem -> Prop.
(* [comment removed for export] *)
Variable IO_FP : list (Z * Z).

(* [comment removed for export] *)
Definition read_icontract_file : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (fd buf count : Z) p off data (lo : Z),
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
  buf = g_read_stage (* [comment removed for export] *) ->
  3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
  fd_lookup F0 (Z_to_bv 64 fd) = Some (FdFile p off) -> fs_lookup fs0 p = Some data ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  let bs := file_read data off (Z_to_bv 64 count) in
  cps asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                    s10 s11 t3 t4 t5 t6 F fc e_read m)))
    (ASTA RT Σ (PMfd (fd_insert F0 (Z_to_bv 64 fd) (FdFile p (off + len_word bs)%bv)) fs0)
       (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (len_word bs) m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(buf, buf + Z.of_nat (length bs))] m m'
          /\ bytes_at asegs m' buf bs)).

(* [comment removed for export] *)
Definition read_icontract_dir : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (fd buf count : Z) (lo : Z),
  a0 = Z_to_bv 64 fd -> a1 = Z_to_bv 64 buf -> a2 = Z_to_bv 64 count ->
  buf = g_read_stage (* [comment removed for export] *) ->
  3 <= fd < 2^32 -> 0 < count <= 65536 -> 0 < buf -> buf + count <= SEGTOP_A -> checked_dst RT Σ m sp buf count ->
  fd_lookup F0 (Z_to_bv 64 fd) = Some FdDir ->
  (forall i, 0 <= i < 4 -> client_static (errno_cell tp + i)) ->
  tp = Z_to_bv 64 0x64cf48 -> (exists v, rw_cells asegs m (errno_cell tp) [C4 v]) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                    s10 s11 t3 t4 t5 t6 F fc e_read m)))
    (ASTA RT Σ (PMfd F0 fs0)
       (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (-1)) m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(errno_cell tp, errno_cell tp + 4)] m m')).

(* [comment removed for export] *)
Definition fprintf_stderr_icontract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (c : fp_case) (errp : Z) (lo : Z),
  a0 = Z_to_bv 64 errp -> a1 = Z_to_bv 64 (fp_fmt c) -> a2 = Z_to_bv 64 (fp_arg c) ->
  errp = STDERR_FILE ->
  (forall a s, fp_str c = Some (a, s) -> bytes_at asegs m a (s ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) s
       /\ Z.of_nat (length s) < 131072 /\ checked_src RT Σ m sp lo a (Z.of_nat (length s) + 1)
       (* [comment removed for export] *)
       /\ bv_unsigned sp <= a
       /\ exists slack, bytes_at asegs m (a + Z.of_nat (length s) + 1) slack
            /\ (- (a + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack)
            /\ a + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= USTACK_TOP - 16) ->
  fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  ERR_rep m -> io_ssp m ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_fprintf m)))
    (evw 2 (fp_msg c))
    (ASTA RT Σ (PMfd F0 fs0)
       (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
          /\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m'))).

(* [comment removed for export] *)
Definition fwrite_stderr_icontract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (sa : Z) (s : list byte) (errp : Z) (lo : Z),
  a0 = Z_to_bv 64 sa -> a1 = Z_to_bv 64 (Z.of_nat (length s)) -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 errp ->
  errp = STDERR_FILE -> 0 < Z.of_nat (length s) <= 64 ->
  (sa = 0x22c59 \/ sa = 0x1673a) (* [comment removed for export] *) ->
  bytes_at asegs m sa s -> checked_src RT Σ m sp lo sa (Z.of_nat (length s)) ->
  fd_lookup F0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  ERR_rep m -> io_ssp m ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_fwrite m)))
    (evw 2 (map bv_unsigned s))
    (ASTA RT Σ (PMfd F0 fs0)
       (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
          /\ ERR_rep m' /\ (forall so, OUT_rep so m -> OUT_rep so m'))).

(* [comment removed for export] *)
Definition emit0_out (so : stdout_st) : list Z := if so_first so then [48; 10] else [].
Definition emit0_next (so : stdout_st) : stdout_st :=
  if so_first so then so_lines 0 else mkStdout true (so_buf so ++ [48; 10]) false false.

Definition vprintf_emit0_icontract : Prop :=
  forall (Σ : rts RT) F0 fs0 (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (so : stdout_st) (ap : Z) (lo : Z),
  a0 = Z_to_bv 64 FMT_emit -> a1 = Z_to_bv 64 ap ->
  rw_cells asegs m ap [C8 (Z_to_bv 64 0)] (* [comment removed for export] *) ->
  ap = bv_unsigned sp + 24 (* [comment removed for export] *) ->
  (so = stdout_init \/ exists k, (k < 500)%nat /\ so = so_lines k) ->
  fd_lookup F0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) ->
  OUT_rep so m -> io_ssp m ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cpsE asegs (ASTA RT Σ (PMfd F0 fs0) (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
                                                     s10 s11 t3 t4 t5 t6 F fc e_vprintf m)))
    (evw 1 (emit0_out so))
    (ASTA RT Σ (PMfd F0 fs0)
       (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
          /\ rt_after RT Σ (bv_unsigned sp) lo m m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) IO_FP m m'
          /\ OUT_rep (emit0_next so) m' /\ (ERR_rep m -> ERR_rep m'))).

(* [comment removed for export] *)
Definition FMT_msg_A : Z := 0x22f02.
(* [comment removed for export] *)
Definition msg_text (str1 : list byte) (line : Z) (str2 : list byte) : list Z :=
  concat (PrintfFormats.pieces_msg (map bv_unsigned str1) line (map bv_unsigned str2)).

(* [comment removed for export] *)
Definition vsn_str (Σ : rts RT) (m : mem) (sp : word) (lo D dn S : Z) (str : list byte) : Prop :=
  exists slack : list byte,
    bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str
    /\ (- (S + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack)
    /\ 0 < S /\ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo
    /\ checked_src RT Σ m sp lo S (Z.of_nat (length str) + 1)
    /\ (D + dn <= S \/ S + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= D).

(* [comment removed for export] *)
Definition vsnprintf_msg_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (D n ap S1 S2 line : Z) (str1 str2 junk : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 FMT_msg_A -> a3 = Z_to_bv 64 ap ->
  rw_cells asegs m ap [C8 (Z_to_bv 64 S1); C8 (Z_to_bv 64 line); C8 (Z_to_bv 64 S2)] (* [comment removed for export] *) ->
  bv_unsigned sp <= ap -> ap + 24 <= USTACK_TOP ->
  let o := msg_text str1 line str2 in
  vsn_str Σ m sp lo D (zlength o + 1) S1 str1 -> vsn_str Σ m sp lo D (zlength o + 1) S2 str2 -> 0 <= line < 2^64 ->
  zlength o <= 80 -> zlength o < n -> n < 2^31 ->
  rw_cells asegs m D [CB (Z.to_nat (zlength o + 1)) junk] -> checked_dst RT Σ m sp D (zlength o + 1) ->
  (D + zlength o + 1 <= lo \/ bv_unsigned sp <= D) -> SEGTOP_A <= D -> (D + zlength o + 1 <= ap \/ ap + 24 <= D) ->
  io_ssp m -> ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_vsnprintf m)))
    (icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (zlength o)) lo D (zlength o + 1) m
               (fun m' => bytes_at asegs m' D (map (Z_to_bv 8) o ++ [Z_to_bv 8 0]))).

Record io_contracts : Prop := mkIOC {
  ioc_read_file : read_icontract_file;
  ioc_read_dir : read_icontract_dir;
  ioc_fprintf : fprintf_stderr_icontract;
  ioc_fwrite : fwrite_stderr_icontract;
  ioc_vprintf : vprintf_emit0_icontract
}.

End IO.
