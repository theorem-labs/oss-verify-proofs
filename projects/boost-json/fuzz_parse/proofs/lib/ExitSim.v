(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit OmniEquivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run OmniRun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SimInv.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_ExitSim () := KReplay.lz_vm "##c3C47Corelib7Classes?Relation!s6&;reflexivityC4ELinuxProcessSemantics?!s<22Fs4path!t+,4Init5Logic6eq_ind!sB88eq_trans!sD87f_equal!sa<ind_rC46Stdlib5Lists4!s+#8nil_co!s~#!u8L2F!tT39Datatypes3app!sq;5Riscv7Prelude5bvmap!tEK5State7PipeBufI!s\KMonad7outcome00!t<Q8in_sysnoc79OSSVerify6Proofs:boost_json:fuzz_parse3!yE#ExitSim:is_exit_noC13~~~K!yh,Numbers7BinNums8positive02!sK=1N02C45stdpp9bitvector;defini!zU#s;bv_unsigned!t;G1!t;>Z02I!yc72eq!veOpecs<syscall_spec!wHQ6in_argC6!s[I3Sys6Kernel4!wL#9!wF$!tE%!uB63iffC5!t%M8Dispatch:lookup_arm!sfX7sa!v'Q!{,$9unmodeledI!vcP<S!wF%Input00!scQ5M!tA#!s\S=!tA&Effec!tB$!ya7or!s@/!zA60!{+G3K!#4:;nat01I!sE;6op!|E#00I!x2X!{B#Arm00!xqO!wR'Table:!xr#_t!s1#!#9dD=iff_R!#9h%e!~gA7Z_to_bvI!sL@2bv!w`4!v<,4list!sF?prod!wh/!sf81K!yN_1!u]A6bv_and!#3YP;with_halted!#7~WA!#4}-!#80#!#8,&!#:2W1!#6e9x!|D:3an!w=5!#7B+1K!s[<1K!t8;1!#5u75proj2!xo=unit!xo?!sF$!#9Z@1!#3]P7MemCopy!zU>!~R$!#5:Revent00!u|=1!#Aq69app_nil_l!xiZ2!t?89False!#D7;3not!y/85!s^$!yL:4True!yM:!sB%1!|UK>!#CL#!sE+6ms_gpr!w8K<MemImageType7Segm!wA$I!tKY=machine_s!x6#!#CfR9m_vm_lazy!{'<!#8r&2!toZ>!to'result!tpM!sn24step!y}K3Run6config!|pM!s[#5s!t5#!ts\>ms_svc_pendingC!tHN?mi_account_!uaS7!sW#_to!#9cL!wkB2!snj3!uxOG!ux2_no!zY&!tZh1!#LiQm!#;i%!|$D1!u[O9sys_input!t]QG!#<b&e!#>W#!vG#esses!slQJmaterialize_!#Gq#!soT!u;#<apply!tY&!#Tw;sym!w9Tkille!#@^Q4m_fs!#BDP!#;6%3!s\X4!#>/<!#D@#!x~P@advance_past_svc!#D}A2!#4|N!#5Y&0I!#3SV0!#41W2!#E%WB!#Vg&_!|-,!#E&#!stXD!#RT#d!#Kn%_ok_inv!sv%!yqQD!~c'_!#GZ,C8!taN3Lib2Nd:and_elimF3!uN^A!#Uc$0!vC3!uKT!|u%_!#J#bJ!w-1no_!#TO'!tgQ!#5p#cfg!#4B$!zlO4star00".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12eq01Zhfbbv_unsignedk12ork13iff3h5LinuxProcessSemanticsfLinuxProcessSem5Monadn67outcome3h5LinuxProcessSemanticsfLinuxProcessSem5Specsqecsyscall_spec3h5LinuxProcessSemanticsfLinuxProcessSem5Stateub5ModelubdSyscallEffectubcSyscallInputub6in_argub8in_sysno5h5LinuxProcessSemanticsfLinuxProcessSem3Sys6Kernel4Exithl49exit_spec69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7ExitSim~~~~~~hp9ais_exit_no37Corelib4Init9Datatypeshu13nilhu14prodhf7Z_to_bvhu14listhu13natn62Okub7MemCopyub5eventub9mkEffectUubbwith_haltedhf6bv_andk13andk13notn69Unmodeled3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypein37Segment3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsir3dmachine_stateir36ms_gpr3h5LinuxProcessSemanticsfLinuxProcessSem3Runjg59sys_inputjg55mkCfgjg57step_tohu14Nonehu16optionir39MachineOkir3emachine_resultir3ems_svc_pendingir34stepjg55SNextjg55sstepub9m_vm_lazyhu14Somehu14consub6ExitEvub4m_fsub8m_haltedjg56configjg59cfg_modeljg54star" s.   (* [comment removed for export] *)

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition is_exit_no : ltac2:(zQ "20!h9!jc>2no@1$1@1$0#k0P") := ltac2:(zQ "60!h9!l5!la!ld!mb!jc\2no@1$5@1$0#k0@2$4@3$1$2@2$3@1$0#k0^1+ld@3$1$2@2$3@1$0#k0^1+le").

Lemma syscall_spec_exit : ltac2:(zQ "a0!n0!q4!tc!hh9!hi1!hj1!hk0!hk9!hoc!ht3>1i$5>1m$3>1o@1$1$4>0@1$9@1$7^3@2$0@3$2^4^3^2@4$8@2$6^4N0^4^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_ExitSim ()) [] "##0:p'0h01Eh11Hh21ih31mh41oh51zi001ai011xp;1p;2p;3p;4p;6p-1g0000R0p4p710p9p1000^p4p70R1p1001N!sA%R2p8P!s8%j!s8&3!s8'2Hp4p7210R4p8P1g002eR1!sL&5p8p1003C!s6&6P!s8'`!t5%7P2p8P7P6!s+$3!s+$4!s+$5p8P7p1004!tS&!s_%4k!t='!sa'!s[2p1005W!t+1!sI2g006Mj1ATg007Ej13Tg008<j1;Tg009Bj10!s/$gj1@Tg00:Ej27!s/$oj11Tg00;Tj19Tg00<2j32!s/$Lj38Tg00=Gj24Tg00><j46Tg00?>R5j25!s1$Wj2?Tg00@Wj4>Tg00ATj4=TP0j4<TP1j6:Tg00BLg00CIg00D?R1#Af2R0#3#;g00E=g00EWR7g00F5#0R4#0!s$+@R3f3R2#3'7R6%14#1#1!sG$1#9R832%14#0#9R49276f4R6?820g00FZR9,46P6P2P0C6'5f0R0%36,73R:=278P7P8g00G9g00G[p-0R8g00HZ/?0P0f7f6R;f5R<C>P1P;P<P6C=n1011010002!s,%014;9!sD&6'5X57R;P8P5g00I^14<9P<P6P2C6R9C<R5%3<,73R3P0E:A8<62/59R9eW0P0O1A27:4P7P4P;P5P!sJ$P!sB'n20!t>%!tH$0!s3&W1W4W3W2o"). Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok : ltac2:(zQ "h42!h9!jc!hv9!ig0!ig8!ih2!iha!ii1!tc!ii6!hh9!hi1!hj1!ij0!hk0!hk9!ij8!ik4!ht3!il2&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1i$c>1m$a>0@1$h2@1$f^2@3$8^3^2@4$7$b@6$h0@2$4@1$0#k0Z@1$2@2$3@1$1@1$0#k0@1$5@1$1@1$0#8~1~1@1$2$9@1$2@2$3@1$1@1$0#k0$6@2$h1@3$h3@1$0#k0@2$e^3N0@2$4@1$0#k0+vf^2@1$2$d").
Proof.
ltac2:(KReplay.run1z (kr_t_ExitSim ()) [] "##1@h04evs2h14evs1h22m1h33Hnoh41ih51mh61xp;1p;2p;6p;3p;4g007Ej1NTg008<j1MTg009Bj16!s/$gj1@Tg00JNj2HTg00K4j1E!s/$Wj1DTg00L7j2=!s/$Wj19Tg00M7j6KTg00=Gj27Tg00:oj14Tg00;Tj1ITg00N5j3:!s/$Zj28Tg00<Lj3GTg00><j4FTg00OTj4LTg006Mj1CTg00Paj4>Tg004Nj3?!s\$2j35Tg00QYj23Tg00R3j2B!s/$Nj2<!s/$hj4ATg00SCj4;!s/$]j4JTg00D?R0f2R1f1R2f0R3C>p=0g00T8R4g00TXR5P2P!s=$2f3R6?512/B3p=1g00BLg00CIR7%N2#Mg00F5R8#6#6#6R9!s-%#@R:g00U8'H%E:R;%@9#E#D'=#91=;;#9R9P9g00UV#9g00VN,=;#9EKR;g00FZR9,71R<%48#4!s$-I,H:R85::/82R=g00VmR>#9R?30R@9G121769RAP6P1A::A8/81RA=0;?RBCF[P<P1P2P@CFR<AG61B[!s6%P3CLP4%D>RC%C4RDP4P6P1P2C>f6/79=::8f5RE'8RF/2?%C0R0A0;F3A0;1?RFA?>2395C?RGC1C1X0C,3CX1C'3X27,37X64RHP5P7PD121217E!sy%4!sy$1/2?P0A0;13PFP!sh1,3CX27P=PCPD!s]'/86R6/22126!s^%63A0;6?!sa2P?!s[$2A?RGPG!sO$A3PBA?>?!tz$!sS&P?12=?R==5D=A50@@R3A?>??R>!uG$?'B1<D=P3P?1<0@1<C>CACAC;!s$%134HeP<eCJW3W5W4o"). Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_ok_inv : ltac2:(zQ "h62!h9!jc!hv9!ig0!ih2!l5!hh9!hi1!ij0!ilb!ig8!iha!ii1!tc!ii6!hj1!hk0!hk9!ij8!ik4!ht3!il2&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0>1i$f>1m$6>3eff$7>2m'$6>3evs@1$4$8>0@1$h4@1$h1^5>0@3$d^6^5@4$c$7^4^3^2@2$9@3$5$7^5@6$h2@2$a@1$0#k0Z@1$2@2$3@1$1@1$0#k0@1$4@1$1@1$0#8~1~1@1$2$e@1$2@2$3@1$1@1$0#k0$b@2$9@3$5$6^4@2$h3@3$h5@1$0#k0@2$h0^7N0@2$a@1$0#k0+vf^6@3$5@1$4$8^3@1$2$8").
Proof.
ltac2:(KReplay.run1z (kr_t_ExitSim ()) [] "##JXp'0h04evs2h12H3h21eh31Hh42H0h52H1h62H2h74evs1h82H4h91lh:1mi001mh;2m1h<2H5h=5Hspech>3evsi013evsh?1oi021oh@1xi031xhA2x2hB2H6hC3HnohD3effhE1ihF2m'hG1shH1uhI2x0hJ2x1p;1p;3p;4p;2p;6g00KWj1WTg007Ej1`Tg008<j1[Tg00<Lj3NTg00><j4STg00OTj4ZTg00Wcj4YTg006MR0j1RTg009Bj1@!s/$gj1OTg00:oj1>Tg00;Tj1^Tg00JNj2VTg00LWj1BTg00K4j1T!s8$7j2KTg00M7j6\!tN$2R1j30Tg00QYR2j24Tg002Hj6ATg00R3R3j27!s1$Nj2C!s/$hj4XTg00X>j2_!sU$ej68Tg00Paj4=Tg00=Gj2ETg00N5j3I!s/$Zj2MTg004Nj3]Tg00D?R4f2R5f1R6f0R7C=p=1g00FZR8,E7p=Ug00T8R9P5P6P!sE$5P9g00TXR:f4R;f3R</E8;I5/M!sG&9g00VmR=?]67p=3f6R>f5R?;0;A0<56/77'7p=;1E58=I<6/M7p=2A04>?g00CIR@?0;<A0567'!sP$:P9P:!tL'?P9P<P5P6C==0;7p=HP4P;P<P5C==0?6/77p=QP4!sK1GA0@67p=6A0467p=D!t,$,7<,7;p=<1767,75p=PA097:p=F1E68=I57p=J1M6790@5p=Lg00BL%W=R8%`;#[A1<569N?;A1;<5RA9N>?f7RB#UPBP>A1?;<RCCS[%U>P>P?PACSRDANB>C[!s6%P6CZP7CYPDP2P9%R9RDA5<56RAg00F5RC#@#@#@RE!s-%#ORFf;RG%>C#>!s$-^,VFRCf:RH%B=RID9%R4RJf9RKf8RL;17g00U8,VF%TFRM%OE#T#W'K#B1KMM#BREPEg00UV#Bg00VN,KM#BE\RM?15IRE1367RN908BF;X08,48X7!s+$;@,4@X@9P>PMP?PFPLPCPBC2P8P;PIF:P7PDPAPFf=RAPCf<ROPID9PJA1GH7PEA08KN!sy7P2P@PDA5;56PFf>RPPCPA!sa'OG!sa%H!sa5PHPMPKPFPOPCPG!tV$L!tV'A5>!st$@RQPCf?RRC2RS/?IPJA1PA!sy%O!sy2P2P8PDA5B<6PFfAREPCPQ!tV'RP7A1M<IA08A!s^/PPPMPAPSP8PO!tK,K?6PFfCRSPCfBRP!sk'EQ7A1M?IA08R!sk+!tE'H>5PFfDR2PCPSC2RN!t}'E7A1M>I1357908Q!s^$!tE$EPNP8PQ!tE,OL;PFfFRNPCfER>!tE'2S7A1MLI13;7908PF;P3!wq$KP?PFfGR<PCPNPID9DHPJP>P2P6A1MKI13?6908SEQPNPMP>PFfHRTPCP<!w4$2!xd+RPGPBPFfIRUPCPT!sq+TP<P;A1MOI13L;908NEQP3PJPUPTP?A1MAIDG13K?908<fJR<PMPUPFfLR?PCfKR3!t6$T!t6&JP3P<PBA1MR!s]$OL908<P1PJfMRL?1?KRKA1MSIRR90J6fPRBPMfORNPFfRR;PCfQRVC2P8fNRWPIF:[!u^$EIRE90JKPJPWPLPHA1MPIRHDGPJP8P0P4P8P7P7POn10110200023010310010100X2JA1NWGPRP7EAA08GIPJP@!sa$@P7P6PB!sa@BNOA1M2IP6EA16N2PJP4!sc$4P7P5P;!sc@VBA!y5$P5EA1DVM1D;MP7fSR>/DMP4PMfTRA/6UROA08PIRPP5PMfVRRPFfYRKPCfX!v1$URX!v1$[XG416>TP7POP@P<A08SIRS1DMMROPFfZRYPCPKC2RK,66P8PRPID<[X:@P7!{m$IPOPFf[RSPCPYC2RY,6LRZP8fWR[PID<X98P813T2A087IR\9POZX>8!s`&ZP813U7!sO$A8P1!}G$?TRTPFf\R1!|&&S/?IRZ90D6!t;$]R]PCP1C2R1,6NR^P8133I!tf$PQ1?KIRK90DTPDPVPLPU1?YIRYDHPD!xN$9!xN&3!w-=DA5;W<PZ!xN&<IPD!xN$9!xNEDA5>N31?1!xM$P^PDP9!s`$9!xK$X!s`@AB?PFf^PCP]!~'$5EA%FA%FXP7%FRP9P:fbR:=JFCfaR55LAR]A08VIR?POfdR0!s@$cR^5LRP813;!v2%[XH9AJF5Cf`5L>P7P]P@PFP^PCP:C2A08;IR;!vw$eR:PCP0C2R0!x[$13>I!x]-;!x]+f!sb%R:/6:R:P8137I!x[+PIAPO:\X98PO1600R:A08IIR\'71C4MP:P\1C@01C8ICXCX13II1_=IE8P>P7E8b8X1?PX!s1$1W6P[!s0$6W5P7O1b!s+0W4P7O1W4n2002!vt%!vl$1A0D7YPO16WSP813<!u<&?DPKO1P71CDYO1b4P2P6E8PRPGE8P2!t6$BX<P!tK&<W8PA!t`%W1!t?$!s+0W6!tK$6!tK6J7HPNPMPWPFPV!#;|'L!}#$X?JPE!tS%JHO1b6W5W4P6P7O2n20010!s#$12!s/&W4W3!sD>3XA8!sE7103!sE%J!sEAI@!sE@@9!sE=b=W=WCW>XF@XD4X:@WEo"). Qed.

(* [comment removed for export] *)
Lemma exit_dispatch_no_unmodeled : ltac2:(zQ "80!im1!im7!tc!hh9!hi1!hj1!hk9!ht3>1i$5>1m$3>0@1$7@1$6^2@1$0@3$2^3^2@1$1$4").
Proof.
ltac2:(KReplay.run1z (kr_t_ExitSim ()) [] "##?$p'0h01Hh14evs1h21eh32m1h42H0h52H2h61xi001xh72H1h82H3h92H4h:5Hspech;1mi011mh<2x0h=2H5h>3Hnoh?1ih@1lhA1oi021ohB1uhC2x1i033evsp;1p;3p;4p;2p;6p;7g007Ej1YTg008<j1XTg00X\j1GTg00<Lj3?Tg00><j4JTg00OTj4UTg00Wcj4STg006MR0j1FTg009Bj17!s/$gj1DTg00:oj16Tg00;Tj1MTg00JNj2KTg00LWj1:Tg00KWj1I!s/$4j1H!sA$7j2CTg00M7j6T!tW$2R1j30Tg00QYR2j21Tg001Nj6ETg00YTj2RTg002Hj6A!s/$ej7Oj6BTg00RNj2NTg00Z3j1QTg00=Gj2>Tg00N5j3<!s/$Zj2;Tg00Paj48!s\$3R3j2WTf0R4g00FZR5'>p=Lf3R6f2R7f1R83</;4p=Vg00T8R9g00TXR:P8P4C89067p==P9P7!s7%p=2g00D?R;!s8,4f7R<f6R=P9P:f5R>f4R?/>5;<6/;7P8C830/W4p=51>75=<68!t?$3P9P:1>65=<?7/;!ss&9P9P!tK&p=PA094:p=@g00BLg00CIR5%Y8#X%G;R@9?78RAA?67@%L?RBP?P6P@CJ[%L6P6P7P@CJRCA??6@[!s6%P8CUP4CSPCg00E=%F9RC%G9RDg00F5RE#7#7#7RF!s-%#DRGPB%6E#6!s$-M,KGREP6CVg00VmRB#:RHC=%IBRBPCA2784RIPGP<PEP=PH%F;RJg00U8,KG%HGRK%DF#H#I'C#:1CKK#:RFPFg00UV#:g00VN,CK#:ETRK?48H70@RFG5X1B'1X35,15X69,19g00ZLRLP4PCPDPGP>PEP?C3PHC=!s8$0P9p-0RDP4PLg00ZiRMn101102000230100!s5$300X2Cg00[ERNPGP=PEP>PHD9P4EEPL1RL4ROb4W0P4O1PCPIPGf8RPPEP<PHP!th%,1B!ti/P2P9!sP&9RQPEPP!sP8P!u3%IPGf;RIPEf:RR!sO5P2P5PCA2684PGf<RSPEPI!sM2!sp%A2>!sJ$>RTPEf=RU!sL/P2P!wd$=74PGf?R2PEPTPHA4K7H90J@!sN$!sn'P?4PGfARFPEf@RV!sM$?!sM&P3PCA2Q>8PGfBR3PEPF!w<%A4K>!sJ$!sl'I<6PGfDR?PEfCRW!sL+P!sL%1PCA2UQ>R>PGfHR1PEfGRXPHD9RY90C8PL[P8PGfFRZPEfE!s?$[90C>A2TR=PGPXPEPZ!s=$Z50CPCPBP0P9PBP4P4PP!x[>A22I<PYP4EAA0B<HPCP5!sa$5P4P8PU!sa@VSPPGfI!xp$1C3R1/PHP8EAA05S1PCP9!sp$9P4P7P3!sp@FUQPGfJ!y6%D9P7EA%@F%@3P4%@W!~f$GfNR:PEfMRWC3905FRFA0BTHRTPL[[XB9PGPWPEfL!sD$VP4PFP5PGfOPEP:C3A0B2HR2PL[X;5P4!xr$HPLX@B!sL$QR2PEfPC3R:A4K4!x'&]4X<5A4K:!s6%JP@P0P;P!|W$P!|R>JPNPGfRPEP2C3=4KH!|O%POb0W4P?P6PIFOPVP4EBb=X9TP3!s1$9W8P?!s0$8W5P4O1b!s+0W7P4O1W7n2002!tG%0!tD$A0C4ZPL[XACP[O1P41NCZO1b7W4W0P8P4O2n2001!sW&2!s/&W0XCB!sE71!sE'<5!sE@69!sE?P4O1!s@-!tD%!sD$b:W:%QAeW>W;W?o"). Qed.

(* [comment removed for export] *)
Lemma in_arg0_sys_input : ltac2:(zQ "90!h9!jc!ih2!l5!iq8!iua!ivb!jj1!hk0>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@2$8@3$7^3^2^1N0@2$6^2N0").
Proof.
ltac2:(KReplay.run1z (kr_t_ExitSim ()) [] "##$Rh02msh14segsh22x8p;1p;2g00KWj15Tg009Bj10!s/$gj12Tg00K4j11Tg00[aj24Tg00RNj23Tg00\_#5g00]^g00F5#0!s$-2#1R0f1g00FZ'4,30W2W0W1o"). Qed.

(* [comment removed for export] *)
Lemma in_sysno_sys_input : ltac2:(zQ "80!h9!jc!ih2!l5!iq8!iua!jj1!hk9>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@1$7@3$6^3^2^1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_ExitSim ()) [] "##$Bh02msh14segsh22x8p;1p;2g00KWj14Tg009Bj10!s/$gj12Tg00K4j11Tg00RNj23Tg00\_#4g00]^g00F5#0!s$-2#1R0f0,30W2W0W1o"). Qed.

Section WithSegs.
Variable segs : ltac2:(zQ "20!ih2!iq8@1$0$1").
Variable code : word.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive to_exit : machine_state -> Prop :=
| te_here : forall ms x8,
    ms_svc_pending ms = Some x8 ->
    is_exit_no x8 ->
    ms_gpr ms 0 = code ->
    to_exit ms
| te_step : forall ms ms',
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_exit ms' ->
    to_exit ms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma sstep_instr_inv : forall ms model ms' evs st,
  m_vm_lazy model = [] ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [] /\ st = SNext (mkCfg ms' model).
Proof.
  intros ms model ms' evs st Hlazy Hsvc Hstep Hss.
  inversion Hss; subst.
  - (* sstep_instr *)
    match goal with H : mi_account_step segs ms model = MachineOk _ |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; inversion H; subst end.
    split; reflexivity.
  - (* sstep_instr_fault *)
    match goal with H : mi_account_step segs ms model = MachineFault |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_instr_unmodeled *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_call: its first premise is the same [MachineUnmodeled] *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_materialization_fault *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_vdso_unmodeled *)
    match goal with H : mi_account_step segs ms model = MachineUnmodeled |- _ =>
      rewrite (mi_account_step_no_lazy segs ms model Hlazy) in H;
      rewrite Hstep in H; discriminate end.
  - (* sstep_syscall *) congruence.
  - (* sstep_syscall_materialization_fault *) congruence.
  - (* sstep_exit *) congruence.
  - (* sstep_killed *) congruence.
  - (* sstep_syscall_unmodeled *) congruence.
Qed.

(* [comment removed for export] *)
Lemma sstep_exit_inv : forall ms model x8 evs st,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  sstep segs (mkCfg ms model) evs st ->
  evs = [ExitEv (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)] /\
  st = SNext (mkCfg ms (with_halted (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) model)).
Proof.
  intros ms model x8 evs st Hh Hsvc Hx8 Hss.
  inversion Hss; subst; try congruence.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = None |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    autorewrite with model in *.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' ?evs0),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_halted ?model' = Some ?code |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (Heff & Hm & Hevs);
      rewrite in_arg0_sys_input in Hm;
      subst evs0 model';
      assert (Hcode : code = bv_and (ms_gpr ms 0) (Z_to_bv 64 255))
        by (autorewrite with model in H6; congruence);
      subst code
    end.
    cbn. split; reflexivity.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model (Ok _ ?model' _),
      H2 : ms_svc_pending ms = Some ?x,
      H6 : m_killed ?model' = Some _ |- _ =>
      assert (Hxe : is_exit_no (in_sysno (sys_input segs ms x)))
        by (rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8);
      apply (exit_dispatch_ok_inv _ _ _ _ _ Hxe) in H3;
      destruct H3 as (_ & Hm & _); rewrite Hm in H6;
      autorewrite with model in H6; discriminate
    end.
  - (* [comment removed for export] *)
    exfalso.
    match goal with
    | H3 : syscall_spec (sys_input segs ms ?x) model Unmodeled,
      H2 : ms_svc_pending ms = Some ?x |- _ =>
      eapply exit_dispatch_no_unmodeled; [| exact H3];
      rewrite in_sysno_sys_input; replace x with x8 by congruence; exact Hx8
    end.
Qed.

(* [comment removed for export] *)
Lemma star_halted_nil : forall c tr c',
  m_halted (cfg_model c) <> None -> star segs c tr c' -> tr = [] /\ c' = c.
Proof.
  intros c tr c' Hh Hstar. inversion Hstar as [|c1 evs c2 tr2 c3 Hss Hstar2]; subst.
  - split; reflexivity.
  - exfalso. destruct c as [ms model]. cbn in Hh.
    inversion Hss; subst; cbn in Hh; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
