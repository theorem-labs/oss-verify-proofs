(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FMapPositive.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel LazyRestrict LazyLedger LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require LazyMadvise.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocBudget AllocRep AllocRepFacts AllocRepX
     AW_Efs AW_Populate AG_WFHit AG_RefillModel AS_Refill1 SecLazy.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AG_Refill3 () := KReplay.lz_vm "#${GK47Corelib7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!sg+4Init9Datatypes4prod!sF?list00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib:LazyLedger>entries_nowrapC13~~~C56Stdlib6ZArith6BinInt1Z2le!t7P<!t7#Restrict:in_rangesb!t5&4ELinuxProcessSemantics?!s<25State=maps_subtractC!vq@;bv_unsigned!v8[5zcov!tx'!sjZ4zin!uc+!x/;negb!sD=andbK!sD15Logic2eq01C!s@78eq_ind_r!u,[@!wp,_!u|/!t;76!t;%!t9[C!t-$_!xJ1!t<$I!uk;!{r>bool00K!sFA2!~0G3I!~0=Z!t1/!sD61!|N>t!uM83and00!s]<3leb!sC>t!sC=8leb_spec!vR<8BoolSpec!tN>8lt!sl%K!#44@1K4!sh&9micromega6VarMap1t!w>#!sD>3I!sD?0!sD6=RingM!s4'7Formula!wb#!sQ47Env!sT#5PExpr!xpI!uC7!tA:1!v6<6option02C!ss55Tauto8B!sl&!sH6:Z!t:+=Z!sT$CheckerC!vJ<4f!}C#!sq@C!sq0_sound!wa@!v$7!u3&G!uy'4!sJF3!sJF5!sJF8!vk<5eKind!~~=unit!y78!se%4kind!x<>!sf%1!#3fA1I!wE@;!|k%!#5z#!tZ8!y{13Op2!vX8!sM65!#7H79False_!v75!sE%5!sE$!#6T3!sC%4True!#6P3!sB/1!#7N8or!w->!x9,6C8!#9-M2As8AllocRep9placed_ok!#:;%!so[4a_st!sjY7!sj$Wf2WF!#;h=5proj1!sA=2!tES>AG_RefillModel<rf_mfa_delta!#@>U>Asan!u@$!su$:get_region!sse<rg_num_freed!sueDrg_mapped!sx$_array!s}eArg_a!s4#ated_user!sze>!ty,!sw-!xXR:AS!xX&17!xT%'!{Tf!#CU%!#@R?2!#?V<add!tMUsShadow5aceil!u:ep!{O'!tt;6modulo!tw\4aapp!tvb5a_thr!skdkobj!tXectx!skefsb!|$e6as_sec!#60&!x/&5Lists4!s+#2In!#4o_sc!}0#_beg!t{e;!ss&size!z1B3mul!{:]dis!xT'!#J@7not!zG`o!#U2B3pow!t0_bot!ywb2RB!shcFA!u\Csu!#Ma=div!#7I]4rf_n!u8Y!sl-6!sl#f1!zye=rg!#;l4!tfafl!tff4zle!vEe7!vE#new!uNhau'!uNe:class!#30-!tcam!tc+!zn<eqb!t3^8rf_tota!#<~%!#S>D1!t;S!#GG&9WF!#E%/I!sn[!sk%_ok00!w&Y!sp'?ro!#Cy$_nonn!#8x'!stZ;!st+le!spa=ro!#De&mod!sra8ro_fa!tad9!sm%!t]d!vC#num!#J%i<as_space!#=~h:!yp&b!xy[!#9z$Kit=!sp,_eq!the?!#7j+_base!tmbB!su2!trY8HeapCeil5h!#IG^!#H;%2sh!shb;!#Jv#_facts!sqY9!v?$RepX@sh_!st#ing!#i|$!sw%!#XR7!#f7#!#fn<7div!|G$!sG;=mod_pos_boun!sMBneg!sM25!#7K#8PreO!s/#1Z;!t>#0_r_ext!sL>!st#!sL3!u14compare!#P4?3!#9&=3Pol!#^j=3na!#g98!#]n05Psatz!sOM7!sOK5!#;5D4!#qL;6length!v[34Znat5Nat2Z9is!#9P&!#QY;of_nat!#cS59SatDivModCZ_!xi$!sp$!sw'!sWB!xr#!sW1!tP;>pow!z<$!sNB:!sN#!sJ%!vTE7!}0P3Lib2Nd;and_elimF15!}vV!sl&:!sl+4!}j'!x{I4!sOK6K!#fZL2!sRN3!#phA2!#dzE7!wbE!{[F3!u+N!#p1D!#he#1!#`&_kFreeArrayMapS!#H'[!#8y'6AHI_LO!#>qekSpace!ta-!ss^9kPag!srj@kPtr!vP$Reserv!#>q_Rep8AFS_SIZE!sn%I!#[B^schun!#I4+!#D/^kUser!y&1!su^>!y~,!swi;kNumClasses!xBg!tm+Offse!$%[8!#3=+:!#=U$ison!$%G=!#<s#1!y/\6AMODEL!#BOb7akernel!snd!t]%X!{Ub?a!$,d#in_l!$,y$!sucs!#3~#_visibl!}Cc7ABUDGET!yie7as!$0F#!spfmp_kin!#O<%K!sp^5m!#|q#3!spl4!uTi!#N7,!$9/?7Z_to_bv!t>c!#\3+!#>W<!$=o#1!$;KP8m_vm!xc$!s]P7vm!yA$!$6R9x00!svQ;vm_noac!s;#!{p\3a_L!xLV!$93,9nooverl!$@F'!u;Tr!#<O$d!#JH;3fst!sC=snd!x-Rvm_limit!s]Q9!#]3$top!w4\4a_Z!#5aV3Lib4TacX2wz!#8/b4hcnt!ske!#t'+!sk^!#i:[6SecGap4zsum!#8Za3a_S!zx'!yy;app!|,[D!$B4/!$IX/c!u%R:!$-1'3I!$DK,!t&+fal!#6_&!t%^H!t%7tru!t$eJ!t$7insid!#8e&!#U<;ltb_l!~b>orb!#U$'4Bool!s'$:orb!u1$!$HTQ!$MH/>!u+-!$$]+!t;'!#|`,:in!sG#_iffK!#:X_apping01!#:Z7!$8%+1!s@<!$,N<6eq_d!$E_36Specif7sum!$I3$!|[S!$5c18r!s2$e!#ibY!st2=!st%!$5e0!sya<rfd!sv&_c!z:B;lt_ge_cases!z_>eb_le!z_<?and!zI&intro!$O+;sym!#8hS6M!#:>#<!$Ss&_li!#8/&!{\\:z!{]'b!w8to!tkdeager_us!#ojW!sq0;pages!#wh-!#=s]Phi!sjY;!sj$Budget6pusage!soe;!so%_grow!uQd_AL!|6B!#km#pos!wR^win_n!wW$Z!xFc9cl!#lV$s!spc5cl_lo!slg!y4+!sl\@!zl-_con!uSd?!sw/!$<[[!#CY+D!#rU,lt_!#a\-!#?yrkee!t}W3Lib9LiaTuning9zify_don!#]BV;!vh#MadviseI!#52%!#xg#!$_/5!trT!#l>08!sl]!#l>+6!sk&!#LdO<map!z%#tains!#:U+!#A-$7!s+#Def3map!#O^Q!vN-I!#Adf!#d;%!sr_!#X<%!sp&!#Y-e2!spl6!spl8!xsWBtarget!$0m&!#SBUpage!#Z/#!#io_!yK%!$3}Z5ASegs8AIMG_TOP!~PV!#hl3R!t_$!#p_e9ALOWSH!#pb+!uRX7!uR$!sj[!#TH,AHC0!skfL!skd7ASECMA!#h]&!#N558ni!#;R%!#3M^PROT_RW!wC_<ASHADOW_B!u&#!soX!#D6/B_PRIM!so%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14boolk15false37Corelib4Init5Logicm82eq01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~o4ain_rangesb46Stdlib6ZArith6BinInt1Zt02lek14listk14prod3h5LinuxProcessSemanticsfLinuxProcessSem5Statevbdmaps_subtract69OSSVerify6Proofsaboost_jsonafuzz_parse3libaLazyLedger~~~~~~hj9eentries_nowraphfbbv_unsignedm83andt02ltk14truem82or79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AllocRepX~~~~~~hqd7AMODELX79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~hv76ast_okhv73a_Lhv74a_AL" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma in_rangesb_subtract_false : ltac2:(zQ "c0!h9!jc!l9!m0!nc!o1!s3!u8!ud!v4!hi9!hn6>1x@1$1@1$0#k0>1C@1$8@2$9@1$1@1$0#k0@1$1@1$0#k0>1l$5>1h$5>0@1$b^3>0@2$7Z^3>0@2$7^4^3>0@3$4$2@2$6^7^6$3@3$4$2@2$6^8@3$a^7^6^5$3").
Proof.
ltac2:(KReplay.run1 (kr_t_AG_Refill3 ()) ["HCW"] "h01bh11Ch21Fh32Hhh42Hlh52NWh61hh71lh81xp;1p;2p;3p;6p;7g0000j10Tg000Uj1DTg0013j1=Tg001Vj2;Tg0026j1CTg002Vj1@Tg003cj29Tg004?j21Tg005Jj3<Tg006Fj24Tg0070j28Tg0084j37Tg0097j1:Tg009Uj25Tg00:3j2BTg00:Mj62Tg00:kj26Tg00<:j6?Tg00<Vj7>Tg00=hj3ATg00>BR0f0R1g00>bR23Ap=3g00?B#0#0#0#0#0#0#DR3#=R41;44#Cg00?gR4f2R5#@g00@E/95f3R6/95f6R7f5R8'1#3P0f4R99<78R:f7R;,43R<'8R=%31X00R>P0187<R?A789<#:'5P>P011;7R>f8,439778#:,51#3X00R3P0P2P31B02P>P1E2P?16;7E?P=P7P8P9P<P6P5f1F>E211;:16;:E2W2W3W4W5X64W7W1W8o"). Qed.
Lemma in_rangesb_subtract_inside : ltac2:(zQ "f0!h9!u8!jc!o1!ho8!l9!m0!ud!v4!hp6!nc!hi9!hn6!s3!hpc>1x@1$2@1$0#k0>1C@1$7@2$8@1$2@1$0#k0@1$2@1$0#k0>1l$3>1h$3>0@1$c^3>0@2$1Z^3>0@2$1^4^3>0@2$9@2$1^5@2$4@1$0#k0^7@2$e@2$4@1$0#k0^7^4@3$a$5@2$d^8@3$b^7^6^5$6").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_Refill3 ()) ["HCW"] "##9gp'0h01bi001bh12H0h24__p1h34__p2h44__x1h54__x2h62b0h71Hh87__arithh94__ffh:8__varmaph;5__with<1Ch=2Hhh>2Hlh?2NWh@1RhA1hhB1lhC1xp;1p;2p;3p;4p;7p;6p;8g0000j15Tg000Uj1aTg0013j1R!s/$Vj2LTg0026j1H!s/$Vj1WTg003cj20Tg006Fj22Tg00@cj23Tg00A?j2;Tg005Jj3KTg0070j2FTg0084j3`Tg0097j1C!s/$Uj27!s\$Zj2GTg00B7j29!s/$Tj2UTg00C6R0j3B!s1$Zj2TTg00:3j2ATg00D<j1Q!s/$\j2@Tg00E:j4?!s/$Xj1PTg00F6j1O!s/$aj2<Tg00GDj1N!s/$ij4:Tg00HTj1MTg00I6j2J!s/$Xj2ITg00=hj3=Tg00JDj3S!s/$cj4_Tg00KUj1^Tg00<Vj7]!tg$Mj6DTg004?j2Z!s8$kj2YTg00L3j7X!s/$Wj6[Tg00M;j7\!s/$_j8VTg00>BR1f0R2g00>bR33=p=1f1R4/72#Cp=4P4g00NCR5g00NbR6P6g00OBR7P2g00ObFXp=8P4P5P6P6P7P2E[p=Ef2R8!s9+4P2F\p=>f3R9!s;+8P4P2GVp=6g00?BR5#5R:#5!s$+aR;#RR<1L<<#Hg00?gR<%W8g00@ER=/081098f4R>f6R?,2;R@'013@9';P1f5R@=K?>RAf7RB,2;RC'FRD%12X01REP11F?CRFA`@>C#C'7RGPEPFP1P1f9RF,2;RE,GBRH19E?'4,72#1P2f8RE,2;RI,U?10?I13I?1G?IRJ3BPHP1P0f:RH,2;RK,0E13KEf<RK!ss$/9FRL,44#1P4f;RM,2;RN,0F1TEFRO13EF10FE;BLRLf=,2;/9HRE!sx$>RP,2;RQ/3MRR10MQRQg00PBRM/!su&?RS,2;RT/3KRU1A13RV14MM#1eW1P2O110KTRTp-0RKg00PbRW#QRX%HWRWP<1@<4P81@<8RYC?%P<RZ%O<R[P<1<<:R:g00QNR\%N5,<<R]C:,8[%M6R6P[1E[>R^P<P]g00R5R_P:!sE$5>[P61E[@R:C6C61J[7R7P2P81A1M1I28==1MdAS<=4C_R=b9b:b;X4<X5<X2KW310241384,;9P@[[^4<^5<^2K^3KP2A=1M3R`fA,2;R;,0SP;PPP4PHO6b814M3!um+n200210!s#&!s0%!s'$b6b0W7!v8$3NFPOPLP!w1$PRPQ143!vs$PXPWP<%^<P4PYC?PZP[P<P]P_1<<5R5!u^$P6!s;$5P\P!v6%=>[^P6P!ul$P7P!uP3X3K13421048/!uQ7P`13;PP;PSP@!uF%RH143M#1eX1UP2O1PH1433!s6$T!uYJ!sI31000!s'$b6b019I@,4J,7M#1ePVn!s@%0020100b0%1GePDP?P@P>PCP9P8P4F]ED1ZBA1YBAEDW@W=W>W?XA<WBW<WCo"). Qed.
Lemma in_rangesb_subtract_true : ltac2:(zQ "c0!h9!jc!l9!hq1!nc!o1!s3!u8!ud!v4!hi9!hn6>1x@1$1@1$0#k0>1C@1$8@2$9@1$1@1$0#k0@1$1@1$0#k0>1l$5>1h$5>0@1$b^3>0@2$7Z^3>0@2$7^4^3>0@3$4$2@2$6^7@3$a^6^5^4$3@3$4$2@2$6^8^7$3").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_Refill3 ()) ["HCW"] "##-Yp'0h01Th11bi001bh21Ch31Hh42Hhh52Hlh62NWh71eh81hh91lh:1xp;1p;2p;3p;6p;7g0000j11Tg000Uj1ETg0013j1>!s/$Vj2=Tg0026j1D!s/$Vj1CTg003cj2<Tg005Jj37Tg004?j25Tg006Fj23Tg0070j24Tg00:kj2:Tg00<:j69Tg0084j38Tg0097j16!s/$Uj22!sJ$Vj7B!s\$3j2@Tg00=hj3;Tg00R\j2?!sA$Mj6ATg00>BR0f0R1g00PBR23;p=0g00?B#1!s$-ER3#>R41=44#Dg00?gR4f2R5#Cg00@E/<5f3R6/<5f6R7f5R8f4R9;76'5#0P0f7R:A7789R;'5%01X10R<P1133:,4;R=1::;E9%0=P0A7:78f8R=,33R;'4P<P114:;A878;#6'2R>P:P7P8P;P9P6P5FBE9%0>P0f9R>,33,4=R5P<P5P0P0f;,3398>=#6R5,21#0f1R<#0]0P1f:!sB$=:#6R:,22#01@02W0g00>bR3/2:#0P01235P0p-0P1g00S;R5g00SXn0110000020000X70g00T4P2P1E9P5A;032/?1b3W0!sP1P<O1b115>=1:>=EAb0b0W0W4W5W6X84W9W2W:o"). Qed.
Lemma in_rangesb_subtract_keep : ltac2:(zQ "f0!h9!u8!jc!l9!hq1!nc!o1!s3!ho8!ud!v4!hq8!hi9!hn6!hpc>1x@1$2@1$0#k0>1C@1$9@2$a@1$2@1$0#k0@1$2@1$0#k0>1l$6>1h$6>0@1$d^3>0@2$1Z^3>0@2$1^4^3>0@3$5$3@2$7^7^6$4>0@2$b@2$e@2$8@1$0#k0^8^6@2$1^5@2$8@1$0#k0^8@3$5$3@2$7^9@3$c^8^7^6$4").
Proof.
ltac2:(KReplay.run1z (kr_t_AG_Refill3 ()) ["HCW"] "##8Hp'0h01bi001bh12H0h22b0h31Hh44__p1h54__x1h64__x2h74__x3h81Ch92Hhh:2Hlh;2NWh<1Rh=1Th>7__arithh?4__ffh@8__varmaphA5__withB1hhC1lhD1xp;1p;2p;3p;4p;7p;6p;8g0000j16Tg000Uj1`Tg0013j1W!s/$Vj2KTg0026j1F!s/$Vj1YTg003cj20Tg004?j2;Tg006Fj22Tg00@cj23Tg00TPj2@Tg005Jj3HTg0070j2GTg0084j3DTg0097j14!s/$Uj21Tg00BTj2XTg00AZj2CTg00C6R0j3B!sC$7j2A!s:$Zj2VTg00D<j1T!s/$\j2?Tg00E:j4O!s/$Xj1NTg00F6j1MTg00GDj1L!s8$aj2:!s8$ij49Tg00HTj1J!u+$jj7ITg00LWj6PTg00I6j2QTg00:3j2R!s8$Xj2STg00JDj3_!s/$cj4^Tg00=hj3=!sS$Mj6<!s/$kj2ETg00<:j6]!s/$Vj7Z!t1$3j7[Tg00M_j8\Tg00>BR1f0R2g00PBR33=p=71132==13p=51132p=Uf1R4g00NCR5g00NbR6P6g00OBR7P2g00ObF[p=8f3R8P5P6P6P7f2R9P4P2G\p=>g00?BR:#6R;#6!s$+`R<#WR=1K==#Fg00?gR=%Y9g00@ER>/091089f6R?f5R@';#7f7RA,2<RB/3@f4RC/0B'@P1AHA?@RBf8RD,2<RE'GRF%72X01RGP11GAERHAD?@E#4RI'1PGP11;DARGf9RJ,2<RK9DA?#4,12#7X01RLP1P3PL1X?E10?E13E?1C?E3B1CAKP1P0f:RK,2<RL,0D13LDf<RL,2<RM/AJRN,14#4#5P4f;RO,2<RP,0J1VMJRQ13MJ10JM;BNRNf=,2</AKR!sz%>RM,2<RR/3ORS10ORRR%U!sp'?!sp%T/3LRUp-0RVg00PbRW#T%FWP=1?=9P41?=8CO%N=%M=RWP=%L:,:=RXg00R5RY1:=;R;C9,8W%J6RZPWP=1:=:R:g00QNR[PX!sC$PZPWPW!x8'P=PXPYP:!sA%=P;P!sN'FI!sP$!sN'@EPC>C>C>1QW7P2P91R13RW1S29#7dA_=>4C^b?b@bAX5=X6=X7=W41394104813C9108C'@P?[[[^5=^6=^7=^4V!yz$>bRV==13fA,2<PMPOP4P@PJO7b>1133#4#5eW1P2O110LTRTPW113V!s=-n200210!s#&211000!s5$b2b0W3!s`$3PJPQPNP!wX$PSPR11V!wI&PW11V!t5%X1UP2O1!s8$!t0%X1T!t170!t15!tT@%5IePGP4E<PH1EDAE]PFPAP?P@PEPCP8P9FZE<1;DB1EDBE<W<W=W9W:W;XB=WCW8WDo"). Qed.

Section AmodelAfterRefill.
  Variables (s : ast) (mo mo' : Model) (c : Z) (L' S' : list (word * word)) (AL2 : Z).
  Let st := a_st s.
  Let sb := a_sb s.
  Let r := get_region st c.
  Let nf := rg_num_freed r. Let mfa := rg_mapped_free_array r. Let au := rg_allocated_user r. Let mu := rg_mapped_user r. Let fl := rg_free_array r.
  Let n := rf_n c. Let csz := class_size c.
  Let mu' := rf_mu' c nf au mu. Let nnew := rf_nnew c nf au mu. Let nf1 := rf_nf1 c nf au mu. Let mfa' := rf_mfa' c nf mfa au mu.
  Let au' := rf_au' c nf au mu. Let fl1 := rf_fl1 c nf au mu fl.
  Let st2 := refilled st c.
  Let s2 := mkAst st2 (a_thr s) (a_ctx s) (a_fsb s) L' S' (a_Zr s) AL2 (a_top s) (a_bot s).
  Let h := m_vmmaps mo.
  Let h' := m_vmmaps mo'.

  Hypothesis AMX : ltac2:(zQ "10!huc@3$0?5HCEIL?1s?2mo").
  Hypothesis OK : ltac2:(zQ "10!ij5@2$0?5HCEIL?1s").
  Hypothesis HC : ltac2:(zQ "20!u8!hp6@2$1@2$0+1?1c@2$0?1c+he").
  Hypothesis EMPTY : pc_count (get_pc st c) = 0.
  Hypothesis ROOM : mu + 2 * kUserMapSize <= kFreeArrayOffset.
  Hypothesis LNW : ltac2:(zQ "20!ijf!hn6@1$1@1$0?1s").
  (* [comment removed for export] *)
  Hypothesis EL : L' = (if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s) (FA s c + mfa) (FA s c + mfa')
                       else (if mu <? mu' then maps_subtract (a_L s) (RB s c + mu) (RB s c + mu') else a_L s)).
  Hypothesis ES : S' = (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else [])
                       ++ (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) ++ a_S s.
  Hypothesis VMM : vm_maps h' = vm_maps h.
  Hypothesis VMR : vm_reserved h' = vm_reserved h.
  Hypothesis VML : vm_limit h' = vm_limit h.
  Hypothesis VMB : vm_mmap_base h' = vm_mmap_base h.
  Hypothesis VMT : alloc_top h' = alloc_top h.                 (* [comment removed for export] *)
  Hypothesis VMN : vm_noaccess h' = (if mfa <? mfa' then maps_subtract (if mu <? mu' then maps_subtract (vm_noaccess h) (RB s c + mu) (RB s c + mu') else vm_noaccess h) (FA s c + mfa) (FA s c + mfa')
                                    else (if mu <? mu' then maps_subtract (vm_noaccess h) (RB s c + mu) (RB s c + mu') else vm_noaccess h)).
  Hypothesis EAG : eager_used mo' <= eager_used mo + (mu' - mu) + (mfa' - mfa).
  (* [comment removed for export] *)
  Hypothesis HAL : ltac2:(zQ "30!u8!hp6!ik6@2$1@2$0Z?3AL2@2$0?3AL2@1$2?1s").

  Let PL : placed_ok s. Proof. exact (proj1 OK). Qed.
  Let WFs : WF st. Proof. exact (proj2 OK). Qed.
  Let RF := rf_facts st c WFs HC ROOM.

  Let B : 0x10007fff8000 <= sb /\ sb + 137438953472 + 4096 <= aceil /\ RB s c = sb + c * 4294967296 /\ FA s c = RB s c + 3758096384
          /\ 0 <= au <= mu /\ mu <= mu' <= mu + 262144 /\ mu' + 262144 <= 3758096384 /\ 0 <= mfa /\ mfa <= mfa' <= 536870912 /\ 1 <= c <= 30
          /\ 8 * ((mu' - mu) / 8) = mu' - mu /\ 8 * ((mfa' - mfa) / 8) = mfa' - mfa /\ (RB s c + mu) mod 8 = 0 /\ (FA s c + mfa) mod 8 = 0
          /\ RB s c mod 8 = 0 /\ mu mod 8 = 0 /\ mfa mod 8 = 0 /\ mfa' <= mfa + 262144.
  Proof.
    pose proof (rf_mfa_delta st c WFs HC ROOM) as FD.
    npose PL as (Y1 & Y2 & Y3 & _).
    ndestruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
    pose proof (WF_region st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia)) as RO.
    pose proof (ro_alloc_nonneg _ _ RO) as A1. pose proof (ro_alloc_le _ _ RO) as A2. pose proof (ro_mapped_mod _ _ RO) as A3.
    pose proof (ro_fa_le _ _ RO) as F1. pose proof (ro_fa_mod _ _ RO) as F2. pose proof (ro_numfreed _ _ RO) as F3.
    assert (ERB : RB s c = sb + c * 4294967296) by (unfold RB, sb, a_sb; rewrite region_beg_eq; reflexivity).
    assert (EFA : FA s c = RB s c + 3758096384) by (unfold FA, RB; rewrite free_array_base_eq; reflexivity).
    acb. unfold AHI_LO, kSpaceSize, kPageSize, kUserMapSize, kFreeArrayOffset, kFreeArraySize, kFreeArrayMapSize in *.
    subst n csz nf mfa au mu nf1 mfa' au' mu' r st sb. unfold a_sb in *. unfold zlen in F3.
    set (MU' := rf_mu' _ _ _ _) in *. set (MFA' := rf_mfa' _ _ _ _ _) in *. set (MU := rg_mapped_user _) in *. set (MFA := rg_mapped_free_array _) in *.
    set (AU := rg_allocated_user _) in *. set (SB := as_space_beg _) in *.
    assert (M : 8 * ((MU' - MU) / 8) = MU' - MU /\ 8 * ((MFA' - MFA) / 8) = MFA' - MFA /\ (RB s c + MU) mod 8 = 0 /\ (FA s c + MFA) mod 8 = 0
                /\ RB s c mod 8 = 0 /\ MU mod 8 = 0 /\ MFA mod 8 = 0).
    { rewrite EFA, ERB. clear - Q8 Q13 A3 F2 Y1; try acb. Z.div_mod_to_equations. lia. }
    clear - Y2 Y3 ERB EFA A1 A2 Q7 ROOM F1 F3 Q12 HC M FD; try acb. repeat split; try lia.
  Qed.

  Theorem amodelx_after_refill : AMODELX s2 mo'.
Proof.
  (* LPS revision repair (75d69e00, checker 2c6b6db8), rule 11g.  The replay that stood here
     destructured amaps_in_ledger and was typed against its OLD first conjunct (the farm printed
     its reconstructed IL1 with the unconditional `In (Z_to_bv 64 (mp_base mp), Z_to_bv 64
     (mp_size mp)) (vm_maps (m_vmmaps mo))`), which no longer exists after the restatement in
     As//Bs AllocRep.v.  The STATEMENT above is unchanged; only the proof moves, and it is
     written out as explicit text rather than re-encoded.
     DONOR: a donor tree:projects/openssl/echconfiglist_parser/proofs/lib/As/AG_Refill3.v
     lines 118-271, whose Section AmodelAfterRefill preamble is character-identical to this one
     (the only differences between the two sections are that three hypotheses and B's two
     pose/destruct lines are spelled plainly there and encoded here).  The donor tree still
     carries the OLD amaps_in_ledger and the text ports unchanged anyway: the first conjunct is
     discharged by `exact (IL1 mp Hin' K1' K2' K3' K4')`, and the restatement moves the guard
     onto the goal and onto IL1 in exactly the same place, so the two sides stay matched.
     That is what the weakening gives for free here: where the goal asks for ledger membership
     it now hands over `0 < bv_unsigned (Z_to_bv 64 (mp_size mp))`, and the refill transition
     does not touch vm_maps at all (VMM : vm_maps h' = vm_maps h), so the membership transports.
     The text is character-identical on the As and Bs sides. *)
    destruct AMX as [[AIL [ASV ABU]] [AK AKR]]. pose proof B as (B1 & B2 & ERB & EFA & B5 & B6 & B7 & B8 & B9 & B10 & M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8).
    assert (NUM := conj B1 (conj B2 (conj ERB (conj EFA (conj B5 (conj B6 (conj B7 (conj B8 (conj B9 (conj B10 M8)))))))))).
    destruct AIL as (IL1 & IL2 & IL3 & NOV & NW & NWA).
    pose proof AK as (K1 & K2 & K3 & K4a & K4b & K4c & K5a & K5b & K5c & K6a & K6b & K7 & K8a & K8b & K8c & K9 & K10 & K11).   (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (subU := fun X : list (word * word) => if mu <? mu' then maps_subtract X (RB s c + mu) (RB s c + mu') else X).
    set (subF := fun X : list (word * word) => if mfa <? mfa' then maps_subtract X (FA s c + mfa) (FA s c + mfa') else X).
    assert (ELs : L' = subF (subU (a_L s))) by (rewrite EL; subst subU subF; destruct (mfa <? mfa'); destruct (mu <? mu'); reflexivity).
    assert (ENs : vm_noaccess h' = subF (subU (vm_noaccess h))) by (rewrite VMN; subst subU subF; destruct (mfa <? mfa'); destruct (mu <? mu'); reflexivity).
    assert (NWU : forall X, entries_nowrap X -> entries_nowrap (subU X)).
    { intros X HX. subst subU. destruct (mu <? mu'); [apply maps_subtract_nowrap; [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| exact HX]. }
    assert (NWF : forall X, entries_nowrap X -> entries_nowrap (subF X)).
    { intros X HX. subst subF. destruct (mfa <? mfa'); [apply maps_subtract_nowrap; [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| exact HX]. }
    assert (SUBf : forall X x, entries_nowrap X -> in_rangesb x X = false -> in_rangesb x (subF (subU X)) = false).
    { intros X x HX F. subst subU subF. destruct (mfa <? mfa'); destruct (mu <? mu');
        repeat (apply in_rangesb_subtract_false; [first [apply maps_subtract_nowrap| idtac]; try exact HX; clear - NUM; try acb; lia| clear - NUM; try acb; lia| clear - NUM; try acb; lia|]); exact F. }
    assert (SUBt : forall X x, entries_nowrap X -> in_rangesb x (subF (subU X)) = true -> in_rangesb x X = true).
    { intros X x HX T. subst subU subF. destruct (mfa <? mfa'); destruct (mu <? mu'); try exact T.
      - apply (in_rangesb_subtract_true x X (RB s c + mu) (RB s c + mu')); [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia|].
        apply (in_rangesb_subtract_true x _ (FA s c + mfa) (FA s c + mfa')); [apply maps_subtract_nowrap; [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact T].
      - apply (in_rangesb_subtract_true x X (FA s c + mfa) (FA s c + mfa')); [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact T].
      - apply (in_rangesb_subtract_true x X (RB s c + mu) (RB s c + mu')); [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact T]. }
    assert (SUBu : forall X x, entries_nowrap X -> mu < mu' -> RB s c + mu <= bv_unsigned x < RB s c + mu' -> in_rangesb x (subF (subU X)) = false).
    { intros X x HX LT R. subst subU subF. rewrite (proj2 (Z.ltb_lt _ _) LT).
      assert (F0 : in_rangesb x (maps_subtract X (RB s c + mu) (RB s c + mu')) = false)
        by (apply in_rangesb_subtract_inside; [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact R]).
      destruct (mfa <? mfa'); [| exact F0].
      apply in_rangesb_subtract_false; [apply maps_subtract_nowrap; [exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact F0]. }
    assert (SUBfa : forall X x, entries_nowrap X -> mfa < mfa' -> FA s c + mfa <= bv_unsigned x < FA s c + mfa' -> in_rangesb x (subF (subU X)) = false).
    { intros X x HX LT R. subst subF. rewrite (proj2 (Z.ltb_lt _ _) LT).
      apply in_rangesb_subtract_inside; [apply NWU; exact HX| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact R]. }
    (* [comment removed for export] *)
    assert (SMONO : forall x, in_rangesb x (a_S s) = true -> in_rangesb x S' = true).
    { intros x T. rewrite ES, !in_rangesb_app, T, !Bool.orb_true_r. reflexivity. }
    split; [split; [| split]|].
    - (* [comment removed for export] *)
      unfold amaps_in_ledger. change (a_st s2) with st2. change (a_L s2) with L'. fold h'. rewrite VMM, ENs, ELs.
      assert (MAPS2 : forall mp, In mp (as_maps st2) ->
                In mp (as_maps st) \/ (mfa < mfa' /\ mp = mkMap (FA s c + mfa) (mfa' - mfa) (MkFreeArrayMap c) PROT_RW false)
                                   \/ (mu < mu' /\ mp = mkMap (RB s c + mu) (mu' - mu) (MkUserMap c) PROT_RW false)).
      { intros mp Hin. unfold st2, refilled in Hin. cbn [as_maps] in Hin. unfold refill_newmaps in Hin.
        fold st r nf mfa au mu in Hin. fold mu' mfa' in Hin. change (free_array_base st c) with (FA s c) in Hin. change (region_beg st c) with (RB s c) in Hin.
        apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [| left; exact Hin].
        apply in_app_iff in Hin. destruct Hin as [Hin|Hin].
        - destruct (Z.ltb_spec mfa mfa'); [| destruct Hin]. destruct Hin as [<-|[]]. right; left. split; [assumption| reflexivity].
        - destruct (Z.ltb_spec mu mu'); [| destruct Hin]. destruct Hin as [<-|[]]. right; right. split; [assumption| reflexivity]. }
      split.
      { intros mp Hin K1' K2' K3' K4'. destruct (MAPS2 mp Hin) as [Hin'|[[_ ->]|[_ ->]]].
        - exact (IL1 mp Hin' K1' K2' K3' K4').
        - exfalso. exact (proj2 (K2' c) eq_refl).
        - exfalso. exact (proj1 (K2' c) eq_refl). }
      split.
      { intros mp Hin KD x Hx. destruct (MAPS2 mp Hin) as [Hin'|[[LT ->]|[LT ->]]].
        - destruct (IL2 mp Hin' KD x Hx) as [F1 F2]. split; [apply SUBf; [exact NWA| exact F1]| apply SUBf; [exact LNW| exact F2]].
        - cbn [mp_base mp_size] in Hx. split; [apply SUBfa; [exact NWA| exact LT| clear - Hx; try acb; lia]| apply SUBfa; [exact LNW| exact LT| clear - Hx; try acb; lia]].
        - cbn [mp_base mp_size] in Hx. split; [apply SUBu; [exact NWA| exact LT| clear - Hx; try acb; lia]| apply SUBu; [exact LNW| exact LT| clear - Hx; try acb; lia]]. }
      split.
      { intros sc x Hsc Hx. change (as_sec st2) with (as_sec st) in Hsc. apply SUBf; [exact LNW| exact (IL3 sc x Hsc Hx)]. }
      split; [exact NOV|]. split; [exact NW|]. apply NWF, NWU. exact NWA.
    - (* [comment removed for export] *)
      unfold ashadow_visible. change (a_st s2) with st2. change (a_S s2) with S'. destruct ASV as [V1 V2]. split.
      + intros c0 x Hc0 Hx. change (RB s2 c0) with (RB s c0) in Hx. unfold st2 in Hx.
        destruct (Z.eq_dec c0 c) as [->|NE].
        * rewrite (rfd_region_c st c WFs HC ROOM) in Hx. cbn [rg_mapped_user refill_region] in Hx. fold st r nf au mu in Hx. fold mu' in Hx.
          destruct (Z.lt_ge_cases (bv_unsigned x) (sh (RB s c) + mu / 8)) as [LO|HI].
          -- apply SMONO. apply (V1 c x Hc0). change (rg_mapped_user (get_region (a_st s) c)) with mu. clear - Hx LO; try acb. lia.
          -- rewrite ES, !in_rangesb_app.
             assert (LT : mu < mu') by (clear - Hx HI M3 NUM; try acb; unfold sh in *; Z.div_mod_to_equations; lia).
             rewrite (proj2 (Z.ltb_lt _ _) LT). cbn [in_rangesb existsb app]. unfold zin_rangeb. cbn [fst snd]. unfold wz.
             rewrite (unsigned_lit (sh (RB s c + mu))) by (unfold sh, ASHADOW_BASE; clear - NUM; try acb; Z.div_mod_to_equations; lia).
             rewrite (unsigned_lit ((mu' - mu) / 8)) by (clear - NUM; try acb; Z.div_mod_to_equations; lia).
             replace ((sh (RB s c + mu) <=? bv_unsigned x) && (bv_unsigned x <? sh (RB s c + mu) + (mu' - mu) / 8)) with true; [rewrite !Bool.orb_true_r, ?Bool.orb_true_l; destruct (mfa <? mfa'); reflexivity|].
             symmetry. apply andb_true_intro. unfold sh in *. split; [apply Z.leb_le| apply Z.ltb_lt]; clear - Hx HI M1 M3 M5 M6 NUM; try acb; Z.div_mod_to_equations; lia.
        * rewrite (rfd_region_o st c WFs HC ROOM c0) in Hx by (clear - Hc0 NE; try acb; unfold kNumClasses in Hc0; lia). apply SMONO. exact (V1 c0 x Hc0 Hx).
      + intros sc x Hsc Hx. change (as_sec st2) with (as_sec st) in Hsc. apply SMONO. exact (V2 sc x Hsc Hx).
    - (* [comment removed for export] *)
      unfold ABUDGET in ABU |- *. change (a_AL s2) with AL2. change (a_S s2) with S'.
      assert (GR : mu mod 262144 = 0 /\ mfa mod 262144 = 0 /\ (mu' - mu) mod 262144 = 0 /\ (mfa' - mfa) mod 262144 = 0).
      { destruct RF as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13 & Q14 & Q15).
        pose proof (WF_region st c WFs ltac:(hci; unfold kNumClasses; clear - HC; try acb; lia)) as RO.
        pose proof (ro_mapped_mod _ _ RO) as MM. pose proof (ro_fa_mod _ _ RO) as FM.
        clear - Q7 Q8 Q12 Q13 MM FM NUM. unfold kUserMapSize, kFreeArrayMapSize, kFreeArraySize in *.
        repeat match goal with x := _ |- _ => subst x end.
        set (MU' := rf_mu' _ _ _ _) in *. set (MFA' := rf_mfa' _ _ _ _ _) in *. set (MU := rg_mapped_user _) in *. set (MFA := rg_mapped_free_array _) in *.
        Z.div_mod_to_equations. lia. }
      destruct GR as (GR1 & GR2 & GR3 & GR4).
      assert (PHI : aPhi s2 = aPhi s - ((mu' - mu) + (mfa' - mfa) + 40960 * ((mu' - mu) / 262144 + (mfa' - mfa) / 262144))).
      { unfold aPhi. change (a_st s2) with st2. change (a_st s) with st.
        assert (RC : get_region st2 c = refill_region st c) by (unfold st2; apply rfd_region_c; [exact WFs| exact HC| exact ROOM]).
        rewrite (pusage_grow st st2 c ltac:(clear - HC; lia)).
        - rewrite RC. cbn [rg_mapped_user rg_mapped_free_array refill_region].
          change (rf_mu' c (rg_num_freed (get_region st c)) (rg_allocated_user (get_region st c)) (rg_mapped_user (get_region st c))) with mu'.
          change (rf_mfa' c (rg_num_freed (get_region st c)) (rg_mapped_free_array (get_region st c)) (rg_allocated_user (get_region st c)) (rg_mapped_user (get_region st c))) with mfa'.
          change (rg_mapped_user (get_region st c)) with mu. change (rg_mapped_free_array (get_region st c)) with mfa. clear; lia.
        - intros c' Hc' NE. unfold st2. rewrite (rfd_region_o st c WFs HC ROOM c') by (clear - Hc' NE; lia). split; reflexivity.
        - exact GR1.
        - exact GR2.
        - rewrite RC. exact GR3.
        - rewrite RC. exact GR4.
        - rewrite RC. exact (proj1 B6).
        - rewrite RC. exact (proj1 B9).
      }
      rewrite PHI. fold h'. rewrite VML.
      destruct ABU as [AB0 AB1]. destruct HAL as [H0 H1].
      assert (KU : (mu <? mu') = true -> (mu' - mu) / 262144 = 1).
      { intros LT. apply Z.ltb_lt in LT. clear - LT GR3 NUM. Z.div_mod_to_equations. lia. }
      assert (KF : (mfa <? mfa') = true -> (mfa' - mfa) / 262144 = 1).
      { intros LT. apply Z.ltb_lt in LT. clear - LT GR4 NUM. Z.div_mod_to_equations. lia. }
      assert (K0 : 0 <= (mu' - mu) / 262144 /\ 0 <= (mfa' - mfa) / 262144) by (clear - NUM; split; apply Z.div_pos; lia).
      assert (PT : pages_total S' <= pages_total (a_S s) + 10 * ((mu' - mu) / 262144 + (mfa' - mfa) / 262144)).
      { rewrite ES, !pages_total_app.
        assert (W1 : pages_total (if mfa <? mfa' then [(wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))] else []) <= 10 * ((mfa' - mfa) / 262144)).
        { destruct (mfa <? mfa'); [rewrite (KF eq_refl)| cbn; clear -K0; lia]. rewrite pages_total_cons. cbn [pages_total].
          pose proof (cl_bounds (wz (sh (FA s c + mfa)), wz ((mfa' - mfa) / 8))) as CB. cbn [fst snd] in CB. unfold wz in CB.
          rewrite (unsigned_lit ((mfa' - mfa) / 8)) in CB by (clear - NUM; try acb; Z.div_mod_to_equations; lia). unfold page_size in CB.
          assert (DV : (mfa' - mfa) / 8 / 4096 <= 8) by (clear - NUM; try acb; Z.div_mod_to_equations; lia). unfold wz. clear - CB DV; try acb. lia. }
        assert (W2 : pages_total (if mu <? mu' then [(wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))] else []) <= 10 * ((mu' - mu) / 262144)).
        { destruct (mu <? mu'); [rewrite (KU eq_refl)| cbn; clear -K0; lia]. rewrite pages_total_cons. cbn [pages_total].
          pose proof (cl_bounds (wz (sh (RB s c + mu)), wz ((mu' - mu) / 8))) as CB. cbn [fst snd] in CB. unfold wz in CB.
          rewrite (unsigned_lit ((mu' - mu) / 8)) in CB by (clear - NUM; try acb; Z.div_mod_to_equations; lia). unfold page_size in CB.
          assert (DV : (mu' - mu) / 8 / 4096 <= 8) by (clear - NUM; try acb; Z.div_mod_to_equations; lia). unfold wz. clear - CB DV; try acb. lia. }
        clear - W1 W2; try acb. lia. }
      unfold page_size in *. clear - AB1 H0 H1 PT EAG NUM K0; try acb. unfold h. lia.
    - (* [comment removed for export] *)
      (* LPS 727298f3: [akernel] is [akernel_pre /\ akernel_resx]; a refill changes neither the
         ledger nor the mappings ([VMR], [VMM]), so the reserved half carries over unchanged. *)
      unfold akernel. split; [| unfold akernel_resx in AKR |- *; cbv zeta in AKR |- *; change (m_vmmaps mo') with h'; rewrite VMR, VMM; exact AKR].
      fold h'. rewrite VMR, VML, VMT, VMM, ENs. change (a_thr s2) with (a_thr s). change (a_ctx s2) with (a_ctx s). change (a_sb s2) with (a_sb s).
      change (a_pa s2) with (a_pa s). change (a_fsb s2) with (a_fsb s). change (a_Zr s2) with (a_Zr s). change (a_L s2) with L'. change (as_sec (a_st s2)) with (as_sec st).
      replace (RB s2) with (RB s) by reflexivity. rewrite ELs.
      split; [exact K1|]. split; [exact K2|]. split; [exact K3|]. split; [exact K4a|]. split; [exact K4b|]. split; [exact K4c|]. split; [exact K5a|]. split; [exact K5b|].
      split.
      { intros x Hx. destruct (K5c x Hx) as [Z1 Z2]. split; [exact Z1|].
        pose proof sh_ceiling_lt_AHI_LO as SC. unfold AHI_LO in *.
        subst subU subF. destruct (mfa <? mfa'); destruct (mu <? mu').
        - apply in_rangesb_subtract_keep; [apply maps_subtract_nowrap; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| clear - NUM; try acb; lia| clear - NUM; try acb; lia| | clear - Hx SC NUM; try acb; lia].
          apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx SC NUM; try acb; lia].
        - apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx SC NUM; try acb; lia].
        - apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx SC NUM; try acb; lia].
        - exact Z2. }
      split; [intros x Hx; apply K6a; apply (SUBt _ x NWA Hx)|].
      split; [intros sc x Hsc Hx; apply (SUBf _ x NWA); exact (K6b sc x Hsc Hx)|].
      split; [exact K7|]. split; [exact K8a|]. split; [exact K8b|].
      split; [| split; [exact K9| split; [exact K10|]]].   (* [comment removed for export] *)
      2:{ (* [comment removed for export] *)
          intros xa xn HB. pose proof (K11 xa xn HB) as FR0.
          assert (FRU : region_free (subU (vm_noaccess h)) xa xn = true) by (subst subU; cbv beta; destruct (mu <? mu'); [apply LazyMadvise.region_free_maps_subtract; [exact NWA| exact FR0]| exact FR0]).
          pose proof (NWU _ NWA) as NWU0. subst subF. cbv beta. destruct (mfa <? mfa'); [apply LazyMadvise.region_free_maps_subtract; [exact NWU0| exact FRU]| exact FRU]. }
      { (* [comment removed for export] *)
        intros x Hx. destruct (K8c x Hx) as [Z1 Z2]. split; [exact Z1|].
        unfold sh, AIMG_TOP, ALOWSH_LO, ASHADOW_BASE in Hx.
        destruct (mfa <? mfa'); destruct (mu <? mu').
        - apply in_rangesb_subtract_keep; [apply maps_subtract_nowrap; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia]| clear - NUM; try acb; lia| clear - NUM; try acb; lia| | clear - Hx NUM; try acb; lia].
          apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx NUM; try acb; lia].
        - apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx NUM; try acb; lia].
        - apply in_rangesb_subtract_keep; [exact LNW| clear - NUM; try acb; lia| clear - NUM; try acb; lia| exact Z2| clear - Hx NUM; try acb; lia].
        - exact Z2. }
  Qed.
End AmodelAfterRefill.

End HCW.

