(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith List PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgBoth ItabBoth RotBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Rot.
Import ListNotations W64 Val Mem FI St Step Plan.
From Stdlib Require Import PrimString.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require PlanDec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require StrLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition EC0 : IMap.t sstate := imap_of nil.
Definition MR0 : sv := (VL (wp 0%uint63)).
Definition OB0 : list obligation := nil.
Definition CL0 : list (int * template) := nil.
Abbreviation WFS c := (ctx_wfb c = true) (only parsing).
Abbreviation CHKS c p r o := (check SEGS c p r = Some o) (only parsing).
Abbreviation PL s := (PlanDec.dec_plan (StrLz.lz_dec s)) (only parsing).
Abbreviation PLR s := (PlanDec.dec_plan s) (only parsing).
Ltac wf_tac := vm_cast_no_check (@eq_refl bool true).
Ltac chk_tac := rewrite (Rot.Rot.check_r_eq SEGS RotBoth.ROT RotBoth.ROT_ok); match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Ltac chk0_tac := match goal with |- _ = ?r => vm_cast_no_check (@eq_refl _ r) end.
Definition sg_of (p : plan) : list (int * sv) := match p with PCut _ l => l | PCutDec _ l => l | PEcall _ l => l | _ => nil end.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr. Import Actr.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB FaC RangeC StrRegC ReadC MemsetC MemcpyC Memcpy0C PubC MemcpyPC MemsetPC RstageC BlobC PayloadC HalfC VprintfC FprintfC FprintfSC StrnlenC FwriteC FwritePostC UnreggC. Import ActrB.TwinB FaC.TwinB RangeC.TwinB StrRegC.TwinB ReadC.TwinB MemsetC.TwinB MemcpyC.TwinB Memcpy0C.TwinB PubC.TwinB MemcpyPC.TwinB MemsetPC.TwinB RstageC.TwinB BlobC.TwinB PayloadC.TwinB HalfC.TwinB VprintfC.TwinB FprintfC.TwinB FprintfSC.TwinB StrnlenC.TwinB FwriteC.TwinB FwritePostC.TwinB UnreggC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GRealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import GTwinSub CaseF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import GshC. Import GshC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import StrlenC. Import StrlenC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import OpDropC. Import OpDropC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import RoLitA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import AmallocNnC. Import AmallocNnC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ReadDirC. Import ReadDirC.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import RoLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GViewDrop2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GUnrealign.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import ShLoadLit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GBgNone.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.BothU Require UnivBoth.
From Stdlib Require Import PrimString.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require TplDec.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require StrLz.

Definition TPL_BLOB : PrimString.string := (StrLz.lz_dec "-$*PRPLPB0XXA0ZPUPLPB0YXA0ZPZPLPB0ZXA0ZP\PLPB0_XA0Z0#7-+;LQA1ZPQPLSA6L000OOOQA0ZRTLaA0ZRTB0SQX0PQZRVLQA0ZLOOOOOOQRVA1Z#0IH1V8IH1V#@IH1V@9I1V#00Li00Dj#00Dj8NDj#HNDj07Ej#87Ej@2Oj#8>1k@@1k#A@1k@45k#H45k@95k#H95k0IF=Q#1IF=Q@FHOU#@FHOU@FH1V#8?K1V@?K1V#HAK1VDBK1V#8CK1V@CK1V#08L5V88L5V#H>O5V0?O5V#8?06V@?06V#0I16V0046VLPL000000@QLSQQ0040H0*2$OW1#<,000TLPL0014#/2$:-$@000VLPLP~Q\~UPLP~WQLPLP~_R~ZP~[P~\P~]PPQh~^Q~`P~aPLUCPTN0DM;SQLPCPXN0E5#.#F5#.#H5#.#I5#.-#(KM;SQLH5GhCPXN0M2#=-#.TN05N;SQLZCPTN06N;SQLQ0%1'5<SQL1)/-#%0180RCPXN0BD<3%<$6E4#.&137h2%9#22#.-$'QLPCQQLPCRQLPCSQLPCTQLPCUQLPCVQLPCWQN0==7hXPR0%.-#*>=7hQL0AKiCPXN0;>G0%1+XN0<>GhQL0)0)=>GhQLX0$75$(-##?>GhQLH;K1V0#2$=77#2#@9#2$A=1(7-#5XN0B=7hQP0RPCPTLPCTTN0C=7hRLR0/:-#+=7hQLQCRQN0E=7hQL@?2%-,N=7hQL88L50#2)2>7hQP11*$$6>0$>0)36#<%@>G0#<-#$TN0C>GhQL8EK1%*#D0#2+GNgCPXN0F0**%FB_0#1-#%?GhQN1H@GhPPU11%4#@1%4,QN0J@GhQPS11&#)@GhQL@B2&#-#'L@GhQLHWCPXN0M@4.##N2%(,XN0O@GhQPW0%(-#?7AGhQN1:AGhPLQCPTLQCTTN0;AGhRN1=AGhPL1S00,#A50,0$<*@AGhPN1A0#)#B0#)#C0#)#F0#)*3BGhPN170#));BGhPLZ0-5'CGhQL01*+#C5#.#G5#.$KC4+--#$LDGhQN1MDGhP@#71*2-#0:EGhXN1CMGhPLD;5\CPXN0EM1):(TN0E1H3#.#F0#.-##HP026RJKPOP1'3$PQ20*&QQPZ0#,&RQPQ0.8#J1181'OOOOW2,8#K>#712#/8#7#M>#7#N>#75#6(OWQLhH71<7*10YJKQOQ02*%-#%HP04RPPJKRORL01$#'PQL021166&QQLT1)5$LH01&?-#4SQLUCPXN0TQL[CPXN0UQL`CPXN0V31'9%WQL01)8'XQL000%)#Y2$4&ZQPX0$+%[QL0/%#\3#5%]QL01.(#^2)=%_QL0176&`QPV0#5#a2#>#b2#+-#'cQL0UHP00dJKSOS021$-#$HP04QPPJKTOU0203-#$HP04SPPJKUOZ0210-#*HP04\PPJKVO\LSH0@03-6-#+W01PJKWOdLPLL1MgQQ@5/*-#<WL002RL0BK1VP2RPP3RPP4RPPQXLRLRPQXPR52)>-#9000VP5RPP6RPP7RPP8RPLH3DaPRPLPLPL0#(-#0PLPLPP9RPP:RPP;RPP<RP@^_;$(:#2@#-$$-#2@^_QPQPPSPvz%PPQPPUPvz%QrQ1(*)NOOS08I1*.-#$Sz%RaQTz%SrR6$%3);'Tz%Tr2#2;#=%UrU@#%#=-#*VrW0=9T0=940Rz%WrZ@#%$.-#9XPQPPZPvz%YPRPPQ0Qez%ZPSPRPez%[LW01,3&uz%\0#,,L80Rvz%]LQ01&$&vz%^0#,+L000Tvz%_0#=(ZXvz%`13$*1#=%aRQ529((vz%bRR8#3%cr\@#%(7+da\Sz%eP\1./-#-fRQRSvz%gPQPP\Pvz%hRS8%4%iP\1*.+jRRRSvz%k61'6+Tvz%lPS0U8#5'mRQL@21*/+Svz%nPQ0S0&=%oRR8#>(0QPQ0S0&--#*1QPdPRUez%2Qr0R0Q011%)-#/3Q[4Q0$&P!H3Da0T0X[cLP)@,23+222=-#40239-#$C=7hRdPQPJKX@#,2+-11=7#221#;02';%<CO01@##37#:42>+8$30&)#7>#7#88#7,H5DaCPXN097#:23*+#:8$23,#%00002(9#;8$;#51$<#<8#9#61#9#=8#9#723-78#9#81#9#?7#91,-#A>#7#B>#7#C>#7#D7#72*7#E8$/$H31,)#F8#:12>@8%)129921(81$/%L1M01#/22#@8$2@&<2;+-#2nJKYOQKRORKSOSKTOUKUOZKVO\122&(H5DaQQ6'1722&#Z322%&LRLR6($-#$OWP1RPP1RPML724(02.6'HQPZP@#322)*R_Q&P!H5@,=1<#1443$FL442?#G5#.*HL;SQQQ032+@$OO03@(#J0#;#2514%0#;#K0#;#@515714#<@#%#;)1M;SQL@010?'2M;SQ81'7-#)CPTN07M;SQdXYPJKZ@#-2#&%GKK033?#95104-#%WQL@5OjCPXN0:7#:#R11=&8#7)YCPXN0<8%(0#+036##=8#=#50#8#>9&;$7H047-#?8#:%N930)1#@8#:11=@8'5037<#B>$.#C>$.#D7#7(M=6CI<12*30/,#E8$%%OOO3/,0$%#F7$%>1&$#G9$&#852#'0$&#H:%*;1%;#I8)@%94:0,(#J>*:#K8#7$0D348+8#;'<6CI<0#<#M7#<21''#N8#8324(51)?3&=#7>#7#8>#7#9>#7#:>#7#;>#7#<>#7#=8#7%8:M1+%#>8#;01*&#?8#74,5#@7#;#R02-9#A8$231/1#B9%,#I157+#C7#:%QQH52/>01$.#D9$&#@;$&#E8&$-$,3SCPQL<SCQQL9SCRQLJQCSQL0QCTQL3SCUQL1SCVQL>SCWQN0F6%&-#?XL>SCPQL?SCQQLDSCRQL0QCSQL?SCTQL@SCUQL56%&#G8%&-#%0QCPQLZCQQN0H6#=#R1/:#E62/3201#F>#7#G>#7#H>#7#I7#731**#J>$0#K>#7724232@?#M7#8>/7#N8%331%3#O8#:#322#662<0(WQL0J5051:#17#:211/@$(31<$LF@##31<1%>831<82<?$CP;31<211(>#783181#7831625+@@.'315'BRJK[@#*316)0IGhQQ@51&=7316-$*KVPPLVPPMVPLPL@5OjL06@jLPLPLD4DhP1WPP2WPP3WPP4WP01@*#L12$$1#06315-$-5WPP6WPP7WPP8WP@^_S_QRTLPez%4QRTLOQvz%5QRWLPez%6QRT22;;)uz%7QRT05'&-#+uz%8Q[U1P$&Q!86Dh9W@,9336%QQ;@##315+dZQPJK\OP12(,-$7PB0SQCQQLQB0SQCRQLRB0SQCSQLSB0SQCTQLTB0SQCUQLUB0SQCVQLVB0SQCW:2**-#$XLWB0SQCPQLX2%>)ZCRQN0I6$+*Sd[RPJK]@#'1,711(+-#'Yez%9Q%5Q%6Q%7Q31'&#R@-$1'&#<@#)1'&%^OP=1$+#Y21')%ZCS:1$4*Td]QPJK_@#.1$4'Zez%:=1$4#S@-$1$4#=@#)1$4#`@#,1$4216;%ZCT:1$=#U01$=#a@#.1$='[ez%;=1$=#T@-$1$=#>@#)1$=#b@#41$=#[22(8%ZCU:1%(#V01%(#c@#.1%('\ez%<=1%(#U@-$1%(#?@#)1%(#d@#=1%(#\228>%ZCV:1%1#W01%1#e@#.1%1']ez%==1%1#V@-$1%1#@@#)1%1#f@$(1%1%]B003+/%ZCW:1%:#X01%:#g@#.1%:'^ez%>=1%:#W@-$1%:#A@#)1%:#h@$11%:%^B013<)81%>$LZ0:/;759-)d]RPJKi@#.1&5'_ez%?=1&5#X@-$1&5#B@#)1&5'jOPL_21&506%(71#@*RdiQPJKk@#.1#@'`ez%@=1#@#Y@-$1#@#C@#)1#@#l61#@#`215504;>71$+#S01$+#m@#.1$+'aez%A=1$+#Z@-$1$+#D@#)1$+#n?1$+#a32&>$CS:1$4#T01$4#o@#.1$4'bez%B=1$4#[@-$1$4#3@#)1$4$0Q<5?7013;75>$+Sd[QPJK1Q@#.1$*'Qez%C=1$*#\@-$1$*#E@#)1$*$2Q@#+13=#b23';05-)714(#U014(#3@#/1$?'cez%D=1$?#]@-$1$?#F@#)1$?#4@#51$?#c237:05-+71%*#V01%*#5@#/1%*'dez%E=1%*#^@-$1%*#G@#)1%*#6@#>1%*#d24*$05--71%3#W01%3#7@#/1%3'eez%F=1%3#_@-$1%3#H@#)1%3#8@$)1%3%eB065-/71%<#X01%<#9@#/1%<'fez%G=1%<#`@-$1%<#I@#)1%<#:@$21%<%fB015-181%@15-1#K85-1(iRPJK;@#/1&7'gez%H=1&7#a@-$1&7#J@#)1&7(<QOPLg21&705-371$$+Rd;QQPJK=@#/1$%'hez%I=1$%#b@-$1$%#K@#)1$%#>71$%#h215:04,;71$.#S11$.#?@#/1$.'iez%J=1$.#c@-$1$.#L@#)1$.#@@##1$.#i22'(05-971$7#T11$7#A@#/1$7'jez%K=1$7#d@-$1$7#M@#)1$7#B@#,1$7#j226=04<371$@#U11$@#C@#/1$@'kez%L=1$@#e@-$1$@#N@#)1$@#D@#51$@#k23(=04<471%+#V11%+#E@#/1%+'lez%M=1%+#f@-$1%+#4@#)1%+#F=60&3;<;02&=760/#T060/#G@#/1$3'Rez%N=1$3#g@-$1$3#O@#)1$3#H@#>14<%lB065.(715'#W115'#I@#/1%4'mez%O=1%4#h@-$1%46=#?+;1%4#J@$)1%4%mB065.)71%=#X11%=#K@#/1%=(nez%0R<1%=#i@-$1%=#1@#)1%=#L@$21%=%nB015.*81&#15.*#L85.*);QRPJKM@#/1&8'oez%1=1&8#j@-$1&8#2@#)1&8(NQOPLo21&805.+71$%+RdMQQPJKO@#/1$%(0Qez%2=1$&#k@-%9($@#)1$&$0R61$&#003*935.-71$0#S11$0$1R@#.1$0(1Qez%3=1$0#l@-%3:.@#)1$0#2@#$1$0#193:371$:#T11$:#3@#/1$:(2Qez%4=1$:#m@-$1$:#5@#)1$:#4@#.1$:#20#,35.471%&#U11%&#5@#/1%&(3Qez%5=1%&#n@-$1%&#6@#)1%&#6@#81%&#30#,35.971%0#V11%0#7@#/1%0(4Qez%6=1%0#o@-$1%0#7@#)1%0#8@$$1%0#40#,34=.71%:#W11%:#9@#/1%:(5Qez%7=1%:#0@-%='+/#8@#)1%;#:@$.1%;#50#,34=671&'#X11&'#;@#/1&'(6Qez%8=1&'#1@-%1&'#5@#*9'+#R@#1='<5029.763%#U063%#=@#/1$>'Sez%9=1$=#2@-%1$=#9@#)16$#>@$816$#60#,<16)15/<#M85/<)MQRPJK?@#/1&@(7Qez%:=1'##3@-%1'##:@#)1'#(@ROPL701$835/?71$(+Rd?RQPJKA@#/1$((8Qez%;=1$(#4@-&=)18@#)1$(#B81$(#8316*050#71$2#S11$2#C@#/1$2(9Qez%<=1$2#5@-%1$2#<@#)1$2#D@#%1$2#932':050%71$<#T11$<#E@#/1$<(:Qez%==1$<#6@-%1$<#=@#)1$<#F@#/1$<#:327603)971%(#U11%(#G@#/1%((;Qez%>=1%(#7@-%1%(#>@#)1%(#H@#91%(#;33)<050)71%2#V11%2#I@#/1%2(<Qez%?=1%2#8@-%1%2#?@#*9)=@$%1%2#<33:.050+71%<#W11%<#K@#/1%<(=Qez%@=1%<#9@-%1%<#@@#*9)<@$/1%<#=0#,350,71&(#X11&(#M@#/1&((>Qez%A=1&(#:@-%1&(#A@#*9),@$91&(#>0#,<1&-14>0#N84>0)?RRPJKO@#/1'$(?Qez%B=1'$#;@-%1'$#B@#*9,*'SOPL?31'$04>071$(,RdORQPJK1S@#.1$((@Qez%C=1$(#<@-%1$(#6@#*='?*#S@#:=-=)03,4763=#V063=#3@#/1%)'Tez%D=1%(#=@-%1%(#C@#*9,.814.#@32(005067148#S1148#5@#/1$1(AQez%E=1$2#>@-%1$2#D@#*9+:@#%1$2#A314>050671$<#T11$<#7@#/1$<(BQez%F=1$<#?@-%1$<#E@#*9+(@#/1$<#B33)<050671%(#U11%(#9@#/1%((CQez%G=1%(#@@-%1%(#F@#*9*3@#91%(#C33:$027$71%2#V11%2#;@#/1%2(DQez%H=1%2#A@-%1%2#G@#)1%2#<@$%1%2#D34,4050671%<#W11%<#=@#/1%<(EQez%I=1%<#B@-%1%<#H@#*9*=@$/1%<#E0#,350671&(#X11&(#?@#/1&((FQez%J=1&(#C@-%1&(#I@#*9*$@$91&(#F0#,<1&-15064=4+4-#$OOWQdORRPJKA@#/1'$(GQez%K=1'$#D@-%1'$#J@#*9,>'SOPLG31'$050671$(+RdASQPJKC@#/1$((HQez%L=1$(#E@-%1$(#K@#*9,481$(#H316*04>071$2#S11$2#E@#/1$2(IQez%M=1$2#F@-%1$2#L@#*9,*@#%1$2#I32':04>071$<#T11$<#G@#/1$<(JQez%N=1$<#G@-%1$<#7@#*='@=@#;62$3=3<+03;/762-#W062-#I@#/1%2'Uez%O=1%1#H@-%1%1#M@#*9+=@#/15-#J33*'050?7157#U1157#K@#/1%')KQez%0S<1%(#I@-%1%(#N@#*9+)@#91%(#K33:-050?71%2#V11%2#M@#/1%2(LQez%1=1%2#J@-%1%2#O@#*9*3@$%1%212)/32(271%<#W11%<#O@#/1%<(MQez%2=1%<#K@-%1%<<=80969)-#T@$.1%<#M0#,350?71&(#X11&($1T@#.1&((NQez%3=1&(#L@-#1&(01%(0=76(#88=8=%0=</49=8623=7@%9=84*$0H?=830@$61((#N0#,?1(-'UPJK2@#(1(-,LPL@7HhQQ@5=8..#W6=70/$<V1=7/5&>VPL0=8*00=700-#6FKKSLQPAVPPBVPPCVPPDVPPEVPRYRV1$-1=70;-$%FKKSLPRTLQRTPFVPPGVPPHVPPIVP@^_T_QRTLOQez%4=1,:#M01,:$JV@,;1=@#1@#)4&%&3TOP1=8&(91-:#F@#$=:*<0=8.'8=:*$2=85,9=:(/$HJ?=:(/@$410:&0QCP:4*/*Qd[YPJK4@#,1.+$HJ@#)1.+$MU11.+'OUPRT41.+-#5PZPRTP2VPP3VPP4VPP5VPP6VPLPLa61.)-$&PPZPLPRTRTRTP7VPP8VPP9VPP:VP@^_U_QLOQRTuz%5S41.$(T1P$&N01.$#;@,<1.$#8@#)1.$$5T@$.=8*002888=8*,04?0#6@#/287'Vez%6=1><#O@-%3+<#9@#)1%:&7TOP173/7=5/=#Q0=5@;#8@#/1#:'Wez%7=1#:#0@-%=87=#:@#)1#:$9T6=5@>073,71$%#R01$%#:@#/1$%'Xez%8=1$%#1@-%1$%<=<8%&KL;S2=@2#%P?T5=@2%-#%dZRPJK;TOPN1262<+&PN139#2#49#2#59#2#69#2#79#273$1%PN173$)%PN17=<9;%PN173$4%PN173$/%PN17=<9&%PN17=<8>%PN173%)+Pd2T^PJK<@#*2@)(P0TPQQ6=;4#72@(-#%1TPP2TPP3TPL53=<=;-#5LQP4TPP5TPP6TPP7TPP8TPP9TPP:T53;2&GKKS:3;1-#6;TPP<TPP=TPP>TP@^_V_Q&MQ!@7Hh@@,:==75$K;32>2;334&<TQW71=+7=21)7=-6.7=(9?7=$.>7917742'%JK=@%#1)/$RT@#)1)/436801)(6367<1)-,W_Q&NQ!@HJ@-$1)-1=</.71),@##==+)@#$==*/*d<TSPJK>@#+4+0@#,=<$(61';?=<$(:1'7@#-=<$(<1'<#X01<)%86D@,<1'<%QQA@##28$,d;TQPJK?TO;24(3=>;382404==.182481=>;3824=1=>;3825$7=>;3825/2=>;382554=>;3825=&QLZC@$,==?:@#$5'>'ZPJK@@$,1/0+ATPPBTPPC@#%1/0-#%GTPPHTPPITPPJ@#01/0-#+KTPPLTPPMTPPNTP@^_Y02$,'86DhO@,?2$,$N17=?#6%PN17=?#1%PN17=?#,%PN17=?#'%PN17=>@@%PN17=>@;%PN17=>@6%PN172'=%PN17=>@(%PN17=>@#%PN17=>?8%PN172),%PN17=>?+%PN172)422@'#181-;$N172@$%PN172@'%PN172@*%PN172@-%PN172@0%PN172@3%PN172@6+Pd<TfPJKA@#12@<61<>@#%2.#*@5OjRXLP@#*2@88113511-?2-=$Z_8=1/6-##T1P$&2R!0IG@-#3#,@)911@*d@T^PJKB@#)5*&#Z02'8@,?1(8136=$JL5>'2#5#.&ML;S6=@1@0>#/*0#>$2M55*3#<85*3*VPJKCTOP@#,1<4%L8H@#*>$'2%0TP21<9(LRLRLR2>$''%P3T<1<>@##>$'$51=6-#+P;TP@^_[_Q&2R!LINg=@,;1;9&CTOP@#+14%#[014%@,</$2>##4$5<0>(1,'QN0264#.&B>Gh080$3>(%<1=@17$>G3>(*1-#.N0F@GhQdCTVPJKDTOPL0BO0>'*99=@<7(DN9cCP<=@<:3$49=@<=$0I1>((?8=@<=1=@3=9>%;8%4DE04=*9=@<30$19=@<3$8M1%@9=@<60$157$3(OWQL8H1=@8.5:==)OWQdYZR7>&&57>&&*%JKE@#,893'MNgQQ7>$3&61</+>TPP?TPP@21</-#/LRPBTPLPPDTPPETPPFTPLNR@#$1<*54'1*PKTP@^_\01<*+D8NgMT0XZ@,310('KDTOP@#*1$9$_\01<'7.?"%pstring).
Definition TPL_ALL : list template := TplDec.TplDec.dec_tpls TPL_BLOB.
Local Abbreviation NT i := (TplDec.TplDec.nth_tpl TPL_ALL i) (only parsing).
Lemma TPL_ALL_length : List.length TPL_ALL = 77%nat.
Proof. vm_cast_no_check (@eq_refl nat 77%nat). Qed.

Definition T_DRV2 : sstate := Eval vm_compute in (t_st (TplDec.TplDec.nth_tpl TPL_ALL 0)).

Definition T_OPENERR_ := Eval vm_compute in (NT 1).
Definition T_SW_OPENERR__1 := Eval vm_compute in (NT 2).
Definition T_SW_OPENERR__10 := Eval vm_compute in (NT 3).
Definition T_SW_OPENERR__11 := Eval vm_compute in (NT 4).
Definition T_SW_OPENERR__12 := Eval vm_compute in (NT 5).
Definition T_SW_OPENERR__13 := Eval vm_compute in (NT 6).
Definition T_SW_OPENERR__14 := Eval vm_compute in (NT 7).
Definition T_SW_OPENERR__15 := Eval vm_compute in (NT 8).
Definition T_SW_OPENERR__16 := Eval vm_compute in (NT 9).
Definition T_SW_OPENERR__17 := Eval vm_compute in (NT 10).
Definition T_SW_OPENERR__18 := Eval vm_compute in (NT 11).
Definition T_SW_OPENERR__19 := Eval vm_compute in (NT 12).
Definition T_SW_OPENERR__2 := Eval vm_compute in (NT 13).
Definition T_SW_OPENERR__20 := Eval vm_compute in (NT 14).
Definition T_SW_OPENERR__21 := Eval vm_compute in (NT 15).
Definition T_SW_OPENERR__22 := Eval vm_compute in (NT 16).
Definition T_SW_OPENERR__23 := Eval vm_compute in (NT 17).
Definition T_SW_OPENERR__24 := Eval vm_compute in (NT 18).
Definition T_SW_OPENERR__25 := Eval vm_compute in (NT 19).
Definition T_SW_OPENERR__26 := Eval vm_compute in (NT 20).
Definition T_SW_OPENERR__27 := Eval vm_compute in (NT 21).
Definition T_SW_OPENERR__28 := Eval vm_compute in (NT 22).
Definition T_SW_OPENERR__29 := Eval vm_compute in (NT 23).
Definition T_SW_OPENERR__3 := Eval vm_compute in (NT 24).
Definition T_SW_OPENERR__30 := Eval vm_compute in (NT 25).
Definition T_SW_OPENERR__31 := Eval vm_compute in (NT 26).
Definition T_SW_OPENERR__32 := Eval vm_compute in (NT 27).
Definition T_SW_OPENERR__33 := Eval vm_compute in (NT 28).
Definition T_SW_OPENERR__34 := Eval vm_compute in (NT 29).
Definition T_SW_OPENERR__35 := Eval vm_compute in (NT 30).
Definition T_SW_OPENERR__36 := Eval vm_compute in (NT 31).
Definition T_SW_OPENERR__37 := Eval vm_compute in (NT 32).
Definition T_SW_OPENERR__38 := Eval vm_compute in (NT 33).
Definition T_SW_OPENERR__39 := Eval vm_compute in (NT 34).
Definition T_SW_OPENERR__4 := Eval vm_compute in (NT 35).
Definition T_SW_OPENERR__40 := Eval vm_compute in (NT 36).
Definition T_SW_OPENERR__41 := Eval vm_compute in (NT 37).
Definition T_SW_OPENERR__42 := Eval vm_compute in (NT 38).
Definition T_SW_OPENERR__43 := Eval vm_compute in (NT 39).
Definition T_SW_OPENERR__44 := Eval vm_compute in (NT 40).
Definition T_SW_OPENERR__45 := Eval vm_compute in (NT 41).
Definition T_SW_OPENERR__46 := Eval vm_compute in (NT 42).
Definition T_SW_OPENERR__47 := Eval vm_compute in (NT 43).
Definition T_SW_OPENERR__48 := Eval vm_compute in (NT 44).
Definition T_SW_OPENERR__49 := Eval vm_compute in (NT 45).
Definition T_SW_OPENERR__5 := Eval vm_compute in (NT 46).
Definition T_SW_OPENERR__50 := Eval vm_compute in (NT 47).
Definition T_SW_OPENERR__51 := Eval vm_compute in (NT 48).
Definition T_SW_OPENERR__52 := Eval vm_compute in (NT 49).
Definition T_SW_OPENERR__53 := Eval vm_compute in (NT 50).
Definition T_SW_OPENERR__54 := Eval vm_compute in (NT 51).
Definition T_SW_OPENERR__55 := Eval vm_compute in (NT 52).
Definition T_SW_OPENERR__56 := Eval vm_compute in (NT 53).
Definition T_SW_OPENERR__57 := Eval vm_compute in (NT 54).
Definition T_SW_OPENERR__58 := Eval vm_compute in (NT 55).
Definition T_SW_OPENERR__59 := Eval vm_compute in (NT 56).
Definition T_SW_OPENERR__6 := Eval vm_compute in (NT 57).
Definition T_SW_OPENERR__60 := Eval vm_compute in (NT 58).
Definition T_SW_OPENERR__61 := Eval vm_compute in (NT 59).
Definition T_SW_OPENERR__62 := Eval vm_compute in (NT 60).
Definition T_SW_OPENERR__63 := Eval vm_compute in (NT 61).
Definition T_SW_OPENERR__64 := Eval vm_compute in (NT 62).
Definition T_SW_OPENERR__65 := Eval vm_compute in (NT 63).
Definition T_SW_OPENERR__7 := Eval vm_compute in (NT 64).
Definition T_SW_OPENERR__8 := Eval vm_compute in (NT 65).
Definition T_SW_OPENERR__9 := Eval vm_compute in (NT 66).
Definition T_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528 := Eval vm_compute in (NT 67).
Definition T_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528 := Eval vm_compute in (NT 68).
Definition T_SW_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 := Eval vm_compute in (NT 69).
Definition T_SW_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 := Eval vm_compute in (NT 70).
Definition T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 := Eval vm_compute in (NT 71).
Definition T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka := Eval vm_compute in (NT 72).
Definition T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63 := Eval vm_compute in (NT 73).
Definition T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka := Eval vm_compute in (NT 74).
Definition E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63_1 : sstate := Eval vm_compute in (t_st (TplDec.TplDec.nth_tpl TPL_ALL 75)).
Definition E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1 : sstate := Eval vm_compute in (t_st (TplDec.TplDec.nth_tpl TPL_ALL 76)).

Lemma templates_wfb : forallb (fun t => sstate_wfb (t_st t)) TPL_ALL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition CONTRACTS : IMap.t contract := imap_of [(27%uint63, (CtrS.c_open_toolong 827812%uint63)); (410%uint63, (MemcpyC.TwinB.MemcpyC.amemcpy_c ImgBoth.SEGS 386080%uint63)); (414%uint63, (Memcpy0C.TwinB.Memcpy0C.amemcpy0_c 386080%uint63)); (421%uint63, (StrnlenC.TwinB.StrnlenC.astrnlen_c 319880%uint63)); (425%uint63, (FprintfSC.TwinB.FprintfSC.afprintf_s_pre_c ImgBoth.SEGS (wlit 126819%uint63) 3%uint63 10%uint63 333440%uint63)); (429%uint63, (UnreggC.TwinB.UnreggC.unregg_c UnreggC.TwinB.UnreggC.CFG_ASAN 309200%uint63)); (440%uint63, (OpDropC.TwinB.OpDropC.op_drop_c 17%uint63 309200%uint63)); (442247048%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 247056%uint63)); (442247084%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 247092%uint63)); (442578308%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 578316%uint63)); (442578312%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 578320%uint63)); (442632760%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 632768%uint63)); (442632764%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 632772%uint63)); (442785164%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785160%uint63)); (442785168%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785164%uint63)); (442785176%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785172%uint63)); (442785880%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785876%uint63)); (442807112%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 807108%uint63)); (442810536%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 810532%uint63)); (442811024%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 811020%uint63))].
Definition mkctx (cl : list (int * template)) (ec : IMap.t sstate) (mr : sv) : ctx := Ctx ITAB (imap_of cl) ec CONTRACTS mr.

