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

Definition TPL_BLOB : PrimString.string := (StrLz.lz_dec "-$*PRPLPB0XXA0ZPUPLPB0YXA0ZPZPLPB0ZXA0ZP\PLPB0_XA0Z0#7-#2LQA1ZPQPLSA6L000OOOQA0ZP?T;#5#0;#5-$)RTLcA0ZRTB0SQX0PQZRTLaA0ZRXLQA0ZLOOOOOOQRXA1ZRZ8#6-)>ZA1Z#0IH1V8IH1V#@IH1V@9I1V#00Li00Dj#00Dj8NDj#HNDj07Ej#87Ej@2Oj#8>1k@@1k#A@1k@45k#H45k@95k#H95k0IF=Q#1IF=Q@FHOU#@FHOU@FH1V#8?K1V@?K1V#HAK1VDBK1V#8CK1V@CK1V#08L5V88L5V#H>O5V0?O5V#8?06V@?06V#0I16V0046VLPL000000@QLSQQ0040H0*2$OW1#<,000TLPL0014#/2$:-$@000VLPLP~Q\~UPLP~WQLPLP~_R~ZP~[P~\P~]PPQh~^Q~`P~aPLUCPTN0DM;SQLPCPXN0E5#.#F5#.#H5#.#I5#.-#(KM;SQLH5GhCPXN0M2#=-#.TN05N;SQLZCPTN06N;SQLQ0%1'5<SQL1)/-#%0180RCPXN0BD<3%<$6E4#.&137h2%9#22#.-$'QLPCQQLPCRQLPCSQLPCTQLPCUQLPCVQLPCWQN0==7hXPR0%.-#*>=7hQL0AKiCPXN0;>G0%1+XN0<>GhQL0)0)=>GhQLX0$75$(-##?>GhQLH;K1V0#2$=77#2#@9#2$A=1(7-#5XN0B=7hQP0RPCPTLPCTTN0C=7hRLR0/:-#+=7hQLQCRQN0E=7hQL@?2%-,N=7hQL88L50#2)2>7hQP11*$$6>0$>0)36#<%@>G0#<-#$TN0C>GhQL8EK1%*#D0#2+GNgCPXN0F0**%FB_0#1-#%?GhQN1H@GhPPU11%4#@1%4,QN0J@GhQPS11&#)@GhQL@B2&#-#'L@GhQLHWCPXN0M@4.##N2%(,XN0O@GhQPW0%(-#?7AGhQN1:AGhPLQCPTLQCTTN0;AGhRN1=AGhPL1S00,#A50,0$<*@AGhPN1A0#)#B0#)#C0#)#F0#)*3BGhPN170#));BGhPLZ0-5'CGhQL01*+#C5#.#G5#.$KC4+--#$LDGhQN1MDGhP@#71*2-#0:EGhXN1CMGhPLD;5\CPXN0EM1):(TN0E1H3#.#F0#.-##HP026RJKPOP1'3$PQ20*&QQPZ0#,&RQPQ0.8#J1181'OOOOW2,8#K>#712#/8#7#M>#7#N>#75#6(OWQLhH71<7*10YJKQOQ02,*-#%HP04RPPJKRORL01$#'PQL021166&QQLT1)5$LH01&?-#4SQLUCPXN0TQL[CPXN0UQL`CPXN0V31'9%WQL01)8'XQL000%)#Y2$4&ZQPX0$+%[QL0/%#\3#5%]QL01.(#^2)=%_QL0176&`QPV0#5#a2#>#b2#+-#'cQL0UHP00dJKSOS023)-#$HP04QPPJKTOU0228-#$HP04SPPJKUOZ0235-#*HP04\PPJKVO\LSH0@03-6-#+W01PJKWOdLPLL1MgQQ@5/*-#<WL002RL0BK1VP2RPP3RPP4RPPQXLRLRPQXPR52)>-#9000VP5RPP6RPP7RPP8RPLH3DaPRPLPLPL0#(-#0PLPLPP9RPP:RPP;RPP<RP@^_;$(:#2@#-$$-#2@^_QPQPPSPvz%PPQPPUPvz%QrQ1(*)NOOS08I1*.-#$Sz%RaQTz%SrR6$%3);'Tz%Tr2#2;#=%UrU@#%#=-#*VrW0=9T0=940Rz%WrZ@#%$.-#9XPQPPZPvz%YPRPPQ0Qez%ZPSPRPez%[LW01,3&uz%\0#,,L80Rvz%]LQ01&$&vz%^0#,+L000Tvz%_0#=(ZXvz%`13&/1#=%aRQ529((vz%bRR8#3%cr\@#%(7+da\Sz%eP\1./-#-fRQRSvz%gPQPP\Pvz%hRS8%4%iP\1*.+jRRRSvz%k61'6+Tvz%lPS0U8#5'mRQL@21*/+Svz%nPQ0S0&=%oRR8#>(0QPQ0S0&--#*1QPdPRUez%2Qr0R0Q011%)-#/3Q[4Q0$&P!H3Da0T0X[cLP)@,23+2@#/2*232;?21#$02'$0$8#7>#7#88#7,H5DaCPXN097#:23'?#:8$23)7%00002&/#;8$;#51$<#<8#9#61#9#=8#9#723+-8#9#81#9#?7#912&8#A>#7#B>#7#C>#7#D7#72*7#E8$/$H31,)#F8#:12<68%)127/21&.1$/%L1M02.&21?68$2@&<28?-#2lJKXOQKRORKSOSKTOUKUOZKVO\12/:(@AOgQQ6)572/:#Z32/9,LPL0DK5VML5(?+WPZPL000Q32,$'HQPZP@#32/5,R_Q&P!4=8i@,;19/14%:%P1T54%<+dPQPJKYOP11'-#241#1)OWQL<CO01,.#37#:)dXRPJKZ@#*1'6(H5DaQQ61,'@#%1'6%RLR61,8-#%OWP1RPP1RPP0T@#@1'4-##S_Q&P!H5Da2@)#1'4$~T11%=)NOO?QLU@$)1'7-#0P?TPL000RLQP@TPL00XLY~Qb@#85'*$FL45%6#G5#.*HL;SQQQ032<7$OO042=#J0#;#452)&0#;#K0#;#@52*81443@#%#;)1M;SQL@02%@'2M;SQ81($+CPTN07M;S24><%P0U71.$'ZPJK[@#,25-&L>LK04'-#952&,-#%WQL@5OjCPXN0:7#:#R02(1#;8#704%7#<8%(0#+04)/#=8#=#50#8#>9&;$7H05*9#?8#:%N930)1#@8#:12388'504+*#B>$.#C>$.#D7#7(M=6CI<12>+00##E8$%%OOO30#0$%#F7$%>1&9#G9$&#8526=0$&#H:%*;1&2#I8)@%94:0,(#J>*:#K8#7$0D35+78#;'<6CI<0#<#M7#<21''#N8#833)>51*63&=#7>#7#8>#7#9>#7#:7#7%P?T0#9#;8$0&@FHO04<?#<>%+#=8#7%8:M1++#>8#;01*,#?8#74,;#@7#;#R04>;#A9'421/7#B9%,#I16*=#C7#:%QQH53%<01$4#D9$&#@;$&#E8&$-#$33KB6M04B;I20(6#F8$%-##438:6I9>?CL15)8#G8$%-#1?SCPQL>SCQQL0QCRQLZCSQN0H6$+#T1.&#E64@72.;#F>#7#G>#7#H>#7#I7#731(:#J8$0$001)-#K8#:01<;#L>%?#M7#7>.%#N8$;31#?#O8#:$HK11@*630:(WQL0J506#:#17#:210#84&(31,0@#14&*$LF@##4&*1%@84&*$PG21/08#9#H1#994%>#I1#994%>#J1#994%>#K1#9@.'4%>'BRJK\@#(31+-#@000RHP13PJK]O?TL00XHP01PJK^O@TLPL0IGhQQ@51';732,-$)LWPPMWPPNWPLPL@5OjL06@jLPLPLD4DhP2XPP3XPP4XPP5X14((#L12#01#0)@FHOUP?3334-$/PP6XPP7XPP8XPP9XP@^_T_QRTLPez%4QRTLMQvz%5QRYLPez%6QRT22;5)uz%7QRT058,-#9uz%8QP@TPRVez%9Qa?TTz%:Qr?T00046V4-7&Sz%;017:34#;-#-vz%<Q[Y1P$&Q!86Dh:X0Z@-.36>%QQ=@##34=+d[QPJK_OP=2,9-$%PB0SQCSQLQB0SQCTQLRB0SQCUQLSB0SQCVQLTB0SQCW:2.%-#6XLUB0SQCPQLVB0SQCQQLWB0SQCRQLX2%>)ZCTQN0I6$=*Ud\RPJK`@#'11%,K]O?TK^O@T11+:-#3Yez%=Q%5Q%6Q%7Q%8Q%9Q%:Q%;Q31(?#R@-91(?#>@#)1(?%aOP@#21&,#Y21)*%ZCU:1&5*Vd`QPJKb@#81&5'Zez%>@#,1&5#S@-91&5#?@#)1&5#c@#>1&521:=%ZCV:1&>#W01&>#d@#81&>'[ez%?@#,1&>#T@-91&>#@@#)1&>#e@$(1&>#[22.;%ZCW:1')#X01')#f@#81')'\ez%@@#,1')#U@-91')#A@#)1')#g@$11')%\B013#$81'-$LZ0:*/74>')d`RPJKh@#81($']ez%A@#,1($#V@-91($#B@#)1($'iOPL]21($%ZCQ:1%/*RdhQPJKj@#81%/'^ez%B@#,1%/#W@-91%/#C@#)1%/#k61%/#^2181%ZCR:1%8#S01%8#l@#81%8'_ez%C@#,1%8#X@-91%8#D@#)1%8#m?1%8#_22+)063$71&##T01&##n@#81&#'`ez%D@#,1&##Y@-91&##E@#)1&##o@#+1&##`22<*05).71&,#U01&,$0Q@#81&-'aez%E@#,1&-#Z@-91&-#F@#)1&-$1Q@#41&.#a33/6$CU:1&7#V01&7#2@#91&7'bez%F@#,1&7#[@-91&7#5@#)1&7$3Q@#+61&017:760%*Ud\QPJK4@#91&%'Qez%G@#,1&%#\@-91&%#G@#)1&%#5@#>17:#b244005:5718%#W018%#6@#91&@'cez%H@#,1&@#]@-91&@#H@#)1&@#7@$)1&@%cB065:771'+#X01'+#8@#91'+'dez%I@#,1'+#^@-91'+#I@#)1'+#9@$21'+%dB015:981'/15:9#K85:9(hRPJK:@#91(&'eez%J@#,1(&#_@-91(&#J@#)1(&(;QOPLe21(&05:;71%1+Rd:QQPJK<@#91%2'fez%K@#,1%2#`@-91%2#K@#)1%2#=71%2#f218605:>71%;#S11%;#>@#91%;'gez%L@#,1%;#a@-91%;#L@#)1%;#?@##1%;#g22+105;#71&&#T11&&#@@#91&&'hez%M@#,1&&#b@-91&&#M@#)1&&#A@#,1&&#h22<5046,71&/#U11&/#B@#91&/'iez%N@#,1&/#c@-91&/#N@#)1&/#C@#51&/#i230$05;'71&8#V11&8#D@#91&8'jez%O@#,1&8#d@-91&8#O@#)1&8#E@#>1&8#j24#:05*%71'##W11'##F@#91'#(kez%0R@#+1'##e@-91'#6=#16;1'##G@$)1'#%kB065*&71',#X11',#H@#91','lez%1@#,1',#f@-91',#6@#)19-#I@#,7#33<?702,:77#<#V07#<#J@#91&.'Rez%2@#,1&.#g@-91&.#1@#)188#K@$2188%lB015;3818<15;3#L85;3):QRPJKL@#91(''mez%3@#,1('#h@-91('#2@#)1('(MQOPLm21('05;471%2+RdLQQPJKN@#91%2'nez%4@#,1%2#i@-91%2#3@#)1%2#O71%2#n218705;471%;#S11%;$0R@#81%;'oez%5@#,1%;#j@-91%;#4@#)1%;$1R?1%;#o22+205;471&&#T11&&#2@#91&&(0Qez%6@#,1&'#k@-:9>6@#)1&'#3@#,1&'#0030&35;671&1#U11&1#4@#91&1(1Qez%7@#,1&1#l@-:4#4@#)1&1#5@#61&1#194#?71&;#V11&;#6@#91&;(2Qez%8@#,1&;#m@-91&;#7@#)1&;#7@#@1&;#20#,35;=71''#W11''#8@#91''(3Qez%9@#,1''#n@-91''#8@#)1''#9@$,1''#30#,35<$71'1#X11'1#:@#91'1(4Qez%:@#,1'1#o@-91'1#9@#)1'1#;@$61'1#40#,<1'615*<#M85*<)LQRPJK<@#91(-(5Qez%;@#,1(-#0@-:=(>'#:@#)1(.(=ROPL501&'35*?71%5+Rd<RQPJK>@#91%5(6Qez%<@#,1%5#1@-:1%5#7@#*9@:#R@#==)0;02?+77$/#W07$/#@@#91&9'Sez%=@#,1&8#2@-:1&8#;@#)17-#A817-#60#,35<;7177#S1177#B@#91%>(7Qez%>@#,1%?#3@-:1%?#<@#)1%?#C@#%1%?#70#,35<@71&+#T11&+#D@#91&+(8Qez%?@#,1&+#4@-;=+(:@#)1&+#E@#/1&+#8331&05=&71&5#U11&5#F@#91&5(9Qez%@@#,1&5#5@-:1&5#>@#*9@%@#91&5#932=%05=*71&?#V11&?#H@#91&?(:Qez%A@#,1&?#6@-:1&?#?@#)1&?#I@$%1&?#:3468031%71'+#W11'+#J@#91'+(;Qez%B@#,1'+#7@-:1'+#@@#*9@5@$/1'+#;0#,35=271'5#X11'5#L@#91'5(<Qez%C@#,1'5#8@-:1'5#A@#*9@%@$91'5#<0#,<1':15=6#N85=6)<RRPJKN@#91(1(=Qez%D@#,1(1#9@-:1(1#B@#*:%$'ROPL=31(105=671%5,RdNRQPJK0S@#81%5(>Qez%E@#,1%5#:@-:1%5#C@#*:$<#S71%5#>319&05+>71%?#S11%?#2@#91%?(?Qez%F@#,1%?#;@-:1%?#D@#*:$6@#%1%?#?32,%05+>71&+#T11&+#4@#91&+(@Qez%G@#,1&+#<@-:1&+#8@#*=)02#S@$(=/?903118=/?507$)#6@#91'$'Tez%H@#,1'##=@-:1'##E@#*:$6@#/18,#@331/05=?7186#U1186#8@#91&4(AQez%I@#,1&5#>@-:1&5#F@#*:$&@#91&5#A319&05=?71&?#V11&?#:@#91&?(BQez%J@#,1&?#?@-:1&?#G@#*:#4@$%1&?#B347#05=?71'+#W11'+#<@#91'+(CQez%K@#,1'+#@@-:1'+#H@#*9@1@$/1'+#C0#,32?071'5#X11'5#>@#91'5(DQez%L@#,1'5#A@-:1'5#I@#)1'5#?@$91'5#D0#,<1':15=?4=56<-#$OOWQdNRRPJK@@#91(1(EQez%M@#,1(1#B@-:1(1#J@#*:&*'SOPLE31(105=?71%5+Rd@SQPJKB@#91%5(FQez%N@#,1%5#C@-:1%5#K@#*:%>81%5#F319&05=?71%?#S11%?#D@#91%?(GQez%O@#,1%?#D@-:1%?#L@#*:%4@#%1%?#G32,%05=?71&+#T11&+#F@#91&+)HQez%0S@#+1&+#E@-:1&+#M@#*:%*@#/1&+#H32=.05+>71&5#U11&5#H@#91&5(IQez%1@#,1&5#F@-:1&5#N@#*:$>@#91&5#I331#05+>71&?#V11&?#J@#91&?(JQez%2@#,1&?#G@-:1&?#9@#)7%3&KSOP13?:7=3@,#Q0=447#L@#91%*'Uez%3@#,1%)#H@-:1%)#O@#*9@(@$%17(#J345)05<'7172#W1172#N@#91'*(KQez%4@#,1'+#I@-:1'+<=:':69>@@$/1'+#K0#,35<'71'5#X11'5$0T@#81'5(LQez%5@#,1'5#J@-81'501&50=:,3#88=:530=:/19=:.:3=99?9=:,2$0H?=:+8@$61)518@(?1):'UPJK1@#21):,LPL@7HhQQ@5=:(6#W6=9)5$=W1=9(;&?WPL0=:$60=9)6-#6=LKSLQPBWPPCWPPDWPPEWPPFWPR\RX1$-1=9*#-$%=LKSLPRTLQRTPGWPPHWPPIWPPJWP@^_U_QRTLMQez%6@#,1.)#K01.)$KW@-21@<#3@#)3'.$2T3=<>%91/)#=@#$=<$9%cCP;=<#?1%(9=<#?%@HJ?=;@,@$412);9=?99<4*Sd\YPJK3@#610&$HJ@#)10&$NV110&'0WPRT410&-#5PZPRTP3WPP4WPP5WPP6WPP7WPLPLc610$-$&PPZPLPRTRTRTP8WPP9WPP:WPP;WP@^_V_QLMQRTuz%7S@##1/=(X1P$&L01/=#<@-31/=#:@#)1/=$4T6=73<06>974$4#R04$4#5@#92;7'Vez%8@#,1@/#M@-:30+#;@#)1%2#671%23=8&.06>571%;#S01%;#7@#91%;'Wez%9@#,1%;#N@-:1%;#<@#)1%;#8@##1%;3=87)06>071&&#T01&&#9@#91&&'Xez%:@#,1&&#O@+91&&#041&&#1@#>1&&<=>8,$KL5=>7%#A7=?2')[RPJK:T@#,=>7&%N1263$=&PN139#2#49#2#59#2#69#2#79#273+%%PN173*;%PN17=>:,%PN173+(%PN173+#%PN17=>95%PN17=>9/%PN173+;#P@//=>9'$N17=>8>%PN17=>89%PN17=>84%PN17=>8/%PN17=>8*%PN17=>8#%PN17=>78%PN173<2%PN17=>7*%PN17=>7%%PN17=>6:%PN173=<%PN17=>6-%PN173>&#P@$3=>6%$N17=>52#P@#@=>52$N184$#$N172);%PN17=5%1%PN17=/;0%PN17=+&&%PN17=%9@%PN17:/3%PN175$>24.=@,;=>9%#0@%*=>9%#B@##=>9%#C@##=>9%#D@##=>9%#E@##=>9%#F@..=>9%'0SJK;@#+3+>-#%0TK^O1TLPP2TP92*<65&5,3TPP4TPP5T0=>8,-#7R[LPP6TPP7TPP8TPP9TPP:TPP;TPP<T:=>8.#P1=>8*4>#8<-#.PP=TPP>TPP?TPP@TP@^_W_43/?-#-P1TPRWez%;Sa0TTz%<Sr0>=>67-#)=S[V1P$&0R!0IGhGT@-030@'K:TOP@)93.,32$)8>##:@#$2$@@&&1@9*d1TePJK<@#;150520;@#&150#53>#?-$LQ@#)15447&*&>LKS:7&)<15/%X_Q07%@-#%[R10R$&1R!@7H@-813>@#06<,&<TQW73-.73-+73-(73-%73,@73,=73,:%JK=@%-1+*$RT@#*2-<36?001+#66?/<1+(-#+Y_Q%7S[Q10R$&2R!@HJ@-31+%12@7$JL5>*%85#.&ML;S6>$2%0>%0*0#>#26>%//#>85+,+VPJK>TOPP3>$6-41*0'OWQP@@##2&##A@##2&#22(,92&#22(,92&#);TUPJK?@#41-9%L8H@#*>&-*%2TP21->*LRP0TPLR3>&,?$5T<3(=(ZPLPLS00+<3(-51/#-#+P=TP@^_Z_Q&0R!LINgD@)#1-/31+2@%9>&@%%QQ2@##64=@##>&@>-##[RPJK@TOPLG2413885'#R04109>&&&#^01,%>5129>%0>11-17#7&R]CP<84?-$)3SCPQL<SCQQL9SCRQLJQCSQL0QCTQL3SCUQL1SCVQL>SCWQ9>%*=-#(XL>SCPQL?SCQQLDS0=/7>-#)CSQL?SCTQL@SCUQL56%&75).%XL058#/72.<#R2176>4>-84?$240084?%$L3@#$4='>>(4>43-%8$0>1801#7818.1#7818,2>**'918+(\cPJKA@#(18*#L@#.>$2<-##MVPPNVPPOVP@##>$2<98?(?>$2<317?(LPP7WP68?,(@^_[_Q0>$20(OQvz%>48?+)[U1P$&30>#92$;W@-1>((#,6TQPJKBTOP11/30=(?3#Q2=(?3#R2=(?3#S2=(?3#T2>$.,$UQ17</#V27</=>$.>07<?#P2=@#(@#%80.)ATRPJKC@#(1+4)_[_Q%=Q<1&?#4@-91&?,8TQPJKDTOP=1$&0=@2,@#%8.7)CTQPJKE@#-1$/#>=1$/#5@-91$/(_QPJKF@#-1$.2160?>%/001$7#G@#-1$7#?=1$7#6@-91$7(aQPJKH@#51$70>#3/@#%>%-;01$@#I@#-1$@#@=1$@#7@-91$@(cQPJKJ@#>1$@0>$%/@#%>%,(01%+#K@#-1%+#A=1%+#8@-91%+(eQPJKL@$)1%+0==0-@#%>%*301%4#M@#-1%4#B=1%4#9@-91%4(gQPJKN@$21%40==@?@#5>%(>)CTRPJKO@#-1&/#C=1&/#:@-91&/+iQPJK0UOP1=>1@@#%>%'+*OTQPJK1U@#,1#:#D=1#:#;@-91#:(kQPJK271#:0=>@:@#%>%%601$%#3@#-1$%#E=1$%#<@-91$%(mQPJK4@##1$%0=?1=@#%>%$#01$.#5@#-1$.#F=1$.#=@-91$.*2TQPJK6U<5=8013/9860)ATQPJK7@#-1$##G=1$##>@-91$#(oQPJK8@#,13/0=@2,@#%>%1/0138#9@#-1$7#H=1$7#?@-91$7#10=734@#51$80>#$$@#%>%/901%##;@#-1%##I=1%##@@-91%##50=@>(@#>1%#0>#4%@#%>$:@01%,#=@#-1%,#J=1%,#A@-91%,#70=@=7@$)1%,0=<>*@#%>$9,01%5#?@#-1%5#K=1%5#B@-91%5#90=@=(@$21%50==0=@#5>$76)OTRPJKA@#-1&0#L=1&0#C@-91&0#;0=@=)%UOP1==??@#%>$5@)AUQPJKC@#-1#;#M=1#;#D@-91#;#=0=@:,71#;0=>0:@#%>$4+01$&#E@#-1$&#N=1$&#E@-91$&#?0=@7/@##1$&0=>?>@#%>$2401$/#G@#-1$/#O=1$/#F@-91$/#A0=@42@#,1$/0=?1-@#%>$0=01$8#I@#-1$8$0R<1$8#G@-91$8)CQQPJKJ@#51$80=@#%@#%>$/(01%##K@#-1%##1=1%##H@-91%#([QPJKL=6-,3;8$>>1-916-5#M@#-1$+#2=1$+#I@-91$+#E0=@.1@#>14,0>#$/@#%>$<:0145#O@#-1%,#3=1%,#J@-91%,#G0=@-@#V@$(1%,0=<?0@#%>$;%01%5$1V@#,1%5#4=1%5#K@-91%5#K0=@-1@$21%50==2%@#5>$'@)AURPJK3@#-1&0#5=1&0#L@-91&0#M0=@-0%VOP1=>#'@#%>$&+)3VQPJK5@#-1#;#6=1#;#M@-91#;#O0=@*071#;1=>1@@#%>$$501$'#7@#-1$'#7=1$'#N@-:82-0=66-@#$1$'1=?#'@#%>#@@01$1#9@#-1$1#8=1$1#O@-91$1#30=63=@#.1$11=?26@#%>#?,01$;#;@#-1$;#9=1$;#00>24$@-49#60=61/@#81$;1=@$1@#%>#=601%'#=@#-1%'#:=1%'#1@-91%'#70=6.?@$$1%'1=@46@#%>#;@01%1#?@#-1%1#;=1%1#2@-91%1)9RQPJK@@$.1%11=;='@#%>#:,01%;#A@#-1%;#<=1%;#3@-91%;#308@8#V@#1='46?>/2006/=#C@#-1$5#==1$5#4@-91$5#;0=?;/@$81501=<?5@#5>$*+)3VRPJKE@#-1&7#>=1&7#5@-91&7#=0=?;1%VOP2==07@#%>$(2)EVQPJKG@#-1#<#?=1#<#6@-91#<#A0=?8.81#<1==?3@#%>#3#01$(#I@#-1$(#@=1$(#7@-91$(#C0=?5+@#%1$(1=>09@#%>#1*01$2#K@#-1$2#A=1$2#8@-91$2#E0=?2(@#/1$21=>@+@#%>#/101$<#M@#-1$<#B=1$<#9@-91$<)GRQPJKN@#91$<1=?2'@#%>#-801%(#O@#-1%(#C=1%(#:@-91%(#I0=?.&#W@$$1%(1=@$-@#%>#+?01%2$1W@#,1%2#D=1%2#;@-91%2#K0=?-7@$/1%21=;,4@#%>#*(01%<#3@#-1%<#E=1%<#<@-91%<#M0=?-*@$91%<1=;=0@#5>#(/)EVRPJK5@#-1&8#F=1&8#=@-91&8,ORQPJK6WOP2=<.2@#%>#&6)5WQPJK7@#-1#<#G=1#<#>@-:28@0>*9+#W@#:=-16?>.>=060+#9@#-1$>#H=1$>#?@-91$>)1SQPJK:813:1==/,@#%>#4;014&#;@#-1$(#I=1$(#@@-:71&(SQPJK<@#%1$(1==>2@#%>#3$01$2#=@#-1$2#J=1$2#A@-:9%@(SQPJK>@#/1$21=>0$@#%=@=*01$<#?@#-1$<#K=1$<#B@-:9%-(SQPJK@@#91$<1=>?>@#%=@;101%(#A@#-1%(#L=1%(#C@-:83%0=>;=@$%1%(1=?2&@#%=@9801%2#C@#-1%2#M=1%2#D@-:81>0=>;0@$/1%21=::'@#%=@7?01%<#E@#-1%<#N=1%<#E@-91%<#?0=>;#@$91%<1=;-#@#5=@6()5WRPJKG@#-1&8#O=1&8#F@-:9'60=>;&%WOP2=;<%@#%=@4/)GWQPJKI@#-1#<$0S<1#<#G@-:9',0=>8#81#<1=<,?@#%=@2601$(#K@#-1$(#1=1$(#H@-:9&@(SQPJKL@#%1$(1=<<'@#%=@0=01$2#M@#-1$2#2=1$2#I@-:26,09&6@#;6.03=3-&?>.+)06.9#O@#-1%)#3=1%)#J@-:96=0=>1;#X@#.1491===>@#%=@?-015%$1X@#,1$<#4=1$<#K@-:703(SQPJK2@#91$<1=>/:@#%=@=401%(#3@#-1%(#5=1%(#L@-:9%-(SQPJK4@$%1%(12(1@#%=@+401%2#5@#-1%2#6=1%2#M@-:9$'(SQPJK6@$/1%2#M0#,@#%=@);01%<#7@#,1%<+RTLNQez%?=1&%#N@-#1&%01%(@#7=@(.3=6=%@#4=?)'@$51((#N0#,?1(-'UPJK8@#(1(-@#/=@($#>2=?*>$@V8=@($-#6FKKSLQPCVPPDVPPEVPPFVPPGVPR^RZ8=@($$FK5=94;-#,HVPPIVPPJVPPKVP@^_\_0=6<9&ez%@=1,:#O01,:$LV@,91,:%QQ1@#$=>&7#@09;<#X@#%=@&@#F@##=8$;#L0=;5.@$@=@&@@#=10;&0QCP:4)(+QdATYPJK:@#,1.-@#+=@&+$OU11.-$1V==@&+-#/4VPP5VPP6VPP7VPP8VPLPLa@#&=@&+-#/9VPP:VPP;VPP<VP@^_]_QLO0=@&+#A51.&-#%T1P$&0T!86Dh=@,:1.&@##29#*5SQPJK;X@$.=77@?>,''04>'#<@#-3+3#8=1>6#101%2@-4<?,)SQPJK=X@#%>&&>0=51$#>@#-1#2#9=1#2#2@-91#2#40=1($#X6=51%?>#&'01#;#@@#-1#;#:=1#;#3@)*1#;@&?=;@-1=9>*712'$R[?29=#I?29=*d<TSPJKA@#(1$;7=;%5@#,=9>76=;>/?=9>7@#+==9'0#0$@F@#/==9+'^_Q&10=+#6@-2=;>-%QQA@##=@5.,d:TQPJKBXO;==5)$L>1>%(68==514=?&68==59(QRXCPX9==5>(QR\CPX9==6%3=<3:%CPX9==60%QL50#87==66+QL@7HhCPX9==6>5=:<;81/0-#+ZCPQL<;JD3@8>5;hCQW9=;'0#R@#/=<?/@&>==9*(\aPJKC@$6153+HTPPITPPJ@#%153-#&NTPPOTPP0UPP1U@#5153-#/2UPP3UPP4UPP5UP@^___Q&20153$6U@,9=<(122:1#?72:10148$DX@)<=>:'2==&;812-*d8X_PJKE@#*48$$P0@#*==<?%1TP2==$+8=>5)122)>===)453/&GKKS:53.5==$'-#,P>TP@^_`_Q&OS!@7HhAT@,:6,+#D3460;5+0$EX@%0=>38#F@%#1)/$RT@#)1)/45.301)(65.2<1)-,a_Q&0T!@HJ@-$1)-?3;&?==4$@#%3;&)EXSPJKG@#+6#+@#,28)61';?28):1'7@#-==(1<1'<#b01<)%86D@,<1'<@##28#)BXQPJKH>3992=>-*@#5399#Z>399#^@%-399138@@$(=>.-?2'(@#%29-)AT[PJKI@$,10&+BTPPCTPPD@#%10&5360$PK@#010&)LTPPMTP237)&@^_c02$@(86Dh0U@,?2$@@&8=?$69>%863=@)'@%7=?$1@##1/$@%'=?$1);T]PJKJ@#13#;@#%>$<?62.@)@5OjR]L357-?3#7:>$<?@#+2.<$d_8=4>7-##T1P$&4T!0IG@-#3$+@)9>&?0*dIX^PJKK@#)7#2#d02(#@,?1(823%'#<73%'-#$>TQPJKLXOPP=@##2:-)JXQPJKM@#+2:-@#,>#1>%0TP21;5&LRLR5>#1<56@'31;:&ZPPR71;$%LPL;>$-=-#'@^_e_Q&4T!LINg>@,;1:5@#)1%@)KXQPJKN@#)13>#e013>@)(0#@&67-712<4(H5<SQL03;>$264#.&B>Gh0:)/)TN0C>Gh3>'2+%>Gh2>#@/-#1N0F@GhQd>TVPJKOXOPL0BOiCP;>'=*&LDN90>,$19>'=+3$49>'=.%0IN0>'2*8>'=.13'28>'=-&L4DE04>993'30$193'3$8M1%@93'60$193'6$8H1>'8@93'8)XZPJK0Y@#47)+(@MNgQQ7>)1761=3+ETPPFTPPG4>$<1-##LRPITPLPPKT34%+%LNR@#,>$<,57*1*P2UP@^_f0>$<,+D8Ng4U0ZZ@,31=8@##212,OXQPJK1YOP@#*1&,@#/1%@1897$PA2203*LRPCTPLP71&<$NR@#$20.548:*PLTP@^_g020.*D8NgNT0X@,41%6@#/1$9$_g02/,7.?"%pstring).
Definition TPL_ALL : list template := TplDec.TplDec.dec_tpls TPL_BLOB.
Local Abbreviation NT i := (TplDec.TplDec.nth_tpl TPL_ALL i) (only parsing).
Lemma TPL_ALL_length : List.length TPL_ALL = 148%nat.
Proof. vm_cast_no_check (@eq_refl nat 148%nat). Qed.

Definition T_DRV2 : sstate := Eval vm_compute in (t_st (TplDec.TplDec.nth_tpl TPL_ALL 0)).

Definition T_OPEN_ := Eval vm_compute in (NT 1).
Definition T_OPENERR_ := Eval vm_compute in (NT 2).
Definition T_SW_OPEN__0_1 := Eval vm_compute in (NT 3).
Definition T_SW_OPEN__0_10 := Eval vm_compute in (NT 4).
Definition T_SW_OPEN__0_11 := Eval vm_compute in (NT 5).
Definition T_SW_OPEN__0_12 := Eval vm_compute in (NT 6).
Definition T_SW_OPEN__0_13 := Eval vm_compute in (NT 7).
Definition T_SW_OPEN__0_14 := Eval vm_compute in (NT 8).
Definition T_SW_OPEN__0_15 := Eval vm_compute in (NT 9).
Definition T_SW_OPEN__0_16 := Eval vm_compute in (NT 10).
Definition T_SW_OPEN__0_17 := Eval vm_compute in (NT 11).
Definition T_SW_OPEN__0_18 := Eval vm_compute in (NT 12).
Definition T_SW_OPEN__0_19 := Eval vm_compute in (NT 13).
Definition T_SW_OPEN__0_2 := Eval vm_compute in (NT 14).
Definition T_SW_OPEN__0_20 := Eval vm_compute in (NT 15).
Definition T_SW_OPEN__0_21 := Eval vm_compute in (NT 16).
Definition T_SW_OPEN__0_22 := Eval vm_compute in (NT 17).
Definition T_SW_OPEN__0_23 := Eval vm_compute in (NT 18).
Definition T_SW_OPEN__0_24 := Eval vm_compute in (NT 19).
Definition T_SW_OPEN__0_25 := Eval vm_compute in (NT 20).
Definition T_SW_OPEN__0_26 := Eval vm_compute in (NT 21).
Definition T_SW_OPEN__0_27 := Eval vm_compute in (NT 22).
Definition T_SW_OPEN__0_28 := Eval vm_compute in (NT 23).
Definition T_SW_OPEN__0_29 := Eval vm_compute in (NT 24).
Definition T_SW_OPEN__0_3 := Eval vm_compute in (NT 25).
Definition T_SW_OPEN__0_30 := Eval vm_compute in (NT 26).
Definition T_SW_OPEN__0_31 := Eval vm_compute in (NT 27).
Definition T_SW_OPEN__0_32 := Eval vm_compute in (NT 28).
Definition T_SW_OPEN__0_33 := Eval vm_compute in (NT 29).
Definition T_SW_OPEN__0_34 := Eval vm_compute in (NT 30).
Definition T_SW_OPEN__0_35 := Eval vm_compute in (NT 31).
Definition T_SW_OPEN__0_36 := Eval vm_compute in (NT 32).
Definition T_SW_OPEN__0_37 := Eval vm_compute in (NT 33).
Definition T_SW_OPEN__0_38 := Eval vm_compute in (NT 34).
Definition T_SW_OPEN__0_39 := Eval vm_compute in (NT 35).
Definition T_SW_OPEN__0_4 := Eval vm_compute in (NT 36).
Definition T_SW_OPEN__0_40 := Eval vm_compute in (NT 37).
Definition T_SW_OPEN__0_41 := Eval vm_compute in (NT 38).
Definition T_SW_OPEN__0_42 := Eval vm_compute in (NT 39).
Definition T_SW_OPEN__0_43 := Eval vm_compute in (NT 40).
Definition T_SW_OPEN__0_44 := Eval vm_compute in (NT 41).
Definition T_SW_OPEN__0_45 := Eval vm_compute in (NT 42).
Definition T_SW_OPEN__0_46 := Eval vm_compute in (NT 43).
Definition T_SW_OPEN__0_47 := Eval vm_compute in (NT 44).
Definition T_SW_OPEN__0_48 := Eval vm_compute in (NT 45).
Definition T_SW_OPEN__0_49 := Eval vm_compute in (NT 46).
Definition T_SW_OPEN__0_5 := Eval vm_compute in (NT 47).
Definition T_SW_OPEN__0_50 := Eval vm_compute in (NT 48).
Definition T_SW_OPEN__0_51 := Eval vm_compute in (NT 49).
Definition T_SW_OPEN__0_52 := Eval vm_compute in (NT 50).
Definition T_SW_OPEN__0_53 := Eval vm_compute in (NT 51).
Definition T_SW_OPEN__0_54 := Eval vm_compute in (NT 52).
Definition T_SW_OPEN__0_55 := Eval vm_compute in (NT 53).
Definition T_SW_OPEN__0_56 := Eval vm_compute in (NT 54).
Definition T_SW_OPEN__0_57 := Eval vm_compute in (NT 55).
Definition T_SW_OPEN__0_58 := Eval vm_compute in (NT 56).
Definition T_SW_OPEN__0_59 := Eval vm_compute in (NT 57).
Definition T_SW_OPEN__0_6 := Eval vm_compute in (NT 58).
Definition T_SW_OPEN__0_60 := Eval vm_compute in (NT 59).
Definition T_SW_OPEN__0_61 := Eval vm_compute in (NT 60).
Definition T_SW_OPEN__0_62 := Eval vm_compute in (NT 61).
Definition T_SW_OPEN__0_63 := Eval vm_compute in (NT 62).
Definition T_SW_OPEN__0_7 := Eval vm_compute in (NT 63).
Definition T_SW_OPEN__0_8 := Eval vm_compute in (NT 64).
Definition T_SW_OPEN__0_9 := Eval vm_compute in (NT 65).
Definition T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d := Eval vm_compute in (NT 66).
Definition T_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557 := Eval vm_compute in (NT 67).
Definition T_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557 := Eval vm_compute in (NT 68).
Definition T_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 := Eval vm_compute in (NT 69).
Definition T_SW_OPENERR__1 := Eval vm_compute in (NT 70).
Definition T_SW_OPENERR__10 := Eval vm_compute in (NT 71).
Definition T_SW_OPENERR__11 := Eval vm_compute in (NT 72).
Definition T_SW_OPENERR__12 := Eval vm_compute in (NT 73).
Definition T_SW_OPENERR__13 := Eval vm_compute in (NT 74).
Definition T_SW_OPENERR__14 := Eval vm_compute in (NT 75).
Definition T_SW_OPENERR__15 := Eval vm_compute in (NT 76).
Definition T_SW_OPENERR__16 := Eval vm_compute in (NT 77).
Definition T_SW_OPENERR__17 := Eval vm_compute in (NT 78).
Definition T_SW_OPENERR__18 := Eval vm_compute in (NT 79).
Definition T_SW_OPENERR__19 := Eval vm_compute in (NT 80).
Definition T_SW_OPENERR__2 := Eval vm_compute in (NT 81).
Definition T_SW_OPENERR__20 := Eval vm_compute in (NT 82).
Definition T_SW_OPENERR__21 := Eval vm_compute in (NT 83).
Definition T_SW_OPENERR__22 := Eval vm_compute in (NT 84).
Definition T_SW_OPENERR__23 := Eval vm_compute in (NT 85).
Definition T_SW_OPENERR__24 := Eval vm_compute in (NT 86).
Definition T_SW_OPENERR__25 := Eval vm_compute in (NT 87).
Definition T_SW_OPENERR__26 := Eval vm_compute in (NT 88).
Definition T_SW_OPENERR__27 := Eval vm_compute in (NT 89).
Definition T_SW_OPENERR__28 := Eval vm_compute in (NT 90).
Definition T_SW_OPENERR__29 := Eval vm_compute in (NT 91).
Definition T_SW_OPENERR__3 := Eval vm_compute in (NT 92).
Definition T_SW_OPENERR__30 := Eval vm_compute in (NT 93).
Definition T_SW_OPENERR__31 := Eval vm_compute in (NT 94).
Definition T_SW_OPENERR__32 := Eval vm_compute in (NT 95).
Definition T_SW_OPENERR__33 := Eval vm_compute in (NT 96).
Definition T_SW_OPENERR__34 := Eval vm_compute in (NT 97).
Definition T_SW_OPENERR__35 := Eval vm_compute in (NT 98).
Definition T_SW_OPENERR__36 := Eval vm_compute in (NT 99).
Definition T_SW_OPENERR__37 := Eval vm_compute in (NT 100).
Definition T_SW_OPENERR__38 := Eval vm_compute in (NT 101).
Definition T_SW_OPENERR__39 := Eval vm_compute in (NT 102).
Definition T_SW_OPENERR__4 := Eval vm_compute in (NT 103).
Definition T_SW_OPENERR__40 := Eval vm_compute in (NT 104).
Definition T_SW_OPENERR__41 := Eval vm_compute in (NT 105).
Definition T_SW_OPENERR__42 := Eval vm_compute in (NT 106).
Definition T_SW_OPENERR__43 := Eval vm_compute in (NT 107).
Definition T_SW_OPENERR__44 := Eval vm_compute in (NT 108).
Definition T_SW_OPENERR__45 := Eval vm_compute in (NT 109).
Definition T_SW_OPENERR__46 := Eval vm_compute in (NT 110).
Definition T_SW_OPENERR__47 := Eval vm_compute in (NT 111).
Definition T_SW_OPENERR__48 := Eval vm_compute in (NT 112).
Definition T_SW_OPENERR__49 := Eval vm_compute in (NT 113).
Definition T_SW_OPENERR__5 := Eval vm_compute in (NT 114).
Definition T_SW_OPENERR__50 := Eval vm_compute in (NT 115).
Definition T_SW_OPENERR__51 := Eval vm_compute in (NT 116).
Definition T_SW_OPENERR__52 := Eval vm_compute in (NT 117).
Definition T_SW_OPENERR__53 := Eval vm_compute in (NT 118).
Definition T_SW_OPENERR__54 := Eval vm_compute in (NT 119).
Definition T_SW_OPENERR__55 := Eval vm_compute in (NT 120).
Definition T_SW_OPENERR__56 := Eval vm_compute in (NT 121).
Definition T_SW_OPENERR__57 := Eval vm_compute in (NT 122).
Definition T_SW_OPENERR__58 := Eval vm_compute in (NT 123).
Definition T_SW_OPENERR__59 := Eval vm_compute in (NT 124).
Definition T_SW_OPENERR__6 := Eval vm_compute in (NT 125).
Definition T_SW_OPENERR__60 := Eval vm_compute in (NT 126).
Definition T_SW_OPENERR__61 := Eval vm_compute in (NT 127).
Definition T_SW_OPENERR__62 := Eval vm_compute in (NT 128).
Definition T_SW_OPENERR__63 := Eval vm_compute in (NT 129).
Definition T_SW_OPENERR__64 := Eval vm_compute in (NT 130).
Definition T_SW_OPENERR__65 := Eval vm_compute in (NT 131).
Definition T_SW_OPENERR__7 := Eval vm_compute in (NT 132).
Definition T_SW_OPENERR__8 := Eval vm_compute in (NT 133).
Definition T_SW_OPENERR__9 := Eval vm_compute in (NT 134).
Definition T_SW_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1 := Eval vm_compute in (NT 135).
Definition T_SW_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1 := Eval vm_compute in (NT 136).
Definition T_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528 := Eval vm_compute in (NT 137).
Definition T_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528 := Eval vm_compute in (NT 138).
Definition T_SW_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 := Eval vm_compute in (NT 139).
Definition T_SW_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 := Eval vm_compute in (NT 140).
Definition T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 := Eval vm_compute in (NT 141).
Definition T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka := Eval vm_compute in (NT 142).
Definition T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63 := Eval vm_compute in (NT 143).
Definition T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka := Eval vm_compute in (NT 144).
Definition R_OPEN__0 : template := (Tpl (nth 0 (match c_apply (CtrS.c_open_dir 827812%uint63) (t_st T_OPEN_) return list sstate with Some l => l | None => @nil sstate end) (t_st T_OPEN_)) (VL (wp 0%uint63))).
Definition R_OPEN__1 : template := (Tpl (nth 1 (match c_apply (CtrS.c_open_dir 827812%uint63) (t_st T_OPEN_) return list sstate with Some l => l | None => @nil sstate end) (t_st T_OPEN_)) (VL (wp 0%uint63))).
Definition R_OPEN__2 : template := (Tpl (nth 2 (match c_apply (CtrS.c_open_dir 827812%uint63) (t_st T_OPEN_) return list sstate with Some l => l | None => @nil sstate end) (t_st T_OPEN_)) (VL (wp 0%uint63))).
Definition R_OPEN__3 : template := (Tpl (nth 3 (match c_apply (CtrS.c_open_dir 827812%uint63) (t_st T_OPEN_) return list sstate with Some l => l | None => @nil sstate end) (t_st T_OPEN_)) (VL (wp 0%uint63))).
Definition R_OPEN__4 : template := (Tpl (nth 4 (match c_apply (CtrS.c_open_dir 827812%uint63) (t_st T_OPEN_) return list sstate with Some l => l | None => @nil sstate end) (t_st T_OPEN_)) (VL (wp 0%uint63))).
Definition E_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 : sstate := Eval vm_compute in (t_st (TplDec.TplDec.nth_tpl TPL_ALL 145)).
Definition E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63_1 : sstate := Eval vm_compute in (t_st (TplDec.TplDec.nth_tpl TPL_ALL 146)).
Definition E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1 : sstate := Eval vm_compute in (t_st (TplDec.TplDec.nth_tpl TPL_ALL 147)).

Lemma templates_wfb : forallb sstate_wfb [(t_st R_OPEN__0); (t_st R_OPEN__1); (t_st R_OPEN__2); (t_st R_OPEN__3); (t_st R_OPEN__4)] && forallb (fun t => sstate_wfb (t_st t)) TPL_ALL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition CONTRACTS : IMap.t contract := imap_of [(410%uint63, (MemcpyC.TwinB.MemcpyC.amemcpy_c ImgBoth.SEGS 386080%uint63)); (414%uint63, (Memcpy0C.TwinB.Memcpy0C.amemcpy0_c 386080%uint63)); (421%uint63, (StrnlenC.TwinB.StrnlenC.astrnlen_c 319880%uint63)); (425%uint63, (FprintfSC.TwinB.FprintfSC.afprintf_s_pre_c ImgBoth.SEGS (wlit 126819%uint63) 3%uint63 10%uint63 333440%uint63)); (426%uint63, (FprintfSC.TwinB.FprintfSC.afprintf_s_pre_c ImgBoth.SEGS (wlit 126840%uint63) 3%uint63 10%uint63 333440%uint63)); (429%uint63, (UnreggC.TwinB.UnreggC.unregg_c UnreggC.TwinB.UnreggC.CFG_ASAN 309200%uint63)); (440%uint63, (OpDropC.TwinB.OpDropC.op_drop_c 17%uint63 309200%uint63)); (443%uint63, (AmallocNnC.TwinB.AmallocNnC.amalloc_nn_c UnivBoth.UNIV 389196%Z 388520%uint63)); (446%uint63, (ReadDirC.TwinB.ReadDirC.aread_dir_c ReadC.TwinB.ReadC.CFG_ASAN 326536%uint63)); (442247048%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 247056%uint63)); (442247084%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 247092%uint63)); (442578208%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 578216%uint63)); (442578212%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 578220%uint63)); (442578308%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 578316%uint63)); (442578312%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 578320%uint63)); (442632760%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 632768%uint63)); (442632764%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 632772%uint63)); (442785164%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785160%uint63)); (442785168%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785164%uint63)); (442785176%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785172%uint63)); (442785880%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785876%uint63)); (442807112%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 807108%uint63)); (442810536%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 810532%uint63)); (442811024%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 811020%uint63))].
Definition mkctx (cl : list (int * template)) (ec : IMap.t sstate) (mr : sv) : ctx := Ctx ITAB (imap_of cl) ec CONTRACTS mr.

Lemma FORK_OPEN_ : c_apply (CtrS.c_open_dir 827812%uint63) (t_st T_OPEN_) = Some [(t_st R_OPEN__0); (t_st R_OPEN__1); (t_st R_OPEN__2); (t_st R_OPEN__3); (t_st R_OPEN__4)].
Proof. vm_compute. reflexivity. Qed.
