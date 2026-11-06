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

Definition TPL_BLOB : PrimString.string := (StrLz.lz_dec "-#<PRPLPB0XXA0ZPUPLPB0YXA0ZP\PLPB0_XA0Z0#7-,*LQA1ZPQ`PTPLSA2A0ZPQPLSA6L000OOOQA0ZRSLWA0ZRSB0QQX0PQZRVLWA0ZLOOOOOOQRVA1Z#0IH1V8IH1V#@IH1V@9I1V#00Li00Dj#00Dj8NDj#HNDj07Ej#87Ej@2Oj#8>1k@@1k#A@1k@45k#H45k@95k#H95k0IF=Q#1IF=Q@FHOU#@FHOU@FH1V#8?K1V@?K1V#HAK1VDBK1V#8CK1V@CK1V#08L5V88L5V#H>O5V0?O5V#8?06V@?06V#0I16V0046VLPL000000@QLSQQ0040H0*2$OW1#<,000TLPL0014#/2$:-$@000VLPLP~Q\~UPLP~WQLPLP~_R~ZP~[P~\P~]PPQ`~^Q~`P~aPLUCPTN0DM;SQLPCPXN0E5#.#F5#.#H5#.#I5#.-#(KM;SQLH5GhCPXN0M2#=-#.TN05N;SQLZCPTN06N;SQLQ0%1'5<SQL1)/-#%0180RCPXN0BD<3%<$6E4#.&137h2%9#22#.-$'QLPCQQLPCRQLPCSQLPCTQLPCUQLPCVQLPCWQN0==7hXPR0%.-#*>=7hQL0AKiCPXN0;>G0%1+XN0<>GhQL0)0)=>GhQLX0$75$(-##?>GhQLH;K1V0#2$=77#2#@9#2$A=1(7-#5XN0B=7hQP0RPCPTLPCTTN0C=7hRLR0/:-#+=7hQLQCRQN0E=7hQL@?2%-,N=7hQL88L50#2)2>7hQP11*$$6>0$>0)36#<%@>G0#<-#$TN0C>GhQL8EK1%*#D0#2+GNgCPXN0F0**%FB_0#1-#%?GhQN1H@GhPPU11%4#@1%4,QN0J@GhQPS11&#)@GhQL@B2&#-#'L@GhQLHWCPXN0M@4.##N2%(,XN0O@GhQPW0%(-#?7AGhQN1:AGhPLQCPTLQCTTN0;AGhRN1=AGhPL1S00,#A50,0$<*@AGhPN1A0#)#B0#)#C0#)#F0#)*3BGhPN170#));BGhPLZ0-5'CGhQL01*+#C5#.#G5#.$KC4+--#$LDGhQN1MDGhP@#71*2-#0:EGhXN1CMGhPLD;5\CPXN0EM1):(TN0E1H3#.#F0#.-#%HP026RJKPOPPT0+$$PQ20+&QQPQ0./#J118('OOOOW2,/#K>#712#&8#7#M>#7#N>#75#6(OWQL`H71<.*10XJKQOQ02);-#%HP04RPPJKRORL01#8'PQL02116--#%QQLTCPXN0RQLH01&6-#4SQLUCPXN0TQL[CPXN0UQL`CPXN0V31'0%WQL01)/'XQL000%)#Y2$4&ZQPX0$+%[QL0.:#\3#5%]QL01-=#^2)=%_QL017-&`QPV0#5#a2#>#b2#+-#'cQL0UHP00dJKSOS020%-#$HP04QPPJKTOU020@-#*HP04\PPJKUO\LRH0@03-$-#+W01PJKVOdLPLL1MgQQ@5.6-#>WL002RL0BK1VP2RPP3RPP4RPPQXPTPPTPPQXPR52)%-#9000VP5RPP6RPP7RPP8RPLH3DaPRPLPLPL0#(-#0PLPLPP9RPP:RPP;RPP<RP@^_;$(:#2@#-$$-#2@^_QPQPPSPvz%PPQPPUPvz%QrQ1(*)NOOS08I1*0-#8Sz%RaQTz%SrT0Q000Qz%TPTPLRnz%UrR6$93*1'Tz%Vr2#2;#=%WrU@#%#=-#<XrW0=9T0=940Rz%YPRPRTez%ZPSPRPez%[LW01+.&uz%\0#,,L80Rvz%]LQ01$=&vz%^12@,,000Tvz%_RQ526;(vz%`r\@#%',+aa\Sz%bP\1,,-#-cRQRRvz%dPQPP\Pvz%eRR8%4#f61$?+Tvz%gPS0U8#5'hRQL@21':+Svz%iPQHR0&+-#(jPdPRUez%kr0R0Q01/1-#-l[m0$&P!H3Da0T0W[cLP)@,93&=$FL43%+#G5#.*HL;SQQQ030:$OO0222#J0#;$N=:#;#K0#;#@;#;#M@#%#;)1M;SQL@02#5'2M;SQ62'7-#+OWCPTN07M;SQdPYPJKW@##2+;&LB:H0%*#952+)-#%WQL@5OjCPXN0:7#:#R02%)#;8#7)YCPXN0<8%(0#+02(-#=8#=#50#8#>9&;$7H03).#?8#:%N930(/#@8#:0)2#A8'502-&#B>$.#C>$.#D7#7)M=6CI<61#1(CPXN0E8$%%OOO3/#0$%#F7$%>1%9#G9$&$8E:$&#H:%*;1%2#I8)@%94:0,(#J>*:#K8#7$0D33*,8#;'<6CI<0#<#M7#<21''#N8#8331251)63&=#7>#7#8>#7#9>#7#:>#7#;>#7#<>#7#=8#7%8:M1+%#>8#;01*&#?8#74,5#@7#;#R03(.#A8$231/1#B9%,#I14),#C7#:%QQH53*301$.#D9$&#@;$&#E8&$-$,ESCPQLCSCQQL1SCRQL7SCSQL5SCTQLJQCUQL0QCVQL0QCWQN0F6%&-#?XL9RCPQL>RCQQL@RCRQLERCSQLDRCTQLZCUQN0G6$7#V1.0#E62@-2/'#F>#7#G>#7#H>#7#I7#731(>#J>$0#K>#7#L8%'1%&#M7#8>.-#N8%331$)#O8#:#221@,6359(WQL0J503@1#18#:+H3DaCPXN0119#1#:22%.#78$20&##88#7$<A1%)#98%)113&#:8$2320,%00012&18$;#51,'#<8#9#61#951:*'OWQP724;-8#9#81#9#?7#922%5>#7#B>#7#C>#7#D7#721#@51@07.0#F8$21.0#G8#814)922;$1%*%L1M03>023228$2@&<4++-#/@RJKXOQKRORKSOSKTOUKUO\13@5)0IGhQQ@51'#73@5-$*KVPPLVPPMVPLPL@5OjL06@jLPLPLD4DhP1WPP2WPP3WPP4WP01?'#L11@?1#053=;-$+P5WPP6WPP7WPP8WP@^_R_QRSLPez%mRSL9Rvz%nRWLPez%oRS22:5(uz%0QR14*3-#+uz%1Q[U1P$&Q!86Dh9W@,932'%QQ7513=530&+dWQPJKYOP@#82+.&PB0Q?2+1-$:QB0QQCPQLRB0QQCQQLSB0QQCRQLTB0QQCSQLUB0QQCTQLVB0QQCUQLWB0QQCVQLX3%>72,8-$'XL0QCPQL9RCQQL>RCRQL@RCSQLERCTQLDRCUQLZCVQN0H6$=*WdXSPJKZ@##1/.11*@-#%Yez%2Q%n%o%0Q31)<#R@-$1)<#8@#)1)<'[OPLY21'5-#'0QCQQL9RCRQL>RC04&2-#*TQLERCUQLDRCVQLZCW:1$@*XdZQPJK\@#*1$@'Zez%3;1$@#S@-$1$@#9@#)1$@#]61$@#Z2175-#80QCRQL9RCSQL>RCTQL@RCUQLERCVQLDR=1%&*LZCPQN0I735+)dZRPJK^@#*1%;'[ez%4;1%;#T@-$1%;#:@#)1%;#_?1%;#[22*0-#10QCSQL9RCTQL>RCUQL@RCVQLE?1%>+DRCPQLZCQ:1&&#R01&&#`@#*1&&'\ez%5;1&&#U@-$1&&#;@#)1&&#a@#+1&&#\22;4-#+0QCTQL9RCUQL>RCVQL@?1&)-#'ERCPQLDRCQQLZCR:1&/#S01&/#b@#*1&/']ez%6;1&/#V@-$1&/#<@#)1&/#c@#41&/#]23/#-#%0QCUQL9RCVQL>?1&2-#-@RCPQLERCQQLDRCRQLZCS:1&8#T01&8#d@#*1&8'^ez%7;1&8#W@-$1&8#=@#)1&8#e@#=1&8#^23@904%4#9?1&;-#3>RCPQL@RCQQLERCRQLDRCSQLZCT:1'##U01'##f@#*1'#'_ez%8;1'##X@-$1'##>@#)1'##g@$(1'#%_B0044:160&91'&@#160&71',#V01',#h@#*1','`ez%9;1',#Y@-$1',#?@#)1',#i@$11',%`B015)&91'/@#75)&71'5#W01'5#j@#*1'5'aez%:;1'5#Z@-$1'5#@@#)1'5'kOPLa21'5@#75)&71$@*XdjQPJKl@#*1$@'bez%;;1$@#[@-$1$@#O@##9-&01$@#m@$56/@@#716>76.?*WdXRPJKn@#*1&>'Qez%<;1&>#\@-$1&>#A@#)16>#o616>#b22+3@#25;$817$15;$#J85;$)jRPJK0Q@#*1%<'cez%=;1%<#]@-$1%<#B@#)1%<$1Q?1%=#c22<0@#,5;&91%@65;&71&(#R01&(#2@#+1&('dez%>;1&(#^@-$1&(#C@#)1&(#3@#,1&(#d23/6@#&5;(91&+<5;(71&1#S01&1#4@#+1&1'eez%?;1&1#_@-$1&1#D@#)1&1#5@#51&1#e24#'=5;*91&4@#%5;*71&:#T01&:#6@#+1&:'fez%@;1&:#`@-$1&:#E@#)1&:#7@#>1&:#f244?75;,91&=@#+5;,71'%#U01'%#8@#+1'%'gez%A;1'%#a@-$1'%#F@#)1'%#9@$)1'%%gB075;.91'(@#15;.71'.#V01'.#:@#+1'.'hez%B;1'.#b@-$1'.#G@#)1'.#;@$21'.%hB0147291'1@#747271'7#W01'7#<@#+1'7'iez%C;1'7#c@-$1'7#H@#)1'7(=QOPLi21'7@#75;271%$+Xd<QQPJK>@#+1%%'jez%D;1%%#d@-$1%%#I@#)1%%#?71%%#j217:@#25)781%)15)7#K85)7)<QRPJK@@#+1%>'kez%E;1%>#e@-$1%>#J@#)1%>#A@##1%>#k22*8@#,5)891&#65)871&)#R11&)#B@#+1&)'lez%F;1&)#f@-$1&)6=#=6;1&)&CQOP4<:3@#72)*8<9;)dnQPJKD@#+1%$'Rez%G;1%$#g@-$1%$#K@#)1%$#E@#,16+#l23.#@#&59;916.<59;7164#S1164#F@#+1&2'mez%H;1&2#h@-$1&2#L@#)1&2#G@#51&2#m23?3=59<91&5@#%59<71&;#T11&;#H@#+1&;'nez%I;1&;#i@-$1&;#M@#)1&;#I@#>1&;#n243.759=91&>@#+59=71'&#U11'&#J@#+1'&'oez%J;1'&#j@-$1'&#N@#)1'&#K@$)1'&%oB0759>91')@#159>71'/#V11'/#L@#+1'/(0Qez%K;1'0#k@-%9=:@#)1'0#M@$41'0$B015:#91'4@#75:#71':#W11':#N@#+1':(1Qez%L;1':#l@-%4%;5='/8;1':(OQOPL1@#@4%<71%',XdNQQPJK0R@#*1%'(2Qez%M;1%'#m@-$1%'#1@#)1%'$1R71%'#20#,@#55:)81%,15:)#L85:))NQRPJK2@#+1&#(3Qez%N;1&##n@-$1&##2@#)1&##3@#%1&##30#,@#/5:-91&'65:-71&-#R11&-#4@#+1&-(4Qez%O;1&-#o@-$1&-#3@#)1&-#5@#/1&-#40#,@#)5*091&1<5*071&7#S11&7#6@#+1&7)5Qez%0R:1&7#0@-%=(7=#4@#)1&8#7@#91&8#50#,@##5*791&<@#%5*771'$#T11'$#8@#+1'$(6Qez%1;1'$#1@-%1'$#1@#*9=3#R66@(3=))9@#22=&9=))'02=&7=$381=(%&#:@#+1%?'Sez%2;1%>#2@-%1%>#5@#)17@#;@$%17@#60#,:5;=918&@#+5;=718,#U118,#<@#+1'-(7Qez%3;1'.#3@-%1'.#6@#)1'.#=@$/1'.#70#,45<(91'2@#15<(71'8#V11'8#>@#+1'8(8Qez%4;1'8#4@-&=+&#@#)1'8#?@$91'8#80#,=1'<@#75<071($#W11($#@@#+1($(9Qez%5;1($#5@-%1($#8@#)1($(AROPL931($@#75<171%(+Xd@RQPJKB@#+1%((:Qez%6;1%(#6@-%1%(#9@#)1%(#C81%(#:318*@#232.81%-132.#M832.)@RRPJKD@#+1&$(;Qez%7;1&$#7@-%1&$#:@#)1&$#E@#%1&$#;32+,@#,5<391&(65<371&.#R11&.#F@#+1&.(<Qez%8;1&.#8@-%1&.#;@#)1&.#G@#/1&.#<32<8@#&5<491&2<5<471&8#S11&8#H@#+1&8(=Qez%9;1&8#9@-%1&8#<@#)1&8#I@#91&8#=3300=5<491&<@#%5<471'$#T11'$#J@#+1'$(>Qez%:;1'$#:@-%1'$#=@#)1'$#K@$%1'$#>34$275+691'(@#+5+671'.#U11'.#L@#+1'.(?Qez%;;1'.#;@-%1'.#>@#)1'.#M@$/1'.#?0#,45+691'2@#15+671'8#V11'8#N@#+1'8(@Qez%<;1'8#<@-%1'8#2@#)7%8#O@##7%83=/:1@#,33)97%;633)77&#1=.%#$0S@#*1&*'Tez%=;1&)#=@-%1&)#?@#*:#'#S@$818?#@0#,=19%@#75<=719+#W119+#2@#+1(#(AQez%>;1($#>@-%1($#@@#*:%('SOPLA31($@#75<=71%(+Xd2SQPJK4@#+1%((BQez%?;1%(#?@-%1%(#A@#*:$#81%(#B318*@#25<=81%-15<=#N85<=)2SRPJK6@#+1&$(CQez%@;1&$#@@-%1&$#B@#*:#-@#%1&$#C32+,@#,2<691&(62<671&.#R11&.#8@#+1&.(DQez%A;1&.#A@-%1&.#C@#)1&.#9@#/1&.#D32<8@#&5<=91&2<5<=71&8#S11&8#:@#+1&8(EQez%B;1&8#B@-%1&8#D@#*:#1@#91&8#E3300=5<=91&<@#%5<=71'$#T11'$#<@#+1'$(FQez%C;1'$#C@-%1'$#E@#*:#'@$%1'$#F34$275<=91'(@#+5<=71'.#U11'.#>@#+1'.(GQez%D;1'.#D@-%1'.#F@#*9@;@$/1'.#G0#,45<=91'2@#15<=71'8#V11'8#@@#+1'8(HQez%E;1'8#E@-%1'8#G@#*9@1@$91'8#H0#,=1'<@#75+671($#W11($#B@#+1($(IQez%F;1($#F@-%1($#H@#*:%-'SOPLI31($@#75+671%(+XdBSQPJKD@#+1%((JQez%G;1%(#G@-%1%(#3@#*=)2##S@#+7$'3=6+6@#&4'$97$*<4'$77$01=4#$#F@#+1&3'Uez%H;1&2#H@-%1&2#I@#*:$58168#J32+:@#25=(816=15=(4=91.-#$OOWQdBSRPJKH@#+1&#(KQez%I;1&$#I@-%1&$#J@#*:#?@#%1&$#K32<<@#,5=(91&(65=(71&.#R11&.#J@#+1&.(LQez%J;1&.#J@-%1&.#K@#*:#+@#/1&.12,#@#)2+&91&2<2+&71&8#S11&8#L@#+1&8(MQez%K;1&8#K@-%1&8#L@#*9@5@#91&8#M34#@=5=(91&<@#%5=(71'$#T11'$#N@#+1'$(NQez%L;1'$#L@-%1'$#M@#)1'$#O@$%1'$#N346$75=(91'(@#+5=(71'.#U11'.$0T@#*1'.(OQez%M;1'.#M@-%1'.#N@#*:#&#T@$.1'.#O0#,45=(91'2@#15=(71'8#V11'8#2@#+1'8(0Rez%N;1'8#N@-%1'8#O@#*9@:@$:1'8049@=1'<@#75=(71($#W11($#4@#+1($(1Rez%O;1($#O@-%1($<==3$6:%6'TOPL101%8@#:5=(71%(+Xd4TQPJK6@#+1%()2Rez%0S:1%(#0@-#=;#(047401$>#88==>.0=@#)9==7;3==$89==53$0H?==4951'(#225?*;48-)4TUPJK7@#$1&',LPL@7HhQQ@5==.=#W6=<07$<V1=</='>VPLW5=<08-#6;:HRLWPAVPPBVPPCVPPDVPPEVPRYRV1$-(DK5VLW0$0-#>PRSLWRSPFVPPGVPPHVPPIVP@^_S_QRSL3Rez%1;1*4#101*4$JV@,:1*4$KS719:31'4$L30#,=493)7TQPJK8@#%19%01#1(4Rez%2;1#1#2@-#1#1%QQ4@#*=*'(#T@#47%+3=<;?=49.97%.@#%49.77%41=9?>#:@#+2,?'Vez%3;1&;#3@-$2,>#M@#.15,$L40#,=5*'0156#;@#+156(5Rez%4;1#;#4@-$2&'#O@#81#;$L50#,=5&>01$'#<@#+1$'(6Rez%5;1$'#5@-$1$'#183<&@#41$'$L60#,=5#701$1#=@#+1$1(7Rez%6;1$1#6@-$1$1#3@$.1$1$L70#,=4>001$;#>@#+1$;(8Rez%7;1$;#7@-$1$;94=0@$*1$;$L80#,=4>/01%'#?@#+1%'(9Rez%8;1%'#8@-%38,#G@#)=:(1&@TOP2>$)$84?/#;@#$>$=:0%)8>$<@2>$(09>$;-$HJ?>$;-@$45$/@#6=:.29=:.)'WdXYQ73>)%JKA@#(5%3$HJ@#)5%3$MU15%3'OUPRS45%3-#2PUPRSP2VPP3VPP4VPP5VPP6VPL45&<0>##&-$%PUPLPRSRSRSP7VPP8VPP9VPP:VP@^_T_QL9RRSuz%9S31/2(T1P$&901/2#;@,<1/2#5@#)44<#B@#>44<3=@=;78)'944?@#+8)'745'1==0$#C@#+45''Wez%:;2#6#:@-%=@=+#6@#)1'&#D@$)1'&3>#1?18(<91')@#18(<71'/1==0'#E@#+1'/'Xez%;;1'/#;@-%1'/<>'$$&KL;S2>).,%P?T5>)..-#%dWRPJKFTOPN126235&PN139#2#49#2#59#2#69#2#79#2729;%PN17293%PN17>'&%%PN1729>%PN17299%PN17>'%.%PN17>'%(%PN172:3%PN17>&53%PN17>&5.%PN17>&5)%PN17>&5$%PN17>&4=%PN17>&48%PN17>&43%PN172>&%PN17>&4%%PN17>&3>%PN17>&35%PN172?0%PN17>&3(%PN172?8%PN172>,%PN1715+%PN1714&%PN17=865%PN17=30&%PN17=.'(%PN17=(;;%PN17=$%7%PN178:#%PN173;#+PdX6QPJKG@#&3$8&P0TP9>'*=63$7,1TPP2TPP3T0>%2=-#7RXLPP4TPP5TPP6TPP7TPP8TPP9TPP:T:>%2?'PLPLP0#(-#0LPP;TPP<TPP=TPP>TP@^_U_Q31;9-#%S1P$&<R!0IGh@@,:>(02@)>1:$?80981.0+Rd7T_PJKH@#-1.05>')9@#&1.0#53>(2)$LW@#)1.44809&B:HR:808<1.5-#*V_Q%n[Q1<R$&=R!@7H@-#1.0@$*43,&HTQY72(%72'@72'=72':72'772'472'172'.71+;%JKI@$=1+5$RS@#*2')346=01+.646<<1+3,W_Q&9R!@HJ@,<1++15/*$JL5>,445#.&ML;S6>)$20>)?10#>$2M530;#<830;*VPJKJTOP@#(2:-%L02@#*>+)@%0TP31(/-#*QXPTPLRP1RPP1RPP3T;2:9@#&>+)751),-#+P;TP@^_X_Q&<R!LINg=@,@1>,1>(:&618@@#$>)4<@#$>)4$*dHTSPJKK@#(1'/@#+>(.:61:8?>(.:@#+3.;<>(.:<1:9'Y_Q&=047+@,;1:9@##460+@TQPJKLTO;3,)3>+&>83,14>)9(83,91>+&>83,>1>+&>83-%7>+&>83-02>+&>83-64>+&>83->#Q@#8</9@#.6:)#M@$(1.7+ATPPBTPPC@#%1.7-#%GTPPHTPPITPPJ@#01.7-#+KTPPLTPPMTPPNTP@^_Z0260'86DhO@,71.72>*7;$5<0>.6*'QN0264#.&B>Gh01(93>.*:1>*'4$>G3>.//-#(N0F@GhQdJTVPJKNT@#$>,$0%0BO0>-065<7.*OWQLDN9c02&=8#:3$49>*,4$0I1>..39>*,7077$8>*,7&L4DE02)(9>*,90$18>*,6%L8M1%@@#2>*,8$02@';>*,8&bJKO@#(7<0'MNgQQ6%@715)-$#>TPP?TPP@TPLRPTPLRLRPBTPLPPDTPPETPPFTPLNR@#&3%'516(*PKTP@^_[03%'-#%D8NgMT0WZcLP)"%pstring).
Definition TPL_ALL : list template := TplDec.TplDec.dec_tpls TPL_BLOB.
Local Abbreviation NT i := (TplDec.TplDec.nth_tpl TPL_ALL i) (only parsing).
Lemma TPL_ALL_length : List.length TPL_ALL = 83%nat.
Proof. vm_cast_no_check (@eq_refl nat 83%nat). Qed.

Definition T_DRVN : sstate := Eval vm_compute in (t_st (TplDec.TplDec.nth_tpl TPL_ALL 0)).

Definition T_SW_DRV_1 := Eval vm_compute in (NT 1).
Definition T_SW_DRV_10 := Eval vm_compute in (NT 2).
Definition T_SW_DRV_11 := Eval vm_compute in (NT 3).
Definition T_SW_DRV_12 := Eval vm_compute in (NT 4).
Definition T_SW_DRV_13 := Eval vm_compute in (NT 5).
Definition T_SW_DRV_14 := Eval vm_compute in (NT 6).
Definition T_SW_DRV_15 := Eval vm_compute in (NT 7).
Definition T_SW_DRV_16 := Eval vm_compute in (NT 8).
Definition T_SW_DRV_17 := Eval vm_compute in (NT 9).
Definition T_SW_DRV_18 := Eval vm_compute in (NT 10).
Definition T_SW_DRV_19 := Eval vm_compute in (NT 11).
Definition T_SW_DRV_2 := Eval vm_compute in (NT 12).
Definition T_SW_DRV_20 := Eval vm_compute in (NT 13).
Definition T_SW_DRV_21 := Eval vm_compute in (NT 14).
Definition T_SW_DRV_22 := Eval vm_compute in (NT 15).
Definition T_SW_DRV_23 := Eval vm_compute in (NT 16).
Definition T_SW_DRV_24 := Eval vm_compute in (NT 17).
Definition T_SW_DRV_25 := Eval vm_compute in (NT 18).
Definition T_SW_DRV_26 := Eval vm_compute in (NT 19).
Definition T_SW_DRV_27 := Eval vm_compute in (NT 20).
Definition T_SW_DRV_28 := Eval vm_compute in (NT 21).
Definition T_SW_DRV_29 := Eval vm_compute in (NT 22).
Definition T_SW_DRV_3 := Eval vm_compute in (NT 23).
Definition T_SW_DRV_30 := Eval vm_compute in (NT 24).
Definition T_SW_DRV_31 := Eval vm_compute in (NT 25).
Definition T_SW_DRV_32 := Eval vm_compute in (NT 26).
Definition T_SW_DRV_33 := Eval vm_compute in (NT 27).
Definition T_SW_DRV_34 := Eval vm_compute in (NT 28).
Definition T_SW_DRV_35 := Eval vm_compute in (NT 29).
Definition T_SW_DRV_36 := Eval vm_compute in (NT 30).
Definition T_SW_DRV_37 := Eval vm_compute in (NT 31).
Definition T_SW_DRV_38 := Eval vm_compute in (NT 32).
Definition T_SW_DRV_39 := Eval vm_compute in (NT 33).
Definition T_SW_DRV_4 := Eval vm_compute in (NT 34).
Definition T_SW_DRV_40 := Eval vm_compute in (NT 35).
Definition T_SW_DRV_41 := Eval vm_compute in (NT 36).
Definition T_SW_DRV_42 := Eval vm_compute in (NT 37).
Definition T_SW_DRV_43 := Eval vm_compute in (NT 38).
Definition T_SW_DRV_44 := Eval vm_compute in (NT 39).
Definition T_SW_DRV_45 := Eval vm_compute in (NT 40).
Definition T_SW_DRV_46 := Eval vm_compute in (NT 41).
Definition T_SW_DRV_47 := Eval vm_compute in (NT 42).
Definition T_SW_DRV_48 := Eval vm_compute in (NT 43).
Definition T_SW_DRV_49 := Eval vm_compute in (NT 44).
Definition T_SW_DRV_5 := Eval vm_compute in (NT 45).
Definition T_SW_DRV_50 := Eval vm_compute in (NT 46).
Definition T_SW_DRV_51 := Eval vm_compute in (NT 47).
Definition T_SW_DRV_52 := Eval vm_compute in (NT 48).
Definition T_SW_DRV_53 := Eval vm_compute in (NT 49).
Definition T_SW_DRV_54 := Eval vm_compute in (NT 50).
Definition T_SW_DRV_55 := Eval vm_compute in (NT 51).
Definition T_SW_DRV_56 := Eval vm_compute in (NT 52).
Definition T_SW_DRV_57 := Eval vm_compute in (NT 53).
Definition T_SW_DRV_58 := Eval vm_compute in (NT 54).
Definition T_SW_DRV_59 := Eval vm_compute in (NT 55).
Definition T_SW_DRV_6 := Eval vm_compute in (NT 56).
Definition T_SW_DRV_60 := Eval vm_compute in (NT 57).
Definition T_SW_DRV_61 := Eval vm_compute in (NT 58).
Definition T_SW_DRV_62 := Eval vm_compute in (NT 59).
Definition T_SW_DRV_63 := Eval vm_compute in (NT 60).
Definition T_SW_DRV_64 := Eval vm_compute in (NT 61).
Definition T_SW_DRV_65 := Eval vm_compute in (NT 62).
Definition T_SW_DRV_66 := Eval vm_compute in (NT 63).
Definition T_SW_DRV_67 := Eval vm_compute in (NT 64).
Definition T_SW_DRV_68 := Eval vm_compute in (NT 65).
Definition T_SW_DRV_69 := Eval vm_compute in (NT 66).
Definition T_SW_DRV_7 := Eval vm_compute in (NT 67).
Definition T_SW_DRV_70 := Eval vm_compute in (NT 68).
Definition T_SW_DRV_71 := Eval vm_compute in (NT 69).
Definition T_SW_DRV_72 := Eval vm_compute in (NT 70).
Definition T_SW_DRV_73 := Eval vm_compute in (NT 71).
Definition T_SW_DRV_74 := Eval vm_compute in (NT 72).
Definition T_SW_DRV_75 := Eval vm_compute in (NT 73).
Definition T_SW_DRV_8 := Eval vm_compute in (NT 74).
Definition T_SW_DRV_9 := Eval vm_compute in (NT 75).
Definition T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 := Eval vm_compute in (NT 76).
Definition T_SWRET_c60f4_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q89352 := Eval vm_compute in (NT 77).
Definition T_SWRET_c6b14_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q89352 := Eval vm_compute in (NT 78).
Definition T_EXIT_2_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0 := Eval vm_compute in (NT 79).
Definition T_SW_SWRET_c60f4_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q89352_1 := Eval vm_compute in (NT 80).
Definition T_SW_SWRET_c6b14_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q89352_1 := Eval vm_compute in (NT 81).
Definition E_EXIT_2_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_1 : sstate := Eval vm_compute in (t_st (TplDec.TplDec.nth_tpl TPL_ALL 82)).

Lemma templates_wfb : forallb (fun t => sstate_wfb (t_st t)) TPL_ALL = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.

Definition CONTRACTS : IMap.t contract := imap_of [(410%uint63, (MemcpyC.TwinB.MemcpyC.amemcpy_c ImgBoth.SEGS 386080%uint63)); (414%uint63, (Memcpy0C.TwinB.Memcpy0C.amemcpy0_c 386080%uint63)); (421%uint63, (StrnlenC.TwinB.StrnlenC.astrnlen_c 319880%uint63)); (424%uint63, (FprintfSC.TwinB.FprintfSC.afprintf_s_pre_c ImgBoth.SEGS (wlit 90434%uint63) 1%uint63 9%uint63 333440%uint63)); (429%uint63, (UnreggC.TwinB.UnreggC.unregg_c UnreggC.TwinB.UnreggC.CFG_ASAN 309200%uint63)); (440%uint63, (OpDropC.TwinB.OpDropC.op_drop_c 17%uint63 309200%uint63)); (442247048%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 247056%uint63)); (442247084%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 247092%uint63)); (442578060%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 578068%uint63)); (442578064%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 578072%uint63)); (442632760%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 632768%uint63)); (442632764%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 632772%uint63)); (442785164%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785160%uint63)); (442785168%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785164%uint63)); (442785176%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 785172%uint63)); (442807112%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 807108%uint63)); (442810536%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 810532%uint63)); (442811024%uint63, (RoLit.RoLit.rolit_c ImgBoth.SEGS RoLitA.RoLitA.VIDS (RoLitA.RoLitA.RV RoLitA.RoLitA.CFG_BOTH ImgBoth.SEGS) 811020%uint63))].
Definition mkctx (cl : list (int * template)) (ec : IMap.t sstate) (mr : sv) : ctx := Ctx ITAB (imap_of cl) ec CONTRACTS mr.

