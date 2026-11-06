(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_MallocKit_AB () := KReplay.lz_vm "#$-<C47Corelib7Classes9Morphisms6Proper!sI-Program6Basics4flip!sg?Krespectful_per_obligation_1C46Stdlib5Lists4!s+#2hdC89OSSVerify!tN#ofs:boost_json:fuzz_parse3lib4Spec6Malloc4aptrC13~~~!ta,4Init5Logic7f_equalI35stdpp9countable9C!s0'00C!sD&4base;RelDecision!s?+gmap;!s'#_lookup!s?0:!s?$empty!s>09!s>$fmap!s=6o!s=3!sl%merge!sl7old!s='8fin_maps@!t[%_insert_eq!t~6fin!t8/!uX#4f!s836!uL&!wM\o!wMA8eq_ind_r!u9CneI!u9/!s'$!wf-!s5#B!uM$partial_alt!zj/!tB$9Datatypes2i!vS+9decid!x^#;prod_eq_decC!y-4>!sD$!s5+!u#4:!tL#!t|%!vM\7s_metas!vP&5!{z&6NArith6BinNat1N3eqb!sC,Z!sC+Int1Z!sC$!un;4andb!tm\<get!to$_rec!trB8eqb_!~M#I!xf72eq00I!tt;7reflect00!u\<!t,;!sk,6option00K!sHC1K!tq;1!zs83not!tE<4!y=#00!s_86eq_sym!sB89False!{s#!we\8aptr_!xm#!wa%!sn[9s!xU&s!sob8pu!so%!sn&!#3`/!|9&!vf;3fs!sC>sn!}v+!x4&;from_!s2%K!wcA1I!#4}[!uC#00!uE%!xq,7Numbers7!{c#ums1N!{C/!sD4Z00!vq\5!tP$!tO&!sk[6mstate!u?'C4!vh%7n!tw%1N6!#5[%!s?3Z6!#5t:;N!#5q4!sD-Z!sD,!|H=bool!}e>!sF%1!#3V75!|L$!scD2!w>P3Lib2Nd9ex_elimF3!{uV!sj&:ex_intro!skX!#8q1are!}QX5Agent9!sn%Rep9!#7q#slot!#7r2!#6k12le!sB>t!wX83and!#7f=3mul!sC=ad!#D$^!sd#!uG$K!tg<1!x3Xand!xx0!#3N\!x1#!}5'K!#30>1!u~\6NSLOTS!#7ibAREA_HDR!#9JbMETA_SIZE!#3z&!wa68eq_trans!#<e8iff!#J}>?eq_p!#Ki#!s,#xy!#Jq'4Bool!s'$=andb_true_!ssBI!#?i#xive_!s0,!s}&!s\=F!sR0!tX-!sY3>!sY+_Prop@!yp#iff_m!s=&!#B5;6eqb_eq!tS?:!#M}+!sM?NR!tz,!#GZ&pp!tP6!}S2!tPFM!x3$_co_!#IU#v_impl!t$,!s`4?Rel!#On#!v<'!v%#T!sj#itive!sWE=!sW#!uF+!#5k_=!#A{&!xf$!zk%c!swU<!sw%Kit_AB@!#G^-_put!s}i<!ty+neq!#?z2!#;F2list!#;f-!#3r28po!w4%02!#4?=N02I!#>S%9bitvector;defini!wV#s2bv!#@lQ3Lib5Frame5munch!#<SY!si%7outside!#3k=7!|z$!#H5Q!t0,6sub_fp!tt`<!u_$_weaken!#:I7!x#32!t8Z3ivl!#9\B!xh,3!#8,[3ctx!#8pa5c_s!{,'!t{G1!#;~?2!#K3/5!#Yz$!ti[Aset_unmap!tq#_map!ubb7!sw#!ud+!sm]upd_!w@e8step!t],!#M4]ctx!#@d&!#53b5mw_ok!uPb:m_last_idx!spefree!#LM#!spa;m_sizeclas!#Sfcm!zJ#l!#3J&!#Gv<pow!#;[_!#JH$word!t8B>pow_pos_nonneg!sN<:!sN#!sJB7compare!#5q;3nat02K!#Cm&9micromega=RingM!s4'5Psatz!sOM7!sOK5!sO6:Z!sL+;!uF%!w2$!tL8!sR;3!#8[A1!sr66VarMap1!v/9!sD,!sbA3I!sD?0I!v7C7Formula00!t567Env!sT#5PExpr!tX8!sI22!sIE!wsE!tb+1!#a?C!t>F5!sIE3C!sI55Tauto8B!tZ&C!x{@=Z!sT$CheckerC!wY<4find!sqAC!sq0_sou!#A/U!#RY/4!#=8&!w=B!|2&6K!v'<G!w_'4!sJF5!sJF8!w?<5eKind!#GC<unit!zr8!se%4kind!zo8!uj13Op2!}t?!t5$!#]W84True!#j1=:!#5c$ison!}>8!#3R:0!#6<@1!#4EM!uvJ5!#7w;4land!#Pf<modulo!sF<9mod_small!xyF7!#9L<!sm#add!#kg;i!tr>4ones!tp=!uV#_!sI#!vHI1!v&=shiftr!#=g<div!tU=div!vG%!u{=!sI#!u{#!sG;?!tO%_!sN#pow2!#q{8or!#`p=;!v+$!#=z$!wxF3!so<5ldiff!v&=lo!vG=7testbi!#m`=or!#v+=negb!x]Bspec!sI<:!u1$!sJA8lor!sHA9bits_inj'!yG=!sI$!wS48Zbitwise1Z<add_!t9#!};@<!u#%!w|'!#Mw=3!#;O=3Pol!#35E!#8q%!#8MF!#9=F9".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~m52wa37Corelib4Init5Logicq43andq42eq46Stdlib6ZArith6BinInt1Zs33adds32les32lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~ub4metak14boolub4aptrubcget_meta_recub8aptr_eqbub6mstateub8put_metaub8upd_meta01N79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~hna9meta_slotub7s_areas35stdpp7numbers1Nht36eq_dec35stdpp7numbers1Zhue6eq_decub4area25stdpp9countableih0bN_countableih0bZ_countableih0eprod_countable25stdpp9decidableil1bprod_eq_dec25stdpp4gmapin14gmapk15falseq43notk14trueq43iff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~iq03ivlk14consiq05munchk14listub7upd_ctxub5c_sequb3ctxub7set_sequb4mctxubh1set_unmap_seq_mapub8step_seqs33eqb25stdpp4basejk95emptyin1agmap_emptyub9set_usageub4optrubaset_activeubam_freeableubam_last_idxub8m_maplenubbm_sizeclasss33powhna9meta_word79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocKit_AB~~~~~~jt25mw_oks34lands36shiftrub5meta0" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition agree_on : ltac2:(zQ "41!h9!jc!l9!m2&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>1A$3>1n$3P") := ltac2:(zQ "a1!h9!jc!l9!m2!pf!r8!re!tb!u1!u6&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1m~0\2m'~0\1A$3\1n$3>1a$3>0@2$5@2$8^3^1@2$9^1@2$7^3^2@3$6@1$2@1$1@1$0#8@1^5@1$4^2@1^6@1$4^2").

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_meta_rec_put : ltac2:(zQ "80!hi9!hj0!hj7!hje!re!hkd!hl8!hm1>2st$6>1g$2>2mr$0>2g'$2@3$4$0@2$3@3$7^3^2^4^1M1\0$1$0@2$5^1^3^2@2$3^4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_AB ()) [] "##K7p'0h01oh11Hh23Heqh31bi001bh43go'h53gr'h61ri011rh71ei021eh81ni031nh91th:2e0h;1gh<2g'h=2goh>2grh?2mrh@2n0hA2sti041pi051zp;1p;4p;6p;2p;3p;?p;7p;5p;Ap-1R0p10000p4p710p9P!s6%SR1!s8,P!s2$2!s3/31!sS,11!sc11i!s6&8g002@R!t&$0R1g003DR2!sC'P1p1003a!s6%R3!s8'4?R4!s:&5p8P1P4!tL&R4p8P1g004XR6!sl,g0051R7!s71IR8!s71`R9!s7067R:!s71OR;!s71fR<!s707HR=!u317a!v&'R>!sK&83!vX+8p1008G!ut%?g009KR@!uP&Ap8P?P!u<$41110RB!s7$!w/+!s3+!w/$8P?P!tZ$<1!s#,0RCp8P!s~$iR?!sD5Dp8P3P5!s+$4!wR$:KRE!tN&FP3p8PF!sE$FP4!s+$>p8PE!t`,>!tA%3101p8PCPAp8PD!s+$B!s@%51110!uA%APBp8P7!uE-!sI%61!sJ2g00:_RB!sO,A!sO%7!u'%!u+%!t4%;!sK4:!uS+!sN/!tt'0RA!u9$>PA!t6$;?j1fTg00;[j4eTg00<9j6VTPEj4Kj3RTP6j4dj3NTPBj4[j3L!sJ$Zj4XTg00=6j15Tg00>=j2;!s/$Zj2:Tg00?7j24!s/$Uj20Tg00@aj2YTg00ACj33!s/$]RBj2FTg00B@j2W!s/$bj1TTg00CDj2S!s/$fj2?TP8j3QTP7j3JTP9j3MTP:j3ITP;j3OTP=j3PTP<l?HTP@j67Tg00D@j1>!s/$YR@j2cTg00E9j4DTP2j6A!s5$Uj2GTg00F4j2`Tg00G<j2_Tg00HEj3^Tg00IMj7\!s/$aj3ZTg00J>j3]TP1j6C!s5$[j5@Tg00K6j4aTP?lAbTP0g00KVR?f4R1f3R2f2R<f1R=f0R;F\p=8g00L\R:g00M:R9;Z;p=<A]:9;p==P?P?f5R7g00MXR8P0P?P1P2P<P=ECD@=3?;p=6P:P9P=P;Cap=1!sJ$!sH$P;ECp=9P?P?P=P8P;D@p=EA3?=;p=2!s=$1P8!sV1D@p=UP0P;P=P<P2P1P7f6R8f7R6f8REf9RAP?f:R>f;RDf<RCf=RFf>R4MAbp=Bg00N]P@P:P9%f?R5P0P:g00OeR3P9g00P>RGCeRHP:P3g00PWP9PGg00Q5EVRGP?CKR3P0PHPGP?CdRIP=P3!to$!s<,[CXRJP;P<%51D8g00QSRKP?%<=%<;RL';%==%=;RM':'4P<101=n010!s#$20000E6P<!tq%P5P3PIP;P3PJ11<=RNP8%5ED8P!sw$N,;L%=N,:M'4P810E;!so411Y=7A3:=71;=7'F1;<8PKPBA3:26!t,%1171RM!t1%AERNPFf?RL#5!t4%1:1ERO,4=PF10LM!t/4=A3:1ERL1W1ERPA391E/FORO1:7AR7!t9%98>RQ!u@$N!t5%FCRRfARSfCRT#5RUD8RVC9RW,E5RXPKP?g00R3RY/4=PS10TNRZ!tG1'2P=A396DR6P:PF!u?';AR[!t0%4FR\fBR]fDR^#5D8R_DUR`/2]X5:P9PC!sX'4;P_P]E6X49%T?Ra1S?S1E5;Rb/2]X0a1??S!u0$RPVC9P0AR0HGR]AQ0HGRcAN0HGRdAJ0HGReAL0HGRfAM0HGRgAI0HGRhAO0HGRiPHAP0HGRGP?PUPRPSM?HE7PEP;E7PAP1E7!w3$4YYPSP!uc2,2XeW:P;O1%>6RjP:PF10^[,2`X5:Pa!u?%FER`PUC9114AR[,0^,2bX0a10T`,??!u9$`!u9$]PcPdPePfPgPhPi!zs$UPRP`PSA30R`R`1c:9RkP9!zB&9P;P;n20011040001!tc$000X9kP[P\PkP\P[P;CDEAA39AFg00RSR[P<P;O1'Gb2W1%>`eM?B!ub/g00S0R1,4!uh;8P;O1n1021001!sE$2111!s'%3b3b6W7!v2%LPPPOP!z&$PQ!ve%1=!s{8P=!xj/>;RQP_10^Q!xn$!vh'ACRC!vh%>FRF!vh/C!vh'C!vh@C!vh%CRCPkP:!vd&:P;P=!vd:R@PF!vf&F!vf':>4R4P!uz$,G[R[!vd%C!vd&!yN%!ua%!v^:X76P;O1!uL%PN!uH&AR>!uH,??ZPW!u=<N!u=%NRR!u=&>!tr&>!tr%P4P!td&R!td&!t^%1!t^:@j!x?D!xaD!x%'=;RjP3PJPMPA%5D!#5g&j%<M';%=j%=!#6\$A10Dj!#4b2eX49X5:P=P;O2!wY01103105X=9X>!sF>!#7=-P<P=%52D8RJ!uv$`;<P=102!#711RKE6e!s^'1_J2#5P!s9/A^<=2R=!s<&10=;/2KeX<0X??X;0WAo"). Qed.

Lemma upd_meta_put : ltac2:(zQ "70!hi9!hl8!re!hj7!hje!hm1!hmc>2st$1>1g$3>1f>0$0$0@3$2$1@3$6^2^1^3@3$5^2@1^1@2$4^3^2^3").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) [] "h01fh11gh22stp;2p;3g00?Uj22Tg00HEj31Tg00Cfj20Tg00N]R0g002@g00KVR1P1[f1R1f0f2R2/21O1;12,00W0W1W2o"). Qed.

Lemma meta_slot_same_areas : ltac2:(zQ "f0!hn7!m2!hrc!hj7!hl8!hs9!hu4!hvf!re!ig9!ii1!ij0!ijf!im2!ind>2st$4>3st'$4>1g$3>0@3$8@4$e$3@4$d$0$6$1$7@6$c$0$6$a$1$7$b$9@1$5^2@1$5^3>0@2$2^4^2@2$2^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_AB ()) [] "##0Kh01ah12arh21kh31gh41Eh52Egh62Hah72Hkh85nd_i2h92sth:3st'p;4p;6p;1p;3p;2p;8p;5p;7g002@R0p4p70R1g00SPR2p4p710p8P1g00TTR1!s7'p1008G!sS%3P!sN$2!sO$3P1!s3+g00;[j4ETg00<9j6DTg00:Kj4=Tg00UYj12Tg00ACj31Tg00V`j2:Tg00Bbj1>Tg004Xj4<Tg00CDj29Tg00Wmj23Tg00XIj27!s/$ej20Tg00Y@j28!s/$]j24Tg00Z:j26Tg00[>j4;Tg009Kj6CTP1j8B!s>$Yj5?TP2j7@Tg0083j6ATP0g00\^R2f3R1f2R3f1R4f0R5EAp=5g00N]R6!sK$L\R7g00OeR8g00M:R9g00P>R:CER;P7P8g00PWP9P:g00Q5EDR:P2C=R8%24%23311:14P0P2P9%>2R7P8P0P;P:P2C<R:P3f7R;#2C51924R<31R=g00]dR>/35g00^BR?,75'0R@f5RAg00_HRBg00`PRC/85'4,63RD510RE'0'0X29X12X001:13P=P@PEf6RE/:A13>4174?'0f4RF18C3,4B'6910;!tm%P8P:P3f<#2C5=17<f;=10D,0@!s|-PAPFP1P8f:#2R@!sX$EP5!u4$A51713>F17F?'0f9RD18CF,4B,6E510!tk$38!sY$AP@!sY$F!sY%1171?'0R?f818C1!sY$A510RA'0P3P?PAP4P5C;C;%2DP;ECGBW5W7X6=D?!th,5F@W8W4X30X:6W9o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)



(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma aptr_eqb_neq : ltac2:(zQ "60!hj7!re!hj0!io5!iod!hkd>1a$0>1b$0>0@1$4@3$1$0^2^1@3$1$2@2$5^3^2$3").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_AB ()) [] "##1yp'0h01bi001bh11ri011rh21ei021eh31fh41ni031nh51Hh61ah72a1h82a2h92b1h:2b2h;2e0h<2n0i041pi051zp;3p;1p;2p;6p;4g00ACj30Tg00D@j13Tg00F4j27Tg00@aj2DTg00>=j28Tg00A]R0j2:!s:$Zj26Tg00B@j2@!sg$YR1j2?Tg00K6j39j2Ej4ATg00Cfj2>Tg003Dj64Tg00aYj6<Tg00EUj2CTg00Iaj3=Tg00J>j3;Tg00?7j2BTg00QSR2f0R3g00S0R430p=5g00L\R5g00M:R6f1R7P3CAp=11B73=024p=2g002@R8P1P5P6A0873#3f2R9/77#5[^08P3!sB%f3R1/19=083#3f4R:/11!sK%P3f6R;f5R<'11173508#3f7R=/D9A05=918=9':f8R>/81P2P0f9R1=05:f:R?/6<R@,27P7A05?<RA1@?<RBA06?</:@R@f;/6;R<!s^$<=06=RCg00R3RD/27P7f==06>REA02D4P>1?56R>f?RFf>RG'111?G11?1P>\6RHP>P3PFO1X3HA956FRIA956?RJPHPIPIPJPH\5RIPHP3f@O1X3I1E56RKPK1>IKE4P5PHPKPFP?P:E4E<E4P6P>PJPGP1P3E4E<O1'C12DDeW;P3O1%3ER11>24RG12D4eW4P3O1n102100101000210!s5$103b0b1W2!s^%APBP@P!um$PC1247P7PG124DeX2EP3O1!s4$4eX<1!syD!tCD11=;R=9=561197R99=56'8A;56=A;569'6'2e17=9#5eW5X:6X95P7P3O2n2001104000121103105X08X86X7!sI>W6o"). Qed.

Lemma aptr_eqb_eq : ltac2:(zQ "60!hj7!re!hj0!ip3!ipa!hkd>1a$0>1b$0@2$4@3$1$2@2$5^2^1$3@3$1$0^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_AB ()) [] "##66p'0h01Hh12H0h22H1h35lemmah42H2h51ai001ah62a1h72a2h81bh91eh:1Bh;2H3h<2b1h=2b2h>1ni011nh?1zi021zi031pp;2p;3p;4p;6p;;p;9g00F4j2>Tg00b7R0j26Tg00>=j2=!s/$Zj2<Tg00?7j2;Tg00XeR1j25!sW$Pj2FTg00c<j2D!s/$]j3MTg00dSj4CTg00eFR2j6LTg00f8j2K!s/$Xj4JTg00g?l;HTg00h:j2GTg00Cfj27Tg009Kj69Tg003Dj6@Tg00[>j4BTg00Iaj3?Tg00J>j3ATg00ACR3j38Tg00K6j4E!sy$Zl9ITg00QSf0R4g00R338p=2g002@R5f1R6;84p=4g00L\R7g00M:R8P6P4CEp=0p-0R9P0g00iTf5R:f4R;f3R<f2R=P6P4M9Ip=:A8764p=3A8864p=1g00DYR>P7P81>64#21464'6^85P4P!s=%0<=R?/>!sB$?4'6P4f6R@/=6RA1<:4RB';#2%2ARC%2BRD'5'6f7RE/==RF1<@6RG!sG%FRF%2GRG'5RHP410E@RI10=6RJ'4RKPK1F9KRLE:W31DAB13@6RB,6CPH13E=R=/5GRHPFP=P4PGPGP!ub%jE9M90RFPGCCELPKPKP!si%K@611:4RC,6DPH11@6RH,5=RDP9P9^:9P0P9P9P0P0CJP1P2P=!s4$FP=CCPGPHP4M;H!sv-G:415BCRCPK[10@:RB1064RL'4RGPD[P1P=PHf8RH/0E/4?R=P4f9R1/3;RDP7P:f:RF/1:f;R0,06/4I[X67111;R9P8P:10E4/4IX78175BPFP4E9W0!s-+6P4O2n20010!s#$12!s-%0X0CP3P5PI10;<RI,4613F:R3/59[P4P5P8!x4%P8P4P4!sh$103!sh%101102X95101HPIP4E@11H<R<P5P7!s]&7P4P6!s]<F110:;P6E@P3130@P4f<R@/3EP7PHf=R3/1HRH136Ff>R;/11'5[X>711@EP4PHP8P11300114F'5X?813FF1111177F1781CBP;P4E9b;W4P3!s0$4W2P4O1b!s+&X1=P4O1X1Kn2002!v=&!vF$144?15D<[X55PJO1P4175?O1b1X0GCBO2O2O2A?78BA?78L'=AA78BAA78L'<';#2/6Ge1>BL!s0%X=8X<7!wP-!v/'1!v/&85X78X6!sI?55o"). Qed.

Lemma get_meta_rec_put_same : ltac2:(zQ "60!hi9!re!hj7!hje!hl8!hm1>2st$4>1g$2>2mr$0@3$1$0@2$3@3$5^2^1^3^2^1").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) [] "h01bh11gh21mh32mrh42stp;2p;3p;1p;6p;4g00F4j27Tg00?Uj20Tg00ACj31Tg00Cfj23Tg00k5j16Tg009Kj62Tg00HEj35Tg00lFj44Tg00N]g002@g00KVR0P0g00QSR1P0f1R2/72R3f0R4f2R5/02n0100000020000A1042X20P1g00R3P1P0P4P2f3/05n0100000020000=102X011304P3%62E2A5245/02P5P2P4P2C4E2W3W1W4o"). Qed.
Lemma get_meta_rec_put_other : ltac2:(zQ "70!hj7!re!hje!hi9!iod!hl8!hm1>2st$5>1g$0>2mr$3>1q$0>0@1$4@3$1$0^1^3@3$1$3@2$2@3$6^4^3^5^2@2$2^5^2").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) [] "h01bh11gh21mh32mrh41qh52stp;3p;1p;2p;6p;4g00ACj30Tg00D@j18Tg00F4j23Tg00?Uj21Tg00Cfj27Tg00m]j36Tg009Kj62Tg00HEj34Tg00lFj45Tg00N]g002@R0g00KVR1f0R2f2R3500#8P1g00QSR4P1f1R5f3R6'3R7P3f4R8/15R9n0100000020000f5/13R:9012X21P4g00S0P4P1P2P6P:n0100000020000=01:X041719P7A6562E2A4638/15P8P6P3P5C5E2UX40W3W1W5o"). Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma munch_grow2 : ltac2:(zQ "71!itc!h9!jc!iu3!l9!iua!iv3&>0@1$2@1$1#k0@1$4@1$2@1$1#8>1f$0>2iv$0>1W@1$6$0>1m~0>2m'~0>0@3$5@3$3$0^5^3^2^1@3$5@3$3$0^6@3$3$0^5^4^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_AB ()) [] "##1^p'0h02H0h11Hh22H1h32H3h41Wh51mh62m'h72ivh82H2h92H4h:2Hxh;2MUh<1fh=3fhih>3floh?2hih@2lohA1xi001pi011zp;1p;3p;2p;4p;5p;6g00o0j1CTg00oPj17Tg0105j1<!s/$Sj1;Tg00Bbj1BTg0116j38Tg0129j24Tg00Wmj22Tg00XIj21!s/$ej23Tg00D@j16Tg00[>j4:Tg00EUj2ATg013>j59!s/$[j2@Tg014_j6?Tg015ij3>Tg00K6j4=Tg016IR0f1R1f0R23>p=0g00M:R3P3P1P2C=p=5g00DYR4P3P3%C0R5g017J#7#7#7R6!s-%#<#;%<6#;#B[R6f4R7f2R8'0?812f5R9f3R:,07R;'0?881[^66]5]4^70P2P!t$$f6R4/59R</08!s\$7R=/54/0;!sW'^56^45P2f9R;f8R>'5!sQ':R?/5;R@/0:RA1597/0:,0@R@P8P1f;RB/5?10<7'0/42f<R</21111B'3#6RC12=11114'3#61491RD'313CD12>8118=!s>%48'312;:11:>!s^$D14=:REf>RF/2:f=RG,1:'3#6/3E14>7f@RE/29R:114EREP9fBRH/2=RIfA,1=RJ!v~$:O1W3W0g00RSRK\E\:12<4R411=<R:P712F>11>G!sS-1PK\:\413IJRJ#6RI14B=fCR=/2>R411>HPK11;=P7P1O1fD,1?PK[P2P1O1PK1AK2b0b2W9X34P2D9X2JPIeP8C:b1b0W8X2DP2D9W0X1CP2D915<B/09/41eW:XA31@A@eP2E?W;X66X56X45X?3X@!yG$O2n2001100000121101101X70X=3X>!sI?<0o"). Qed.

Ltac munch_grow MU iv :=
  lazymatch type of MU with
  | munch (?f :: ?W) ?a ?b => apply (munch_grow2 f iv W a b) in MU
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)


Section CTXFRAME.
Variables (st st' : mstate) (m m' : word -> option byte) (W : list (Z * Z)).
Hypothesis MR : mrep st m.
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis ER : s_regions st' = s_regions st.
Hypothesis EM : s_metas st' = s_metas st.
Hypothesis EA : s_areas st' = s_areas st.
Hypothesis EG : s_groups st' = s_groups st.
Hypothesis ES : s_shadow st' = s_shadow st.
Hypothesis ERs : s_reserved st' = s_reserved st.
(* [comment removed for export] *)
Hypothesis WIN : forall lo hi, In (lo, hi) W -> CTX <= lo /\ hi <= CTX + 928.
End CTXFRAME.

(* [comment removed for export] *)

Ltac amo_align AMO :=
  try (rewrite AMO; cbv beta iota delta [negb]);
  try (rewrite Z.eqb_refl; cbv iota).

Ltac amo_step AMO :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with Some ?w =>
    let d := eval vm_compute in (decode_any w) in
    lazymatch d with Some (?i, ?sz) =>
      eapply evt_step;
      [ split; [reflexivity|];
        rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
        exec_cbv; simp_regs; amo_align AMO; exec_cbv; amo_align AMO; simp_is_x0; simp_regs; vnorm_for i;
        try solve_load; try solve_store; reflexivity
      | simp_regs; vnorm_for i; mem_after_store_opt ]
    end end
  end.


Ltac fix_lit_store :=
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
           change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) =>
           change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) =>
           change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z)); mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) =>
           change (Z_to_le_bytes 1 z) with [Z_to_bv 8 z]; mem_after_store
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 ?z))) _) =>
           change (le1 (Z_to_bv 64 z)) with [Z_to_bv 8 z]; mem_after_store
       end).

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; fix_lit_store; try nrm.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma step_seq_eq : ltac2:(zQ "h20!m2!hl8!iva!hj0!jg4!jgc!jh2!ij0!hvf!re!jhc!ji3!jj8!tb!jk3!jl5!ind!jle>2st$1@3$9$1@1$c^1M3\0$3$1@2$e@1$4@1$5^1+vf@2$2@1$6+1@2$2\1c$a@2$b@2$f@4$h0$0$8$7$0@4$h1$0$8$7$0^1^1@2$2@1$6@2$d@1$4@1$5^1+1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_AB ()) [] "##+Dp'0h01ch11bi001bh22stp;1p;2p;4p;3g017oj15Tg0192j13Tg01:7j11!s/$\j16Tg00>Zj2?Tg00:Kj4=Tg0051j4<Tg01;:j2;!s/$Mj2:Tg01<^j27j12Tg01=ej20Tg00Y]j24Tg00ACj39Tg00Cfj28Tg01>lj1>Tg00N]R0f0R1#5#3R2g017JR3#1!s$06'?R4g00QSR5P5P5P0P1g01@4R6%63R3g00M:R7g00P>R8g00Q5R9P7C=P7P8P9P7C<';/:1R7'7W0f2R9'0%31/43/71X06/09n010!s#$20000!t1%%23R8P7X06R6/09'0%59#3/43#2!sX4590P1f1R9,06,08,8!sS1,80n011!sV,b1%>1!t5$41061,08142!sR$1!t#4eW2o"). Qed.


(* [comment removed for export] *)
Lemma rec_set_usage : ltac2:(zQ "70!m2!hje!re!hj7!hi9!hl8!jmc>2st$5>2sc$0>1v$0>1q$3@3$2$4@2$1@3$6^3^2^4^1@2$1^4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) [] "h01qh12sch22sth31vp;2g00?Uj21Tg00Cfj20Tg00N]g00M:R0g002@g00KVf3f0'1'0W0X30W1W2o"). Qed.
Lemma rec_set_active : ltac2:(zQ "80!hje!re!m2!hj7!hi9!hl8!jn8!jnf>2st$5>2sc$2>1v$6>1q$3@3$1$4@2$0@3$7^3^2^4^1@2$0^4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) [] "h01qh12sch22sth31vp;2g00?Uj21Tg00Cfj20Tg00N]g00M:g008Gg002@g00KVf3f0'1'0W0W3W1W2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mw_ok : ltac2:(zQ "10!hi9>2mr$0P") := ltac2:(zQ "90!r8!u1!joc!jp9!jq6!jr1!hi9!u6!jrf\2mr$6@2$0@2$0@2$1Z@1$3^1@2$1@1$3^1+hf@2$0@2$0@2$1Z@1$2^1@2$1@1$2^1+1@2$0@2$0@2$1Z@1$5^1@2$1@1$5^1+jf@2$0@2$1Z@1$4^1@2$7@1$4^1@2$8+2+j4").

Lemma meta_word_range : ltac2:(zQ "70!js5!r8!kh7!hi9!u1!u6!jrf>2mr$3>0@1$2^1@2$1@2$4Z@1$0^2@2$5@1$0^2@2$6+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_AB ()) [] "##::h02Hah16__sat1h2!s/%3h34__x1h44__x2h54__x3h64__x4h72FBh82LIh92MLh:3SCRh;7__arithh<4__ffh=!sq%0h>!s/%2h?8__varmaph@5__withA2mrhB5nd_i3p;1p;2p;3p;4p;7p;8g01A:j1lTg01BFj1OTg01:7j1:!s/$\j12Tg00Wmj25Tg01CPj1BTg01DZj1DTg01Eej1CTg00oPj10Tg01Fmj2MTg00XIj24Tg01GJj1KTg01HWj2ZTg01I?j3X!s/$cj2hTg00Cfj2VTg01JDj13!s/$cj2UTg01KLj2=Tg01L5j3<!s/$^j2RTg01MJj2`Tg01N6j1_Tg015ij3Q!t^$0j1^!sA$Vj2PTg01O4j1]!s/$Rj4NTg01P0j1\!s/$Nj1[Tg01Q9j2L!s/$\j2@Tg0105j1STg01R?j3T!s/$bj4JTg01SMj1k!s/$oj3HTg01TRj3ATg01U5j2j!s/$Wj2iTg00ACj3gTg01VCj3f!s/$bj4e!vG$ej2ETg00Y@j2F!s/$]j2GTg01WTj7cTg01XYj3dTg01YBj7W!s/$fj7bTg01ZJj8aTg00]dR0f1R1'5f0R2'Ep=11502p=;g00M:R3/U2p=9Ad312p=6f2R4g01ZnR5g01[MR6P6g01[mR7P3P1g01\MP2CJg01]4R8FWp=71L32p=8P1P5P6P6P7P2P!s@$YP4!s9+1P2Fbp=>f3R8!s;+4P1P2Gap=?1512,E4p=Ig00KV%l2%O1!tR$7JR9#:R:#!s$$R;#2R<,55'1R5%B1R=%29R>,5='1%D1R=%:;#2R;!s7%C1R=%09R?#2R@%0:#:#0#0RA#2RB'MRC,4='1%K!sL$?RD#0!sE$E#0RF#2RG,M@RH!sJ%B4R=15=>'1%D8!s1$;'1f4R=#CRI14IC'11Z@B140@RI%;B140C[RJ[%;@RKg01]TRLAX@B1UW0%;C\L^0K1Z@G%;G140H[RB\IAX@G1VLX0K%;H!sH$!w7$^01h0@'VPIeRIO1PBP=PIO1PJg01^VRJg01_BRI#3RB#3RK#91U3IRI'6%0FRL#2,=3%3KRK#3#3RM!s+$N#3#3#95<31=3@%9NRN5<3%9MRM'6'6,6Ig01_aRO'R'`%0L!v7%#0#2RL,=3=<3N1=3G=<3M%2ERE,=3%9K!si$B/6I'6'6'6/RO%_J5QJ3Q%^JP3P31P3=P4%]3CNP11P38CN%\3%[3RJ1L30RO1@3DRD57JP3PDg01`MRI%8@R@%SA5T3CJ,YJ5>J%k6R6PJ1@3:R:97JO%8;97J:5>JP!s>%?R?!s>%>97J?!s>,9R9!s>%<97J9!s>$%8E=H3?9A39%8G=H3:5A3%8L=H3D5A3RD97JOP3PDPI%SF9T3@!tU'C?!s$%1jJ7P2P4g00QSRJg00R3R7'V1i24=gJ7dAf301Ceb<b?b@X33X43X53X63%;8R1148C'EAI18;AI18>AI18<f5R1,FE,G=f6,FG'Gf7RG,FL'GRL14LH'1[[[[^33^43^53^63P2f<R3#C%D3%B3%O3PGf8f9f:O8b;b2b1b=b1b>b2%K1R1141H'1eW9W:W7X85P2FcWBWAo"). Qed.
Lemma meta_word_last_idx : ltac2:(zQ "70!re!m2!kh7!js5!jp9!hi9!ki0>2mr$5>0@1$2^1@3$0$1@2$6@1$3^2+hf@1$4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_AB ()) [] "##;Hh06__sat1h17__arithh24__ffh3!s@%0h48__varmaph55__with64__x1h71zh82Hah94__x2h:4__x3h;4__x4h<2FBh=1Hh>2LIh?2MLh@3SCRhA2mrhB5nd_i4p;1p;2p;3p;4p;8p;6p;7g01A:j1lTg01BFj1;Tg01:7j17!s/$\j12Tg00Wmj24Tg01CPj1@Tg01DZj1?Tg01Eej1>Tg00oPj10Tg01Fmj2KTg00XIj2ATg01GJj1JTg01a4j2Q!s/$Rj2ETg01HWj2aTg01I?j3]!s/$cj2\Tg00Cfj2MTg01N6j1Z!t1$0j1Y!s8$Vj2GTg01O4j1X!s/$Rj4LTg01P0j1W!s/$Nj1VTg01Q\j2CTg01Rbj4BTg01U5j2U!s/$Wj2TTg00ACj3FTg01VCj3R!s/$bj4STg00Y@j21!sn$9j2PTg01SMj1kTg01ZJj8jTg01b2j3i!s/$Uj6hTg01c9j4`Tg009Kj6N!s8$Zj6_Tg01d6j1^!s/$Tj3bTg01WTj7c!vP$ej2d!t1$oj3eTg01TRj3fTg01YBj7[!t^$]j2H!s8$fj7gTg00]dR0f1R1'4f0R2'dp=3g00M:R3?F12p=51402p=D1P32p=6Ae312p=<Af!s-$:P1g01ZnR4g01[MR5P5g01[mR6P2g01]4F[p==f2R7/H1/H2p=91112,H7p=8P3!sd$\MP2CBp=IP7P4P5P5P6P1P2Fgp=Og00KV%l2%;1R8g017JR9#7R:#7#7#7R;#2R<,48'3R=%@1R>%29R?,4>'3%?1R>%7;#2R;!s7%>1R>%09R@#2RA%0:#7#0#0#2RB'KRC,A>'3%J1/Q</58%@7R8148?'3f3R8#?R?14?;'3f4R?#>R;1A;C'3P3f5R;#JR>%7@#2RD,KA'EREf6RF#;RG,52X731aABRH1A0ARI%DB1A0C[RJ[RK%DARLg01]TRMA]AB1UW8RB%DC\M^8LRL!v=$^01\0A'MPIeO1RIPJg01^VRM#ZRC%YMRMP3P31G3?P7%X3R?CLP11G38CL%W3RN%V3ROP31C39R91C3@RP%6A1C3:R:'<':%0@R@!v#$0RQ#0RR#0RS#2RT#6!sT$@!sK$2QRQ#6RU'<':g01e7RV1<UP,:9%2RRR#6/<:':%0S!sp%!vu$S#6/<@':CB'=1UO6R@P2P7g00QSR:g00R3RP'M1T27=F:PdAR301CSRPb2b4b5X63X93X:3X;311A711T8591=82QA82Q111R711S839'5^63^93^:3^;3P2f9R8#>%?8%@8%;8O4b1b0b3b0%;;R8%@;R7%?;R:,1A%>;R;,1T39;8QA88Q711R:11S;39'5P3%@FR;%?F!sS&FRF!sS$RT=8GQRA1E2Qf7#;R7'5X73P31EGQ1527X73PHPKPBPLPIPJPCPM1G31PNPO!{I'1P30R7/I9,=ORW%6<,!s1$5OO%k5P3P9g01`MPUCB,=O9OOWGjP@P!v;,142<,321A1Q,31[^63P2f:#;f8O2!ug'9iGQ1EAQPGPTPQ!t`3P?!t^/P3PUPVP7!t>$Eh!t:,AF3Q0g00RS[P!t$+C`ENA8GQ;!vN&F39P2E_b=15E8e%^D,Q>!t>7%6D,I7,=O!t-,%DD!s~,9b>DENW?W@W<X>=P2FcWBWAo"). Qed.
Lemma meta_word_sc : ltac2:(zQ "80!re!m2!kh7!js5!jr1!hi9!ki0!ki7>2mr$5>0@1$2^1@3$0$1@2$6@2$7@1$3^2+6+jf@1$4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_AB ()) [] "##BEh06__sat1h14__x1h21zh37__arithh44__ffh5!sK%0h68__varmaph75__with84__x2h91Hh:2Hah;4__x3h<4__x4h=2FBh>2LIh?2MLh@3SCRhA2mrhB5nd_i5p;1p;2p;3p;4p;6p;7p;8g01A:j1|Tg01BFj1HTg01:7j1>!s/$\j13Tg00Wmj26Tg01CPj1?Tg01DZj14Tg01Eej1:Tg00oPj1<Tg01Fmj2STg00XIj2@Tg01GJj1\Tg01e^j2ZTg01a4j2X!s/$Rj27Tg01f>j2LTg01HWj2mTg01I?j3i!s/$cj2hTg00Cfj2[Tg01N6j1d!tC$0j1c!s8$Vj2KTg01O4j1a!s/$Rj4QTg01P0j1`!s/$Nj1_Tg01Q\j2ITg01U5j2^!s/$Wj2]Tg00ACj3NTg01VCj3{!s/$bj4zTg00Y]j2A!se$9j2YTg01SMj1yTg01Rbj4J!ui$ej2PTg01b2j3s!s/$Uj6rTg01c9j4qTg009Kj6G!s8$Zj6WTg01JDj1D!s/$cj2ETg01XYj3MTg01L^j2UTg01MJj2lTg01KLj2k!sA$5j3jTg015ij3T!vb$[j3nTg01g>j4o!s/$_j3gTg01d6j1f!s/$Tj3pTg01WTj7e!u<$oj3tTg01TRj3uTg01YBj7v!ui$@j2w!s8$fj7xTg01ZJj8bTg00]dR0f1R1'6f0R2'Pp=5%<2#<p=Cg00M:R3?N12p=11602p=F1Y32p=9At312p=;Au!s-$8P3P1g01e7P2CJp=O!s4$ZnR4g01[MR5P5g01[mR6P2g01]4Fvp=2f2R71w12'Ap=0!sh&\M!sh%=P7P4P5P5P6P1P2Fxp=Bf3R8!s;+7P1P2Gbp=R1612,P7p=Vg00KV%|2%H1R9g017JR:#>R;#>#>#>R<#3R=,69'5R9%?1R>%3:R?,6>'5%41R>%><#3R<!s7%:1R@%<:RA#3RB%<;RC#>#C#3RD'SRE,@@'5%\1%3CRC'Z/X</1>%?7R>16>?'5%48!s1$<'5f4R>#:R@1@@E'5P3f5R@#\RF/ZCRG1SBCRH'7f6RI#4RJ,12X23P31LFHRK172H/1JX231mBDRL1@0BRM%FD1@0E[RN[RO%FBRPg01]TRQAiBD1UW:RD%FE\Q^:PRP!vs$^01h0B'[PMeO1RMPNg01^VRB#dRQ%cBREP3P31K3>P7%a3R>CQP11K38CQ%`3RR%_3RS1I3:R:%<ART#<#CRU#3RV#91I3ARA';'8RW1I3;R;%<U!sC$X#9RY1I3TRT';'8/;Y'81;Y;,8W%CU#C!vk$U#9/;T'8'O'21^S6RTP2P7g00QSR;g00R3RZ'[1]27=N;ZdA{301CzRZb4b6b7X13X83X;3X<3A02V1R;A07X8;0XA0;X7?0U8'1^13^83^;3^<3P2f9R;#:%4;%?;%H;O4b3b0b5b0%H@%?@70VR;%4@R[%:@R@70X!ss&[?0U@'1P3%HI%?I70VR@%:IRI90JXR;;0XR\1L2X/7Xf7R]#4R^'1!x:&@XR_/A;172XR`/1^!s=$P0%:]Ra90^XRb,A2/7X!sA&LPOPDPPPMPNPQPE!wa$7P1P>CQRcPR1;AY,8:1Y30Rd1;YA,8:'8'O,2SPTP!v90A021XA02X1,A0!v$'P2f:Re#:%4eO2!ut'A0JIX1A0;'1P3A0^aXRff8Rg#4Rh,1`!u?%7^X112h!tr61K31PRPS1=d:,2SRh%9<,=:,2S5BS%y5R`P3P:g01`MRiPYCJ,2S9BShCR!u%0162<,52%F1R<1@1X'P[^13P2f;#4P]!t|,9s^X17fXP^PaPX!vO4>PRPS!#30&1OYd,2SEr!t8,AN3X0g00RS[P!sz+R6CqEG1A0bP2EWb9P_!s~/g01_BR_#DRb#DR0,E31E3_R_5M3%D0R0#D#D,E39M3_g01_aR5'U'l1k3V1E305j31E3b=M3_5M3/U5=TBQ5TBPEPc!vU&A,2S%9?,=A!vS%P`PS%9=!vc%9BShP`1=dW,2SP3PWP!vc'5BSCR!vd2X83AV<1?AV<1=A07V8RV1@VX'5[[!xq'%?e%HeP]Pg!{h,9n@XEG1L\XP@P;PXP6CoEGA0@XJ?0UI!v5%17KH/1[ePG!w=7%9C,=d!zH0%FC!w'-Z9gFCEG%fC,XGApGCZEGW?W@W=X>9P2FeWBWAo"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)





Lemma land_upper : ltac2:(zQ "40!u1!m2!ki0!r8>1f$1>1a$1>0@2$0Z^2>0@2$0Z^2@2$3@2$0Z@2$2^4^3@2$0@2$2^4^3^4").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_AB ()) [] "##@}p'0h01bi001bh14__x1h21Sh31ah41Hh52Hih67__arithh74__ffh84__p1h98__varmaph:5__with;4__x2h<4__x3h=4__x4h>1ih?1zh@1DhA1EhB2H0hC2HahD2HfhE1fp;2p;1p;6p;3p;4p;7p;8g01a4j23Tg00Wmj2GTg01hHj2<!s/$bj2VTg01N6j1gTg00o0j1`!s8$Vj2HTg01P0j1[!s/$Nj1ZTg01Q9j2Y!s/$\j2DTg01SMj1oTg01iGj6lTg01U5j2aTg00Cfj2>!s8$Wj2_Tg00ACj3:Tg01VCj3]!s/$bj4\!se$kj28Tg01jJj2B!s/$gj21Tg01kHj25!s/$ej16Tg00?7j20Tg01lCj3F!s/$fj3NTg01mJj3X!s/$lj3MTg01nOj1WTg009Kj6J!s8$oj2qTg00Y]j24Tg01cZj6pTg00b7j2CTg01oWj2nTg00XIj2UTg01JDj1=!s/$cj2KTg020=j1k!s/$[j2fTg021<j3eTg01XYj3OTg01L^j2cTg015ij3QTg01O4j1b!s/$Rj4RTg01:7j1d!wI$Pj1STg01Rbj4LTg01TRj3TTg00[>j4hTg01YBj7i!t:$ej7jTg01ZJj8^Tg022Ij7mTg00]dR0f0R1'Gp=2g00M:R2f1R3g01\MP1CLp=AP3g01ZnR4g01[MR5P5g01[mR6P1g01]4Fip=9f2R7P4P5P5P6P3P1Fjp=If3R8!s;+7P3P1G^p=?g00QSR9?:31p=7P9f4R:P8!sG%EJp=@A:231p=;g00S0R;9:91p=EP!t/1mp=P%23R<1387R=#2R>1G=8g00Xe1331#2%27R?/<<R@[%21RA,<<1373#2[RBP>\@1V31P1n20010!s#$12!s-%0X02X32PB^02^32P1P:P8p-0RBg01^VR@#gR>%`@RC1H23%[2RD%Z2RE1Y20RFg017JRG,D2RH'A,9ERI%o5RJPE!u6+8El9IEIC?1aE6R6P1P7g00R3R5,>91_17=:95dA]203C\R4b7b9b:X12W81<<7\A^12^8BP1%2:f5RBP8O3b6O3b41887/B=R=18B:RK/13RL13B:RM/13RN'5f6RO/17RP/71X0911B3RQ11:3RR#6'013OBRS/17,51,7PX0910QR11B7RR#6,0P/!s>'PQP9P911O8RT#6,01101T'5,71P1PRP9P9%61RT,05RU1051RV'59:95P1%65RW,051055'5,>9%6;RX!s7%;!s7$n01!wX%!wV$b0!sv%10;TRT10;1RR!sr$;P110;W10;!sn%10;X10;!sj9!sz4NAFB:3D@PLAN!s/$1BKMRL/13AXKM3D@X5AX>25M81;8=18:813:8'3R=18OBRN/13RX11S3R5'01107RW,!vr&O3RY%6Q'0f7RZ/3OR[/17,01/7W!vp$YQ11Z7RQ%6P'0R\/!s@'P9P;10QP,0\!we%PY!w'%Z8RY!w''Y'0#EP1PP!v2%UV#EP11>9;R;P;!u\4!sL&TR!sZ$!sH6!s631103%W3EJP5AFOB3D@PXAN!s/$13NSRX/13AFNS!v?+7M0A:2=01qKM13KM,4L14KM';P2PX18ZORX/B[RM/4114X[RX';X?2P1P0P3Ep1BNS/4014NS!sX$M1410f8RM/8Z13MZRN'4!sW'ZP8EJ14Z0/;X1VMZ%2N%2M%2Z'<'Cf9RZ/nM18ZM#2%2Z1UM0'<'Cg01_BRN#=#=#=RX!s-%,K2%kG,f21K2X5e21K2N5O25O2g01_a'cRNAQ@N>5Q@PCP2P2%b2P71H2:CRP31H28CRPDPE%dGRD#S,D2R:,AF,9E%S!~W$G!s4%RCP21D2DRDg01`MPFCL,9E5IE5PEPJPE1AFD,9ERD9IEC9PEIPJPEP2AT2GFg01e7AT2:H!s[$!s@$D!s+$CPJ1AHG,9EC?!s$'P6P!#3,+X;2X<2X=2%28R41U70,<<'C1<?4,C<148014B7';%2BR01GBO\0[[[[^12^;2^<2^=2P1f;R1f:R0'8P0P11310P3P7P8PMPZO9b6bBb4b2!s$$@bAChXC<WDX32XE2o"). Qed.





(* [comment removed for export] *)
Ltac unmask64 K :=
  try (change 18446744073709551615 with (Z.ones 64) in K; rewrite !Z.land_ones in K by lia; rewrite !Z.mod_small in K by lia).

(* [comment removed for export] *)
Lemma meta_word_meta0 : ltac2:(zQ "40!re!m2!js5!kj0@3$0$1@1$2$3Z").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_AB ()) [] "p;2g00Cfj20Tg00M:g00]d'0o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
