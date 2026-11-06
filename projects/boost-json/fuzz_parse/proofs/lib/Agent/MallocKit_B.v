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
Ltac2 kr_t_MallocKit_B () := KReplay.lz_vm "#$lXC47Corelib7Classes9Morphisms6Proper!sI-Program6Basics4flip!sg?Krespectful_per_obligation_1C46Stdlib5Lists4!s+#2InI!su+4Init9Datatypes4prod00K!sFA1!sF=list01C5!tE&6ZArith6BinInt1Z2le!sB>t!tf25Logic3and00C!sA8notc89OSSVerify!vj#ofs:boost_json:fuzz_parse3!u}#Agent;MallocKit_B9ivs_avoidC13~~~!tQ,7Numbers7BinNums1Z00!to85False!sC4!v430!vTB2!t'82eq!us:7f_equal!sC88eq_ind_rK!s{;1!t=9or00I35stdpp9countable9C!s0'00C!sD&4base;RelDecisionC!wPO3Lib5Frame7outside!wF%K!td;1!s@<2K!yM<1C!w:;8!w:#!vA#!sc84True!tA/!x{38positive!tL/!yH4N!xC#!vj&bitvector;defini!}W#s2bv!yN>6op!sL#00!vxZ5munch!vv%!},<3add!u9>Z02!sa=pow!tiT3Mem2wa!td%!}sb=!}o$_!yW0C!w7@;bv_unsigned!uN<>pow_pos_nonneg!sN<:!sN#!sJB7compare!~[<3nat!y[#!sf&9micromega=RingM!s4'5Psatz!sOM6!sO6:Z!sL+;!tu%!w9$!s{86VarMap1t!sDB3I!sD?0I!t}C7Formula00!t567Env!sT#5PExpr!|y?!}F,1!snE3K!tdL!#;1<!}S'2!t>E!taF7C!sI55Tauto8B!tZ&C!x?@=Z!sT$CheckerC!w[<4find!sqAC!sq0_sound!~EX;wa!|{,!~Ng8agree_on!#8z&!vR;G!x-'4!sJF5!sJF8!yID3Op203!x5<5eKind!#>a<unit!{j8!se%4kin!#BW?!sf$1!#8wY3ivl!#<m2!|p=3!#8}?!#?>8!#<?$!#;1<:!#5}$ison!#3;7!#4i:0!#6V@1!#5\M1!xQI5!x2=bool!#Cm>!sF$!wjQ4Spec6!{i%4aptr!#;'%!#Bb%7tactics<!#D:%_help!#C#'gmap;!s'#_looku!s?1:!s?$empty!s>09!s>$fmap!s=6o!s=3!sl%merge!sl7old!s='8fin_maps@!t[%_insert_eq!t~6fin!t8/base4f!s836!uL&!vn\o!vn4!ts;ne!sH5!sA&!u=+I!u=/!s'$!#GR,!s5#B!uQ$partial_alt!#O\-!yB22i!vW+9decidable;prod_eq_dec!sD+!#Hr'>!sD$!s5+!u#4:!tL#!t|%!vQ\7s_metas!#E&2N!#A''Nat1N3eqb!#Dd<!sC#!|2<andb!tm\<get!to$_rec!trB8eqb_spec!~-<7reflect00!uB<!sk+!#>eC1!#Ne76eq_sym!sB89!#Pe#_i!#<kQ!v-/8aptr_!w6#!v&%!sn[9s!vv&s!sob8pu!so%!},1!~,%!zZ&!#7w;fs!sC>sn!|?+!w9&;from_!s2%I!#3&[!t{#00!#UrCN!#NcQ!t2/5!t2$!t1&!sk[6mstate!ty'!#Lt&7n!tw%1N6!#3>%!s?3Z6!#3W:;N!#3T4!sD-Z!sD,!#;9A2!z7]del_slot!z7c7s!smh!{o$!so[3Lib2Nd9ex_elimF3!sj]:ex_intro!skX!v72are!~7X!#Hn$9!sn%Rep9!#6x#!v<#!#6y2!#8P2mul!#A<]add!vX^and!wE0!~y]!vV#!|~+!}n\NSLOTS!#6VbAREA_HDR!{FcMETA_SIZE!#3M&!~7'!#gg$7!s+#Def3map!#h&69nth_erro!#@h25Peano2lt!sx<seq!sZ23Nat3!x[#!y^;6of_nat!#N25;Zify!#jH%7rew_iff!sm34Znat5Nat2Z9i!#[2&!#OqE3!so>7inj!t:$!#=g67iff!#>+$!t~@;!t~&_rev!#Yq?!#cc<7na!#cb#!t8B5mkrel!sKB6mkapp2!sqEapp!#B%;!#NK#0!vW>6!vW#lt!sH+5!sG$8!yL$!xu#!xy:!wA3!sIA8!sI#succ!#OPH!#o,<6to!z7$!~S\active!#6re2pw!#6kCax!#m98!yz%fl!#F\<max!#F\1!#UG53!#]t=3Pol!#S_E!#c:%4!#[eaA!#4+'_map_seq!w$f7!wr%!#;g%!~~F6!|968!|9#Inst@!#4a$_!yW%_eq!#Dd\usag!yYhwz!slf6!t]$!#C,cbounce!#?tf2b8!slf8!t_&!#Dgcun!zQm:!ss+s!#==2!#Q42length!#=A6:!sA%!ta$!sE>mapK!#5=[!#KZ%1!v[b5s_ctx!wHcs_region!#Qzcs_shadow!snb:s_next_rid!t`egroup!uPc6s_tick!v>fecret!v>ereserv!#mS&!#Ts]ctx0!#Shc!yU%!sne!yT%!snd4ghdr!#UF+!#=x6eq_trans!sD83!#E~/!$2v4?eq_p!$3b#!s,#xy!#3+'4Bool!s'$=andb_true_!ssBI!#_2#xive_!s0,!s}&!s\=F!sR0!tX-!sY3>!sY+_Prop@and!#Gi#m!s=&!#a<;6eqb_!#K@-!tS5:!$5v+!sM?NR!tz,!#fa&pp!tP6!#Dz2!tPEM!x3$_co_!$1L#v_impl!t$,!s`4?Rel!$7g#!v<'!v%#T!sj#!#qw#!sWE=!sW#!uF+!#:J_=!#ba&!#EA$!zk$!#Cma@!#fd-_put!s|h<!tw+n!#=;W!}Q0conc!sjb3!#;9'!uObD!#Z5'_same!#[5k:!s~$cells!#4xU!#ys#C!sc#4!si#!#Y>c1M!sgb5queue!skb6m!#=j#!slb8o!#k}h8!|7#hea!#?Fb:m_set_prev!spi!vBgupd!#m`-!sn\s!vB0!#Fj[<undef_!|j#!#rL#!sta2ev06!~\h8!{=$_st!{@e!xn,!uNU5STree5stree02!#36U!v<3!#Atb5l!xc#!sm'!w'i!#9-c9free!{<-!tebE!#;o2!#8O#!t%h5fm!yj+K!wJb2!t`h;ivs_cover!#JN&!#e[8!#DI#!$:/U!$5@$6sub_fp!xVV!sj,<!$G}#_weake!$:$%!#DL<modulo!$Ek@7Z_to_bv!#\g59SatDivModCZ_mod!#i]%!$EL&!u7S6MState<!$=+&_li!#3_&4ELinuxProcessSemantics5Riscv3Sem;amo_al!s^$K!sT@5Instr6awidth!$5GQ!y/%=F_m!y1$_!|`#3sxv!y%3!#Fy;eq!#GQ/!w>?8bv_swrap!s}E<eq!#Gw,!#Ib=J!#La+eq_dom!#MF+C5!s]+!#eT%6PosDef3Pos!#p7?7pos_sub!y7+;setoid_ring>Algebra_syntax8!$8W#it!#NW?@!#NW2!uxISymmetric!sUE8s!sR%y!xld9sxv_ran!#d[g;wz!$Ei1!tnfextw_!zb-!wk66Nc!s,#;eq_not!vG%!sN>>!s'#_plus_comp!#m3<!y'#!sC<opp!yH9!t3%_!{n$al4Zops!sOG2Zr!vLd:!vL+'!#69A3lo!t=e;lor!yS%64!#8CY8PropExec;Z_!st+!u2B7testbi!$4^=orb!tX]>Z_!t/&_hig!$[$B8!u+#spec!t?]AZ_bounded_by_bits!tBB9mod_s!wO#!teAcomm!xSd=!uW$xv_mod32!thB;lt_le!#_>%!~Zdle4_cong!$Dv%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4prodhc4pair37Corelib4Init5Logick93andk93not36Stdlib5Lists4Listm92In46Stdlib6ZArith6BinInt1Zo12leo12lthc3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentbMallocKit_B~~~~~~q99ivs_avoidhc4cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hg07outside04Npos35stdpp9bitvectorbdefinitionshkd2bvhc6option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hn92wak92eqo13addq98agree_onhg03ivlhg05muncho13pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~hu54metahc4boolhu54aptrhu5cget_meta_rechu58aptr_eqbhu56mstatehu58put_metahu58upd_metahu59del_slotshu57s_slotshu59set_slots01N79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~iq09meta_slothu57s_areas35stdpp7numbers1Niva6eq_dec35stdpp7numbers1Zjh56eq_dechu54area25stdpp9countablejj8bN_countablejj8bZ_countablejj8eprod_countable25stdpp9decidablejn9bprod_eq_dec25stdpp4gmapjp94gmaphc4Someiq07activesiq02pwhu56activem99nth_erroro16to_natiq06usagesiq02wzhu55usageiq02b8iq08bouncesshu57bouncesiq0aunmap_seqshu59unmap_seqhc6lengthhc3nathc5falsehc4truek93iffhu54optrhu54conchu53ctxhu54mctxiq0ameta_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ko64cellhu5am_set_nexthu5am_set_prevhu56m_prevhu55lheadhu58set_headq97fm_linkq99fm_singlehu58get_headhu51Mhc4Noneq98queue_sthu56m_nexthu55queuehu55LFreehu55meta0q95fm_sthu59free_metahu56regionk92exhu54ghdrk92orhu56r_base25stdpp4baselpe6lookupjp9bgmap_lookupiq03CTXhu57RKGrouphu56r_kindhu55r_lenhu55rkindhu5bround_up_pghu59s_regionsiq05lr_lohu55Knownhu59cell_readhu57cellvalhu5aget_shadowhu58s_groupso13subq9bivs_covered3h5LinuxProcessSemantics5Riscv5Instrmm52AW3h5LinuxProcessSemantics5Riscv3Semmofbamo_alignedo16modulohkd7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdF_malloc_free~~~~~~mt43sxvhkd8bv_swraphn93le4o13lor" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ivs_avoid : ltac2:(zQ "30!h9!j4!jb>1W@1$1@2$2$0$0>1P>0$0PP") := ltac2:(zQ "90!h9!jb!j4!k2!ld!m3!nc!p9!pe\1W@1$2@2$1$0$0\1P>0$0P>2lo$0>2hi$0>1a$0>0@3$6@2$1$0$0@4$3$0$0^3^2^5>0@2$4@2$7^4^2@2$8^2^3@1$5@1^6^3").

Lemma ivs_avoid_nil : ltac2:(zQ "40!h9!q3!jb!ud>1P>0$0P@2$3@1$1@2$2$0$0^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##&Qh01Hh11Ph21ah32hih42lop;2p;4p;1p;3p-1R0p10000p4p710p9P!s6%SR1!s8,P!s2$2!s3/31!sS,1!sQ-g001iR!st'8g002@j28Tg002`j47Tg003@j10TP0j31!s5$`j26Tg004<j22!s/$Xj23Tg0053j14!s/$Lj25Tg006[R0p-0[1800R1P0P0f2R2f1C7%01R131g0079f4/62f3R3,22'3f6P3O1#4[f0R3n0!ue$000W0X20X30X401513eW1o"). Qed.

Lemma ivs_avoid_cons : ltac2:(zQ "a0!h9!jb!ud!v9!j4!k2!ld!m3!p9!pe>2lo$0>2hi$0>1W@1$4@2$1$0$0>1P>1x$0P>0>1a$0>0@2$6@2$8^5^1@2$9^1^4@1$7@1^3^2>0@2$2^3^2@2$2@3$3@2$1$0$0@4$5$0$0^6^5^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##34p'0h01ah11Eh22H1h31Hh42H0h52H3h62Hah71eh82hih92loh:1zi001zh;2H2h<2H4h=3Hinh>1Ph?1Wh@3hi'hA3lo'hB1pi011phC1xp;2p;1p;3p;6p;8p;4g002@R0j2?Tg007Vj1>Tg003`j23Tg004<j24!s/$Xj25Tg0053j12!s/$Lj2:Tg0086j38Tg001ij36!s8$VR1j31Tg0090j67!s/$Mj89j6;!s2$kj2=Tg002`j4<Tg006[R2P2f1R3f0R4C<p=01?22R5#>p-0^C2f4R6/34f3R7,44'5f2R8P3O1#2[^021:831083f8R9f7R:'0R;f6R<585565g00:Ef9R=/09R>1078R?515A65?:13681487'5P9P7!sv$P4f:R?/0=1067R@515f5RA/371476'5RBP1P5f<R1f;RC'0RDA153;P1P:!se%310<ARE915Df=RD/0110:<RF515P5P2P0P2!s$$4P4n2001101000120100100X75f>RG/0DP;P4E7A12D:!s_23!s_;?R0/0GR;P>P3!sa$0=f@R>=12?P4fAR?=12CRHP2P1fBRI=121RJP?P1!u1$X:2P4PJP2PDPIPDO1#2X:2P2PG1334fERG!wB%DRD!wB-03G10>0515PDP0O1#2]1]2X921304144D'5fCRJ!sX/0D=15;P2P013I41443'5fFR0!sJ/I310I?515P0P?!s|+8213?4144>'5PG!sV/?>R?=15?P3P>P1O2W1W2PGP7P3P4G9!s4$DP7P>P=G9PJP4E;b<X5HPI!s1$5W4P4O1b!s+&W3P4O1W!w-$2!w-%000101A154FPCP<!vO%B5PEO1P41=5FO1b3W6W1P4O1A65@9P:P<PAP6P3P4O5X6BW=P4O1!x&$!sw%21!x0$0000W3X02X@2XA210A6=857/:8eW;W2W>W?X82X92o"). Qed.

Lemma avoid_outside : ltac2:(zQ "50!h9!j4!jb!ud!hjc>1W@1$1@2$2$0$0>1P>0$0P>1x$0>0@2$3^3^2>0@1^3^2@2$4^5^3").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "p'0h01Ph11xh21Wh32HPh42HWh51ah62Hah73Hinh82Hxh92IHh:2hih;3hi'h<1lh=2loh>3lo'i001pi011zp;2p;1p;3p;4p;5p100:_p4p710R0p100;=R1p4p710p8P0P1p4p7210p8g002@R1j2BTg007Vj1ATg005Lj22Tg00;Vj21Tg003@j1@Tg0086j33Tg003`j25Tg004<j26Tg004Xj27Tg0053j19Tg008Vj38Tg001ij34Tg009kj2?Tg00<[j3<Tg00=5j3;Tg00=Oj4:Tg00=jj5=Tg002`j4>Tg006[R0P0f1R2f0R3C>p=01B00R4#AR5P4p-0\0R6f2R7/22P7P2O1R8f4R9/17[[^10]0R:X25%@4R;/22g00>L11;7eX38W4X10X06P1P0P0f3R19349/22f6R;f5R<534/17\8[^10^06\:^<5P310<9=341/22f7R=/57167;'7R>#9R?11<7P7f8R@P=P110@=RA=84AA44A;1?4A3<P3P2O6X8>P?eP9P1P71072=44@15121627'7P;P9P1P7f<f;'01091R9584f:9449;;2P3O5W6W7X50X;0X>012<1eP3O4C:10=;=34</17eX38W4X10X06X9:X25X:0X=0P2P3O2n2001100000120101101X54P3D=W2o"). Qed.

(* [comment removed for export] *)
Definition agree_on : ltac2:(zQ "41!hk7!hma!hn0!h9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>1A$3>1n$3P") := ltac2:(zQ "a1!hk7!hma!hn0!h9!hr3!ld!hr9!hre!p9!pe&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1m~0\2m'~0\1A$3\1n$3>1a$3>0@2$5@2$8^3^1@2$9^1@2$7^3^2@3$6@1$2@1$1@1$0#8@1^5@1$4^2@1^6@1$4^2").

Lemma munch_agree : ltac2:(zQ "e1!hk7!h9!hma!p9!hn0!hre!j4!ld!hs4!ud!hsf!ht6!pe!htf&>0@1$2@1$0#k0@1$4@1$2@1$0#8>1W@1$6$a>1m~0>2m'~0>1P>0$1P>1A$1>1n$1>0@3$b^6^5^4>0@2$9^7^4>0>1a$1>0@2$7@2$3^5^1@2$c^1@2$5^5^4@1^7^2>0@2$3Z^5>0@2$3@2$5^6^5@2$d+2+k0@4$8^a^9^7^6").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##6Sh02Hah16__sat1h24__x1h34__x2h44__x3h51ah61Ah72HAh82HBh92HPh:2HWh;2MUh<1Ph=1Wh>7__arithh?4__ffh@!s~%0hA8__varmaphB5__withC1mhD2m'hE1nhF1zp;1p;3p;2p;5p;4p;6p;7p;8g007Vj1FTg00>hj11Tg00?Mj1>!s/$kj1BTg00@Nj1dTg00A0j3TTg005Lj2OTg003`j20Tg00B3j25Tg004<j23!s/$Xj29!sA$Pj1C!s/$nj2GTg00CKj1cTg00;Vj2VTg00DIj5UTg00E\j2STg00FFj2Q!s/$nj3PTg00GRj2NTg009kj2ATg00H3j18!s/$Rj24Tg00I;j36!s/$dj2@!tp$@j1MTg0086j3=Tg00JPj2?!s/$nj4LTg00KLj1K!s/$jj1JTg00LUj2:Tg00M8j1I!s/$]j3HTg00N@j4;!s/$kj1RTg00OMj2ETg00P0j3b!s/$Sj2aTg00Q5j2W!tL$Vj3X!s8$aj3YTg00R@j4ZTg00S2j2[!uN$Mj6\Tg00T9j4]Tg00UGj7^!s/$kj7_Tg00VOj8`Tg006[R0f1R1g00W3f0R2C;p=7P!s6$ZR3g00X9R4P4g00XYR5P2g00Y9F^p=2f2R6P3P4P4P5P1P2F_p=Df3R7!s;+6P1P2G`p=<g00YY#Fg00ZZR3#1R8#1#1R9#1!s-$:#>R;#B%>9#B#d[R9p-0\0f5R<f4R=;T7f6R>/O710=215=7,32'9P>P1O1[^50g00[?R?/0=15<=%C8R@%C:R:'GRA'0f7RB/0215B>!s^&%c1RCP0P1f=/V2XF0f<RDf9REP1P<P=P1P2O2DU1S;C1Q@:13?@RC10?:13?A[RF[10?@RGg00[]RHAP@:1UW010?A\H^0G!v\$\91N?@'APCeO1PFg00\_RFg00]KRC#8RG#8RH#8R:,40140H140CRC560560g00]jRH'@%8!sE&G=60C560/@H%MF5=F3=%FFP01?06P11?07CL%K0%J0RF1:08R81:03RH'7,2FP0PHg00^VRC%I3,:09H08R3C;,2F5DF%R4R4PF1E0@=b0;R;,73,2FP!s:%?R3/78!s6$173H!su&PCP;!sf'C<C<C<1aF5P2P6g00_=!u_$_]R5'A1W26=XF5dAY0?1CZb?bAbBX20X30X4010121516!w`$1567/0A10?7R?137A,9?[[[^20^30^40P2f;PD!wi$>PBO6b>b1b@b1,[1E\O2W0X50PEf8P>P<C]eW8W7W9W:W;XE0X60W<XD9WCW=o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma get_meta_rec_put : ltac2:(zQ "80!ii3!iib!ij2!ija!hr9!ika!il6!im0>2st$6>1g$2>2mr$0>2g'$2@3$4$0@2$3@3$7^3^2^4^1M1\0$1$0@2$5^1^3^2@2$3^4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##Jmp'0h01oh11Hh23Heqh31bi001bh43go'h53gr'h61ri011rh71ei021eh81ni031nh91th:2e0h;1gh<2g'h=2goh>2grh?2mrh@2n0hA2sti041pi051zp;1p;4p;6p;2p;3p;?p;7p;5p;Ag00`=R0p4p70R1g0090R2p4p710p8P1p100:_!s6%R3!s8'aAR4!s:&5p8P1P!s4$210R4!sI';=R6!sI&7!sI$6!sI'6p8P1g00a^R8!t7,g00b7R9!s71OR:!s71fR;!s70c=R<!s71UR=!s71lR>!s70dNR?!uV1dgp4p73110R@!sK&e9R1!sK'p100eM!v?%AP5p8PAP4p8PAg009M!v#0AP!uH$41110RB!s7$1!um&!s3,31!s4&!tf$<1!s#,0RC!s~&fQRD!sD5Ep8PAp100g3!sC4p8g00gURA!t]&FP3p8PFP7!s+$6!s+$@!sf$!to+@!tP%3101p8PC!uQ$E!s+$B!s@%51110!uP%5PBp8P9!uT-!sI%61!sJ2g00giRB!sO,5!sO%7!tu%!u;%!t4%=!sK4:!uE+!sN/!tt'0R5!u9$@P5!t6$hIj1fTg00hej4eTg00iCj6VTPAj4Kj3RTP8j4dj3NTPBj4[j3L!sJ$dj4XTg00j@j15Tg00kGj2;!s/$dj2:Tg00lAj24!s/$_j20Tg00mkj2YTg008Vj33Tg00nMRBj2FTg00o0j2WTg00@Nj1T!s8$Rj2STg009kj2?TP:j3QTP9j3JTP;j3MTP<j3ITP=j3OTP?j3PTP>l?HTP4j67Tg0053j1>Tg002@R4j2cTg0104j4DTP2j6A!s5$Pj2G!s/$oj2`Tg0127j2_Tg013@j3^Tg014Hj7\!s/$\j3ZTg0159j3]TP1j6C!s5$Vj5@!t6$`j4aTPDlAbTP0g0161RDf4R1f3R2f2R>f1R?f0R=F\p=8g0177R<g006[R;;Z=p=<A]<;=p==PDPDf5R9g017UR:P0PDP1P2P>P?ECD@=3D=p=6P<P;P?P=Cap=1!sJ$!sH$P=ECp=9PDPDP?P:P=D@p=EA3D?=p=2!s=$1P:!sV1D@p=UP0P=P?P>P2P1P9f6R:f7R8f8RAf9R5PDf:R@f;REf<RCf=RFf>R6MAbp=Bg018ZP4P<P;%fDR7P0P<g019bR3P;g01:;RGCeRHP<P3g01:TP;PGg01;2EVRGPDCKR3P0PHPGPDCdRIP?P3!to$!s<,[CXRJP=P>%51D8g00_=RKPD%<?%<=RL';%=?%==RM':'4P>101?n010!s#$20000E6P>!tq%P7P3PIP=P3PJ11>?RNP:%5AD8P!sw$N,;L%=N,:M'4P:10A=!so411Y?9A3<?91;?9'F1;>:PKPBA3<28!t,%1191RM!t1%5ARNPFf?RL#5!t4%1:1ARO,4?PF10LM!t/4?A3<1ARL1W1ARPA3;1A/FORO1:95R9!t9%;:@RQ!u@$N!t5%FCRRfARSfCRT#5RUD8RVC9RW,E7RXPKPDg00_]RY/4?PS10TNRZ!tG1'2P?A3;8ER8P<PF!u?'=5R[!t0%6FR\fBR]fDR^#5D8R_DUR`/2]X5<P;PC!sX'6=P_P]E6X4;%TDRa1SDS1E7=Rb/2]X0a1?DS!u0$RPVC9P0AR0HGR]AQ0HGRcAN0HGRdAJ0HGReAL0HGRfAM0HGRgAI0HGRhAO0HGRiPHAP0HGRGPDPUPRPSM?HE7PAP=E7P5P1E7!w3$4YYPSP!uc2,2XeW:P=O1%>8RjP<PF10^[,2`X5<Pa!u?%FAR`PUC91165R[,0^,2bX0a10T`,?D!u9$`!u9$]PcPdPePfPgPhPi!zs$UPRP`PSA30R`R`1c<;RkP;!zB&;P=P=n20011040001!tc$000X9kP[P\PkP\P[P=CDEAA3;5Fg0079R[P>P=O1'Gb2W1%>`eM?B!ub/g01;PR1,4!uh;8P=O1n1021001!sE$2111!s'%3b3b6W7!v2%LPPPOP!z&$PQ!ve%1?!s{8P?!xj/@=RQP_10^Q!xn$!vh'5CRC!vh%@FRF!vh/C!vh'C!vh@C!vh%CRCPkP<!vd&<P=P?!vd:R4PF!vf&F!vf'<@6R6P!xd$,G[R[!vd%C!vd&!yN%!ua%!v^:X7!v_$!uL%PN!uH&5R@!uH,?DZPW!u=<N!u=%NRR!u=&@!tr&@!tr%P6P!td&R!td&!t^%1!t^:@j!x?D!xaD!x%'?=RjP3PJPMP5%5E!#5g&j%<M';%=j%=!#6\$510Ej!#4b2eX4;X5<P?P=O2!wY01103105X=;X>!sF>!#7=-P>P?%52D8RJ!uv$`=>P?102!#711RKE6e!s^'1_J2#5P!s9/A^>?2R?!s<&10?=/2KeX<0X?DX;0WAo"). Qed.

Lemma upd_meta_put : ltac2:(zQ "70!ii3!il6!hr9!ij2!ija!im0!imc>2st$1>1g$3>1f>0$0$0@3$2$1@3$6^2^1^3@3$5^2@1^1@2$4^3^2^3").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "h01fh11gh22stp;2p;3g00l_j22Tg013@j31Tg009kj20Tg018ZR0g00`=g0161R1P1[f1R1f0f2R2/21O1;12,00W0W1W2o"). Qed.

Lemma del_slots_eq : ltac2:(zQ "70!h9!in8!il6!hr9!ij2!io5!ip0>1p$4>1s$0>1c$0>2st$2@3$3$2@4$1^4^3^2^1@2$6@1$5@4$1^4^3^2^1^1").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "h01ch11ph21sh32stp;4p;1p;2g01<0j43Tg01=9j12Tg01>@j20Tg009kj21Tg00`=g006[R0g018ZR1f3f2f1f0R2C3#2/02,11W3X00W2W1o"). Qed.

Lemma meta_slot_same_areas : ltac2:(zQ "f0!ipd!h9!iu2!ij2!il6!iuf!jgb!ji6!hr9!jj0!jk9!jl8!jm7!joa!jq5>2st$4>3st'$4>1g$3>0@3$8@4$e$3@4$d$0$6$1$7@6$c$0$6$a$1$7$b$9@1$5^2@1$5^3>0@2$2^4^2@2$2^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##0Kh01ah12arh21kh31gh41Eh52Egh62Hah72Hkh85nd_i2h92sth:3st'p;4p;6p;1p;3p;2p;8p;5p;7g00`=R0p4p70R1g01?IR2p4p710p8P1g01@MR1!s7'p100eM!sS%3P!sN$2!sO$3P1!s3+g00hej4ETg00iCj6DTg00gUj4=Tg01ARj12Tg008Vj31Tg01BYj2:Tg00@Nj1>Tg00a^j4<Tg00oRj29Tg003`j23Tg004<j27!s/$Xj20Tg01Cfj28Tg00B3j24Tg01DCj26Tg00=Oj4;Tg009Mj6CTP1j8BTg01EGj5?TP2j7@Tg00e9j6ATP0g01FLR2f3R1f2R3f1R4f0R5EAp=5g018ZR6!sK$77R7g019bR8g006[R9g01:;R:CER;P7P8g01:TP9P:g01;2EDR:P2C=R8%24%23311:14P0P2P9%>2R7P8P0P;P:P2C<R:P3f7R;#2C51924R<31R=g00[?R>/35g01GRR?,75'0R@f5RAg01HXRBg01I`RC/85'4,63RD510RE'0'0X29X12X001:13P=P@PEf6RE/:A13>4174?'0f4RF18C3,4B'6910;!tm%P8P:P3f<#2C5=17<f;=10D,0@!s|-PAPFP1P8f:#2R@!sX$EP5!u4$A51713>F17F?'0f9RD18CF,4B,6E510!tk$38!sY$AP@!sY$F!sY%1171?'0R?f818C1!sY$A510RA'0P3P?PAP4P5C;C;%2DP;ECGBW5W7X6=D?!th,5F@W8W4X30X:6W9o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma nth_error_map_seq : forall {X} (f : nat -> X) n s i,
  (i < n)%nat -> nth_error (map f (seq s n)) i = Some (f (s + i)%nat).
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##Bap'0h04__x1h12Hih23Hi0h37__arithh44__ffh58__varmaph65__with74__x2h84cstrh91ih:5cstr0h;1ni001nh<1sh=4__p1h>1xh?2IHh@1XhA!sO$1hB1fhC1ohD1yp;2p;1p;3p;4p;6p;8p;<p;7p;Bp200R0g01JiR1p4p7210p8P0g00aAR2p4p7!s7%P2!sD19MR3!sD,g01KER4!s7'g01KcR5j23Tg00@Nj1=Tg01L;j2;TP4j39!s5$Wj28Tg00oRj25j1KTg008Vj30j1J!sG$nR4j11Tg004<R6j27Tg009kj24Tg01MNj4DTg01N5j1?Tg003@j1jTg007Vj1hTg00JPj2OTg00KLj1_!s/$jj1^Tg00OMj2MTg00LUj2LTg00N@j4B!s/$kj1\!t$$Zj6[Tg00PSj2ZTg00Q5j2Y!s/$aj3XTg00R@j4WTg00H3R7j16!u<$6j3ETg00B3R8j22Tg01O>j2U!s/$aj3T!sC$Pj1lTg00M]j3@Tg01P>j4HTP2j8A!s5$ij1g!u=$nj4fTg00>hj1eTP3j6`Tg01QGj4aTP1j4b!s5$hl<C!v#$`j2cTg00UGj7dTg00VOj8]Tg01RMlBQTg01S3l<i!s/$XR1f2R3f1R2f0R9Cbp=>P1g006[R:P5P4P6g01T7R;f3R<P3P2g00]KR=g00[?R>P9M<Cp=V1c>9p=<!sE$WZR?g00X9R@P@g00XYRAP9g00Y9Fdp=:P:!sM$^VP9CBp=GP<P?P@P@PAP3P2P9G]p=FP1!s$$:P:P:g01TYRBP4!s$$8g01U9RCP!t]$P=P>P9MBQp=S!sV$9P4P2P3P<f4RDf5REf6RFf7RGf8RH!t{$R!t$+7!sw$<g01U\!tJ%M<ip=I!sE$!us$P;!t/$<!sD'Cp=k!ti/P!td+PCPEPD!sP+BQp=P!sn0!sD/<Cp=NP2\11393%=F1;3<9>FE=9F2PE1832R;O1,5F30[^91^<1R6X;1139=132=%12R4/7>R5P2P414:4RC14:>R8CVP9CDP5%?3R5%13#<RBp-0R7g00\_RI#jRJ%hIRI1O:2RK%_:RL%^:RMP:1M:>RNg00W3g00ZZRO,L:RPCB,:M%\@RQPM1GPN,:MPQPM!wy+<E[CFCF1ZMARAP9P3g00_=R@g00_]R?'41Y93=0@?dAX:>2CWR?b4b5b6X0:W=%<9172>P<[[^0:^=7P9%=HR71;E=9>HG=9HDPG18EDO1,5H30%1DP2P3O4b3b8b2W1X91X<1%6<R@,39P1%6ERR,39f9RS#=RTPHPDO1%6DRU/;F9>SH5ES=9S2PH18D2O1,5S30]1P213=UPHP7%KHRDPDPGP<O1RVPG18<=RWO1RXPT\H/4DP1PHPGPGP<PWPS\1/4GA01<W%1<RD12D>RT50:%J1RY%J:RZ%1990:4A01291U293TXD1X>1R[P<PD14:DR\PWPTP<PDP\P8CSM9R13=R%1ER\%lORD'2RT,7>RWP8PR129DR8X>:R]P\O1P]PEP\14:\R^CIR_Ck!xs$W%?F%1FRW#<%?E%<\PJPIPKPLP:PPg01V@RKA@:PN!xQ$PAP!w_,129>90:9^0:P9%1GR>O1b3b:b8b2CHGAGA1;@E9>HG9EHV=9H=15HX507eW1%69%6F'3f:R7#=RXPS18R2R=O1RV,57f;R@#=RNP7%63,8FO1,5@709XCXP7PX%K7R`P`PVPS%62RV,8ERaO1RbPN\7/4`P1P7PSPSP=PaP@\1/4SA01=a12T4R`124DRN,2\Rc50:PYPZP[P=P`PRPTP_P2P4PCEPPaPcPEP\P^PVPNP]!s>%CIR^EPM9R%6GRc,3V12>D,7NRNPVP]P4O1P^PcP]P>!w8$GP>!}%$]CIENP9CDRcPNP5PB%?SR^%1S#<Ra%?H%1H#<!w@$:1O:3P2%g:CfRHPL!}%$DR_9@:PRT%e!|~$O5@:PKA@:O_!s@%!wc5X7:1282122DRD,2950:^0:^7:P9PW%17O2b3bA!ws1RG9>7SRW=972PFPRP2132G174>!us%PGP>P]ENP!u;&P^Pa!u'$HPLPM1GT_!~V$1GPO,:MCF!t_478D1723[!tX'%1@P\P<O3!yM,O3E`PSPEO1=E7W=97V157b50Xe!}|$P9O1n0110000020111100P9O1%=G1;3U9>GF=9G2PFP;O1,5G30e!~]'X?6X;1P9CaX;1WBX@0o"). Qed.

Lemma actives_nth : ltac2:(zQ "f0!hk7!hma!jqd!hn0!ld!hr9!h9!jr4!jrf!js5!il6!jsf!p9!pe!jtb>2st$a>2sc$6>0@2$4@2$cZ^1@2$d^1+j0@3$5@1$3@1$1@1$0#k0@3$b@1$1@1$0#k0@1$7^3@1$e^2@2$2@1$1@1$0#k0@2$8^3@2$9^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##>`h04__p1h14__p2h24__x1h34__x2h41xh52H0h67__arithh74__ffh84__p3h98__varmaph:5__with;2z0h<1Hh=1ih>1oh?2sch@2sthA1yp&0p;2p;1p;3p;<p;4p;8p;6p;Bp;7g003`j2;Tg00M8k100Tg00>hj11Tg00BPj1WTg004<R0j26!s1$Xj23Tg00?Mj1f!s/$kj1bTg00@Nj1]Tg01VgR1j1YTg01LWj2V!s/$nR2j1ITg01WGj2@j1eTg01XMj2Aj1lTg00oRj2Cj1nTg008Vj37j1_Tg009kj22Tg01YSj2H!tg$3R3j2PTg01Z0j1^Tg01Qhl<J!s8$Nj2XTg00:Ej2FTg00H3j1!uP$HRj2=Tg00I;j3?!s/$dj2BTg01[0j1U!s/$Nj2T!s/$oj3RTg003@j1S!tc$6j3<Tg007Vj1~Tg00JPj2}Tg01Pij1|!s8$nj4uTg00KLj1t!s/$jj1pTg00LUj2NTg00OMj2MTg00N@j4:!s/$kj1m!wL$]j3kTg00PSj2jTg00Q5j2g!s/$aj3hTg00R@j4i!tC$>j4KTg00aAj8G!w+$;j2cTg01Jij4oTg01KEj3O!s/$cR4j2aTg01\Xj6q!vx$Mj6rTg01]oj1sTg01S3l<QTg01RMlBvTg01NZj6wTg00UGj7x!s/$kj7yTg01_:j7zTg00VOj8{Tg006[R5f1R6f0R737p=5P5g01SXR8P5P5P1f4R1P2f3R9g01_^f2R:P6P7M<Qp=\P8!s$$5P!s\%TYP2!s$$3g01U9g00]KR3g00[?R;P9P!s`%Bvp=[!s\'P2P2f5R<P1!sF+<Qp=ZP6g00WZR=g00X9R>P>g00XYR?P7Ewp=DP5P6g01V@P7C:p=EP6P=P>P>P?P7g00Y9Fxp=4P:!s<+6P7Fyp=9!s92zp=LP9!s9+!tP$G{p=>%07#0#0#0p=d!s2+!s$'p=!um%4P2P0g01T7P!u80Jp=`g018Z1;!}i$ZZR0$00#1!s$&WR2,67'3%10R4!s<+1#f#bR=#]R@%Y6RA,V3RB#IRC,@:RD,A:RE,C=1@9:,A9,C=97@7X>@P=P@%n=RFPFPE1@:6RE,A:RGP@\=/2Fg00eMRFP=%l:RHPHPDPEP=\F/2HP5PF%e!s<%CP6PF\5/2H15C61H;6RH,P;RF/56P5P5%_5REP7X45RDPE1567#^XA5X45PCPFPDPD%I7RC,25X48PBPF125;PAPHPD1H;7X45P6P61256RDD\RFC[EZP6P6PDM<J1X;6RD16;615H6'31;6;RBA75H;'3'FRE1H;:RIP5p-0RJg00\_RK%03RL#0RM,=5RN1=5L1=53RL5?55?5g00]jRO'BRP%0M!sK$%U0,T5=R5N=?5L!sO$/BO1BLO%SKRL5<K5<K3<%~KROP51}5:P6%|5CuRN%t5RQ%p5RR1DR11N50R01N54R4'E,4R59RRSP5P4g00W3RT1M5;RUC:,4R1E0U,4RRV59R5LR%m>R>PRP5PUPTP4!sI%DR<RT59RP>Ak5U0/E4,4RC>C>1jR?R?P7P:g00_=RUg00_]RW'21g7:=7UWdAh5;6CiRWb7b9b:X25X35X0JW11576,3:RUA757;RX,3B'F1;;:/311P;:/59[[^25^35^0J^1JP7161216;1RBP1P6P:P9O6b6b;b5CKG!s#$P8P=1@9C,A9X=8R8%0M#d#8!s$'RM,c3Co=O=AP=P8PMP3PA1aAM16H2!x|$FPMP21252E`!zH$IP5A<KPLPOPNPQPRA9RTV9LRSP>PRf6,DR!vv&^VR41M52RS!vS$!vM$P5P0P4P!s8%C>C>P?P!v#3X1JX8J139X,FU16:2R2,3<P2!ur1^8JP71;;11;1;P!uu,7!uu'EqEr%s:=O=A1C=G57@eW<X?5W@o"). Qed.

Lemma usages_nth : ltac2:(zQ "f0!hk7!hma!jqd!hn0!ld!hr9!h9!ju4!jue!il6!jv4!jsf!p9!pe!jtb>2st$9>2sc$6>0@2$4@2$cZ^1@2$d^1+j0@3$5@1$3@1$1@1$0#k0@3$b@1$1@1$0#k0@1$7^3@1$e^2@2$2@1$1@1$0#k0@1$8@2$a^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##>Nh04__p1h14__p2h24__x1h34__x2h41xh52H0h67__arithh74__ffh84__p3h98__varmaph:5__with;2z0h<1Hh=1ih>1oh?2sch@2sthA1yp;2p;1p;3p;<p;4p;8p;6p;Bp;7g003`j2:Tg00M8j1~Tg00>hj11Tg00BPj1XTg004<R0j27!s1$Xj22Tg00?Mj1f!s/$kj1bTg00@Nj1]Tg01VgR1j1ZTg01LWj2W!s/$nR2j1ITg01`Kj2=j1jTg01aPR3j1@Tg00oRj2Gj1mTg008Vj35j1aTg009kj23Tg01YSj2H!tf$3R4j2PTg01Z0j1_Tg01Qhl<J!s8$Nj2YTg00:Ej2CTg00H3j10!s/$Rj2?Tg00I;j3A!s/$dj2BTg01[0j1V!s/$Nj2U!s/$oj3TTg003@j1R!tc$6j3<Tg007Vj1STg00JPj2}Tg01Pij1|!s8$nj4{Tg00KLj1t!s/$jj1sTg00LUj2NTg00OMj2MTg00N@j49!s/$kj1l!wJ$]j3kTg00PSj2iTg00Q5j2h!s/$aj3eTg00R@j4g!tC$>j4KTg00aAj8F!w'$;j2cTg01Jij4nTg01KEj3O!s/$cR5j2`Tg01\Xj6p!vx$Mj6qTg01bVj1rTg01S3l<QTg01RMlBuTg01NZj6vTg00UGj7w!s/$kj7xTg01_:j7yTg00VOj8zTg006[R6f1R7f0R835p=6P6g01SXR9P6P6P1f4R1P2f3R:g01_^f2R;P7P8M<Qp=^P9!s$$6P!s\%TYP2!s$$4g01U9g00]KR4g00[?R<P:P!s`%Bup=\!s\'P2P2f5R=P1!sF+<Qp=[P7g00WZR>g00X9R?P?g00XYR@P8Evp=DP6P7g01V@P8C9p=EP7P>P?P?P@P8g00Y9Fwp=4P;!s<+7P8Fxp=;!s92yp=LP:!s9+!tP$Gzp=>%08#0#0#0p=d!s2+!s$'p=8!u7$5P2P0g01T7P!u80Jp=og018Z1:<8g00ZZR0#~#1!s$&XR2,78'2%10R5!s<+1#f#bR>#]RA%Z7RB,W4RC#IRD,=;RE#@RF,G>1=:;#@,G>95A8X>AP>PA%m>RGPGPF1=;7RF#@RHPA\>/3GP6P>P3P3PEPFP>\6/33P6P6%j;R3P3PDP7P6!s<$16D71H<7R3,P<RF/67!sN$a6REP8X46RGPE1678#_XA6X46PDPFPGPG%I8RD,36X49PCPF136<PBP3PG1H<8X46P7P71367RGD^RFC\E[P7P7PGM<J1Y<7RG17<71637'21:7<RCA563<'2'CRE1H<;RIP6p-0RJg00\_RK%04RL#0RM,?6RN1?6L1?64RL5A65A6g00]jRO'BRP%0M!sK$%V0,U6=T6N=A6L!sO$/BO1BLO%RKRL5<K5<K3<%SKROP61}6;P7%|6C{RN%t6RQ%s6RR1DR11N60R01N65R5'E,4R5;RRSP6P5g00W3RT1M6<RUC9,4R1E0U,4RRV5;R5LR%l?R?PRP6PUPTP5!sI%DR=RT5;RP?Ak6U0/E5,4RC>C>1iR@R@P8P;g00_=RUg00_]RW'31h8;=5UWdAe6<7CgRWb7b9b:X26X36X0JW11687,2;RUA568<RX,2C'C1:<;/211P<;/6:[[^26^36^0J^1JP8171217<1RCP1P7P;P:O6b6b;b5CKGFGFGFP9P>1=:D#@X=9R9%0M#d#8!s$'RM,c4Cn=O>BP>P9PMP4PB1`BM1732!x{$FPMP21362EoPGPEPIP6A<KPLPOPNPQPRA;RTV9LRSP?PRf6,DR!vu&^VR51M62RS!vR$!vL$P6P0P5P!s8%C>C>P@P!u~3X1JX8J12:X,CU17;2R2,2=P2!uq1^8JP81:<11:1<P!ut,7!ut'EpEq%r;=O>B1G>H55AeW<X?6W@o"). Qed.

Lemma bouncess_nth : ltac2:(zQ "f0!hk7!hma!jqd!hn0!ld!hr9!h9!jvd!kg3!kgf!il6!jsf!p9!pe!jtb>2st$a>1i$6>0@2$4@2$cZ^1@2$d^1+i0@3$5@1$3@1$1@1$0#8@3$b@1$1@1$0#8@1$8^3@1$e^2@2$2@1$1@1$0#8@1$7@2$9^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##=|h04__p1h14__p2h24__x1h34__x2h41xh52H0h67__arithh74__ffh84__p3h98__varmaph:5__with;1ih<2z0h=1Hh>1oh?2sth@1yp;2p;1p;3p;<p;4p;8p;6p;Bp;7g003`j2;Tg00>hj1:Tg00BPj1`Tg004<R0j27!s1$Xj22Tg00?Mj1k!s/$kj1dTg00@Nj1_Tg01VgR1j1[Tg01LWj2X!s/$nR2j1ITg01c`j2=j1jTg01dgR3j1<Tg00oRj2Hj1rTg008Vj35j1aTg009kj20Tg01YSj2G!tf$3R4j2OTg01Z0j1^Tg01Qhl<J!s8$Nj2YTg00:Ej2CTg00H3j11!s/$Rj2?Tg00I;j3@!s/$dj2BTg01[0j1W!s/$Nj2V!s/$oj3UTg003@j1T!tc$6j3ATg007Vj1RTg00JPj2STg01Pij1|!s8$nj4{Tg00KLj1z!s/$jj1yTg00LUj2QTg00OMj2MTg00N@j49!s/$kj1iTg00M]j3hTg00PSj2gTg00Q5j2f!s/$aj3eTg00R@j4c!tC$>j4KTg00aAj8F!w'$;j2bTg01Jij4lTg01KEj3N!s/$cR5j2mTg01\Xj6o!vx$Mj6pTg01emj1qTg01S3l<PTg01RMlBsTg01NZj6tTg00UGj7u!s/$kj7vTg01_:j7wTg00VOj8xTg006[R6f1R7f0R835p=6P6g01SXR9P6P6P1f4R1P2f3R:g01_^f2R;P7P8M<Pp=]P9!s$$6P!s\%TYP2!s$$4g01U9g00]KR4g00[?R<P:P!s`%Bsp=\!s\'P2P2f5R=P1!sF+<Pp=ZP7g00WZR>g00X9R?P?g00XYR@P8Etp=DP6P7g01V@P8C9p=EP7P>P?P?P@P8g00Y9Fup=4P;!s<+7P8Fvp=8!s92wp=LP:!s9+!tP$Gxp=>%18#1#1#1p=3!t{$5P2P0g01T7P!t|0Jp=ng018Z1;<8g00ZZR0#:R2#:#:R5#:#:#`R>,78'2%k5#dR5#_RA%[7RB,X4RC#IRD,=;RE#<RF,H51=:;#<,H595A8X>AP5PA%r5RGPGPF1=;7RF#<RHPA\5/0G!tg$3P3PEPFP5\6/03P6P6%j;R3P3PDP7P6!s<$16D71G<7R3,O<RF/67!sN$a6REP8X46RGPE1678#^X@6X46PDPFPGPG%I8RD,06X49PCPF106<PBP3PG1G<8X46P7P71067RGD]RFC\EZP7P7PGM<J1Y<7RG17<71637'21;7<RCA563<'2'CRE1G<;RIP6p-0RJg00\_RK%14RL#1RM,?6RN1?6L1?64RL5@65@6g00]jRO'BRP%1M!sK$%W0,V6=U6N=@6L!sO$/BO1BLO%TKRL5AK5AK3A%RKROP61S6;P7%|6C{RN%z6RQ%y6RR1DR11Q60R01Q62R2'E,4R58RRSP6P2g00W3RT1M6<RUC9,4R1E0U,4RRV58R5LR%i?R?PRP6PUPTP2!sI%DR=RT58RP?Ah6U0/E2,4RC>C>1gR@R@P8P;g00_=RUg00_]RW'01f8;=5UWdAe6<7CcRWb7b9b:X26X36X0JW11687,2;RUA568<RX,2C'C1;<;/211O<;/6:[[^26^36^0J^1JP8171>17<1RCP1P7P;P:O6b6b<b5CKGFGFGFP9P51=:D#<X;9R9%1M#3!s$/RM,b4Cl=N5BP5P9PMP4PB1mBM173>!x}$FPMP>106>EnPGPEPIP6AAKPLPOPNPQPRA8RTV9LRSP?PRf6,DR!vw&^VR21M6>RS!vT$!vN$P6P0P2P!s8%C>C>P@P!v$3X1JX8J12:X,CU17;>R>,2=P>!us1^8JP81;<11;1<P!uv,7!uv'EoEp%q;=N5B1H5H55AeW=X;6W?o"). Qed.

Lemma unmap_seqs_nth : ltac2:(zQ "f0!hk7!hma!jqd!hn0!ld!hr9!h9!jvd!kha!il6!ki8!jsf!p9!pe!jtb>2st$9>1i$6>0@2$4@2$cZ^1@2$d^1+i0@3$5@1$3@1$1@1$0#8@3$b@1$1@1$0#8@1$8^3@1$e^2@2$2@1$1@1$0#8@1$7@2$a^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##=|h04__p1h14__p2h24__x1h34__x2h41xh52H0h67__arithh74__ffh84__p3h98__varmaph:5__with;1ih<2z0h=1Hh>1oh?2sth@1yp;2p;1p;3p;<p;4p;8p;6p;Bp;7g003`j2;Tg00>hj1:Tg00BPj1`Tg004<R0j27!s1$Xj22Tg00?Mj1k!s/$kj1dTg00@Nj1_Tg01VgR1j1[Tg01LWj2X!s/$nR2j1ITg01g9j2=j1jTg01dgR3j1<Tg00oRj2Hj1rTg008Vj35j1aTg009kj20Tg01YSj2G!tf$3R4j2OTg01Z0j1^Tg01Qhl<J!s8$Nj2YTg00:Ej2CTg00H3j11!s/$Rj2?Tg00I;j3@!s/$dj2BTg01[0j1W!s/$Nj2V!s/$oj3UTg003@j1T!tc$6j3ATg007Vj1RTg00JPj2STg01Pij1|!s8$nj4{Tg00KLj1z!s/$jj1yTg00LUj2QTg00OMj2MTg00N@j49!s/$kj1iTg00M]j3hTg00PSj2gTg00Q5j2f!s/$aj3eTg00R@j4c!tC$>j4KTg00aAj8F!w'$;j2bTg01Jij4lTg01KEj3N!s/$cR5j2mTg01\Xj6o!vx$Mj6pTg01hBj1qTg01S3l<PTg01RMlBsTg01NZj6tTg00UGj7u!s/$kj7vTg01_:j7wTg00VOj8xTg006[R6f1R7f0R835p=6P6g01SXR9P6P6P1f4R1P2f3R:g01_^f2R;P7P8M<Pp=]P9!s$$6P!s\%TYP2!s$$4g01U9g00]KR4g00[?R<P:P!s`%Bsp=\!s\'P2P2f5R=P1!sF+<Pp=ZP7g00WZR>g00X9R?P?g00XYR@P8Etp=DP6P7g01V@P8C9p=EP7P>P?P?P@P8g00Y9Fup=4P;!s<+7P8Fvp=8!s92wp=LP:!s9+!tP$Gxp=>%18#1#1#1p=3!t{$5P2P0g01T7P!t|0Jp=ng018Z1;<8g00ZZR0#:R2#:#:R5#:#:#`R>,78'2%k5#dR5#_RA%[7RB,X4RC#IRD,=;RE#<RF,H51=:;#<,H595A8X>AP5PA%r5RGPGPF1=;7RF#<RHPA\5/0G!tg$3P3PEPFP5\6/03P6P6%j;R3P3PDP7P6!s<$16D71G<7R3,O<RF/67!sN$a6REP8X46RGPE1678#^X@6X46PDPFPGPG%I8RD,06X49PCPF106<PBP3PG1G<8X46P7P71067RGD]RFC\EZP7P7PGM<J1Y<7RG17<71637'21;7<RCA563<'2'CRE1G<;RIP6p-0RJg00\_RK%14RL#1RM,?6RN1?6L1?64RL5@65@6g00]jRO'BRP%1M!sK$%W0,V6=U6N=@6L!sO$/BO1BLO%TKRL5AK5AK3A%RKROP61S6;P7%|6C{RN%z6RQ%y6RR1DR11Q60R01Q62R2'E,4R58RRSP6P2g00W3RT1M6<RUC9,4R1E0U,4RRV58R5LR%i?R?PRP6PUPTP2!sI%DR=RT58RP?Ah6U0/E2,4RC>C>1gR@R@P8P;g00_=RUg00_]RW'01f8;=5UWdAe6<7CcRWb7b9b:X26X36X0JW11687,2;RUA568<RX,2C'C1;<;/211O<;/6:[[^26^36^0J^1JP8171>17<1RCP1P7P;P:O6b6b<b5CKGFGFGFP9P51=:D#<X;9R9%1M#3!s$/RM,b4Cl=N5BP5P9PMP4PB1mBM173>!x}$FPMP>106>EnPGPEPIP6AAKPLPOPNPQPRA8RTV9LRSP?PRf6,DR!vw&^VR21M6>RS!vT$!vN$P6P0P2P!s8%C>C>P@P!v$3X1JX8J12:X,CU17;>R>,2=P>!us1^8JP81;<11;1<P!uv,7!uv'EoEp%q;=N5B1H5H55AeW=X;6W?o"). Qed.

Lemma actives_length : ltac2:(zQ "70!kj5!kje!hr9!hk7!jr4!il6!hma>2st$5@3$2$1@2$0@1$6@1$3#k0@1$4^1Nj0").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##&uh01ih11nh22stp;2p;3p;6p;1p;4g01L;j2@Tg01iPj23Tg008Vj34Tg009kj2?Tg01j0j2;!s8$Mj65Tg00>hj11Tg00?Mj18!s/$kj17Tg01Lnj16Tg01WGj29Tg01XMj2:Tg01Jij4>!sw$Oj4=Tg01]oj1<Tg00H3j10Tf0R0#!s$2p=2g018Zg01SXR1g00]KR2%22#!s$+R3'@R4,31R5A4103X11R6P1P3P61?13P51;32E5g00ZZ#1!s$-8#7R2P1P2f1R5%60,95':X01R5P4C>'3P1P2P5P4C=E5%<0,32=413eW2o"). Qed.
Lemma usages_length : ltac2:(zQ "70!kj5!kje!hr9!hk7!ju4!il6!hma>2st$5@3$2$1@2$0@1$6@1$3#k0@1$4^1Nj0").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##&rh01ih11nh22stp;2p;3p;6p;1p;4g01L;j2@Tg01iPj23Tg008Vj34Tg009kj2?Tg01j0j2;!s8$Mj65Tg00>hj11Tg00?Mj18!s/$kj17Tg01Lnj16Tg01`Kj29Tg01aPj1:Tg01Jij4>!sw$Oj4=Tg01bVj1<Tg00H3j10Tf0R0#!s$2p=2g018Zg01SXR1g00]KR2%22#!s$+R3'@R4,31R5A4103X11R6P1P3P61?13P51;32E5g00ZZ#1!s$-8#7R2P1P2f1%60'9#:X01R5P4C>'3P1P2P5P4C=E5%<0,32=413eW2o"). Qed.
Lemma bouncess_length : ltac2:(zQ "70!kj5!kje!hr9!hk7!kg3!il6!hma>2st$5@3$2$1@2$0@1$6@1$3#8@1$4^1Ni0").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##&hh01ih11nh22stp;2p;3p;6p;1p;4g01L;j2@Tg01iPj22Tg008Vj34Tg009kj2?Tg01j0j2;!s8$Mj65Tg00>hj13Tg00?Mj18!s/$kj17Tg01Lnj16Tg01c`j29Tg01dgj1:Tg01Jij4>!sw$Oj4=Tg01emj1<Tg00H3j11Tf0R0#1!s$%p=0g018Zg01SXR1g00]KR2%02#0!s$/R3'@R4,21R5A4103X11R6P1P3P61?13P51;32E5g00ZZ#3!s$$8#7R2P1P2f1%60'9#:X01R5P4C>'!s>$P5P4C=E5%<0,22=413eW2o"). Qed.
Lemma unmap_seqs_length : ltac2:(zQ "70!kj5!kje!hr9!hk7!kha!il6!hma>2st$5@3$2$1@2$0@1$6@1$3#8@1$4^1Ni0").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##&hh01ih11nh22stp;2p;3p;6p;1p;4g01L;j2@Tg01iPj22Tg008Vj34Tg009kj2?Tg01j0j2;!s8$Mj65Tg00>hj13Tg00?Mj18!s/$kj17Tg01Lnj16Tg01g9j29Tg01dgj1:Tg01Jij4>!sw$Oj4=Tg01hBj1<Tg00H3j11Tf0R0#1!s$%p=0g018Zg01SXR1g00]KR2%02#0!s$/R3'@R4,21R5A4103X11R6P1P3P61?13P51;32E5g00ZZ#3!s$$8#7R2P1P2f1%60'9#:X01R5P4C>'!s>$P5P4C=E5%<0,22=413eW2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)


Lemma put_meta_put_meta_same : ltac2:(zQ "50!im0!ii3!il6!hr9!ij2>2st$2>1g$4>1a$1>1b$1@3$3$2@3$0^3^2@3$0^3^1^4@3$0^3^2^4").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##9Kp'0h01ah11bh21gh37s_areasi00!s1'h45s_ctxi01!s/%h58s_groupsi02!s2+h67s_metasi03!s1'h7:s_next_ridi04!s4-h89s_regionsi05!s3,h9:s_reservedi06!s4-h:8s_secreti07!s2+h;8s_shadowi08!s2+h<7s_slotsi09!s1'h=6s_ticki0:!s0&h>2sti0;1mp;3p;4p;6p;2p;1p;:p;9p;8p;7p;5p;@p;;g013@j32Tg008Vj36Tg00gUj43j3VTg00hej4ITg00iCj6YTg002@j2?Tg007Vj1U!sV$ij4Qj3P!sM$dj4MTg01jnl:7l98j89j7Gj6Ej5Cj4Wl;5Tg009kj21Tg00bOj3TTg00a^j3S!s8$7j3R!s/$fj3OTg00c=j3N!s/$Uj3LTg00dNj3K!tI$3l@J!se$Aj80Tg01l6j1:Tg01m;j1;Tg01nDj1<Tg01oLj1DTg00j@j1=Tg01ARj1FTg020Vj1@Tg01=9j1BTg021^j1ATg022dj1>Tg023lj1HTg014Hj7XTg00`=R0g0161R1f4R2f3R3f2R4f1R5f0R6FXp=4g018ZR7P7A23569234A2346567P3g0256g0177R8g019bR9g01:TR:g026<C3P8P9P:g027DC3P0P8P9g006[R;g01:;R<CIR=!sK%P;P<g01;2EYR<P1C3R:P0P=!s;$FLC3R9!s5'28LC3R>!s5%1?0;C3R?1?;;#UR@P@P7f:RAf9RBf8RCf7RDP:P0P1P!sv&P1CQCMREfHRFfGRGP:PEPFfFRHf6RID4D4RJf5RKP2P3P4P5M:7PAPBPCPD!sQ%PGPID4RLP!sI06P6P;P7\@RM!sU+J!sI'M98!s;+L!s;/5P5P8PM\;!s\5G9!sY3G9P4P4P?PM\8!sV3FG!sT1FGP3P3P>PM\?!sR1EE!sP/EEP2P2P9PM\>!sN/DC!sL,DCPKPKP:PM\9!sJ,CWRNPNPJPLPM\:/1NP0AV0=<AT0=<AS0=<AR0=<AP0=<AO0=<AN0=<AL0=<P=AK0=<P1PI!vm$HM@JG0119KG011>2G011?3G01184G011;5G011@6G0!tc+I!wD,P6M;5R@#:R?%;@R>%<@R9%D@R<!wv&H%=@R=D4%F@RN%@@RM%B@RL%A@RJ%>@RO%H@RPM;5RQ#:%;Q%<Q%DQ!x['%=QD4%FQ%@Q%BQ%AQ%>Q%HQM;5P?P>P9P!t5'GP=D4PNPMPLPJPOPPM;5567eA2FH@92FGA2FG@567eW9X:;X=8W<W5W3W6X78W;W8W4!uU9O;n0110;0001;110110510810410310010210910:107106X11X01X20W>o"). Qed.

Lemma aptr_eqb_neq : ltac2:(zQ "60!ij2!hr9!iib!kk4!m3!ika>1a$0>1b$0>0@1$4@3$1$0^2^1@3$1$2@2$5^3^2$3").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##1yp'0h01bi001bh11ri011rh21ei021eh31fh41ni031nh51Hh61ah72a1h82a2h92b1h:2b2h;2e0h<2n0i041pi051zp;3p;1p;2p;6p;4g008Vj30Tg0053j13Tg010oj27Tg00mkj2DTg00kGj28Tg00nMR0j2:!s:$dj26Tg00o0j2@Tg002@R1j2?!s1$`j39j2Ej4ATg009kj2>!s/$0j64Tg029Rj6<!t;$Pj2CTg014\j3=Tg0159j3;Tg00lAj2BTg00_=R2f0R3g01;PR430p=5g0177R5g006[R6f1R7P3CAp=11B73=024p=2g00`=R8P1P5P6A0873#3f2R9/77#5[^08P3!sB%f3R1/19=083#3f4R:/11!sK%P3f6R;f5R<'11173508#3f7R=/D9A05=918=9':f8R>/81P2P0f9R1=05:f:R?/6<R@,27P7A05?<RA1@?<RBA06?</:@R@f;/6;R<!s^$<=06=RCg00_]RD/27P7f==06>REA02D4P>1?56R>f?RFf>RG'111?G11?1P>\6RHP>P3PFO1X3HA956FRIA956?RJPHPIPIPJPH\5RIPHP3f@O1X3I1E56RKPK1>IKE4P5PHPKPFP?P:E4E<E4P6P>PJPGP1P3E4E<O1'C12DDeW;P3O1%3ER11>24RG12D4eW4P3O1n102100101000210!s5$103b0b1W2!s^%APBP@P!um$PC1247P7PG124DeX2EP3O1!s4$4eX<1!syD!tCD11=;R=9=561197R99=56'8A;56=A;569'6'2e17=9#5eW5X:6X95P7P3O2n2001104000121103105X08X86X7!sI>W6o"). Qed.

Lemma aptr_eqb_eq : ltac2:(zQ "60!ij2!hr9!iib!kkc!kl3!ika>1a$0>1b$0@2$4@3$1$2@2$5^2^1$3@3$1$0^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##66p'0h01Hh12H0h22H1h35lemmah42H2h51ai001ah62a1h72a2h81bh91eh:1Bh;2H3h<2b1h=2b2h>1ni011nh?1zi021zi031pp;2p;3p;4p;6p;;p;9g010oj2>Tg02:0R0j26Tg00kGj2=!s/$dj2<Tg00lAj2;Tg004XR1j25!sW$Ij2FTg02;5j2D!s/$Vj3MTg02<Lj4CTg02=?R2j6LTg02>1j2K!s/$Qj4JTg02?8l;HTg02@3j2GTg009kj27!s/$Mj69!s/$0j6@Tg00=Oj4BTg014\j3?Tg0159j3ATg008VR3j38Tg002`j4E!sy$Sl9ITg00_=f0R4g00_]38p=2g00`=R5f1R6;84p=4g0177R7g006[R8P6P4CEp=0p-0R9P0g02AMf5R:f4R;f3R<f2R=P6P4M9Ip=:A8764p=3A8864p=1g002@R>P7P81>64#21464'6^85P4P!s=%0<=R?/>!sB$?4'6P4f6R@/=6RA1<:4RB';#2%2ARC%2BRD'5'6f7RE/==RF1<@6RG!sG%FRF%2GRG'5RHP410E@RI10=6RJ'4RKPK1F9KRLE:W31DAB13@6RB,6CPH13E=R=/5GRHPFP=P4PGPGP!ub%B>9M90RFPGCCELPKPKP!si%K@611:4RC,6DPH11@6RH,5=RDP9P9^:9P0P9P9P0P0CJP1P2P=!s4$FP=CCPGPHP4M;H!sv-G:415BCRCPK[10@:RB1064RL'4RGPD[P1P=PHf8RH/0E/4?R=P4f9R1/3;RDP7P:f:RF/1:f;R0,06/4I[X67111;R9P8P:10E4/4IX78175BPFP4E9W0!s-+6P4O2n20010!s#$12!s-%0X0CP3P5PI10;<RI,4613F:R3/59[P4P5P8!x4%P8P4P4!sh$103!sh%101102X95101HPIP4E@11H<R<P5P7!s]&7P4P6!s]<F110:;P6E@P3130@P4f<R@/3EP7PHf=R3/1HRH136Ff>R;/11'5[X>711@EP4PHP8P11300114F'5X?813FF1111177F1781CBP;P4E9b;W4P3!s0$4W2P4O1b!s+&X1=P4O1X1Kn2002!v=&!vF$144?15D<[X55PJO1P4175?O1b1X0GCBO2O2O2A?78BA?78L'=AA78BAA78L'<';#2/6Ge1>BL!s0%X=8X<7!wP-!v/'1!v/&85X78X6!sI?55o"). Qed.

Lemma get_meta_rec_put_same : ltac2:(zQ "60!ii3!hr9!ij2!ija!il6!im0>2st$4>1g$2>2mr$0@3$1$0@2$3@3$5^2^1^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##%yh01bh11gh21mh32mrh42stp;2p;3p;1p;6p;4g010oj27Tg00l_j20Tg008Vj31Tg009kj23Tg02Bnj16!s8$Mj62Tg013@j35Tg02D?j44Tg018Zg00`=g0161R0P0g00_=R1P0f1R2/72R3f0R4f2R5/02n010!s#$20000A1042X20P1g00_]P1P0P4P2f3/05!sP1=102X011304P3%62E2A5245/02P5P2P4P2C4E2W3W1W4o"). Qed.
Lemma get_meta_rec_put_other : ltac2:(zQ "70!ij2!hr9!ija!ii3!m3!il6!im0>2st$5>1g$0>2mr$3>1q$0>0@1$4@3$1$0^1^3@3$1$3@2$2@3$6^4^3^5^2@2$2^5^2").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "h01bh11gh21mh32mrh41qh52stp;3p;1p;2p;6p;4g008Vj30Tg0053j18Tg010oj23Tg00l_j21Tg009kj27Tg02EUj36Tg009Mj62Tg013@j34Tg02D?j45Tg018Zg00`=R0g0161R1f0R2f2R3500#8P1g00_=R4P1f1R5f3R6'3R7P3f4R8/15R9n0100000020000f5/13R:9012X21P4g01;PP4P1P2P6P:n0100000020000=01:X041719P7A6562E2A4638/15P8P6P3P5C5E2UX40W3W1W5o"). Qed.

Lemma pw_put_meta : ltac2:(zQ "90!jrf!hr9!hk7!ij2!ii3!il6!kl9!im0!hma>2st$5>1g$3>2mr$4>1p$6@3$1@1$8@1$2#k0@2$0@3$7^3^2^4^1@2$0^4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##$Nh01gh12mrh21ph32stp;1p;2g00>hj10Tg00?Mj14!s/$kj12Tg01XMj21Tg009kj23Tg018Zg00`=g0161g00eMg00ZZ#0!s$-4#2f3f0'1'3W2W1W0W3o"). Qed.
Lemma conc_put_meta : ltac2:(zQ "70!ij2!km1!hr9!h9!ii3!il6!im0>2st$5>1g$0>2mr$4>1p$0@3$2$3@2$1@3$6^3^2^4^1@2$1^4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "h01gh12mrh21ph32stp;2g02Fgj21Tg009kj20Tg018Zg00`=R0g0161g006[f3f0'1'0X20W1W0W3o"). Qed.
Lemma ctx_put_meta : ltac2:(zQ "70!km9!hr9!ij2!kn0!ii3!il6!im0>2st$5>1g$2>2mr$4@3$1$3@1$0@3$6^2^1^3@1$0^3").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "h01gh12mrh22stp;1p;2g02Gkj11Tg009kj20Tg018Zg00`=g0161g0256f2#1'0W1W0W2o"). Qed.
Lemma meta_slot_put_meta : ltac2:(zQ "50!iu2!ij2!ii3!il6!im0>2st$3>1g$1>2mr$2>1q$1>0@2$0^4^1@2$0@3$4^4^3^5^2").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "h01gh12mrh21qh32stp;2p;3p;4p;6p;1p;5g01BYj27Tg013@j36Tg00hej40Tg00iCj61Tg00gUj45Tg01ARj12Tg009kj23Tg02Hnj54Tg018Zg00`=R0g0161f3R1f0R2'7f4R3f2=613f1P0g0177R1g019bR4g006[R5g01:;R6C0P1P4g01:TP5P6g01;2E1g01FLC5%23'3P2D4UX20W1W0W3o"). Qed.
Lemma meta_cells_put_meta : ltac2:(zQ "80!kn8!ii3!j4!hr9!ks2!ij2!il6!im0>2st$6>1g$5>2mr$1>1r$1@3$3@1$2$4@2$0@3$7^3^2^4^1@2$0^4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "h01gh12mrh21rh32stp;1p;2g007Vj12Tg02JHj21Tg009kj20Tg018Zg00`=g0161R0g02KV#2f3f0'1'0X20W1W0W3o"). Qed.

(* [comment removed for export] *)
Definition fm_link : ltac2:(zQ "20!ij2!il6>3st0$1>1g$0>4head$0$1") := ltac2:(zQ "b0!ij2!il6!jqd!imc!hn0!ksa!kt8!ija!ku6!ii3!kl9\3st0$1\1g$0\4head$0=5hprev$a@1$8@2$7^3^1=3st1$1@3$3^3\1r$9@2$6^2@2$5@2$2$0^3^1^4=3st2$1M4\5hprev@1$4$0$1^2\2pv$0@3$3^1@1$5@2$2$0^5^2^1@3$3^4@1$6@2$2$0^5^1").

Definition fm_single : ltac2:(zQ "30!il6!ij2!kv0>3st0$0>1h$2>1g$1$0") := ltac2:(zQ "90!ij2!jqd!kv0!ksa!kt8!ii3!il6!kv9!imc\3st0$6\1h$2\1g$0@3$7^2@2$1$0^1@3$8^1\1r$5@2$4@2$1$0^2@2$3@2$1$0^2^1^3").

Definition queue_st : ltac2:(zQ "30!il6!ij2!kv0>1h$2>1g$1>3st0$0$0") := ltac2:(zQ "70!ij2!hn0!il6!lg5!lgf!lhb!kv0\1h$6\1g$0\3st0$2M1\1x@1$1$0$2@2$5^1^3\4head$0@3$3^2^3^1@3$4^1^3^2").

Lemma queue_eq : ltac2:(zQ "c0!hr9!li7!ij2!lic!ija!il6!kl9!lj3!kv0!lje!ku6!lk8>1RT>1h$8>1g$2>3st0$5>1k>0$5@1$1^5>4bail@1$1^5>0@3$0$6@1$9@2$4^3^4@1$3$2>0@3$0$6@1$a@2$4^4^5@1$3$2@3$0@1$1^8@6$b^8^7^6^5^4^3@1^4@3$7^7^6^5").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##5jp'0h01rh11oi001oh22Hnh32Hph41Rh51ai011ah64bailh71gh81hh91kh:3st0i021ci034headi045hprevi052pvi061xp;1p;2p;3p;6p;5p200R0g02LZR1p4p710p8P0g02M[R2!s7+1j15Tg00l_j2<Tg02N`j1?Tg00Nkj1FTg008Vj33Tg02Ofj2:Tg02Pnj2BTg02R6j19j22Tg02S@j18j26Tg02TJj30Tg02URj3;Tg00>hj1JTg00BPj1ETg02VZj1DTg02Whj1CTg02Xlj3@Tg009kj2ATg02Z:j1>!s8$Mj6=TP2j6ITg00oRj2HTg02[@j5GTf1R2f0R1'<#>p=1g00`=R3/H1p=4g02\Fg006[R4f2R5P2P1DGp=7g02]Jg018ZR6f4R7#5R8\6g00eMR9f3R:,<5#?%F3R;3311:7=39;P9P;f8R<#5R=g00_=R>f9R?#5R@1:1;RAP>P@f5RBf6RC'1/:;g00@NRDP3P@f7RE,BBPB%4ERF#9PDP3P611C1%4<RG#8g0161RH11<5%45/61RI'2W0=0<E50111E2%42/61RJ'2X0H=0ECn10110400021010500501O1P7%4CRK16F1,2F!sR$CB5;EO1RL!sY%6!sY'300RMg00ZZRN#J#E#D#CROP7V4RP57<RQn0110200!s&$0%EN!sH$N=7<PRP!sC1P7A@ECBO1RR33X19P9P;P>P@1:;;R!s0$PAPMP!sy2P!sl2=3=RX191B7CRRP!vE%DP3f:#5R9P1PC%9G!vZ'E1%4?#811?5/2I!u_$?<!vK$<2/2J!s7$<E!vD8R?O1RPPB16G1,2G!vo&9;<FR<O1!vD5PB!tC%P1P?P<!sF5O153@P11A9PX53P1O11A=!w4&0!sN'100b1%5ERL!ss$=PRP7%9K!uE'B1%8F11E!uC+EC!uC$C!uC+CB!xa;:%4B16K1,2K!sP$B75;C!u?7RHP:A@CB7O1RK33eP>P=!wn$=P;PHP:V4R497EO!w\1A7EN4!wo3LKe1<7BR4#>P1E=%?4P2E=PEPCPBP7P:P5EI!sL$W3W2X68W9W:X73W8X40o"). Qed.

Definition fm_st : ltac2:(zQ "20!il6!ij2>2st$0>1g$1$0") := ltac2:(zQ "60!lj3!ll1!ij2!lla!il6!im0\2st$4\1g$2@3$0$1^1@3$5^1$3^2").

Lemma free_meta_eq : ltac2:(zQ "60!li7!il6!hr9!lm3!ij2!lmb>1RT>2st$1>1g$4>1k>0$1@1$0^4>4bail@1$0^4@3$2@1$0^5@5$5^5^3^4^2^1@1^2@2$3^4^3").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "h01mh11Rh24bailh31gh41kh52stp;1p;3p;2p;6p;8p;5p200R0g02LZR1p4p710p8P0g02^QR2p4p710p8P0g02__R3p4p710p8P1j12Tg013@j3<Tg02N`j14Tg00Nkj13Tg008Vj30Tg009kj2;Tg00l_j2:Tg02`hj35Tg009Mj61Tg02Z:j16TP2j87TP3j58Tg02bCj29Tg018ZR3g00`=R2f3R1#2R4\3f4R3g02cNf2R5g017UR6=<51R7f1R8f0R9g0161R:P6g00eMR;%49%32R230X0:1;;2R<1:75R7A5156R=E1P:P6%69=0;2X0:P<P7P=E1G7%23P3P5P1P8P9D8P81915O130eX24W4W3W5X10o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Definition free_fp : ltac2:(zQ "20!h9!il6>2st$1>2lo$0>2sp$0>1a$0P") := ltac2:(zQ "i90!ipd!ln8!ld!h9!jgb!lo2!lo7!hr9!jk9!ij2!p9!pe!lof!lp4!hre!ji6!jqd!hn0!lqa!jq5!lr4!ls3!lsa!km1!lt5!ltf!lu8!lv1!mg0!jl8!jm7!joa!m3!mgd!mh6!mhf!mic!mj7!il6!mk5!ml1\2st$i6\2lo$3\2sp$3\1a$3@2$c@2$c@2$2@2$a^3^1@2$b^1^2@2$c@2$2@2$a$h5^1@2$b^1@2$e$h5+jq0@2$5$0\3rid$0@2$5$1\1r$1@2$2@3$7@1$h1$1@6$h2$0$1@4$h3$0$4$8$1@4$h4$0$4$8$1^2@1$hc^6@2$h0$1^1@2$2@1$i0@3$7$ha@1$h8^1$h6@2$2@2$a@1$i1^1^3@2$b^3@2$e@1$d^1@1$hb@1$h9^1@2$c@2$5$9\1b$9@2$5$6\2gh$6@2$2@3$7@1$h1$6@6$h2$9$6@4$h3$9@4$hf$0$4$3$f@6$he$0$4$8$3$f$hd$6@4$h4$9@4$hf$0$4$3$f@6$he$0$4$8$3$f$hd$6^2@1$i7^6@2$h0$6^1@2$2@2$a@2$h7^6^2^3@2$b^3@2$e@2$h7^6^2+8@2$5$0\3rid$0@2$5$1\1r$1@2$5$3\1v$3@2$2@3$7@1$h1$1@6$h2$0$1@4$h3$0$4$8$1@4$h4$0$4$8$1^3@1$hc^7@2$h0$1^2@2$2@3$7$ha@1$h8^2$h6@2$2@2$2@2$a@1$d^2^4@2$b^4@2$e@1$d^2@1$hb@1$h9^2@3$7$i4@2$i3@2$i5^7^3@2$i8^4@1$d^2@1$i2^1").

(* [comment removed for export] *)
Lemma outside_of_cover : ltac2:(zQ "a0!h9!jb!j4!k2!ld!m3!hjc!nc!p9!pe>1C>0$0P>1W@1$2@2$1$0$0>1a$0>0>2lo$0>2hi$0>0@3$7@2$1$0$0@4$3$0$0^2^1^4>1x$0>0@2$4@2$8^4^1@2$9^1^3@1^8^2>0@1$5@1^4^2@2$6^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##/pp'0h01ah12hih22loh31xh41Wh52HCh62HWh71Ch82Hah93Hinh:2Hxh;2IHh<3hi'h=1lh>3lo'i001pi011zp;2p;1p;3p;4p;5g002@R0j2ATg007Vj1@Tg001ij31Tg003`j28Tg004<j27!s/$Xj26Tg0053j10Tg00;Vj22!sS$@j1:Tg0086j34!s/$Vj35Tg009kj29Tg00<[j3?Tg00=5j3>!s/$Oj4<!s/$jj5;Tg002`j4=Tg006[R1P1f1R2f0R3C=p=3p-0\11A11R4#@R5P41323R6f3R7514R81873f2R9,73'6R:f8P2O1[^31[^11^21f4R;P2O1#01279R<[[^01X45%:4R=9146f7R>P2O1R?\:!s],P7!s[%g00>L12=9eW5W6X01P0P1P1f:R0!s[$=!s[$\8!t;&6R@!s^%P!t7%f5RA=44;RB!t9$;RCP2O1!t7/%0?12B9!sT$[^=5P3f=!sJ+!s~+9R8!s~013@!s~%<!s~$>!s|5=18@9179A'6R=#0RB12;9P2P9P>P@13>@R>=54>A14>A194>3?P7P3O5O1X8=PBeP7P9A146@P@P;P713C013;7R;554A14;8;>9P2P3O5X::X31W9X<1X>1P3O3C<12<!vP+W;X45X11X21!sW$2n2001100000121101101X04P3D;W4W7o"). Qed.

(* [comment removed for export] *)
Fixpoint ivs_covered (C : Z -> Prop) (W : list (Z * Z)) : Prop :=
  match W with
  | [] => True
  | (lo, hi) :: W' => (forall x, lo <= x < hi -> C x) /\ ivs_covered C W'
  end.

Lemma ivs_covered_In : ltac2:(zQ "90!h9!jb!j4!k2!ld!ml7!nc!p9!pe>1C>0$0P>1W@1$2@2$1$0$0>0@2$5^2^1>2lo$0>2hi$0>0@3$6@2$1$0$0@4$3$0$0^2^1^4>1x$0>0@2$4@2$7^4^1@2$8^1^3@1^8^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##7Tp'0h01xh12hih22loh31Eh41Hh52H1h62H0h73Hinh81Wh92H3h:2Hxh;1eh<3hi'h=3lo'h>1zi001zh?1Ch@2H2hA2H4hB2IHhC1ahD1lhE1pi011pp;2p;1p;3p;6p;8p;5p;4g002@R0j2BTg007Vj1ATg02dUj22Tg001ij34Tg003@j1;Tg0086j35Tg004XR1j27!s:$VR2j31Tg00:ER3j2:Tg0090j66!s/$Mj88j69!s2$kj2@Tg00=jj5?Tg002`j4<!t1$`j2=!t$$<j2>Tg006[R4P4f1R5f0R6C<p=0f3R7f2R8'=1>56'7p=3p-0\41B44R9#AR:P912861056R;=497R<P7P6P6P8C3R=f8R>P5O1[^04[^14^24[X8:g00[]g0079R?P?P>P8O1P8n010!s#%X:=X04W7X<4X=4W4%;9R?,25A49;?f7R?P5O1\=!s{-eP0P4P4f4R@/26f:RAP5O1RB!sK$\<!sL&f5RCA5985'2A59C@949;f;RD!su4[^D:P612?6f=RE!sE+!so+P@!uZ$7C3PB[^0412>5'7f6RB/0CR<=19;A49;@':P1PAP6P6f9R1C3f@RF!v-'f>RG/2?f?RH!uv$Cf<RC!s}$DC3fBRI!sO+ARJ/2AP310ECR310>?RK519A49KDfCRKPBO1PB10GE101>RL519P2P910HGR210CDRM9195fGRNPAO1[P610A1RO919210FH10DAR2519P9P4!vg%P4P6P6n20011!w]$120100100X;910JFPMP6E6A14FD!s\25!s\<IJP3P5!s\$IEA14KGP6fDRE=14HR3P4PFfER0=14FRMfLPHO1[X>4P6PMP4PJfMPFO1X>4P4PIP5!vs$HRFC3fORJ!vJ'105F10EK519PJPIO1]3]5X24PK!vx$NC3fN!sR,KN10KI519P4PKfFRJ!sK$5C3fQRM!sM,J510J0519PMPE!sy&14P0!sT$EC3fP!sR,0ERE=19EP5PKPIO2W3W5PFP7P5P6G8!s4$NP7PDP>G8PJP6E9bAX93P0!s1$9W6P6O1b!s+&W4P6O1W4n20021!|,'101A1962PJP1O1[XE9POO1P61@92O1b4W3P6O1A49LCPCP8PAP1P6P?PBO6W7P6O1!wg$!sr%21!wm$0000W@W5P5P6O2!sF-121!}I91078=595,2>A59<!|Y$PG!}N5WBX8:X14X24!t'-!y4'1!y4&C9P6D?W8W?o"). Qed.

(* [comment removed for export] *)
Lemma munch_grow2 : ltac2:(zQ "71!hsf!hk7!hma!v9!hn0!ht6!j4&>0@1$2@1$1#k0@1$4@1$2@1$1#8>1f$0>2iv$0>1W@1$6$0>1m~0>2m'~0>0@3$5@3$3$0^5^3^2^1@3$5@3$3$0^6@3$3$0^5^4^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##1^p'0h02H0h11Hh22H1h32H3h41Wh51mh62m'h72ivh82H2h92H4h:2Hxh;2MUh<1fh=3fhih>3floh?2hih@2lohA1xi001pi011zp;1p;3p;2p;4p;5p;6g007Vj1CTg00>hj17Tg00?Mj1<!s/$kj1;Tg00@Nj1BTg00A0j38Tg00;Vj24Tg003`j22Tg004<j21!s/$Xj23Tg0053j16Tg00=Oj4:Tg010Pj2ATg02efj59Tg02fCj2@Tg02gGj6?Tg0086j3>Tg002`j4=Tg00YYR0f1R1f0R23>p=0g006[R3P3P1P2C=p=5g002@R4P3P3%C0R5g00ZZ#7#7#7R6!s-%#<#;%<6#;#B[R6f4R7f2R8'0?812f5R9f3R:,07R;'0?881[^66]5]4^70P2P!t$$f6R4/59R</08!s\$7R=/54/0;!sW'^56^45P2f9R;f8R>'5!sQ':R?/5;R@/0:RA1597/0:,0@R@P8P1f;RB/5?10<7'0/42f<R</21111B'3#6RC12=11114'3#61491RD'313CD12>8118=!s>%48'312;:11:>!s^$D14=:REf>RF/2:f=RG,1:'3#6/3E14>7f@RE/29R:114EREP9fBRH/2=RIfA,1=RJ!v~$:O1W3W0g0079RK\E\:12<4R411=<R:P712F>11>G!sS-1PK\:\413IJRJ#6RI14B=fCR=/2>R411>HPK11;=P7P1O1fD,1?PK[P2P1O1PK1AK2b0b2W9X34P2D9X2JPIeP8C:b1b0W8X2DP2D9W0X1CP2D915<B/09/41eW:XA31@A@eP2E?W;X66X56X45X?3X@!yG$O2n2001100000121101101X70X=3X>!sI?<0o"). Qed.

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
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma amo_aligned_intro : ltac2:(zQ "d0!hr9!h9!iib!kkc!ld!hk7!mo9!mr1!p9!pe!ms0!htf!ms9>1a$1>0@2$4@2$8Z^1@2$9^1@2$b+2+k0>0@3$0$1@2$a^2+4Z@3$0$2@2$7$6@2$c@1$5#k0^3$3").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "h02Hah16__sat1h24__x1h31zh42Hmh57__arithh64__ffh76__sat0h86__sat2h98__varmaph:5__with;1ap;1p;2p;3p;6p;4p;7p;8g00>hj11Tg00BPj15Tg00Bnj2ATg004<j24Tg004Xj2<Tg02hQj23Tg008Vj39Tg00kdj28Tg009kj26Tg009Mj6=Tg00?Mj1>Tg02i1j2WTg00E\j2VTg02iWj2UTg00FFj2OTg00Fnj3NTg00GRj2KTg003@j1HTg007Vj1GTg00JPj2FTg00KLj1ETg00Kjj1DTg00OMj27Tg00LUj2CTg00N@j4;Tg00P0j3BTg00Ukj7ITg00Nkj1JTg00VOj8@Tg00PSj2LTg00Q5j2MTg00Qaj3?Tg00R@j4PTg02jHj2QTg02kSj2RTg003`j2STg00UGj7TTg00[?R0f0R1'Sp=0g00_=R2g00_]R3791p=2f1R4g00WZR5g00X9R6P6g00XYR7P1g00Y9FTp=:g006[R8%01g00ZZR9#1R:#5R;%1:R:#1#1#1#1R<#5R='AR>,41'<R?%5:R:,34=980P8f2R@131:/80#2X38P8P01810#2X381623R313@:P1E=%><R<1W<@R2'V1U@:%0@%0:f4/3:#0[[1O;=140;R:%0=140>[RA[%0;RBg00[]RCAN;=4UW0%0>\C^0BP4g00\91K0;'6P:eO1PAg00\_RA#H%GA1F84%E8%D8RAP5P6P6P7PAP5P6P6P7P81780g00W31C89R9C;,:AP8P9g00^V178;=B8<C;,:AFIR<%J6P<G@1LA7P1P@P31M1@#2dA?804CPb6b9b:X28%04144>'<\?^28P1f7f6O2b5b1b7b1b8,Q@E=g02lA/R2#2eW4W0W;o"). Qed.

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

(* [comment removed for export] *)
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
Lemma sextw_sxv0 : ltac2:(zQ "90!hk7!nha!hr9!h9!jue!hre!ms9!hma!ni1>1v$3@3$2@1$7@1$0#k0@2$6@1$0#k0@2$8@1$0#i0@2$5@1$1^1Z@1$4@1$1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##1+p'0h01zh15lemmah21vh31xi001xh41yi011yi022x'i032y'p;1p;2p;3p;4p;6p;;p;7p;9p;@g00>hj10Tg00?Mj1;Tg02lnj19Tg01aPj18Tg00E\j2?Tg008Vj3Sj12!sV$kj1OTg02n9j1DTg00B3j25!s8$iR0j26Tg02i1j2<j1RTg02>Qj41Tg02oPj1>Tg030?j43Tg02;Vj3=!sj$Pj17Tg0316j2Q!s/$Wj2:Tg01[0j1NTg0328j2F!s/$ej4Ej7JTg02:Ij24Tg033Rj1GTg034Aj6HTg02?8l;CTg02@Sl9K!sA$lj1BTg036=j2ATg037Lj1MTg038]l9@Tg039El@PTg006[R1g00[?R2f2R3f1R4g01CfR5g03:0R6g03:MR7f0R8g03:jR9M9@p=LP1P2f6f5P5P6P7f4P9g03;Sf3P3P4P2P2P8M@Pp=Ig00ZZR9#0!s$'R7#0#;R6%98R5#8'?=S15%O6R:%2:R;%D:%;7R7%94R</52R='6R>,<6%8<R?,?6R@/52RA,67RB,<6P:^01RCP1P:%21RDP;C1REP1P:P;%>:C39=CE%R6P>PBg0177RBP1^01R>%2BR6P1P1%79R9P1P1P4P8!s-&31Q48RE#71:48n0110100030010103!s'$!sP+:84%NE!sK9!s<$0!s<,2!s'$X41X31RE;LD,F1PDC1R4P0P>\BR3PBP>P6P4C1R6!s2$4!t7$D%>1C3C39=36P0CEP714B7P=PAP9PEPDP<P@!sM$G1P@P<P8EH1412FIM;CFJP?P?14:?M9KW1%B8,A5%M8O2X21o"). Qed.
Lemma sextw_sxv1 : ltac2:(zQ "80!hk7!nha!hr9!h9!jue!ms9!hma!ni1>1v$3@3$2@1$6@1$0#k0@2$5@1$0#k0@2$7@1$0#i0@1$1^1@1$4@1$1^1").
Proof.
ltac2:(KReplay.run1 (kr_t_MallocKit_B ()) [] "h01zh15lemmah21vp;1p;2p;3p;4p;6p;;p;7p;9g00>hj10Tg00?Mj1<Tg02lnj18Tg01aPj14Tg00E\j25Tg008Vj3Hj12Tg00?kj1CTg02n9j1=Tg02niR0j26Tg02i1j27j1ITg02>Qj41Tg02oPj19Tg030?j43Tg02;Vj3;Tg032ej4Gj7ATg02:Ij2:Tg033Rj1FTg034Aj6BTg02?8l;@Tg02@Sl9?Tg034lj1>Tg036=j2DTg03<:j1ETg006[R1g00ZZ#0#0#0#0#0R2#0#<R3f0R4#8R5#4'5=H15%C3R6%26R7%=6%<2R2f1#8R8'6R9,73%48R:,53R;,62R<,73P6^01R=P1P6%21R>P7C1R?P1P6P7%96C39;=?%I3P9P<g0177R<P1^01R9%2<R3P1P1P>P>C1R?P0P9\<R=P<P9P3P?C1R3P<P9P?P1P1P>%91C3C39;=3P0CGP21:<2P8P;P1P>%F1P;P8P4EBM;@FAP:P:1:6:M9?W1%>4,D5%E4O2W2o"). Qed.

(* [comment removed for export] *)
Lemma le4_lor_sxv : ltac2:(zQ "e1!ld!hk7!h9!nha!nid!p9!nj4!pe!htf!j4!hr9!jue!ms9!hma&@2$0@2$5Z^2@2$7^2@2$8+2+i0>1f$2>1s$2>0~0>0~0@3$a@1$9@1$d@1$1#8@1$4@2$c@1$1#k0@2$6@1$3^3@1$3^4@1$4@1$b@2$6^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_MallocKit_B ()) [] "##Aqh06__sat2h1!s/%4h2!s/%1h3!s/%3h47__arithh54__x1h64__ffh78__varmaph85__with92Hah:1bh;1zh<4__p1h=!sn%0h>1Hh?2H0h@2HfhA2HkhB2HshC1fhD1khE1sp;1p;2p;4p;3p;6p;5p;7p;8g00>hj17Tg00BPj1A!s/$nj2HTg004<j20!s/$Xj24Tg00?Mj1MTg02lnj15Tg03=Lj21Tg02i1j2ITg01aPj1>Tg034lj1G!sJ$ij4PTg00FFj2O!s/$nj3NTg00GRj2kTg009kj2DTg003@j1^Tg007Vj1]Tg00JPj2\Tg00KLj1Z!s/$jj1YTg00OMj2@Tg00LUj2XTg00P0j3JTg00N@j4?!s/$kj1W!sA$Sj2VTg00Q5j2UTg008Vj39!s8$aj3STg00R@j4RTg03?<j4QTg02hQj26Tg00E\j2FTg01NZj6TTg01Pij1l!u&$`j2=Tg03@Hj2<!s/$ij2CTg03AFj6K!uW$Mj63Tg03BUj3jTg03C7j5iTg00=Oj4LTg03DIj3`Tg0104j4_!s8$lj2aTg03ENj4bTg03Fcj5cTg036=j2dTg02jHj2eTg03GHj3fTg00UGj7[!s/$kj7gTg00VOj8hTg00[?R0f0R1'=p=2g006[R2f1R3g00W3P1C?p=;P!s4$ZR4g00X9R5P5g00XYR6P1g00Y9F[p=8f2R7P4P5P5P6P3P1Fgp=Ef3R8!s;+7P3P1Ghp=:g00_=R9g01;PR:791p=B%23R;g00ZZR<#7R=#AR>%7=#7#7!s5&?'HR@,03'4RA%7=RB#MRC%57RD%58RE'1RF'I1187#>PDPE%G7%G8CP%2F%ABRB,H>RE,0F'4f4RFP81O>?RD100>RG%2?RH100@[RI[RJ%2>RKg00[]RLAN>?3UW9RM%2@\L^9KRN1O>BRO%2B100E[RP\GRQAN>B3VLX9KRB%2E!sP%K!vY$\91k0>'DPGeRGO1RLPPPFPGO1RGPIg00\_RR#^RS%]RRR1\23RT%Z2RU%Y2RV1@20RW1X2<R<';,8VRXP2P<g00^VRY1@2>R>%M=5J2R=C?,8V5EVRZ%W5R[P2P<PYAJ2>CR>!sB$9EVXRYC:1VV6R\P1P7g00_]R],D91U17=99]dAS203CRR0b6b7b8X52R]%21R^101@'4R_103E,4;R`[^52RaP1f;Rbf9O2Rcb4b3b2b=b2b0b3PDPJPMPNPOPQPBPKPLPPPGPIP]PaP1f:Raf8R]O2!s\1CQ11F8Rd#210dE'4P2%5Ff5Rd#5Re'1Rf161@Rgf6Rh/1dRi#>,FC/6@592X;2P211dFRj%5h,1e/6@=92g!s>&FdRg16i@9921X;2RiP2PjPiP216j@Pj%2jRi10j@!u-;p-0RePSPRPTPUPVPV!{B+8ET9EVXP[PXC:P\P!vZ,W<14^3P;[^52^<eP1f<Re/1bR;/0EP;f7R;O3b4b1b0!uu%b1RXP?Pj!v[<SPR%l2R8PU1@2?R6,;W,8V!tC,PHP1!sw2HPX1=?1RWP91<;3R51<h3R4'C%B1X:9P9P:1<;7,C1#B!s6'C:!s3%1D9:P4P?PhP3PH!td?!v4&ZP[PZ!u|2RZPA\_^52R_P1f=Pb!xc$!tq-!s~E1;6<,8VR6P[P6!t,21=?3\W^52P1P]P;!t'3RWEKE3P5P?P;!u;@ZP_P1f>Pe!tm4!sh$11;h/<3Aj;h3E3WAXD2DiR;CL9`j@C_Pg1aFdE316f@PFPd!t5@c!uvJ!ta$PePa!ta3CbE3%>j,FCPi10jEPXPjP@PEP;!vj@8PU1;=>!yH01=@E!yJ3DcCL,djE31ICf,FC!xgFYP[PY!w`301E,4^P`[!wd$%5b%5e'1P]!uE3,efE3b?b>3fXBAW@XE2XC2o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
