(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep AsObj AsStack0 AsWalk N8Kit CXXLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AXpres AKitChk AKitCells AKitIn AKitRV AKitSeg W_bnum0 W_apstring0.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import N8Store.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_W_bpesc0 () := KReplay.lz_vm "#$>%C47Corelib7Program6Basics4flipK!sD,Numbers7BinNums8positive02!sK=1Z02C56Stdlib6ZArith6BinInt1Z6modulo!sF<3div!sC=addC89OSSVerify6Proofs:boost_json:fuzz_parse3lib3BJB7W_bnum03sh8C13~~~!uVG1!u8=shiftr!ts=pow!sC<7div_mod!wG,4Init5Logic3not!s}=mul!sC<=mod_pos_bound!sM<2lt!siAneg!siDeI!u28and00!s]+5omega8PreO!s/#1Z;!uo#0_r_ext!sL>!tS#!sL3!vb4compareK!tV72eq01!s@29Datatypes3nat!zyB3K4!tF&9micr!tp$7EnvRing3Pol!t+#!sG4=!sD#M!s4'5Psatz04!sOK2!sO6:Z!sL+;!uv%!{R$!sRP3!tOK7!sOK5!vx<4list!w@>!sF%2I!sFA0!tW66VarMap1t!ur8!sD,1!sD@3I!sD?0I!uwC7Formula!tq8!y6'5PExpr!y8F!st+!vO=6option!uk85Tauto8G!sl'7!tbE5!sIE2C!t8<B!t8&C!z;@=Z!sT$CheckerI!}U;0C!wQ<4find!t3AC!t30_s!#4\#!sX59SatDivModCZ_!#51#onneg!s,&!#3b;?!#8'$_div_pow2!#7N78eq_ind_r!#:&[6sh8_eq!#:,&!yDB!}3&6!xxF4!sJF!xyF3!smF8!#6E?1I!sD?0!ujD3Op203!zP<5eKind!#3T<uni!#3T8!se%4kind!#4\>!sf$1!ttI1!#?6F3!tz<:!#:m$ison!#467!#8+:0!#;+@!u37!sq;!u_J5!w6=bool!t`>!sF%1!~q85False!~t8!}{0!}I#!}{0!#>>9x01!sq+!~=&4Zdiv:!~f%mult!~486!~4%c!~2S8W_bpesc08!~3#off!#E<%!#CP<op!#H1=1N02C45stdpp9bitvector;definitions7bv_wrap!sLA8bv_s!sM$!tV;>pow!#Dc#!#5jA:!sN#!w9'!#3@B7!um=sub!sfE4!sIE!#5^F3!y38!#E{#!#IP<9!y6#smal!#H7<7add!#I6#5!yx61Z>!yx$od!zk#ide!x6BZ_to_bv!sLA;bv_unsigned!sPA@!sv&!sU+!|}84True00!{M]>!yl$32_of_u64!{SB!vO$0_rI!u1@2bv!ta_@!ta1_0!tc&!swPLib3Mem4sx32!sf&!u&@?bv_half_!#R0#us!sTA>!}E'!yw&!sS@9!sS#!x`F>!x`'!sS&!#@d;mul!zU$idemp_!{E>!sK#ad!sp=;lt_ge_cases!#Cg8or00!#R<8iff!xQ]Bmod64!xO#!v^$_neg!wk%!sy]E!sy3!#5]$!#Br:!#3i29!sJF6!x-AD!}c-_in_rang!#3;A:bv!z/+!wk;4l!#VG>=!}H#!sH#_diag!sk>xor!|PT5Bytes:!t,$!v}$!}@Z9LiaTuning9zify_done!#Z[2!#5'3!#8$<4one!vN?a!#X@=9!sD#_!sg#!z%]:!#4O&id!#3a&!#>>'Classes?Rela!xQ#!s6&=eq_Tran!#Dn$!sV59Morphisms:respectful!s}E<eq_Reflex!s|BJr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^??eq!tM#per!tT;!sR,@!u$0per!sS?Mt!wc#_co_!#Df#v_impl_m!sE&!{WT8PropExec!#8w+congr!#<MA4of_N!#Q[8iff!wI$!#G~5;Zify!uH&3inj!sIB5mkre!snC9!~Q%rph!sOB;rew_!tk%v!|`]=!#?k6!u=Dapp!sKB6!sK$2!#Qt=N!#Kq78!sj#Inst7Inj_Z_Z!#KJ9minus!#Dp#!#6YX<!#4<#lt!#WD$!y3A!#4h$comm!sI<:!sI$assoc!sJ<3lo!#id<7testbi!#Mi2!#QC,orb!v&3:!s,%_dec;Z!uC#le!s2#!#?716Specif7sum!#Pm$!#:q<ones_spec_l!#kC=6eq!t5#!#8V=og!#nx<<!sD#!w@+!}%75proj!#9{<?bits_above_!t8@>!uE,high!sN<8lor!sM$!xp=!tA$inj'!#TIA2!#RU]!tT#m1_l!zLB!sN$!zK$!{`Y;!sf#!{_Jdiv!#H6F=!#SP%!sR&!tfS6MState<!#CI'lit!thB!#sC$!#HO<!#b^$l_mul!u_$!#Yh;!#gE&0!#LSW7mem_inv!#?s2!{3%Peano!#s2>6of_na!sF>to!sF@3max!y>=max!{<$!#gg9x!#P8^:esc_target!#OJF5bv_eq!#9%A7!#:o%K!{>TCells4cell05!#GOY!sj%6cb!|1#!#GH7!yJ51!#i-S;W_apstring0<!t9#_list!#i8'C3!vc%7tactics<f_equal_hel!#\n34Znat5Nat2Z9i!#\k'!{+W3le!#>8'ELinuxProcessSeman!tW#?!s<2>Riscv!sE+=ov_read_!v\%!#Nj@!#Sr&oblig!#E^#_1K!#W|C1!x@UImage:ro!td%_b!#@kG9and!#B]&!xm;length!t_Z>ro_!zh#s_i!s5#!zmZ4Step8!sq'!#4,25Lists7!s+#Def3map!{vZ5csiz!tr[!yq#2wa!uX_@!vK+!yu$a!#3s%!#7t;!#kx#!#E,?@!#6q$_!#6X$!}0#!|e=6inj_lt!#5|\6AESCJT!uxV2Bs5ASegs5aseg!xO&I!#5o^0!#<@8!ue-8!ue#suc!#F@=eqb!#:K<eqb!vn6!sF+7!sF#neq!vm]4ptsh!#8-ZFrame5munc!sia7outsid!}o\TacX2b8!seW!#{?,9sh8!$3$%!}S]3mrd!tVc!vo$_!soe?!#99%1_of!suZ2Bs7AsIface3mem!xT`3ivl!tQY8AsShadow7AAPP_HI!sm%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init5Logichc2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7W_bnum0~~~~~~j53sh846Stdlib6ZArith6BinInt1Zn93addn92len93divn96modulohc2exn92ltn93mul04Nposn93powhc3andn93opp35stdpp9bitvectorbdefinitionst37Z_to_bvt38bv_swrapt3bbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~hh34sx32t32bvt39bv_signedhc3iffhc2orn93subn94lxorn94landt37bv_wrapn93lorn96shiftrn96shiftl37Corelib4Init9Datatypeshq74booln93eqbhq74listhq76option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB8W_bpesc0~~~~~~htf6AESCJT79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~ii85asegshq74Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsin4dov_read_byteshtfaesc_targethh33le4hh37mem_invhc3not79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~iu24cellhq74consiu22C8hq73nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB6AKitRV~~~~~~jjb2rvjjb3rs0jjb3rs1jjb4rs10jjb3rs2jjb3rs4jjb3rs5jjb3rs6jjb3rs8jjb3rs9jjb3rsp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~js53memiu22CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~kgf8rw_cellsiu22C1iu22C4kgf8ro_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kme2b8hh33mrdhh32wahtf4ptsh79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~ks47AAPP_HI79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~lgd3ivllgd5munchlgd7outside" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs; try transport_cond_ro segs m a bs.
Local Ltac addr_diff E A ::=
  lazymatch A with
  | E => constr:(0%Z)
  | _ =>
    match E with
    | Z.add ?X ?c1 =>
        let c1 := zlit c1 in
        lazymatch A with
        | Z.add X ?c2 => let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
        | X => c1
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    | _ =>
        lazymatch A with
        | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
        | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
        end
    end
  end.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
(* [comment removed for export] *)
Lemma sh8_off8 : ltac2:(zQ "70!h9!j0!n3!p1!p7!pc!q2>1a$0>1c$0>1k$0>0@2$4Z^3>0@3$1$0@2$6^4+8Z>0@2$4Z^4>0@3$1$0^4@2$5^5+8@3$1$0@1$2@2$3^7^6@2$3@1$2^7^5").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##C}h01zh11Hh22H0h33H11h42H5h57__arithh64__ffh78__varmaph85__with94__x1h:4__x2h;4__x3h<4__x4h=4__x5h>4__x6h?4__x7h@4__x8hA1khB2H1hC3H10hD3H12hE3H13hF3H14hG2H2hH2H3hI2H4hJ2H6hK2H7hL2H8hM2H9hN2HahO2HchP6__sat9hQ1ahR1chS1qhT2q0hU2q1hV1rhW2r0hX2r1p;1p;2p;3p;4p;6p;7p;8p-1R0p10000R1p4p710p9P0P!s2$2!s3/3110p9g000Nj1<Tg0013j1Q!s/$Qj20Tg0021j22!s/$Nj21!s/$kj1KTg003nj1?Tg004Sj2GTg0053j2x!s/$Pj2XTg0061j1s!s/$Jj2B!s/$gj2VTg007Nj2=!s/$jj2UTg008Qj2E!s/$mj2OTg009Hj2Y!s/$nj2STg00:Tj2hTg00;5j2]!s/$Oj17!s/$nj1gTg00<Lj2f!s/$mj3ITg00=Vj2[Tg00>?j2Z!s/$kj2eTg00?Wj2dTg00@@j3c!s/$ij1zTg00AIj3b!s/$ij1yTg00BIj2P!s/$gj1wTg00CEj4J!s/$cj1uTg00DAj1t!s/$lj2LTg00EOj4HTg00F:j1r!s/$\j6qTg00G@j3R!s/$cj2_Tg00HFj2p!s/$hj2oTg00ITj3M!s/$nj3lTg00JMj4mTg00K?j3nTg00L0j3^!s/$Yj6DTg00M7j1`Tg00N=j3T!s/$fj7kTg00OJj7j!s/$nj3iTg00PQj8vTg00Q5R1f0R0'Ep=Cg00QSR2?M01p=Af1R3=M20p=Nf2R411305M2p=3%?0#?p=>%<0#<p=;1E141=30'Op=81[20p=6AT230p=\!s-$9T24p=F1_20p=:P2P3g00R1P0CHp=W!s4%XR5g00S7R6P6g00SWR7P0g00T7Fkp=4P4P5P6P6P7P3P0Fjp=a!sn&TW!sn%@Ai!tA$9f3R8!sS+4P3P0Gvp=5%C4g00U>R9#<R:#<R;#<R<#QR=,08#A%C8f4R>/2=,N8P2f5R?/2=f7R@f6RA'1RB#K%K@RC;30XA2P211A?RD%?9RE#QRF'GRG%?ERH#?#>!s$-<#;!s$0QRI'112A=RJ930CX02P21GAFRC/1I1GBF/1I?30J!s?$%Q:/xFRK,2D110IRL1G@F/1I;3!sF%12AK12BK!sZ$LJX021XD=%A=RL#sRJ12B=,B=10B=53B[1VB=1=1=RBf8RK/1@RM/0=RN?8N=[1UM=1==1RMf9RN/1KRO/0=RP,==1EP1'O[1YO=f:RO/1NRP/2=#A\L1SP=f;RP/1ORQ/0=/NQ\L12Q=P2f<RQ/1P/0=P2f=RR/X=f>RS12S!tb%S=33\J1VS=f?RS/0=RT?8T=\B1US=f@!s9&!tM$T1'O\M1YS=fART!tI+T=fBRU!tD$U\L12U=P2fCRV!tA$1XV=fDRW12W!t>%W!t>&W=fERW/0=RJ?8J!t>$W=fFRJ/0=RX!t>$X!t>&J=fGRJ!t>+J=fH!sM$/NJ\L12J=P2fI!t<$P?g00Uc1h1=']PBeRBO1A800=PRP!s1$KK=PW!s1%SS=g00VIRSg00W5RB#7RW#7RR#7RM#7RX#7RY#7RZ#7R[#7#6%g9,f2R\%6ZRZ5I2%6YRY9I2\%6M%6RRR%6WRW9I2\'\3F3F1[2BRB/\Wg00WTRM'Z'e%6[%6XAI2\R1d2==c2B7FW5FY7FZ/ZM%zSRM5bS3b%ySRSP2P2P21P2KP>%w2RZCJP41P2ACJP3!s?$?P81P2@CJCJ%u2RY%t2RW1L21RB%:<R<'W,4WP2P<g00X@RR1L2=R\CH,4W5aW%r6RXPW!s$$!}`&1@\B,4WEqR6PX%<E#:R5%:ERE9R2\/9<'@,4WC5P!s]%6PX%:;R;%::R<9R2\%?:#:R:'9!sN-%:HRH,WB!tX%HPRP!tO+!sm,19;51_29R9!t7%H!sg-1@:!sc$X1L2IRX,9919<X/9E!sJ&!s$,1pW7R7P0P4g00XgREg00YGRX']1o04=MEXdAl213CmR1b6b7b8X92X:2X;2X<2X=2X>2X?2X@2A8@@=g00Yg\LRL1B=>RX=3@N[A3AX@\LA8NN=11KO1B=?;3P\L%AN11AI11@I;3K[!s#$^92^:2^;2^<2^=2^>2^?2^@2P0P>PUfNPPfOP?PQPVP8POPTP3PJfKO>b5b2b4b3bXbUbFbEbDb3bCbWbTbMbKbJb4bIbVbSbHbGbBb2b1PCAnA=8%C=10@=#C[PMPSPZPY1L2F!wC&7P!uk&%CFR1P0b5bPP1eR19^AFEDPGA^DF1ED%KA%`AED%KD%`DEDP>P0EDW1WOWLWNXA2XR2XQ2o"). Qed.
(* [comment removed for export] *)
Lemma mod0_lin : ltac2:(zQ "60!h9!j0!qb!r0!q2!r5>1a$0>1n$0>0@2$3Z^1>0@3$1$0@2$4^3^2Z@2$2$0\1k$0@3$1$0^5@2$5^4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_W_bpesc0 ()) [] "h04__x1h17__arithh24__ffh36__sat0h48__varmaph55__with64__x2h74__x3h84__x4h91Hh:2Hmh;2Hnh<6__sat1h=1ah>1kh?1np;2p;3p;1p;4p;6p;7p;8g007Nj2FTg001Qj24Tg006Jj23Tg00ITj30Tg0021j2=Tg00K?j2CTg00@ij1OTg00Aij1KTg00BIj2;Tg00Ccj1ITg00DAj1GTg00Dlj2_Tg00Gcj28Tg00EOj4>Tg00F:j1WTg00F\j6VTg00HFj2UTg00;5j2STg00Hhj2RTg00Inj3QTg00JMj4NTg0061j1MTg005Pj3LTg002Nj2@Tg00ZDj2JTg00;Oj1:Tg00=Vj2<Tg00N=j35Tg00>?j2?Tg00;nj1HTg00<Lj2PTg00<mj3ATg00AIj3DTg00Bgj1TTg00CEj4BTg000Nj1ETg003nj1^Tg00G@j3]Tg00Onj3\Tg00[5j4[Tg008Qj2YTg00Nfj7XTg00PQj8ZTg00QSR0f0R1g00Q5R230p=91Y21p=2f1R3g00RXR4g00S7R5P5g00SWR6P1g00T7FXp=1P0P3g00TWP1C>p=6f3R7P4P5P5P6f2R8P3P1GZp=71F21R91483#9P0f4R:1371500X>01=78R;1C78%27R<f5R=/4:#2\<[g00VIR<#OR>%K<R?1;03%I0R@%G0RAP01_02RBg00X@RCg00U>RD,80REC>,1A%W5RFPAP4P5P5P616EB,1AEVC71UA6R6P1P8g00XgR5g00YGR4'S1R18=054dAQ023CNR4b2b4b5X00%93g00Yg[\9^00P1P:P7O2b1b3%98#Me9L78138;1478'@90071C:7%2:R;f6R9/4=#2\;[1J=:%2=R;f7R5/=9RG#2\;[g00W5R;#:#:RH#:,<0RI1<0HRH1<0;R;550550g00WTRJ'?%HD,P0RK=A0IAA0KH=50;550/?J=D<>5D<P?P0P01;0:P8%T0CBP31;07CBP@PA%EDR@,80R?%^D,805]0RD%E@,80R@5\0,6E,1APFPA16@B,1APFPAP0PBPCP?C>,1APF16ED,1AC7C7C7P6P4b2b4b5X00X60X70X801338/@79001%9:1F2713:=9007[[[^00^60^70^80P11459PGP9P5P7P:P=O7b1b3b<1=:7,37900:eb9C[W:W;X?0X=0o"). Qed.
Lemma sh8_off16k : ltac2:(zQ "70!h9!j0!n3!p1!p7!pc!r5>1a$0>1k$0>1c$0>1j$0>0@3$1$0^4@2$6+h0^3>0@2$4Z^5>0@2$4Z^4>0@3$1$0^4@2$5^5+8@3$1$0@1$2@2$3^8^6@2$3@1$2^8^5").
Proof.
ltac2:(KReplay.run1 (kr_t_W_bpesc0 ()) [] "h02Hah14__x1h21ah31Eh41Hh52Hch62Hjh77__arithh84__ffh96__sat0h:8__varmaph;5__with<1ch=1jh>1kh?1zp;1p;2p;3p;4p;7p;6g000Nj13Tg0013j16Tg006Jj20Tg00ITj31Tg0021j28Tg001Qj27Tg00ZDj3?Tg00@ij1=Tg00Aij1<Tg00BIj2;Tg00Ccj1:Tg00DAj19Tg00Dlj25Tg00Gcj2KTg00G@j34Tg00EOj4JTg00Nfj7ITg00HFj2HTg00;5j2@Tg00Hhj2ATg00Inj3BTg00JMj4>Tg00[Oj2CTg00[oj6DTg00LYj7ETg00\Kj7FTg008Qj2GTg00Q5R0f0R1'Gp=2g00QSR2f3R3g00U>R4#3R5#3#3R6#3#6R7f2R8'0512f4R9#2%23%66R6,899123f7R:f5P9P8P2f6R9,07R;%21f1R</76=120]0X22%2;A?968%2618:6#2[g00VIR9#=%<91;2<%:2%92R9g00RXg00S7R;P;g00SWR;P2%65R5,521K24R45421526542g00TW1527=424CJg00T7FI1H9;P1P8g00XgR;g00YGR9'@1A18=1;9dAB20<C>b8b:b;X121051/061071512^12P1f9O1b7b9105:/06107:512R9eP9P2f8R9,05R5/061716=120X?21C561079P1EDb4W0P:P3P8FEP<P1FFW6W5W0W3X=2X<2X>2W2o"). Qed.
Ltac norm_shpa :=
  repeat match goal with
  | EPA : bv_unsigned ?pa = 16 * ?kp |- context [sh8 (bv_unsigned ?pa' + ?c)] => constr_eq pa pa';
      let j := eval vm_compute in (c / 8) in
      rewrite (sh8_off16k (bv_unsigned pa) kp c j EPA ltac:(lia) ltac:(lia) eq_refl)
  end.
  Lemma swrap32_of_u64 : ltac2:(zQ "c0!p1!rb!h9!s1!s7!j0!p7!r0!sd!v0!va!hg5>1b$2>1k$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0@2$b@1$1#k0@2$9@1$1#k0^3^2@2$0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##@yh06__sat1h14__x1h24__x2h37__arithh44__ffh5!sN%0h6!s/%3h78__varmaph85__with91zh:2Hah;4__p1h<!sR%2h=1Hh>!s3%4h?3Hbkh@1bhA1kp;1p;2p;3p;4p;6p;7p;8g000Nj17Tg0013j1BTg003nj1<Tg0053j2DTg00]Tj1oTg002Nj20Tg008Qj2=Tg007Nj25!s8$mj2;Tg00^1j1?!s/$Oj2RTg00_5j2C!s/$\j2NTg00`Dj3ITg006Jj2JTg00K?j2_!tU$Qj22Tg00:Tj2]Tg00;5j2GTg00@ij1ZTg00Aij1YTg00BIj2X!s/$gj1WTg00CEj4V!s/$cj1UTg00DAj1TTg00Gcj2F!s8$lj2E!tU$hj3KTg00HFj2Q!s/$hj2PTg00ITj3A!s/$nj3OTg00JMj4STg00aKj28!s/$hj3nTg00bKj2mTg00EOj4:!s8$nj6lTg00F:j1kTg00cRj4f!s/$mj3eTg00LYj6>Tg00[oj6@!sS$\j6`!v5$1j1aTg00dPj4H!u3$@j3b!sS$5j4^Tg00e1j4c!s/$Wj2dTg00f=j2\!s/$gj2gTg00Onj3hTg00Nfj7[!s8$Jj7iTg00PQj8jTg00QSR0f1R1f0R23Ap=1g00Q5R3/=2p=3Ah012p=6P0P1g00TWP2C:p=9!s4$RXR4g00S7R5P5g00SWR6P2g00T7F[p=4f2R7P4P5P5P6P1P2Fip=Mf3R8!s;+7P1P2Gjp=Lg00U>R9#7R:#BR;%<9#<#<#<R<#BR='DR>#oR?1012R@'=15@>';P0%7:#7#7#7RA#7#?RB/R7RC%?ARD1027'C1087RE'1X90%BARA,N;RF153;RG%3A1D;ARH,53[RI[RJ%3;RKg00gVRLAI;A1UW:RA%3H\L^:KRMf4RN1JHHRO'_%3N%3Of6RP/2O#3[[1N;=RQ%3=153>[RR\GRSAI;=1VLX:KR=%3>!sm%K!vZ$Uc1]3;'GPGeRGO1RLPRf5RTPGO1PIg00VIRU#ZRV%YURUP01X07P1%W0RWCVRX%U0RY%T0RZ1F09R91E0;R;%?<5K0R<'61F0:R:'616:9/6<'9'41QZ6R[P2P7g00XgR\g00YGR]'G1P27=A\]dAO031CSR]b4b7b8X10X20102>/0110@>'1^10^20P2f:R@/2Of9R\O2b3b>b0b5b0b<b6b>101>R^127OR_'010_1/0>'1R_eP_P0107>R_128OR`'0Ra122H/8>Rb10N8Rc!wq$P012_HRd12`HRe'0/2H182>Rf/1cX90RgP0128HRh108>Ri/2H/02/!sn$!sH%P010_8Rj/2HPgPQPSP=PKPLPRPVPUPXPY169:Rg/6<Rk16:</69'9,4ZP[P!us31R9/0>R:10^2!uw,PPf7R^!ur$!up$10E>/1jRjePjP010c>Rj10TNRT,1b!t_$Pj11fTX90!t]7An0k</9g!tQ78:>/19!tG+^f8R:!tG-8j>/1ce12jH%3jRc15jHRT!t3/p-0Rf!t8'PZP01m0<g00R1RbPgC:,4ZPZ!}I+NElRE5MZ%k5RlP01E03RmPbPk!sO$CL!tn3W;1=?9/;71017/0>Rb#3[!t|%^;fP210:^/5>P^P:PPO4!u-'PcePFPJPAPM!v/0NPGO1RGPI!u#/Pgg00X@RgP<!tT$9MZEPlP0PkPgAK0;DR;!tl:X;f159>,;715bH!tf/f;Rf/0@,=?P@PfP\!ti$6!{-,PTeCf1;cTe9ejHE>10iNP2E@b=10dh/2HP_P8PH!u;8!u5'W!u5$!vx&19;m,4ZE`!tr,AA0H3R3g00Yg[P2!tO1%a3eR3CHE@PeP8POPHP01J2H,1OX90!tHEAb0;;R;/9;!yl011OORO!t;3POeC^CcE>12aHP_P`PHP3C!um$`7/0>!up'C1,CD1071'1e1dB7,\B1gB7E>W?XA0X@0o"). Qed.
  Lemma swrap32_of_u64_0 : ltac2:(zQ "b0!rb!h9!s1!s7!j0!p7!r0!sd!v0!va!hg5>1b$1>0@2$3@2$5@1$7@2$2+2+hf^1@2$6^1@2$2+2+hf@3$4$1@2$9@1$0#i0@2$a@1$0#k0@2$8@1$0#k0^2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##5/h06__sat1h14__x1h24__p1h37__arithh44__ffh5!sN%0h68__varmaph75__with82Hah91zh:2Hbh;1bp;1p;2p;3p;4p;6p;7p;8g000Nj10Tg0013j1?Tg003nj16Tg0053j2CTg00]Tj1]Tg008Qj21Tg007Nj24!s8$mj27Tg00^1j19Tg00eWj2DTg00f=j2BTg002Nj28Tg00_5j2>Tg00ITj35!s8$\j2VTg00`Dj3UTg00:Tj2STg00;5j2=Tg00@ij1RTg00Aij1PTg00BIj2OTg00Ccj1NTg00DAj1GTg00Gcj2F!s8$lj2<Tg00Onj3ETg00EOj42Tg00HFj2H!s/$hj2I!t^$nj3JTg00JMj4K!t^$hj3LTg00bKj2M!s/$nj6ATg00F:j1QTg00cRj4@Tg00h2j3TTg00LYj6\Tg00iAj1[Tg00[oj6ZTg00Nfj7W!t^$Jj7XTg00PQj8YTf1R0g00RXR1g00S7R2P2g00SWR3f0R4g00T7FWp=3f2R5P1P2P2P3P0P4FXp=:f3R6!s;+5P0P4GYp=;g00QSR7g00U>R8#0R9#?R:%68#6#6#6R;#?R<'CR=#]R>/14R?144=R@'7P7%09#0#0!s[$0#9RA1DA0'BRAg00Q5RB'8RC%99R9/>4=575X97P7180BRDA5745X971V:<RE14B:RF11B<14B=[RG[RH11B:RIg00gVRJAU:<0UW8R<11B=\J^8IRIP0g00Uc1SB:'=PFeO1RFPGg00VIRJ#RRK%PJRJ1O70RL%N7RM%G7RNP71F78R81<7B5E7ROg00TWP8C2'31HN3RPP4P5g00XgRQg00YGRR'=1I45=5QRdAJ7B0CKRRb4b6b7X17184B=574^17P4f5RQO1b3b0b5b0A57D0e1>9C11>DR914D=RDPEPHP<PIPFPGp-0RCPKPJPLPMPNP71<7:%9;5L7R;,M7R:g00R1R5P8C2,3NPN!x2+6EAR65:N%Q2R2P7P:P5PO!sK$C;PPP!to,W217?0P9[^17^2CP414Q=PQf4R=O3!ty'P9e!tf/!ta/P8g00X@R8P;!t,$9:N6P2P7POP!s9'!t@2X2C170@PD!tA,1>QPQP!t?/DeC@179De9T0BE\PA%[AEZW:W;o"). Qed.
  Lemma sx32_ssmall : ltac2:(zQ "b0!rb!s1!v0!s7!j0!h9!hkd!p7!r0!sd!hl5>1b$5>0@2$3@2$7@1$9@2$1+2+hf^1@2$8^1@2$1+2+hf@3$4@1$a@1$0#k0@1$6@2$2@1$0#k0^2@2$2@1$0#k0^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##3Qh04__p1h16__sat1h24__x1h32Hah47__arithh54__ffh6!sL%0h78__varmaph85__with92Hbh:1bh;1zp;1p;2p;3p;4p;6p;7p;8g000Nj10Tg0013j1=Tg003nj14Tg0053j2ATg00]Tj1[Tg008Qj21Tg007Nj22!s8$mj23Tg00^1j16Tg00ibj1BTg00eWj25Tg00ITj38Tg00;5j27Tg00f=j2ZTg00_5j2U!s/$\j2TTg00`Dj3OTg00:Tj2NTg00@ij1LTg00Aij1KTg00BIj2JTg00Ccj1HTg00DAj1E!s/$lj2D!sn$hj3FTg00bKj2CTg00Gcj2GTg00EOj4:!sA$nj6ITg00F:j1@Tg00HFj2M!s/$hj2?!u3$nj3PTg00JMj4QTg00cRj4>Tg00jEj2RTg00LYj6STg00kVj1YTg00Nfj7XTg00OJj7WTg00PQj8VTf1R0g00RXR1g00S7R2P2g00SWR3f0R4g00T7FXp=;f2R5P1P2P2P3P0P4FWp=9f3R6!s;+5P0P4GVp=<g00QSR7g00U>R8#0R9#=R:%48#4#4#4R;#=R<'AR=#[R>/14R?124=R@'3P7P0%09#0#0!s]$0#6RA#BRB15A415A538X;715A0RC,7B%691ZAC'U11>0RA120=R91T:<RDg00Q5RE/2:RF11E<12E=[RG[RH11E:RIg00gVRJAO:<0UW3R<11E=\J^3IRIP0g00Uc1NE:'7PFeO1RFPGp-0RJg00VIRK#LRL%KKRK1J70RM%H7RN%E7ROP71D7:%6;5F7R;,C7g00R11G78R8C:,;OR:PO!vQ+6EIR659O%@2R2P:C<1MO3R3P4P5g00XgR:g00YGR1'71?45=8:1dAP7E0CQREb5b7b8X27W013?0PA[^27^0JP4f5R?/2=P?f4R=O3b4b1b6b1PAePDPHP<PIPFPGPLPKPMPNPOP7P8g00X@P;!tr%;99O6P2P;C<P3P!t8,X0J130@P9!t9+11>?P?P!t4/9eC>13A9e,R0ES%YC=8BCeW9W:o"). Qed.
  (* [comment removed for export] *)
  Lemma signed_of_small : ltac2:(zQ "a0!rb!h9!s1!s7!j0!p7!r0!sd!v0!hla>1b$1>0@2$3@2$5@1$7@2$2+2+jf^1@2$6^1@2$2+2+jf@3$4$1@2$9@1$0#k0@2$8@1$0#k0^2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##3Lh04__p1h16__sat1h24__x1h32Hah47__arithh54__ffh6!sL%0h78__varmaph85__with92Hbh:1bh;1zp;1p;2p;3p;4p;6p;7p;8g000Nj11Tg0013j18Tg003nj14Tg0053j2ATg00]Tj1=Tg008Qj20Tg007Nj22!s8$mj23Tg00^1j1:Tg00_5j2BTg00ITj3;!s8$\j2?Tg00`Dj3>Tg00:Tj2[Tg00;5j2<Tg00@ij1VTg00Aij1UTg00BIj2TTg00Ccj1KTg00DAj1H!s/$lj2G!sw$hj3FTg00bKj2ETg00Gcj2DTg00EOj47!sA$nj6CTg00F:j1ITg00HFj2J!s/$hj2@!ty$nj3LTg00JMj4MTg00cRj4NTg00lVj1OTg00mDj3PTg00eWj2QTg00n1j2R!s/$Yj2STg00LYj6ZTg00Nfj7YTg00OJj7XTg00PQj8WTf1R0g00RXR1g00S7R2P2g00SWR3f0R4g00T7FYp=6f2R5P1P2P2P3P0P4FXp=9f3R6!s;+5P0P4GWp=5g00QSR7g00U>R8#1R9#8R:%48#4!s$%R;#8R<'AR=#=R>/04R?124=R@'3P7%19#1!s$&:R9/B0A;745X;710>0RA120=RB1?:<RCg00Q5RD/2:RE10D<12D=[RF[RG10D:RHg00gVRIA>:<0UW3R<10D=\I^3HRHP0g00Uc1[D:'<PEeO1REPFp-0RIg00VIRJ#VRK%UJRJ1T70RL%K7RM%H7RNP71G7:%:;5F7R;,E7g00R11D78R8C7,6NR:PN!v7+6ECR659N%I2R2P:C51JN3R3P4P5g00XgR:g00YGR1'<1@45=;:1dAL7D0CMRDb5b7b8X27W013?0PA[^27^0IP4f5R?/2=P?f4R=O3b4b1b6b1PAePCPGP<PHPEPFPKPJPLPMPNP7P8g00X@P;!tr%;99N6P2P;C5P3P!t8,X0I130@PB!t9+10>?P?P!t4/BeCN13ABe%O9RB#=/00120B'3e9P901Q90,R91S90EZW9W:o"). Qed.
  Lemma swrap32_mul_u64 : ltac2:(zQ "c0!r5!rb!h9!s1!s7!j0!p7!r0!sd!v0!va!hg5>1b$2>1k$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0@2$b@1$1#k0@2$9@1$1#k0^3^2@2$0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##=ch06__sat1h1!s/%3h24__x1h34__x2h47__arithh54__ffh6!sN%0h78__varmaph85__with91zh:2Hah;4__p1h<!sR%2h=3Hbkh>1bh?1kp;1p;2p;3p;4p;6p;7p;8g000Nj17Tg0013j1ATg003nj1<Tg0053j2LTg00]Tj1nTg006Jj21Tg008Qj2=Tg007Nj23!s8$mj2;Tg00^1j1@!s/$Oj2TTg00_5j2B!t1$Qj20Tg002Nj24Tg00aKj28!sJ$\j2ITg00`Dj3GTg00:Tj2_Tg00;5j2NTg00@ij1\Tg00Aij1[Tg00BIj2Z!s/$gj1YTg00CEj4X!s/$cj1WTg00DAj1VTg00Gcj2E!s/$@j3D!sA$lj2J!tC$hj3CTg00Onj3S!tg$hj3RTg00HFj2Q!s/$hj2PTg00ITj3?!s/$nj3UTg00JMj4mTg00bKj2lTg00EOj49!s8$nj6kTg00F:j1jTg00cRj4f!s/$mj3eTg00LYj6:!sJ$\j6b!w-$1j1aTg00dPj4HTg00[oj6MTg00oFj4F!s8$5j4`Tg00e1j4c!s/$Wj2dTg00f=j2^!s/$gj2gTg00Nfj7h!uW$Jj7]Tg00PQj8iTg00QSR0f1R1f0R23?p=2g00Q5R3/=2p=5P0P1g00TWP2C9p=>!s4$RXR4g00S7R5P5g00SWR6P2g00T7Fhp=6f2R7P4P5P5P6P1P2F]p=Of3R8!s;+7P1P2Gip=Kg00U>R9#7R:#AR;%<9#<#<#<R<#AR='LR>#nR?1112R@'=13@>';P0%7:#7#7#7R@#7#@RA/T7RB%@@RC1127RD'B1187R8'2X90P0%A@R@,L;RE/1ERF,07RG/11RH/0ERI10>ERJ'4/0E182>/28X90RKP010GERL/11/0E142J/0E/8!sF'MP0107ERN10DE/4!sC0P01171R8/0ERDPMP0148>RM/0EROPKP0PMPK1I;=RK133;RP%5=133>[RQ[RR%5;RSg00gVRTAG;=1UW:R=%5>\T^:SRU!wJ$Uc1_3;'NPPeRVO1RWPQg00VIRX#\RY%[XRXP01Z07P1%Y0RZCXR[%W0R\%V0R]1E091E0:5D0R:1J0;R9%@<5C0R<5S0R^=R0</>:'61Q]6R_P2P7g00XgR`g00YGRa'N1P27=?`adAU031CmRab5b7b8X20X301121R`/4>!v1$`^20^30P2f5Rbf6RcO2b4b0b6b018M>/28ePO%5MRO13MERdPKPRP=PUPWPQp-0RePYPXP[P\P]P01l0<g00R1RfP:C9,6]P]!yo'f4RgEkRh5O]%j5RiP01J03RjPfP^!sQ$CKP_P!tx0W;1=?`/;71117/4>Rf#5[!t~%^;eP211cb/3>PbPcPgO4!u-'POe1I;@Rc%5@133E[Rb\PRPAG;@1VTX:SR@%5E!wx%S!uF/PgPVO1RVPb!uK/P:g00X@R:P<!tv$9O]hPiP0P^P:AC09CR9!u6:X;e13`>,;713fE!u0/f9Ref8Rf'1,=?PfPef7!u6$1!u8%b<b1PdeCf1;Ode9eMEE:14DJ/0EP8P>PEPcPPP@P!u41!u-'Z!u-$!w=&1>9j,6]Eb!tk,A?0E3R3g00Yg[P2!tE1%a3eR3CHEM11N1/0E!~o$EP3CFE:PLP7PFPEP0112E,2FX90!t[EAD099R9/>!y#$!tU+12FFRF!tN3PFeC`CcE:PIPG!tH+M14H>/0EPH!ut$3CHE:11B1,BC/28e1dA7,^A1gA7E:W=X?0X>0o"). Qed.
  (* [comment removed for export] *)
  Lemma mod64_of_small_nonneg : ltac2:(zQ "70!h9!s7!j0!p7!r0!q2!s1>1x$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+hggggggggggggggg0^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##2Sh04__p1h16__sat1h24__x1h32Hah47__arithh54__ffh6!sL%0h78__varmaph85__with92Hxh:1xp;1p;2p;3p;4p;6p;7p;8g000Nj10Tg0013j15Tg0053j2VTg007Nj23Tg008mj24Tg00_\j2@Tg00`Dj3>Tg00:Tj2=Tg00;5j2;Tg00@ij1UTg00Aij1TTg00BIj2STg00Ccj1GTg00DAj1F!s/$lj26Tg00Gcj2DTg00EOj47Tg00bnj6BTg00F:j1ETg00HFj2A!s/$hj2HTg00ITj3I!s/$nj3JTg00JMj4KTg00^1j1L!ty$hj3MTg00cRj4N!s/$mj3O!uN$Qj2PTg00Nfj7QTg00OJj7<Tg00PQj8RTg00Q5R0f0R1'Pp=2%01#0#0#0p=?!s2$p=C!s:+!s$'p=1f1R2g00RXR3g00S7R4P4g00SWR5P1g00T7FQp=8f2R6P3P4P4P5P2P1F<p=9f3R7!s;+6P2P1GRp=:g00QSR8%21R9g00U>R:#0R;#5R<%0;#?!s1$='VR>,31R?'4%C;#1!s$05R@%22RA132@RB1@<=RC130<RD%2=130>[RE[RF%2<RGg00gVRHA><=2UW3R=%2>\H^3GRGP2g00Uc1=0<';PDeO1RDPEp-0RHg00VIRI#URJ%TIRI1S82RK%G8RL%F8RMP81680g00R11D8:R:C7,8MRNPM!uh+7EBR759M%E4R4PNC:1AM5R5P1P6g00XgRNg00YGR3';1H16=IN3dAJ802CKR0b5b7b8X28W01492PA[^28^0HP1f5R9/3>P9f4R>O3b4b1b6b1PAePCPFP=PGPDPEPJPIPKPLPMP8P:g00X@RL168<%L;5M8!t|$99M7P4P8P:PL168@!s;$C:P5P!tM,X0H142?PB!tN+%29P9P!tH/BeCN14ABe5O2W9W:o"). Qed.
  Lemma mod64_of_small_neg : ltac2:(zQ "90!h9!s1!s7!j0!p1!p7!r0!q2!sd>1x$0>0@2$2@2$5@1$8@2$1+2+k0^1@2$6^1Z@3$3$0@2$7^2+hggggggggggggggg0@2$4^2@2$1+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##6zh06__sat1h14__x1h27__arithh34__ffh44__p1h5!sN%0h68__varmaph75__with82Hah92Hxh:1xh;1zp;1p;2p;3p;4p;6p;7p;8g000Nj10Tg0013j1:Tg0053j2CTg00]Tj1bTg008Qj23Tg007Nj26!s8$mj28Tg006Jj2BTg002Nj25!sn$Qj2<Tg00ITj37Tg00_\j2]Tg00`Dj3VTg00:Tj2UTg00;5j2;Tg00@ij1STg00Aij1RTg00BIj2QTg00Ccj1NTg00DAj1ITg00Gcj2H!s8$lj29!s8$@j3FTg00Onj3=Tg00^1j1G!tC$hj3DTg00EOj44Tg00HFj2K!s/$hj2L!ty$nj3MTg00JMj4ATg00bKj2O!s/$nj6PTg00F:j1@Tg00cRj4a!s/$mj3`Tg00LYj6_!u&$gj1\!sS$\j6W!v>$1j1XTg00ooj4YTg00[oj6ZTg00Nfj7[!u&$Jj7TTg00PQj8^Tf0R0#!s$&p=J%0!s-$E!s-$!s$/p=1f1R1g00RXR2g00S7R3P3g00SWR4P0g00T7F[p=2f2R5P2P3P3P4P1P0FTp=>f3R6!s;+5P1P0G^p=?g00QSR7g00U>R8#0R9#:R:%09#J!s1$;'CR<#bR=/30R>g00Q5R?,60R@'8P7%:8RA%E9#1!s$0:RB'BRC,51RD/<BRE155<9770X;7RFP7PDPF1]:;RF16?:RG13?;16?<[RH[RI13?:RJg00gVRKAV:;1UW8R;13?<\K^8JRJP1g00Uc1U?:';PGeO1RGPHg00VIRK#SRL%RKRK1Q71RM%N7RN%I7ROP71H78R8197A197BRP5F75=7RQg00TWRR197:%G95D7R99=78C4'21KO4R:P0P5g00XgRSg00YGRT';1L05=7STdAM7?1CARTb3b6b7X17150C150<577^17P0f5RCO1b2b0b5b0151<977DePE13?DRE16DBR<PFPIP;PJPGPHp-0RSPLPKPMPNPOP71O79g00R1R9P8C4,2OPO!x<+6EPR65>O%@3R5P7197?RUP9PQ!sO$C?P:P!tj,W418>1PE[^17^4SP016C?PCf4R>O3!tq'PEe!t]/!tX/P8g00X@R8PU!t,$9>O6P5P7PQP8PP!t@7X4S181@P<!tA,3=CPCP!t?/<eCa18E<e9`DBE_1<1BP1PAPB!tV3%\7!tW$!us'7PPPR!tZ&EW!tG,A77B?RBg00Yg[P0!t7'%XBeCYEZW9W:o"). Qed.
  Lemma mod64_le_iff : ltac2:(zQ "80!p7!s7!s1!h9!r0!hm6!q2!sd>1x$3>1c$3>0@2$1@2$0@1$7@2$2+2+jf^2@2$4^2@2$2+2+jf>0@2$1@2$0Z^2@2$4^2@2$2+2+jf@2$5@2$0@2$6^4+hggggggggggggggg0^3@2$1@2$0Z^4@2$0^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##?=h06__sat1h14__x1h27__arithh34__ffh44__p1h5!sN%0h6!s/%3h78__varmaph85__with92Hah:4__x2h;!sN%2h<1Hh=4__p2h>2Hch?2Hxh@1chA1ohB1xhC1zp;1p;2p;3p;4p;6p;7p;8g000Nj10Tg0013j1=Tg003nj1;Tg0053j2CTg00]Tj1STg008Qj21Tg007Nj24!s8$mj23Tg010Pj2\Tg0115R0j2V!sy$Qj2E!s:$Oj29Tg002Nj2KTg00_\j2JTg00`Dj3MTg00:Tj2`Tg00;5j2G!s/$Oj1ATg00=Vj2@Tg00N=j3FTg00>?j2_Tg00@ij1^Tg00AIj3]!s/$ij1[Tg00BIj2D!s/$gj1ZTg00CEj4Y!s/$cj1XTg00DAj1WTg00Gcj2B!s8$lj2OTg00F:j1TTg00^1j1R!ty$hj3QTg00bKj2PTg00Onj3mTg00HFj2l!s/$hj2hTg00ITj3g!s/$nj3fTg00JMj4eTg00cRj4H!v5$hj2dTg00LYj6ITg013;j2cTg00EOj4L!ui$fj7b!tC$nj6a!tC$Jj7iTg014Qj7jTg00PQj8kTg00Q5R1f0R2'1p=21421p=8%02#0#0#0p=U!s2$p=n!s:+!s$'p=7g00QSR3f1R4g00X@P2CLp=>P4g00RXR5g00S7R6P6g00SWR7P2g00T7Fbp=5P4P5P6P6P7P2Eap=?f2R8!s9+4P2Fip=:P3!ss%1!t%%<P!sI1jp=Nf3R9!s;+8P4P2Gkp=6g00U>R5#0R:#=R;%;5#;!s$%R<#=R='CR>#SR?/14144>R@'3%24RA/3@1\91%89%29R@'VP0f4R0#8%20f5RB%0:#URC#n#7!s$0=RD'E/10%2BRE11B0'3'9P2%8BP3f6RF%=CRG,C;RH'KRI112Ff7RJ#211JF'3'9XC3RK1J;=RL141;RM%2=141>[RN[RO%2;RPg00gVRQAM;=4UW9R=%2>\Q^9PRR1J;GRS%2G141H[RT\MRUAM;G4VQX9PRG%2H!sP%P!vn$Uc1`1;'GPMeRMO1RQPTP0PMO1RMPNp-0RVg00VIRWg00W5#ARX#ARY#A,@31@3Y1@3X5F35F3g00WT'_%^WRX3]%[WRWP31D38P4%Z3CYRY%X3RZ%W3R[1B35R51O31R\'>,5[R]%T6R6P[1?[01B3:R:1O3;R;%R<5Q3R<!sL$5:[P6P[1P3</<5,5[R^1?[B!s=$%RC9Q3;R;9m35/<:,5[1<\!sK$\1<5:,5[R:5:[RC5N[C6C6C61l[7R7P2P8g00XgR_g00YGR`'G1h28=g_`dAf314CeR1b3b7b8X13X:3X4VW=%82R`148>,3911?8/3B1K9H/101190,3@'9[[[^13^:3^4V^=VP2f=R@/4>R_f<Ra#2PaP@PJf:RJf;RaO7b2b6b0b5b0b;b611IB%2FRI11FBRB'3Rb'9e1EFDRD%SHRc/1FRd%8FRePLPOP=PRPSPUPGPPPQPTPMPNPXPW1D34RfPZ!vy$9R99:[^P61P3;!va%C6P7P!uU-4V11?2/3411c4!u6$4VP2P_P@PaO3!tq1Pd!tI,Q!t=%P!t9$P]P6P]!t%2%84\`^13P2PJP0O2R`b2!sr%PeeCH13dee,dFEIW<P2O1P3PFPK!t-4Y!t-$\P6AN[:C!u43:3%22RC1148R813A8'9!wJ&P2f9!tF$3!tD'19BbePDPI14FHRD!u@:\P6P\!t52PA\C^13P!u7,I!wJ@!sq%1>5<,5[9:[9P61>5;!wD942>,34144H!wD+11?@!wF8D!vV$IDe,cFEIX<EP2O1n20010!s#$211000!s'$bAW>W?X@3XB3o"). Qed.
  Lemma mod64_lt_iff : ltac2:(zQ "80!r0!s7!p7!s1!h9!hm6!q2!sd>1x$4>1c$4>0@2$1@2$2@1$7@2$3+2+jf^2@2$0^2@2$3+2+jf>0@2$1@2$2Z^2@2$0^2@2$3+2+jf@2$5@2$0@2$6^4+hggggggggggggggg0^3@2$1@2$2Z^4@2$0^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##?=h06__sat1h14__x1h27__arithh34__ffh44__p1h5!sN%0h6!s/%3h78__varmaph85__with92Hah:4__x2h;!sN%2h<1Hh=4__p2h>2Hch?2Hxh@1chA1ohB1xhC1zp;1p;2p;3p;4p;6p;7p;8g000Nj11Tg0013j1=Tg003nj1<Tg0053j2CTg00]Tj1STg008Qj26Tg007Nj20!s8$mj23Tg010Pj2\Tg0115R0j2V!sy$Qj2E!s:$Oj29Tg002Nj2KTg00_\j2JTg00`Dj3MTg00:Tj2`Tg00;5j2G!s/$Oj1@Tg00=Vj2?Tg00N=j3FTg00>?j2_Tg00@ij1^Tg00AIj3]!s/$ij1[Tg00BIj2D!s/$gj1ZTg00CEj4Y!s/$cj1XTg00DAj1WTg00Gcj2B!s8$lj2OTg00F:j1TTg00^1j1R!ty$hj3QTg00bKj2PTg00Onj3mTg00HFj2l!s/$hj2hTg00ITj3g!s/$nj3fTg00JMj4eTg00cRj4H!v5$hj2dTg00LYj6ITg013;j2cTg00EOj4L!ui$fj7b!tC$nj6a!tC$Jj7iTg014Qj7jTg00PQj8kTg00Q5R1f0R2'6p=21021p=8%12#1#1#1p=U!s2$p=n!s:+!s$'p=7g00QSR3f1R4g00X@P2CLp=:P4g00RXR5g00S7R6P6g00SWR7P2g00T7Fbp=4P4P5P6P6P7P2Eap=>f2R8!s9+4P2Fip=;P3!ss%1!t%%AP!sI1jp=Nf3R9!s;+8P4P2Gkp=5g00U>R5#1R:#=R;%<5#<!s$%R<#=R='CR>#SR?/64104>R@'3%24RA/3@1\91%89%29R@'VP0f4R0#8%20f5RB%1:#URC#n#7!s$0=RD'E/00%2BRE10B0'3'9P2%8BP3f6RF%=CRG,C;RH'KRI102Ff7RJ#210JF'3'9XC3RK1J;=RL101;RM%2=101>[RN[RO%2;RPg00gVRQAM;=4UW9R=%2>\Q^9PRR1J;GRS%2G101H[RT\MRUAM;G4VQX9PRG%2H!sP%P!vn$Uc1`1;'GPMeRMO1RQPTP0PMO1RMPNp-0RVg00VIRWg00W5#@RX#@RY#@,?31?3Y1?3X5F35F3g00WT'_%^WRX3]%[WRWP31D38P4%Z3CYRY%X3RZ%W3R[1B35R51O31R\':,4[R]%T6R6P[1>[01B3:R:1O3;R;%R<5Q3R<!sL$5;[P6P[1P3</A5,4[R^1>[B!s=$%RC9Q3;R;9m35/::,4[1A\!sK$\1:5!t3$:5;[RC5N[C5C5C51l[7R7P2P8g00XgR_g00YGR`'G1h28=g_`dAf314CeR1b3b7b8X13X:3X4VW=%82R`108>,3916?8/3B1K9H/001090,3@'9[[[^13^:3^4V^=VP2f=R@/0>R_f<Ra#2PaP@PJf:RJf;RaO7b2b6b0b5b0b;b610IB%2FRI10FBRB'3Rb'9e1EFDRD%SHRc/6FRd%8FRePLPOP=PRPSPUPGPPPQPTPMPNPXPW1D34RfPZ!vy$9R99;[^P61P3;!va%C5P7P!uU-4V16?2/3416c4!u6$4VP2P_P@PaO3!tq1Pd!tI,Q!t=%P!t9$P]P6P]!t%2%84\`^13P2PJP0O2R`b2!sr%PeeCH13dee,dFEIW<P2O1P3PFPK!t-4Y!t-$\P6AN[:C!u43:3%22RC1048R813A8'9!wJ&P2f9!tF$3!tD'19BbePDPI10FHRD!u@:\P6P\!t52PA\C^13P!u7,I!wJ@!sq%1:5<,4[9;[9P61:5;!wD902>,34104H!wD+16?@!wF8D!vV$IDe,cFEIX<EP2O1n20010!s#$211000!s'$bAW>W?X@3XB3o"). Qed.
  Lemma mod64_ge_iff : ltac2:(zQ "90!p7!r0!s1!s7!h9!hm6!hmc!q2!sd>1x$4>1c$4>0@2$3@2$0@1$8@2$2+2+jf^2@2$1^2@2$2+2+jf>0@2$3@2$0Z^2@2$1^2@2$2+2+jf@2$5@2$0^3@2$7^4+hggggggggggggggg0@2$6@2$1^4Z@2$0^3^4").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##?[h06__sat1h14__x1h27__arithh34__ffh44__p1h5!sN%0h6!s/%3h78__varmaph85__with92Hah:4__x2h;!sN%2h<1Hh=4__p2h>2Hch?2Hxh@1chA1ohB1xhC1zp;1p;2p;3p;4p;7p;6p;8g000Nj11Tg0013j1>Tg003nj1<Tg0053j2DTg00]Tj1TTg008Qj20Tg007Nj24!s8$mj26Tg010Pj2\Tg0115R0j2;!sy$Qj2P!s:$Oj2:Tg002Nj2LTg00_\j2JTg00`Dj3NTg00:Tj2`Tg00;5j2H!s/$Oj1BTg00=Vj2ATg00N=j3GTg00>?j2_Tg00@ij1^Tg00AIj3]!s/$ij1[Tg00BIj2E!s/$gj1ZTg00CEj4Y!s/$cj1XTg00DAj1WTg00Gcj2C!s8$lj2OTg00F:j1UTg00^1j1S!ty$hj3RTg00bKj2QTg00Onj3nTg0155j7mTg00HFj2i!s/$hj2hTg00ITj3g!s/$nj3fTg00JMj4eTg00cRj4K!v>$hj2cTg00LYj6ITg013;j2dTg00EOj4M!ur$fj7b!tL$nj6a!tL$Jj7jTg014Qj7kTg00PQj8lTg00Q5R1f0R2'0p=21421p=5%12#1#1#1p=V!s2$p=o!s:+!s$'p=8g00QSR3f1R4g00X@P2CMp=?P4g00RXR5g00S7R6P6g00SWR7P2g00T7Fbp=3P4P5P6P6P7P2Eap=@f2R8!s9+4P2Fjp==P3!ss%1!t%%9P!sI1kp=Ff3R9!s;+8P4P2Glp=7g00U>R:#1R;#>R<%<:#<!s$%R=#>R>'DR?#TR@/04144?RA'6%24RB/6A1\91%59%29';P0f4R0#5RC%20f5RD%1;#VRE#o#8!s$0>RF'P,00%5DRG100D';':P2P3f6RH%>ERI,D<RJ'LRK10H2f7RL#510HL';':XC3RM1J<>RN141<RO%2>141?[RP[RQ%2<RRg00gVRSAN<>4UW9R>%2?\S^9RRT1J<IRU%2I141J[RV\ORWAN<I4VSX9RRI%2J!sP%R!vk$Uc1`1<'HPOeROO1RSPVP0POO1ROPPp-0RXg00VIRYg00W5RZ#B#BR[#B,A31A3[1A3Z5G35G3g00WT'_%^YRZ3]%[YRYP31E38P4%Z3CYR[%X3R\%W3R]1C3;R;1O31R^'?,3]R_%U6R`P]1@]01C3:R:1O3<R<%S=5R3R=!sL%a5=]P`P]1Q3=R=/9;,3]1@]D!s=$%SE9R3<R<9n3;,9:,3]P]!xz+_19:;!t8$FmR65F]C7C7C71i]7R7P2P8g00Xg!zd$YGRE'H1h28=g5EdAf314CeR1b3b7b8X13X:3X4XW=%54RE169A10@9/6D1L0J,091090,;C':[[[^13^:3^4X^=XP2f=RC/4?RAf<R5#2PCP5PLf:RLf;R5O7b2b6b0b5b0b;b610DK%5HRK10DHRb';Rc':e1PHFRF%TJRd/0HRePKPNPQP>PTPUPWPIPRPSPVPOPPPZPY1E34RfP\P]19=:!vL%9R9!vN$1Q3</!vE$C7P7P!uU-4X10@2/6410d4!u9$4XP2PAPCP5O3!tt1Pee!tO+S!tC%P!t?%?:^,3]RAP`PA!t02%52PE[^13P2PLP0O2REb2!sz%PKeCK16eKe,cHEIX<GP2O1%2DP3PHPM!t:4[!uS%^;,3]P`AF]_6!uE3:31048R6%58/;6':\B!w\%P2PLf9P0!uI$!tK$1:bcePF%2HRF14HJRc!uR:9^:,3]R^P`P^!uR322PB!uR$!uJ,Fe!wk?!sz%A=]9aP`1?:<!wY942?,64144J!wY+10@C!w[8c!vc$Fce,dHEIW<P2O1n20010!s#$211000!s'$bAW>W?X@3XB3o"). Qed.
  Lemma mod64_gt_iff : ltac2:(zQ "90!r0!s1!s7!h9!p7!hm6!hmc!q2!sd>1x$3>1c$3>0@2$2@2$4@1$8@2$1+2+jf^2@2$0^2@2$1+2+jf>0@2$2@2$4Z^2@2$0^2@2$1+2+jf@2$5@2$0^3@2$7^4+hggggggggggggggg0@2$6@2$0^4Z@2$0^3^4").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##?[h06__sat1h14__x1h27__arithh34__ffh44__p1h5!sN%0h6!s/%3h78__varmaph85__with92Hah:4__x2h;!sN%2h<1Hh=4__p2h>2Hch?2Hxh@1chA1ohB1xhC1zp;1p;2p;3p;4p;7p;6p;8g000Nj11Tg0013j1?Tg003nj1<Tg0053j2DTg00]Tj1TTg008Qj27Tg007Nj20!s8$mj25Tg010Pj2\Tg0115R0j29!sy$Qj2P!s:$Oj2:Tg002Nj2LTg00_\j2JTg00`Dj3NTg00:Tj2`Tg00;5j2H!s/$Oj1BTg00=Vj2ATg00N=j3GTg00>?j2_Tg00@ij1^Tg00AIj3]!s/$ij1[Tg00BIj2E!s/$gj1ZTg00CEj4Y!s/$cj1XTg00DAj1WTg00Gcj2C!s8$lj2OTg00F:j1UTg00^1j1S!ty$hj3RTg00bKj2QTg00Onj3nTg0155j7mTg00HFj2i!s/$hj2hTg00ITj3g!s/$nj3fTg00JMj4eTg00cRj4K!v>$hj2cTg00LYj6ITg013;j2dTg00EOj4M!ur$fj7b!tL$nj6a!tL$Jj7jTg014Qj7kTg00PQj8lTg00Q5R1f0R2'7p=21021p=4%12#1#1#1p=V!s2$p=o!s:+!s$'p=8g00QSR3f1R4g00X@P2CMp=;P4g00RXR5g00S7R6P6g00SWR7P2g00T7Fbp=3P4P5P6P6P7P2Eap=@f2R8!s9+4P2Fjp=>P3!ss%1!t%%=P!sI1kp=Ff3R9!s;+8P4P2Glp=6g00U>R:#1R;#?R<%<:#<!s$%R=#?R>'DR?#TR@/74104?RA'5%24RB/5A1\91%49%29'9P0f4R0#4RC%20f5RD%1;#VRE#o#8!s$0?RF'P,00%4DRG100D'9':P2P3f6RH%?ERI,D<RJ'LRK10H2f7RL#410HL'9':XC3RM1J<>RN101<RO%2>101?[RP[RQ%2<RRg00gVRSAN<>4UW9R>%2?\S^9RRT1J<IRU%2I101J[RV\ORWAN<I4VSX9RRI%2J!sP%R!vk$Uc1`1<'HPOeROO1RSPVP0POO1ROPPp-0RXg00VIRYg00W5RZ#B#BR[#B,A31A3[1A3Z5G35G3g00WT'_%^YRZ3]%[YRYP31E38P4%Z3CYR[%X3R\%W3R]1C3;R;1O31R^';,3]R_%U6R`P]1@]01C3:R:1O3<R<%S=5R3R=!sL%a5>]P`P]1Q3=R=/=;,3]1@]D!s=$%SE9R3<R<9n3;,;:,3]P]!xz+_1;:!t8%FmR65F]C6C6C61i]7R7P2P8g00Xg!zd$YGRE'H1h28=g5EdAf314CeR1b3b7b8X13X:3X4XW=%44RE159A17@9/5D1L0J,091090,9C':[[[^13^:3^4X^=XP2f=RC/0?RAf<R5#2PCP5PLf:RLf;R5O7b2b6b0b5b0b;b610DK%4HRK10DHRb'9Rc':e1PHFRF%TJRd/7HRePKPNPQP>PTPUPWPIPRPSPVPOPPPZPY1E34RfP\P]1==:!vL%9R9!vN$1Q3</!s;$C6P7P!uU-4X17@2/5417d4!u9$4XP2PAPCP5O3!tt1Pee!tO+S!tC%P!t?%;:^,3]RAP`PA!t02%42PE[^13P2PLP0O2REb2!sz%PKeCK15eKe,cHEIX<GP2O1%2DP3PHPM!t:4[!uS%^;,3]P`AF]_6!uE3:31048R6%48/96':\B!w\%P2PLf9P0!uI$!tK$1:bcePF%2HRF10HJRc!uR:=^:,3]R^P`P^!uR322PB!uR$!uJ,Fe!wk?!sz%A>]9aP`1;:<!wY902?,54104J!wY+17@C!w[8c!vc$Fce,dHEIW<P2O1n20010!s#$211000!s'$bAW>W?X@3XB3o"). Qed.
  (* [comment removed for export] *)
  Lemma mod64_geh_iff : ltac2:(zQ "90!s1!p7!s7!r0!h9!hm6!q2!sd!hn1>1x$4>1c$4>0@2$2@2$1@1$7@2$0+2+jf^2@2$3^2@2$0+2+jf>0@2$2@2$1@2$0+2+jf^2@2$3^2@2$0+2+k0@2$5@2$1^3@2$6^4+hggggggggggggggg0@2$2@2$1@2$8^3@2$0+2+k0^4@2$3^4Z").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##@Uh06__sat1h1!s/%3h24__x1h37__arithh44__ffh54__p1h6!sN%0h7!s/%2h88__varmaph95__with:2Hah;4__x2h<1Hh=4__p2h>2Hch?2Hxh@1chA1ohB1xhC1zp;1p;2p;3p;4p;6p;7p;8g000Nj11Tg0013j1?Tg003nj1<Tg0053j2CTg00]Tj1UTg008Qj20Tg007Nj23!s8$mj22Tg010Pj2\Tg0115R0j2X!sy$Qj2RTg00aKj2:!sC$Oj29Tg002Nj2NTg00_\j2JTg00`Dj3STg00:Tj2bTg00;5j2HTg00@ij1aTg00Aij1`Tg00BIj2G!s/$gj1^Tg00CEj4]!s/$cj1[Tg00DAj1ZTg00Gcj2K!s8$lj2DTg00F:j1YTg00^1j1P!tL$hj3QTg00Onj3W!u&$hj3VTg00HFj2o!s/$hj2nTg00ITj3m!s/$nj3iTg00JMj4hTg00bKj2ITg00cRj4O!ui$hj2gTg00LYj6M!uN$Oj1ATg00=Vj2BTg00N=j3LTg00>?j2f!u`$Ij3eTg013;j2dTg00EOj4E!sS$fj7F!ty$Jj7cTg014Qj7jTg00PQj8k!tU$nj6lTf0R1#!s$&p=_g00Q5R2,31p=51021p=4%1!sB$p!s-$!s$/p=8g00QSR3f1R4g00X@P1CEp=;P4g00RXR5g00S7R6P6g00SWR7P1g00T7R8FFp==f2R9P5P6P6P7P3!s[%1P1CEP!sF$7P!sD,4P1Fcp=>!s92jp=Tf3R8!s;+9P4P1Gkp=6P4!s;+1Elp=@g00U>R5#1R:#?R;%<5#<!s$%R<#?R='CR>#UR?/04134>'210>4R@%1:#_RA#?RB,C;RC,34RD'21\82%58%48'XP0f4R0#5RE%40f5RF%pA#8!s$0?RG'R,001:0C/0F%5FRH'2'9P1P3f6RI/NCRJ10I11:ICf7RK'0%5K'2'9XC3RL1J;=RM132;RN%4=132>[RO[RP%4;RQg00gVRRAS;=4UW:R=%4>\R^:QRS1J;BRT%4B132C[RU\NRVAS;B4VRX:QRB%4C!sP%Q!wE$Uc1b2;'HPNeRNO1RRPUP0PNO1RNPOg00VIRW#aRX%`WRYP31G39P4%^3C]RZ%[3R[%Z3R\1K3:R:1D32R]';,=\R^%Y6R61K35R51D3;R;%PA5Q3RA9W3:57\AV35A=7\:=>\^R^5T\C61o\7R7P1P9g00XgR_g00YGR`'H1n19=m_`dAi324ChR2b4b8b9X23X;3%54R`1N9C,041:4C/09%59'2'9[^23^;3P1f=R9f<R_PKO3b3b1b0b6b0b7b110FJ1:FC/0I%5IRJ'2Ra'9e1RIGRG%UCRb/0IRcPJPMPPP=PSPTPVPBPQPRPUPNPOp-0RdPXPY1G34ReP[P\%P<9Q3;R;,I3=7\51@\8R<5>\P61I3A=7\5C6P7P!u<,W510?1/2410b4!u+$5dP1139>P9f;Rb!u+3Pce!t^;PXPYP!tU$1;5],=\RfP6Pf!t?2%51P`[^23P1P9PKO2R`!t02JeCO12cJe,gIEMX<HP1O1%4FP3PIPL!tL;g00W5#ARL#ARH#A,B31B3H1B3L5L35L3g00WT'f=eWXPYPZP[P\A7\]:P6!s/$;51@\0!vH$P\1@\F1;:;,=\!s8$A7\5:=T\^C6C6!uF2X;3X5dX=d%44R^12@8138>,2F10801:8C/00/2E'9[[!y'&^5d^=dP110?9R?13_CP9P_PKf:PbO7!y;4I/9aePG%4IRG13ICRC!wGEA7\]5R]P6P]!wE341P^!wE$!w=3G!xGI;,=\9>\<P61;5A,=\!v-35d131>,24PD!yf+P?P9P!yb5C!xX$GCe,dIEMW<P1O1n20010!s#$211000!s'$bAW>W?X@3XB3o"). Qed.
  Lemma mod64_lth_iff : ltac2:(zQ "a0!s1!r0!p7!s7!h9!hm6!hmc!q2!sd!hn1>1x$4>1c$4>0@2$3@2$2@1$8@2$0+2+jf^2@2$1^2@2$0+2+jf>0@2$3@2$2@2$0+2+jf^2@2$1^2@2$0+2+k0@2$5@2$1@2$7^4+hggggggggggggggg0^3@2$6@2$2Z^4@2$1^4@2$9^3@2$0+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##@Wh06__sat1h1!s/%3h24__x1h37__arithh44__ffh54__p1h6!sN%0h7!s/%2h88__varmaph95__with:2Hah;4__x2h<1Hh=4__p2h>2Hch?2Hxh@1chA1ohB1xhC1zp;1p;2p;3p;4p;7p;6p;8g000Nj11Tg0013j1@Tg003nj1<Tg0053j2DTg00]Tj1UTg008Qj26Tg007Nj20!s8$mj25Tg010Pj2[Tg0115R0j2;!sy$Qj2QTg00aKj2?!sC$Oj28Tg002Nj2STg00_\j2HTg00`Dj3RTg00:Tj2aTg00;5j2JTg00@ij1`Tg00Aij1_Tg00BIj2I!s/$gj1]Tg00CEj4\!s/$cj1ZTg00DAj1YTg00Gcj2K!s8$lj2ETg00F:j1XTg00^1j1O!tL$hj3PTg00Onj3W!u&$hj3VTg0155j7pTg00HFj2o!s/$hj2nTg00ITj3m!s/$nj3hTg00JMj4gTg00bKj2GTg00cRj4N!ur$hj2fTg00LYj6M!uW$Oj1BTg00=Vj2ATg00N=j3LTg00>?j2e!ui$Ij3dTg013;j2cTg00EOj4F!sS$fj7bTg014Qj7iTg00PQj8j!tL$nj6k!uE$Jj7lTf0R1#!s$&p=^g00Q5R2,01p=91621p=2%1!sB$q!s-$!s$/p=7g00QSR3f1R4g00X@P1CFp=:P4g00RXR5g00S7R6P6g00SWR7P1g00T7Fbp=3P3!sM%1!s[%=f2R8P5P6P6P7P4P1Fip=Tf3R9!s;+8P4P1Gjp=4P4!s;+1Ekp=CP!sa1lp=>g00U>R:#1R;#@R<%<:#<!s$%R=#@R>'DR?#UR@/64104?'516?4%1;#^RA#@RB,D<RC,04RD'51[92%99%29RE';P0f4R0#9%20f5RF%qA#7!s$0@RG'Q/00%2FRH1?0CRI,0F';'8P1%9FP3f6RJ/SCRK101Jf7RL#21?JC,0L';'8XC3RM1H<>RN102<RO%2>102?[RP[RQ%2<RRg00gVRSAR<>4UW:R>%2?\S^:RRT1H<BRU%2B102C[RV\ORWAR<B4VSX:RRB%2C!sP%R!wF$Uc1a2<'JPOeROO1RSPVP0POO1ROPPg00VIRX#`RY%_XRZP31I38P4%]3C\R[%Z3R\%Y3R]1K3:R:1E32R^':,3]R_%X6R`1E3<R<%OA5P3RA9W3:1K3;R;!sJ$P]!w{'1=^!s[$^AV3;A,::,3]FpR65T]C41o]7R7P1P8g00Xg!yl$YGRa'J1n18=m5adAh324CgR2b4b8b9X23X;3%91Ra1S4C/08%24R51?8C,04';'8[^23^;3P1f<Rbf=RcPLO3b3b1b0b6b0b7b110KF%2JRK1?FC,0J';Rd'8e1QJGRG%UCRe/6JRf%9JRgPNPQP>PTPUPWPBPRPSPVPOPPp-0RhPYPZ1I34RiP\P]%O=9P3<R<,G3/=:,3]1C]9R=5>]P`1G3A!s;%C4P7P!uE,W516@1/5416e4!u3$5hP110c?Pcf;Re!u33Pfe!tb;PYPZP!tY$P_P`P_!t82%94\a^23P1PcPLO2Ra!t$2geCN15fge,fJEMW<P1O1P3PJPM!t@;g00W5RM#B#BRg#B,A31A3g1A3M5L35L3g00WT'e=dXYPZP[!ti$^P`P]1=<;!v?%0!v=$P]1C]F1::<,3]R<!vQ%::;,3]=T]6C4C4!uD2X;3X5hX=h%21R616?8/59108?,5F1090109I,;E'8[[!y%&^5h^=hP116@cR@10bCPbPcPLf:PeO7!y93JF/8dePGPK10JCRC!w;F^P`P^!tu2P5\6^23P!w23K!x4FA>]=<!u~$A!yN5X5h101?,54PD!yM+P@PcP!yI5C!xG$KCe,cJEMX<HP1O1n20010!s#$211000!s'$bAW>W?X@3XB3o"). Qed.
  Lemma mod64_leh_iff : ltac2:(zQ "a0!p7!s1!s7!h9!r0!hm6!hmc!q2!sd!hn1>1x$3>1c$3>0@2$2@2$0@1$8@2$1+2+jf^2@2$4^2@2$1+2+jf>0@2$2@2$0@2$1+2+jf^2@2$4^2@2$1+2+k0@2$5@2$0@2$7^4+hggggggggggggggg0^3@2$6@2$0Z^4@2$0^4@2$9^3@2$1+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##@Wh06__sat1h1!s/%3h24__x1h37__arithh44__ffh54__p1h6!sN%0h7!s/%2h88__varmaph95__with:2Hah;4__x2h<1Hh=4__p2h>2Hch?2Hxh@1chA1ohB1xhC1zp;1p;2p;3p;4p;7p;6p;8g000Nj11Tg0013j1?Tg003nj1<Tg0053j2DTg00]Tj1UTg008Qj20Tg007Nj23!s8$mj26Tg010Pj2[Tg0115R0j2;!sy$Qj2QTg00aKj2>!sC$Oj29Tg002Nj2STg00_\j2HTg00`Dj3RTg00:Tj2aTg00;5j2JTg00@ij1`Tg00Aij1_Tg00BIj2I!s/$gj1]Tg00CEj4\!s/$cj1ZTg00DAj1YTg00Gcj2K!s8$lj2ETg00F:j1XTg00^1j1O!tL$hj3PTg00Onj3W!u&$hj3VTg0155j7pTg00HFj2o!s/$hj2nTg00ITj3m!s/$nj3hTg00JMj4gTg00bKj2GTg00cRj4N!ur$hj2fTg00LYj6M!uW$Oj1BTg00=Vj2ATg00N=j3LTg00>?j2e!ui$Ij3dTg013;j2cTg00EOj4F!sS$fj7bTg014Qj7iTg00PQj8j!tL$nj6k!uE$Jj7lTf0R1#!s$&p=^g00Q5R2,31p=:1021p=2%1!sB$q!s-$!s$/p=7g00QSR3f1R4g00X@P1CFp=@P4g00RXR5g00S7R6P6g00SWR7P1g00T7Fbp=4P3!sM%1!s[%8f2R8P5P6P6P7P4P1Fip=Tf3R9!s;+8P4P1Gjp=5P4!s;+1Ekp=CP!sa1lp==g00U>R:#1R;#?R<%<:#<!s$%R=#?R>'DR?#UR@/04134?'610?4%1;#^RA#?RB,D<RC,34RD'61[92%:9%29RE';P0f4R0#:%20f5RF%qA#7!s$0?RG'Q/00%2FRH1>0CRI,0F';'9P1%:FP3f6RJ/SCRK101Jf7RL#21>JC,0L';'9XC3RM1H<>RN132<RO%2>132?[RP[RQ%2<RRg00gVRSAR<>4UW:R>%2?\S^:RRT1H<BRU%2B132C[RV\ORWAR<B4VSX:RRB%2C!sP%R!wF$Uc1a2<'JPOeROO1RSPVP0POO1ROPPg00VIRX#`RY%_XRZP31I38P4%]3C\R[%Z3R\%Y3R]1K3:R:1E32R^'@,4]R_%X6R`1E3<R<%OA5P3RA9W3:1K3;R;'8,4]P]!w{'18^:,4]R^AV3;A,8:,4]FpR65T]C51o]7R7P1P8g00Xg!yl$YGRa'J1n18=m5adAh324CgR2b4b8b9X23X;3%:1Ra1S4C/08%24R51>8C,04';'9[^23^;3P1f<Rbf=RcPLO3b3b1b0b6b0b7b110KF%2JRK1>FC,0J';Rd'9e1QJGRG%UCRe/0JRf%:JRgPNPQP>PTPUPWPBPRPSPVPOPPp-0RhPYPZ1I34RiP\P]%O=9P3<R<,G3/!u_$1C]9R=5=]P`1G3A!s;%C5P7P!uE,W510@1/6410e4!u3$5hP113c?Pcf;Re!u33Pfe!tb;PYPZP!tY$P_P`P_!t82%:4\a^23P1PcPLO2Ra!t$2geCN16fge,fJEMW<P1O1P3PJPM!t@;g00W5RM#B#BRg#B,A31A3g1A3M5L35L3g00WT'e=dXYPZP[!ti$^P`P]18<;!v?%0!v=$P]1C]F1@:<,4]R<!vQ%8:;,4]=T]6C5C5!uD2X;3X5hX=h%21R610?8/69138?,6F1090109I,;E'9[[!y%&^5h^=hP110@cR@13bCPbPcPLf:PeO7!y93JF/9dePGPK13JCRC!w;F^P`P^!tu2P5\6^23P!w23K!x4FA=]=<P`1@:A!yN5X5h131?,64PD!yM+P@PcP!yI5C!xG$KCe,cJEMX<HP1O1n20010!s#$211000!s'$bAW>W?X@3XB3o"). Qed.
  Lemma mod64_gth_iff : ltac2:(zQ "90!r0!s1!s7!h9!p7!hm6!q2!sd!hn1>1x$3>1c$3>0@2$2@2$4@1$7@2$1+2+jf^2@2$0^2@2$1+2+jf>0@2$2@2$4@2$1+2+jf^2@2$0^2@2$1+2+k0@2$5@2$0^3@2$6^4+hggggggggggggggg0@2$2@2$0@2$8^3@2$1+2+k0^4@2$0^4Z").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##@Uh06__sat1h1!s/%3h24__x1h37__arithh44__ffh54__p1h6!sN%0h7!s/%2h88__varmaph95__with:2Hah;4__x2h<1Hh=4__p2h>2Hch?2Hxh@1chA1ohB1xhC1zp;1p;2p;3p;4p;6p;7p;8g000Nj11Tg0013j1?Tg003nj1=Tg0053j2FTg00]Tj1UTg008Qj27Tg007Nj20!s8$mj22Tg010Pj2\Tg0115R0j2W!sy$Qj2RTg00aKj2:!sC$Oj29Tg002Nj2PTg00_\j2LTg00`Dj3TTg00:Tj2bTg00;5j2ITg00@ij1aTg00Aij1`Tg00BIj2H!s/$gj1^Tg00CEj4]!s/$cj1[Tg00DAj1ZTg00Gcj2K!s8$lj2ETg00F:j1YTg00^1j1D!tL$hj3OTg00Onj3X!u&$hj3VTg00HFj2o!s/$hj2nTg00ITj3m!s/$nj3lTg00JMj4hTg00bKj2GTg00cRj4Q!ui$hj2gTg00LYj6N!uN$Oj1ATg00=Vj2BTg00N=j3MTg00>?j2f!u`$Ij3eTg013;j2dTg00EOj4S!sS$fj7J!ty$Jj7cTg014Qj7iTg00PQj8j!tU$nj6kTf0R1#!s$&p=_g00Q5R2,01p=51721p=3%1!sB$p!s-$!s$/p=8f2R3g00RXR4g00S7R5P5g00SWR6g00QSR7f1R8g00X@P1CSg00T7R9FJp=6P3P4P5P5P6P8P1Fcp=>!s92ip=Cf3R:!s;+3P8P1Gjp=4P7P8g00R1P1CSp=<P8!sK+1P!t-$;!s9/Ekp=@g00U>R4#1R9#?R;%=4#=!s$%R<#?R='FR>#UR?/78108>'217>8R@%19#_RA#?RB,F;RC,08RD'21\:2%5:%3:'WP0f4R0#5RE%30f5RF%pA#8!s$0?RG'R,001:0C/0F%5FRH'2'9P1P7f6RI/PCRJ10I11:ICf7RK'0%5K'2'9XC7RL1L;=RM102;RN%3=102>[RO[RP%3;RQg00gVRRAT;=8UW:R=%3>\R^:QRS1L;BRT%3B102C[RU\NRVAT;B8VRX:QRB%3C!sP%Q!vo$Uc1b2;'IPNeRNO1RRPUP0PNO1RNPOg00VIRW#aRX%`WRYP71H73P8%^7C]RZ%[7R[%Z7R\1K79R91E72R]56\R^%Y5R51K74R41E7;R;%DA5O7RA9X7956\AV74A=6\9=>\^R^5C\C41o\6R6P1P3g00XgR_g00YGR`'I1n13=m_`dAl728ChR2b4b8b9X27X;7%58R`1P3C,081:8C/03%53'2'9[^27^;7P1f=R3f<R_PKO3b3b1b0b6b0b7b110FJ1:FC/0I%5IRJ'2Ra'9e1RIGRG%UCRb/7IRcPJPMPPP=PSPTPVPBPQPRPUPNPOp-0RdPXPY1H78ReP[P\%D<9O7;R;,G7/<4,;\1@\:R<5>\P51G7A!s;%C4P6P!u@,W517?1/2817b8!u0$5dP1103>P3f;Rb!u03Pce!tb;PXPYP!tY$A6\4]RfP5Pf!t=2%51P`[^27P1P3PKO2R`!t-2JeCQ12cJe,gIENX<HP1O1%3FP7PIPL!tJ;g00W5#ARL#ARH#A,B71B7H1B7L5M75M7g00WT'f=eWXPYPZP[P\1<]9,;\P5P\1<;!vN&0!vL$P\1@\FA6\9;!s6$A6\49=C\^C4C4!uH2X;7X5dX=d%38R^12@:10:>,2F10:01::C/00/2E'9[[!y/&^5d^=dP117?3R?10_CP3P_PKf:PbO7!y?4I/9aePG%3IRG10ICRC!wGE1<]4,;\R]P5P]!wI331P^!wI$!wA3G!xIJ;9>\<!v4%A!v+35d101>,28PD!yd+P?P3P!y`5C!xX$GCe,dIENW<P1O1n20010!s#$211000!s'$bAW>W?X@7XB7o"). Qed.
  Lemma mod64_eq_iff : ltac2:(zQ "90!h9!s1!s7!j0!p7!r0!hm6!q2!sd>1x$0>1c$0>0@2$2@2$4@1$8@2$1+2+jf^2@2$5^2@2$1+2+jf>0@2$2@2$4Z^2@2$5^2@2$1+2+jf@2$6@3$3$0@2$7^4+hggggggggggggggg0^3@3$3$0^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##@5h06__sat1h14__x1h27__arithh34__ffh44__p1h5!sN%0h6!s/%3h78__varmaph85__with92Hah:4__x2h;!sN%2h<1Hh=2Hch>2Hxh?1ch@1ohA1xhB1zp;1p;2p;3p;4p;6p;7p;8g000Nj10Tg0013j1BTg003nj1?Tg0053j2ITg00]Tj1WTg008Qj29Tg007Nj23!s8$mj26Tg010Pj2bTg0115R0j2]!sy$Qj2T!s:$Oj2;Tg002Nj2LTg00_\j2NTg00`Dj3QTg00:Tj2eTg00;5j2K!s/$Oj1=Tg00=Vj2:Tg00N=j3>Tg00>?j2E!sJ$nj1cTg00<Lj2a!s/$mj3`Tg00@ij1_Tg00Aij1^Tg00BIj2H!s/$gj1\Tg00CEj4[!s/$cj1ZTg00DAj1XTg00Gcj2F!s8$lj2STg00F:j1rTg00^1j1V!u3$hj3UTg00bKj2GTg00Onj3qTg00EOj4ATg00HFj2p!s/$hj2oTg00ITj3P!s/$nj3iTg00JMj4hTg00cRj4O!vP$hj2gTg00LYj6MTg013;j2f!uE$Ij3j!v+$fj7k!tC$Jj7l!tU$nj6mTg014Qj7nTg00PQj8dTg00Q5R1f0R2'9p=11321p=<%02#0#0#0p=Y!s2$p=s!s:+!s$'p=8g00QSR3f1R4;P2p=4g00VIR5?j42p=5P3P4g00X@P2CAp=D!s4$RXR6g00S7R7P7g00SWR8P2g00T7Fkp=2!s[&R1!s[%Cf2R9P6P7P7P8P4P2Flp=@P4!s9+2Emp=JP!sJ1np=Rf3R:!s;+9P4P2Gdp=7g00U>R6#0R;#BR<%?6#?!s$%R=#BR>'IR?#WR@/94134?RA'6%14RB/6A1b:1%<:%1:']P0f4R0#<%10f5RA%0;#YRC#s#8!s$0BRD'T/4014A0';P2%<AP3f6RE%BCRF,I<RG'LRH142Ef7RI/4E';XB3RJ1N<>RK131<RL%1>131?[RM[RN%1<ROg00gVRPAQ<>4UW9R>%1?\P^9ORQ1N<FRR%1F131G[RS\LRTAQ<F4VPX9ORF%1G!sP%O!w-$Uc1e1<'KPLeRLO1RPPSP0PLO1RLPMp-0RUg00W5RV#=RW#=RX#=RY,:31:3X1:3WRW5>35>3g00WTRX'ERZ%c6,a3=`3WRW1:3V5>3/EXRV%=YRY#=!sc%Y=>3W!s@%%_5RX'5,5V'5,5Z'5%^5R5P31H39P4%\3C[RZ%Z3RW%X3RY1F36R61S31R['D,2YR\%r7R7PY1F3;R;,C[,2Y1S3<R<%V=5U3R=,D;,2Y5@YP7PY1G3=/C6,2YR]1JY0!s=%3%VC9U3<R<9q36g00TWRCP;CA,2YP3P6P!s3'R;5RYC7C7C71pY8R8P2P9g00XgRCg00YGR^'K1o29=PC^dAi314ChR1b3b7b8X13X:3W4%<2R^%19139?'619@9/601L:G!yB$:0';[[[^13^:3^4UP2f=R9/3?RCf<P9PIf:RIf;R_O6b2b6b0b5b0b;b614HA14EARH';e1TEDRD%WGR`/9ERa%<ERbPKPNP>PQPRPTPFPOPPPSPLPMPXP51H34RcPWPY1JY:R:9@Y]P71G3<!vM%C7P8P!u?-4U19@2/6419`4!t|$4UP2PCP9P_O3!th1Pae!tI+P!t=%P!t9$P\P7P\!t%2%<4\^^13P2PIP0O2R0b2!sr%PbeCO16abe,gEEMW<P2O1%1AP3PEPJ!t1/15VX,5V!s%%P5PZPWARY;;!u:1:31424R;/;;!w5%P2f9PIO2!t?'1;HHePD%1ERD13EGRH!u>91C[!yi$[P7P[!uE312PB[^13P!u>,De!wQ?!sz&D6=,2Y9@Y:P71D6<!wK932?,64134G!wK+19@9!wM8H!v]$DHe,f!v]+n20010!s#$211000!s'$b@W=W>X?3XA3o"). Qed.
  Lemma mod64_eqh_iff : ltac2:(zQ "a0!s1!h9!s7!j0!p7!r0!hm6!q2!sd!hn1>1x$1>1c$1>0@2$2@2$4@1$8@2$0+2+jf^2@2$5^2@2$0+2+jf>0@2$2@2$4@2$0+2+jf^2@2$5^2@2$0+2+k0@2$6@3$3$1@2$7^4+hggggggggggggggg0^3@3$3$1^4@2$9^3@2$0+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##AEh06__sat1h1!s/%3h24__x1h37__arithh44__ffh54__p1h6!sN%0h7!s/%2h88__varmaph95__with:2Hah;4__x2h<1Hh=2Hch>2Hxh?1ch@1ohA1xhB1zp;1p;2p;3p;4p;6p;7p;8g000Nj10Tg0013j1CTg003nj1>Tg0053j2JTg00]Tj1YTg008Qj27Tg007Nj22!s8$mj26Tg010Pj2bTg0115R0j2\!sy$Qj2UTg00aKj2@!sC$Oj2<Tg002Nj2PTg00_\j2MTg00`Dj3KTg00:Tj2iTg00;5j2H!s/$nj1eTg00<Lj2c!s8$Oj1=Tg00=Vj2:!sA$mj3aTg00N=j3?Tg00>?j2ETg00@ij1`Tg00Aij1_Tg00BIj2I!s/$gj1^Tg00CEj4]!s/$cj1[Tg00DAj1ZTg00Gcj2T!s8$lj2XTg00^1j1W!u&$hj3VTg00Onj3u!u`$hj3tTg00HFj2s!s/$hj2qTg00ITj3S!s/$nj3pTg00JMj4oTg00bKj2RTg00F:j1mTg00cRj4O!vP$hj2lTg00LYj6LTg013;j2k!uE$Ij3jTg00EOj4F!ur$fj7nTg014Qj7h!t$$nj6g!tp$Jj7rTg00PQj8fTf0R1#0!s$%p=dg00Q5R2,21p=;1721p=4%01#0p=v!s-$!s$/p=9g00QSR3f1R4;S1p=3g00VIR5?j41p=5P3P4g00TWP1CFp=G!s4$RXR6g00S7R7P7g00SWR8P1g00T7Fnp=1f2R9P6P7P7P8P4P1Fhp=N!sp&R1!sp%AP4!sI+1Egp=QP!sZ1rp=Bf3R:!s;+9P4P1Gfp=8!sq&X@!sq%Dg00U>R6#0R;#CR<%>6#>!s$%R=#CR>'JR?#YR@/74124?'617?4%0;#dRA#CRB,J<RC,24RD'61b:2%;:%4:'\P0f4R0#;%40f5RE%vA#9!s$0CRF'U/301@0CRG,3E'<P1%;EP3f6RH/PCRI131Hf7RJ1@HC'3'<XB3RK1M<>RL122<RM%4>122?[RN[RO%4<RPg00gVRQAK<>4UW:R>%4?\Q^:PRR1M<BRS%4B122C[RT\MRUAK<B4VQX:PRB%4C!sP%P!v@$Uc1i2<'HPMeRMO1RQPTP0PMO1RMPN%e6,c3g00W5RV#=RW,:3RX5a3RY1:3V5?!sB$TRV'ERZ%`5R[,5Z!s%%'5%_5R5P31I39P4%^3C]RZ%[3R\%Z3R]1T36R61X3<R<%WA5V3RA5u31T3;R;'G,1]At3;A,G6,1]R^3N1s]8R8P1P9g00XgR_g00YGR`'H1q19=S_`dAp324CoR`b4b8b9X23X;31P1C/341@4C,31'<^23^;3P1f<R_f=RaO2b3b1b0b6b0b7b113IE1@EC,3HRI'<e1UHFRF%YCRb/7HRc%;HRdPLPOP>PRPSPUPBPPPQPTPMPNp-0ReP[P51I34RfP\P]%W=9V3<R<,R3/A6,1]1Q]:R=5B]%m7R71R3A!s>%C8P8P!u2,W517@1/6417b4[^23^5eP112a?Paf;RbO3!u/1Pce!te;P[P5P!t\$1X32R2,D!vt$gP7Pg!tD2%;1%;!t=$P1PaPJO2Rg!t62deCO16cde,lHELW<P1O1%4EP3PHPK!tQ;%=WRW#=RK#=Rd,:31:3W=?3Y5?3/EVRY%=!s<&K=?3X!s<&V15V['5,5Y,5Y'5P5PZ!u;$A2!u6$2P7P]1A<;,1]1D;A,1]5B]!s;$Q]01D6<,1]R<!s:$1G6;,1]=N]^C8C8!ul2X;3X5e%41R^17?9129C'6129?,6013:013:G'<[[!wM$;!wP&7@aR@P_PaPJf:PbO6!y_3HE/<IePF%4HRF12HCRC!whEP2P7P2!w\344\^^23P!wR3F!xbFAB]=<P71D6A!y|5X5e121?,64PD!y{+P@PaP!yw5C!xg$FCe,k!xg+n20010!s#$211000!s'$b@W=W>X?3XA3o"). Qed.
  Lemma byte_range : ltac2:(zQ "60!rb!hg5!s7!p7!r0!hl5>1b@1$5@1$0#8@2$2@2$3Z@2$1@1$0#8^1@2$4@2$1@1$0#8^1+hg0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##2Vh04__p1h16__sat1h24__x1h32Hah47__arithh54__ffh6!sL%0h78__varmaph85__with91Rh:1bp;1p;2p;3p;4p;6p;7p;8g000Nj11Tg00^1j1VTg00ibj1CTg015Yj2?Tg00f=j28Tg016Lj1FTg007Nj22Tg008mj23Tg0013j14Tg00_\j2>Tg0053j2=Tg00`Dj3<Tg00:Tj2UTg00;5j2;Tg00@ij1TTg00Aij1ITg00BIj2HTg00Ccj1GTg00DAj1E!s/$lj26Tg00Gcj2DTg00EOj45Tg00bnj6BTg00F:j1ATg00HFj2@!s/$hj2JTg00ITj3K!s/$nj3LTg00JMj4M!tp$hj3NTg00cRj4O!uN$Qj2PTg00Nfj7QTg00OJj7RTg00PQj8STg00Q5R0f0R1'Pp=0f1R2g00RXR3g00S7R4P4g00SWR5P1g00T7FQp=7f2R6P3P4P4P5P2P1FRp=9f3R7!s;+6P2P1GSp=:g00U>R8#1R9#1#1R:#VR;#C1?;118;1R<#0%F;,2<'318;2R<#0R=%1:#1!s$&4R>,2<R<%49R9%4:R:'>R?1209R@%0:1=9:RA,20[RB[RC%09RDg00gVREA<9:2UW3R:%0A\E^3DRDP2g00Uc1U09';P@eO1R@PBp-0REg00QSRFg00VIRG#TRH%IGRG1HF2RI%GFRJ%EFRKPF16F0g00R11DF8R8C5,7KRLPK!ut+7EBR759K%A4R4PLC:1@K5R5P1P6g00XgRLg00YGR3';1J16=KL3dALF02CMR0b5b7b8W2W0%01/32%02[^2F^0EP1f5,8;R3/2AP3f4RLO3b4b1b6b1P=eP?PCP:PDP@PBPHPGPIPJPKPFP8g00X@RJ16F9=NF;!u#$99K7P4PFP8PJ16F>!s;$C:P5P!tP&X2FX0E121A,32122>!tT+%03P3P!tK/<eCO13=<eb9W:o"). Qed.
  Ltac pose_byte_ranges K :=
    repeat match type of K with
    | context [bv_unsigned (?b : bv 8)] =>
        lazymatch goal with
        | _ : 0 <= bv_unsigned b < 256 |- _ => fail
        | _ => pose proof (byte_range b)
        end
    end.
  (* [comment removed for export] *)
  Lemma lxor_m1_64 : ltac2:(zQ "80!h9!s7!j0!p7!r0!hn7!s1!hn1>1w$0>0@2$1@2$3Z^1@2$4^1@2$6+2+k0@3$2$0@2$5^2+vvvvvvvvvvvvvvvf@2$7+vvvvvvvvvvvvvvvf^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##>9h06__sat1h14__x1h24__p1h37__arithh44__ffh5!sN%0h68__varmaph75__with81zh92Hah:4__x2h;1Dh<1Hh=2Hwh>1wp;1p;2p;3p;4p;6p;7p;8g000Nj17Tg0013j1@Tg0053j2STg007Nj24Tg008mj28Tg0175j1>!sS$Qj2=Tg003nj10Tg00aKj23!sJ$Sj1tTg002Nj2;Tg00]Tj1<Tg00_\j2gTg00`Dj3cTg00:Tj2bTg00;5j2K!s/$nj1_Tg00<Lj2^!s8$Oj1[Tg00=Vj2G!sA$mj3ZTg00N=j3YTg00>?j2XTg00@ij1VTg00AIj3U!s/$ij1TTg00BIj2E!s/$gj1QTg00CEj4P!s/$cj1NTg00DAj1OTg00Gcj2DTg00Onj3C!sA$lj2?Tg00bKj2FTg00F:j1u!ur$hj3MTg00HFj2s!s/$hj2rTg00ITj3B!s/$nj3qTg00JMj4lTg006Jj2kTg00^1j1j!v5$hj3f!tL$@j3e!t:$nj6dTg00EOj49Tg00cRj4I!s/$mj3aTg00LYj6J!t^$\j6h!t$$1j1`Tg00ooj4iTg00[oj6LTg018:j2m!s/$Xj2n!xK$Qj2o!vk$fj7]Tg00PQj8\!ur$Jj7pTg00Q5R0f0R1'op=1%01#0p=W!s-$#0#0p=R!s2+!s$'p=6g00QSR2f1R3;B1p=2P2P3g00TWP1C9p=A!s4$RXR4g00S7R5P5g00SWR6P1g00T7F]p=5f3R7P4P5P5P6f2R8P3P1G\p=:P8!s='P3P1Fpp=H%11R9g00U>R:#7R;#@R<%7;#7!s$%R=#@R>'SR?,41R@'8P2%>3RA/=?%0:#W#R#6!s$0@RB/38,21X82%t31;3A%@:RA#<RC'21g<>RD140<RE%1>140?[RF[RG%1<RHg00gVRIAc<>3UW9R>%1?\I^9HRH!un$Uc1b0<'KPEeO1REPFg00VIRI%_:,^2g00W5RJ#[,G25Z21G2J5Y!s<$T'X%VIRJ3U%TIRIP21E28P3%Q2RKCP%N2RL%O2RM1D2:R:1D2;R;5C21?2ARN,F2'A,5M%u5RO1F2:=M2NRP/A;,5MC:1sM6R;P1P8g00XgRQg00YGRR'K1r18=BQRdAq203ClRRb4b6b7X12X:21;13/2C%<3/3ARC/28[^12^:2P1f6RQ#>PQf4RSO3b3b0b5b0%<8/3A%>8'2R8eP8P2%<7/3AR81=1?13BSRT'2X82P21kA?RU,;8RV/=?RW121TX82RTP2PVPTPDPGP>PHPEPFPJPI1E23RTPL1?2<%j=5f2R=9e2N9C2PRP1?2B=M2:!u{$P;P!u<,%<1/3A/;U13B1'2^12P1f7RNO1!u&'13B7,2VePW%1VRW14V?R<!tM/p-0RXPJPIPTPLPMPM!z^+7EdRYP2P:g00X@RZP=C9,5MR[5HMR\POP21?20R]g00R1R^PP!sE$C:!tp0W2183@R@1;CURU#1!w%$2XP1%1NPNPQ!v|,PWe!v53!ta&2P]P^P:!tL%:=HMYRYPOP2PPP!tc'!tD2X2X1893R914U?!tA+14N?!tB2<eCI18W<e9aV?EJ1=8?P8PAP?!tY4K!tY$!v:&1A=],5MEh!tD,AB2?0R0g00Yg[P!wF+%`0eCiEL%>7P1ELb<b;1m3B%13RB143?R7!uk:YPOP:!uM5PB\9!uF'f5R9/4?P9P!zc-PB!ve;\POP[!sx67\@!w[,9!st27!v?$B7e,n3EJW=X>2o"). Qed.
  Lemma swrap32_id : ltac2:(zQ "90!h9!s1!s7!j0!rb!p7!r0!sd!va>1x$0>0@2$2@2$5@1$7@2$1+2+hf^1@2$6^1@2$1+2+hf@3$3$0@2$8@1$4#i0^2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##2Th04__p1h16__sat1h24__x1h32Hah47__arithh54__ffh6!sL%0h78__varmaph85__with92Hxh:1xp;1p;2p;3p;4p;6p;7p;8g000Nj13Tg0013j18Tg003nj14Tg0053j2@Tg00]Tj1<Tg008Qj20Tg007Nj21!s8$mj22Tg00^1j16Tg00_\j2ATg00`Dj3?Tg00:Tj2>Tg00;5j2;Tg00@ij1VTg00Aij1UTg00BIj2TTg00Ccj1RTg00DAj1Q!s/$lj2G!sw$hj3FTg00bKj2ETg00Gcj2DTg00EOj47!sA$nj6CTg00F:j1BTg00HFj2H!s/$hj2ITg00ITj3J!s/$nj3KTg00JMj4LTg00cRj4MTg00lVj1NTg00mDj3OTg00Nfj7PTg00OJj7=Tg00PQj8STf1R0g00RXR1g00S7R2P2g00SWR3f0R4g00T7FPp=9f2R5P1P2P2P3P0P4F=p=5f3R6!s;+5P0P4GSp=:g00QSR7g00U>R8#3R9#8R:%48#4#4#4R;#8R<'@R=#<R>/04R?114=R@'2%39#3!s$$6R910>0RA110=RB1A:<RCg00Q5RD/1:RE10D<11D=[RF[RG10D:RHg00gVRIA?:<0UW3R<10D=\I^3HRHP0g00Uc1>D:';PEeO1REPFp-0RIg00VIRJ#VRK%UJRJ1T70RL%R7RM%Q7RNP71G7:%6;5F7R;,E7g00R11D78R8C7,9NR:PN!u~+6ECR655N%B2R2P:C:1HN3R3P4P5g00XgR:g00YGR1';1I45=J:1dAK7D0CLRDb5b7b8X27W012?0PA[^27^0IP4f5R?/1=P?f4R=O3b4b1b6b1PAePCPGP<PHPEPFPKPJPLPMPNP7P8g00X@P;!tr%;95N6P2P;C:P3P!t8,X0I120@PB!t9+10>?P?P!t4/BeCM12ABe%N9R9#</001109'2e7O0W9W:o"). Qed.
  Lemma mod64_eq_mod64_iff : ltac2:(zQ "90!h9!j0!r0!q2!s1!hn1!s7!hm6!sd>1x$0>1y$0>0@2$6@2$2@1$8@2$4+2+k0@2$5^2^1@2$2@2$5^2^1@2$4+2+k0@2$7@3$1$0@2$3^3+hggggggggggggggg0@2$3^2+hggggggggggggggg0@3$1$0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##Lwh06__sat1h1!s/%2h2!s/%3h3!s/%0h4!s/%4h57__arithh64__ffh7!s@%5h88__varmaph95__with:4__x1h;4__x2h<4__x3h=4__x4h>2Dxh?3Hxyh@1EhA2H0hB2H6hC2HahD4__p1hE4__x5hF4__x6hG1ahH1xhI1zhJ2BxhK2ByhL2DyhM1HhN2H1hO3H10hP2H2hQ2H3hR2H4hS2H5hT2H7hU2H8hV2H9hW1QhX1yhY2zhp&0p;1p;2p;3p;6p;4p;7p;8g000Nj13Tg0013j1TTg0053j2iTg00]Tk106Tg00aKj2HTg007Nj2!s8$1Qj21Tg00K?j29Tg00_\k205Tg00`Dk304Tg00:Tj2^Tg00;5j2JTg00@ij1~Tg00Aij1{Tg00Bgj1zTg00Ccj1wTg00DAj1r!s/$lj2QTg00F\j6mTg00HFj2l!s/$hj2kTg00ITj3E!s/$nj3jTg00JMj4hTg0061j1g!uH$Pj3Wj2fTg0021j22Tg00ZDj2=!sM$gj3Vj2e!uV$jj2cTg008Qj2U!s/$mj2ITg009Hj2a!s/$nj2`Tg019`j2_!uT$nk10!vc$<Lk200!s:$Oj1>Tg00=Vj2C!sB$mj3FTg00>?j2R!s/$kj2]!uz$Ij2GTg003nj1\Tg00Gcj2@Tg00bnj6y!uz$:j1v!sA$@j3NTg00Onj3OTg00^1j1q!w@$hj3p!s\$Kj2t!x$$hj3u!u\$Jj2YTg00[oj6XTg00LYj7nTg00cRj4xTg00EOj4STg00Nfj7|!vL$Nj2b!s8$=j3}!w~$Ij3d!wu$Ek40!xq$OJk70!vr$PQj8MTf0R0#3!s$%p=sf2R1f1R2/60'Ip=8%30#3p=o!s-$!s$/p=<g00QSR3?E20p=5g00Q5R4/U0p=0P3P2g00TWP0CSp=;!s4$RXR5g00S7R6P6g00SWR7P0g00T7F|p=4AE304p=Lf3R81Y12/b05E3p=:!st&X@!st%KA}320p=7g00VIR9Ad9207d1p=DP3P1P2P0H01p=B!s^&R1!s^%?P1P5P6P6P7P2P0K02p=[P8!s:+!s`$GMp=Pf6R:!s='f5R;f4R<!sO5GMp=A1b209E31p=Zg00U>R=#3R>#TR?%3>R@#sRA#TRB'iRC$06RD1H20RE'6?8EC%oA#<!s$0TRE,11RF112ERG'5RH1581[1512RI118ERJ/5F[191E%01%0ERF11<ERK#0[[19<ERL%0<11:E#0\F[RM205?BRN164?RO%0B164C[RP[RQ%0?RRg00gVRSB04?B2UWCRB%0CRT\S^CRRU!v\$UcRV1^4?'JPOeROO1RWPP%~9RX%{9R9%z3RY%w3RZ%r3R[!vB'1Q3ER\1Q34R]';,4[EmR^1l[7R_P0P1g00XgR`g00YGRa'J1k01=E`adAj342ChRab6b8b9%LE!sL%g[RbP0b5b0b3b0Rcb1b2%g`Rde9W8EP8PE128EPJC:Re198E%0811;ERf#0Rg\F[19;ERh%0;Rif7Rj/1!v?&k1=:ERl%0:Rmf8Rn/2ERo!sA%pP!t4$b4P!t3&ePLPM19:ERM11nERL#0\F\mRmPlPp1=nERp%0nRlf:Re/2!t/&cPNPQPBPUPWPPPXP9PYPZ1K]\,4[P_P!u^&164ERq!uW-r!tI%b7Pqe9V;EA8gfERgPhPk19jE%0jRkf9Rh/1!uZ$\F[1=jE12hERs!te$k1=hE%0hRtf;Ru!t]'P!s~3PgPMPm19nE11e!sJ$\lPpPc1=eE%0ef<!s`+!u=&f=Rc/fEf>RpPE12pE11pEC:\d1epEf?Rp/1ERl#0?8lE\q1cpE16E4Rlf@Rm/1ERM,6E1UM4'I[1amEfARM/2ERg#L\`1`MEfBRr/1E/5r\`g01:kRv1_rERwePw1frEfCRwPE12wE11w!tG&wEfDRw/1ERd#0?8d!tG$wEfERd/1ERx!tA$x4'I\l1adEfFRl/2E!t@%lEfGRl!t@$l\`Pv1_lERlePlP<1^4E,JVPqeRqO1fHRV/1ER4#0?84EPuPqO1fJ/1ERq#0?8qEP1PSPmP0P2O2XGRPT^GRPMPOO1PPp-0RO&03=-003!}-$W5RT#>Rm#>RS#>Rq#>#>#>R4#>,C3Rl5F31C34R41C3qRq1C3SRS'7'7'71C3TRT1C3mRm'7g00WTRv'RR`']RxAF3R4AF3Rq/7m'7,7l/]`R`AD`xX9Dx`9D`x3DP91G3<R`1G3:7B11G3;?B8Y7B2PZP[%\=Rx#3,@3Rl,?],4[P!~7+PnEy5[[%v6R6P[P[P^P61@3@R@1@3>R79N3\=O3l!~S$CPP!sK/xRx1@3=R=9N3\%\>,@3R>5O3!sR01?]x,4[P6!s1$\,4[R^P61?]=,4[FA!sK+@!sK&!t&$?]7!sD+1;>l!sg'Q3?%qA5p3RA,t3Au3x@Rx'K,4[1KxA,4[5[[P61;=7,4[RxCPFAFAFA!}O,X:3X;3X<3X=3XE3XF3WD1Ii:1YE8RA=Z;j\bRbPi\F\iPk!}-$5he1HnhRk,6D?8kC15jn[[[[\b[[^:3^;3^<3^=3^E3^F3^DOP0fNRO/1ERb/6EPbfORb/1EPOPb12OE12bEP;PuPMPwPdfLfMO>!#3-%YbAbBfI/2E12VE'5ebObVbUbTbBbSbRbQbPbNbAbMb3b0!~X'12jERj12:E'5P3PoPhPEP0PfC:XI3P<PjP0EXPnPEPjPLC:P3PfPePEPsP0!sI%0PLP:EX!s^$oPLC:19hE11u!#3E$t19uE%0uRt11c!s9$[1=uE12c!sF'=cE%0c12p!#3`0PWPPAF3Rm/7T,7S/RvAF3RS17mT'7/Rv;DX!zu$8?B1YAB`<!zm'AN3\>=O3@R@,;7!xi';=!y8&x!x>;AZ2A1P2PEP<P8C:1518!wh1P0Pg11MEPMPrPcPnO6!w>&!vj,5eheb>b>bWbKbJbLb>X@HP3P11H08RH!xq$HC15GK]?XH31H11R1!s<$1C1J3JW?P8P0P2FnX@ICxW?XX3XH3o"). Qed.
  (* [comment removed for export] *)
  Ltac unmod64 K :=
    pose_byte_ranges K;
    repeat match type of K with
    | context [?x mod 18446744073709551616 = ?y mod 18446744073709551616] => rewrite (mod64_eq_mod64_iff x y) in K by (clear K; lia)
    | context [?x mod 18446744073709551616 <= ?c] => first [rewrite (mod64_le_iff x c) in K by (clear K; lia) | rewrite (mod64_leh_iff x c) in K by (clear K; lia)]
    | context [?x mod 18446744073709551616 < ?c] => first [rewrite (mod64_lt_iff x c) in K by (clear K; lia) | rewrite (mod64_lth_iff x c) in K by (clear K; lia)]
    | context [?c <= ?x mod 18446744073709551616] => first [rewrite (mod64_ge_iff x c) in K by (clear K; lia) | rewrite (mod64_geh_iff x c) in K by (clear K; lia)]
    | context [?c < ?x mod 18446744073709551616] => first [rewrite (mod64_gt_iff x c) in K by (clear K; lia) | rewrite (mod64_gth_iff x c) in K by (clear K; lia)]
    | context [?x mod 18446744073709551616 = ?c] => first [rewrite (mod64_eq_iff x c) in K by (clear K; lia) | rewrite (mod64_eqh_iff x c) in K by (clear K; lia)]
    | context [?x mod 18446744073709551616] => first [rewrite (mod64_of_small_nonneg x) in K by (clear K; lia) | rewrite (mod64_of_small_neg x) in K by (clear K; lia)]
    end.
  Lemma land1_small : ltac2:(zQ "50!h9!p7!s7!j0!hne>1x$0>0@2$2@2$1Z^1@2$1^1+1@3$3$0@2$4^2+1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##2oh04__p1h14__x1h27__arithh34__ffh48__varmaph55__with62Hah76__sat1h82Hxh9!s4%0h:1xh;1zp;1p;2p;3p;6p;4p;7p;8g0013j1<Tg008Qj24!s/$mj21Tg000Nj1ZTg0053j2MTg001Qj2FTg00ITj3:Tg007Nj23Tg00@ij1ATg00Aij1@Tg00BIj2>Tg00Ccj1=Tg00DAj1Y!s/$lj25Tg00Gcj2UTg00bnj6LTg00F:j1ETg00HFj2DTg00;5j27!s8$hj2C!tL$nj3BTg00JMj4GTg00_\j2HTg00`Dj3ITg00:Tj2JTg00^1j1K!sA$hj3?Tg00EOj4;Tg00cRj4N!s/$mj3OTg01;Gj1P!s/$ej2Q!u<$gj1RTg01<Cj3STg00LYj6TTg00Nfj7XTg00OJj7WTg00PQj8VTg00Q5R0f0R1'4p=0g00QSR2f1R3g00R1P1C;p=6P!s4$XR4g00S7R5P5g00SWR6P1g00T7FXp=2f2R7P4P5P5P6P3P1FWp=9f3R8!s;+7P3P1GVp=8%01R9g00U>R:#<R;,41R<'1P2%Z:#<R=/M;R>,F3A:217X;2%03R?133>R@p-0RAg00VIRB#ARC%@BRB1>23RD%=2RE%Y2RF1520RG1U2:RH'6,2FRIPF!tV+8ELR859F%E5R5PIC81DF6R6P1P7g00XgRIg00YGR4'71C17=:I4dAB203CGR4b3b4b5X12W01193P?[^12^0AP1147;P7P3O3b2P?e1H=;130=R7%0;R9130>[RI[%0=RJg00gVRKAI=;3UW6%0>\K^6J!w-$Uc1J0='7P7eO1PIPCPBPDPEPF152;RD,6H,2F99F8P5P2PHg00X@152=%K:5?2C;,2FC8P6P!tx,X0A113<P@!ty+f5RA#0PAf4O3b2b7b9b7P@eCN11?@e9O3>%P;,Q3PCPB%R2PE16GD,2F!s},P9P1b2P9e9S3;ETW8X:2o"). Qed.
  Lemma swrap32_id_m64 : ltac2:(zQ "a0!s1!hn1!h9!s7!j0!rb!p7!r0!sd!va>1x$2>0@2$3@2$6@1$8@2$0+2+hf@2$1^1@2$0+2+k0@2$7@2$1^1@2$0+2+k0@2$0+2+hf@3$4$2@2$9@1$5#i0^2@2$1^2@2$0+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##=9h06__sat1h1!s/%3h22Hah34__x1h47__arithh54__ffh64__p1h7!sS%0h8!s/%2h9!s/%5h:8__varmaph;5__with<!sB%4h=1zh>1Hh?2Hxh@1ahA1bhB5lemmahC1xp;1p;2p;3p;4p;6p;:p;9p;7p;8g000Nj13Tg0013j1;Tg003nj17Tg0053j2=Tg00]Tj1qTg00aKj25Tg008Qj28Tg007Nj21!s8$mj29Tg00^1j1BTg00_5j2E!s/$\j2?Tg00`Dj3ATg00:Tj2fTg00;5j2CTg00@ij1]Tg00Aij1\Tg00BIj2[Tg00Ccj1YTg00DAj1X!s/$lj2G!sw$hj3@Tg00bKj2WTg00Gcj2V!ty$hj3UTg00EOj4:!sJ$nj6RTg00F:j1PTg00HFj2O!s/$hj2NTg00ITj3>j1i!s2$nj3QTg00JMj4MTg00cRj4STg01<fj2T!t=$@j3pTg00Onj3oTg006Jj2nTg002Nj26Tg01>1j1h!w$$QR0j24!s:$aj4JTg01?Hj1eTg01@7j4I!s/$nj3_Tg01Adj1^Tg01BSj6`Tg01C>j2H!s/$jl:aTg01DWl9b!vL$gj1c!uS$\j6d!tW$1j1ZTg00ooj4gTg00LYj6K!wi$Oj2LTg01EQj4jTg00Nfj7k!u>$Jj7lTg00PQj8mTg00QSR1f1R2f0R33>p=2g00Q5R4/83p=0P2g00RXR5g00S7R6P6g00SWR7P3g00T7Fkp=<f2R8P5P6P6P7P2P3Flp=Ff3R9!s;+8P2P3Gmp=Dg00U>R:#3R;#;R<%7:#7#7#7R=#;R>'=R?#qR@%3;#3#3!sL$3RA#;RB,=<RC,53RD'8RE11D?RF'9P1%B;RG152CRH'E158CRI,23X=118@HRJ11H?RK1?<>RL114<RM%0>114?[RN[RO%0<RPg00gVRQAA<>2UW2R>%0?\Q^2PRR1?<BRS%0B114C[RT\MRUAA<B2VQX2PRB%0C!sP%V!vH$Uc1f4<'CPMeRWO1RXPTf4PWO1RYPNp-0RZg00VIR[#]R\%\[R[1[12R]%Y1R^%X1R_P11G1<R`%B=5@1R=,W1g00R11V1:R:%BA9@1`5U1RAC:,<_RaP_!w++9ERRb5F_%P6RcPaCD1O_7RaP3P8g00XgRdg00YGRe'C1N38=>dedAQ142CMReb5b:b;X31W619E2PJ[^31^6ZP3f8RE/5CRd/1?PEf7R?O3b4b1b0b7b0b8b1PJePSPUPBPVPLPOP>PRPXPNPYPTP\P[P]P^P_P1PAg00X@P=!u1%=9F_bPcP=CDPaP!tO,X6Z192FPK!tP+18@dPEP!tF5KeCS19JKe,TH1EG2PGP2PH%;;R;,?<RK%0;1=<;RJ,14[RE\MRMAA<;!x+&;%0J!x+%P!u5<?!x+$WPE!u?+1A@1`GR`=p1`9o1Ag00TWRAP:!uL$!u@01nJJR:,6D/23^31P3f;O1b4b9!u;/b<b916H:/22RDePD16I:RD/28P1%i1R8%h1149J159CRC/6:R:/4JP1^A1R]^@1R?P1P]P8P1P1P8P8CJRQCJR<!s<$Q!s<%%e1CICI9_?<P0P9P:!s;$^1P:P9P3E`PJPJ1H1JM:a14CJRCPC1H1CM9bWBP3P114IJR9123CX=11C1914DJPIPJPJPKPMP;PP!vW+!vg'XPTPYPNP!vY&%c1!xs$!zj'1P`PA1G14!vT$Ed!vV,A>1J4RJg00Yg[P3!vM7%ZJeCgEKO2b>1LG21LGH'2eCjEKW?XC1o"). Qed.
  Ltac norm_s32 :=
    repeat match goal with
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) + ?k)] => rewrite (swrap32_of_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) * ?k)] => rewrite (swrap32_mul_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_0 b) by lia
    | |- context [sx32 (Z_to_bv 64 ?b)] => rewrite (sx32_ssmall b) by lia
    | |- context [bv_swrap 32 ?x] => first [rewrite (swrap32_id x) by lia | rewrite (swrap32_id_m64 x) by lia]
    | |- context [Z.lxor ?w 18446744073709551615] => rewrite (lxor_m1_64 w) by lia
    | |- context [bv_unsigned (b8 ?x)] => rewrite (b8_unsigned x) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 1)] => rewrite (land1_small a) by lia
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac achk := fail.
  Ltac step1 := first [ achk | st1b | arm_inputs; st1b ]; norm_lits; fold_sh8; norm_shpa; norm_s32; gen_data.
  Ltac run_to stops ::=
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                lazymatch stops with
                | context [pc] => fail
                | _ => step1
                end
            end).
  (* [comment removed for export] *)
  Lemma land7_mod8 : ltac2:(zQ "50!h9!j0!hne!p7!q2>1x$0>0@2$3Z^1@3$1$0@2$2^2+7@2$4^2+8").
Proof.
ltac2:(KReplay.run1 (kr_t_W_bpesc0 ()) [] "h02Hxh17__arithh24__ffh38__varmaph45__with51xh61zp;2p;1p;3p;4p;7p;6g008Qj26Tg000Nj12Tg0013j11Tg003nj17Tg0053j2GTg001Qj20Tg00ITj33Tg00;5j24Tg01;Gj1<Tg01;ej2;Tg00@ij18Tg00Aij19Tg00Bgj1:Tg00Ccj1FTg00DAj1ETg00Dlj25Tg00EOj4DTg00Nfj7CTg00HFj2BTg00Hhj2?Tg00Inj3@Tg00JMj4ATg01<Cj3>Tg00LYj6=Tg00QSR0g00Q5R1f0R2'6P0f1R3g00U>R4#2R5#1%74#1R4'G'0f2R6%25#2#1R5'09302X601035,40%<4,;3g00VIR5#8%95%:0%F0%E0R5g00RXg00S7R7P7g00SWR7P01501g00R11504CDg00T7FC1B57P2P6g00XgR7g00YGR5'41?26=375dA@013CAb2b3b41614R1P2b1P1e9>34E=W0W5o"). Qed.
  Ltac box_ugly K ::=
    try (rewrite !signed_lit in K by (clear K; lia)); try (rewrite !signed_of_small in K by (clear K; lia));
    try (rewrite !wz_unsigned in K by (clear K; lia)); try (rewrite !b8_unsigned in K by (clear K; lia));
    try (rewrite !lxor_m1_64 in K by (clear K; lia)); try (rewrite !swrap32_id in K by (clear K; lia)); try (rewrite !swrap32_id_m64 in K by (clear K; lia));
    try (rewrite !land7_mod8 in K by (clear K; lia));
    try unmod64 K;
    try (rewrite !signed_of_small in K by (clear K; lia));
    lazymatch type of K with
    | context [Z.lor _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.land _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.lxor _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.shiftl _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.shiftr _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [Z.modulo _ 18446744073709551616] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [bv_swrap _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | context [bv_signed _] => change (boxP ltac:(let T := type of K in exact T)) in K
    | _ => idtac
    end.
  (* [comment removed for export] *)
  Ltac fin_atom ::=
    first [ eassumption
          | reflexivity
          | lazymatch goal with
            | |- @eq Z _ _ => rv_cbv; fin_arith
            | |- (_ <= _)%Z => rv_cbv; fin_arith
            | |- (_ < _)%Z => rv_cbv; fin_arith
            | |- not _ => rv_cbv; fin_arith
            | |- _ \/ _ => rv_cbv; first [ eassumption | lia ]
            | |- @eq _ _ _ => rv_cbv; first [ reflexivity | eassumption | f_equal; lia | apply bv_eq; rewrite ?unsigned_lit by lia; lia
                                             | lazymatch goal with |- Z_to_bv _ ?a = Z_to_bv _ ?b =>
                                                 let a' := zlit a in let b' := zlit b in apply bv_eq; rewrite !Z_to_bv_unsigned; vm_compute; reflexivity end ]
            | |- _ => rv_cbv; first [ reflexivity | eassumption ]
            end ].
  Ltac norm_s32 ::=
    repeat match goal with
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) + ?k)] => rewrite (swrap32_of_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) * ?k)] => rewrite (swrap32_mul_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_0 b) by lia
    | |- context [sx32 (Z_to_bv 64 ?b)] => rewrite (sx32_ssmall b) by lia
    | |- context [bv_swrap 32 ?x] => first [rewrite (swrap32_id x) by lia | rewrite (swrap32_id_m64 x) by lia]
    | |- context [Z.lxor ?w 18446744073709551615] => rewrite (lxor_m1_64 w) by lia
    | |- context [bv_unsigned (b8 ?x)] => rewrite (b8_unsigned x) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 1)] => rewrite (land1_small a) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 7)] => rewrite (land7_mod8 a) by lia
    end.
  (* [comment removed for export] *)
  Lemma wrap32_of_u64 : ltac2:(zQ "60!rb!h9!ho5!j0!v0!hg5>1a$1@3$3$1@2$2@1$0#i0@2$5@1$0#k0@2$4@1$0#k0^1@2$2@1$0#i0^1").
Proof.
ltac2:(KReplay.run1 (kr_t_W_bpesc0 ()) [] "h01zh12Hah26__sat1h37__arithh44__ffh56__sat0h68__varmaph75__with81ap;1p;2p;3p;4p;7p;6g000Nj10Tg00^1j19Tg00^Oj22Tg00ITj31Tg0013j1:Tg0053j2MTg001Qj23Tg00;5j25Tg006Jj27Tg00_\j2>Tg007Nj28Tg008Qj24Tg00`Dj3;Tg00:Tj2QTg00@ij1PTg00Aij1OTg00Bgj1LTg00Ccj1KTg00DAj1JTg00Dlj2DTg00`hj3CTg00G@j3BTg00EOj4ATg00Nfj7@Tg00HFj2ETg00Hhj2?Tg00Inj3FTg00JMj4GTg00[5j4HTg00e1j4ITg00LYj66Tg00eWj2=Tg00f=j2<Tg00fgj2NTg00QSR0P0g00U>#0R1#0#0#0#0R2#0#9R3f0R4'2R5%92R6/24R7f1R8,26510X00P0%:1R1%:2R2'MR9,34R:13899104X00150:1799R:,34/39P4P:P9P01749910:X00P91>12g00Q5R;/81R<14;218;9[R=[14;1R>g00gVR?A;128UW114;9\?^1>P8g00Uc1Q;1'5P<eO1P=g00VIR=#P%O=%L0%K0%J0R=g00RXg00S7R<P<g00SWR<P01D01=C06R1=B01R1g00TWP1CAg00T7F@1E=<P4f2R<g00XgR=g00YGR1'51?4<=1=1dAF0;8CGb4b6b7A10::R:P4b3b2b5b2P:eCHCIE61265=107e1=34,<31N34E6W8o"). Qed.
  Lemma swrap32_of_u64_2 : ltac2:(zQ "c0!rb!p1!h9!s1!v0!hg5!s7!j0!p7!r0!sd!va>1a$2>1b$2>0@2$6@2$8@1$a@2$3+2+hf@2$1^2^1@2$9@2$1^2^1@2$3+2+hf@3$7$2@2$b@1$0#i0@2$1@2$5@1$0#k0@2$4@1$0#k0^3@2$5@1$0#k0@2$4@1$0#k0^2@2$1^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##=\h06__sat1h12Hah24__p1h34__x1h44__x2h51zh67__arithh74__ffh8!s^%0h98__varmaph:5__with;1xh<!sF%3h=1Hh>!s3%2h?1ah@1bhA1mhB1nhC1yp;1p;2p;3p;4p;6p;<p;7p;8p;Bg000Nj17Tg0013j1@Tg003nj19Tg0053R0j2;Tg00]Tj1sTg002Nj21Tg008Qj22Tg007Nj25!s8$mj28Tg00^1j1BTg00_5j2C!s/$\j2FTg00`Dj3OTg00:Tj2qTg00;5j24Tg00@ij1jTg00Aij1fTg00BIj2_!s/$gj1^Tg00CEj4\!s/$cj1[Tg00DAj1Z!s/$lj2H!t1$hj3GTg00bKj2XTg00Gcj2ETg00Onj3WTg00EOj4>!sJ$nj6VTg00F:j1STg00HFj2R!s/$hj2QTg00ITj3=j1i!s2$nj3PTg00JMj4TTg00cRj4UTg01<fj2rTg00eWj2NTg00f=j2MTg016Lj1p!w&$Qj20!vA$Oj26Tg01F`R1j1KTg0061j1?Tg01G>j1h!s/$\j4gTg01H?l<a!s/$dj3b!t~$\j6cTg01IMj4dTg00dPj4ITg00[oj6]Tg01J8j1JTg00LYj6:Tg01EQj4kTg00Nfj7l!v1$Jj7mTg00PQj8nTg01KFl<o!s/$klBYTg00QSR2f1R3f0R43=p=3P3g00RXR5g00S7R6P6g00SWR7P4g00T7Flp=Af2R8P5P6P6P7P3P4Fmp=Df3R9!s;+8P3P4Gnp=Lg00Q5R:9=24p=<g01LQR;P2!s$$1P1f5R1f4R<P9!sZ%M<op=e!sF&!s$%0P4P3P8P0P9P<P1f6R0f7f8f9MBYp=`g00U>R=#7R>#@R?%9=#9#9#9R@#@RA';RB#sRC1134RD'215DB'8P2%7>#7#7#7RD#BRE1183RF'C1198RG,34X5212CFRH15FBRI1F?ARJ15:?RK12:A15:B[RL[RM12:?RNg00gVROAO?A3UW1RA12:B\O^1NRP!vq$Uc1q:?'4PKeRQO1RRPLp-0RSg00VIRT#jRU%fTRTP21_28P3%^2RVC\RW%[2RX%Z2RYP21H2?RZ%B@5G2R@,X2g00R11E2=1E2>5W2R>C>,AYR=PY!wQ+<EVR[5DY%S6R\P=CL1RY7R=P4P8g00XgR]g00YGR^'41Q48==]^dAP2:3CTR^b7b9b:X32X42W21143R],2C/881138R_,2C[^32^42^2SP41101R`/5BP1P0P<O4b6b0b8b0PHePJPMPAPPPRPLPUPTPWPXPYP2P>g00X@P@!u1%@9DY[P\P@CLP=P!tO0X2S15]B,8815_B!tF02C`!tA4IeCU18HIe,rF%7D#BRI1NI8'MRH1NI3,MIRI'1R0,CEPEP0PFP2%pER1,0H10I1R`'1/01RC10G1!y&'RSP216E8R_16EHRB,14/01/3GX52!s@$3R]16E9/!s>10F1RGPS142G10811031!t'$!{Z$1%KERS,;?R9#<R@#?R\%@DRD,;?R[#<R>#?P2P2%i2RWP4X;2RaPW1334#hXC2X;2P9P[Pa!s$$2P2g01Lo1;34Cg,42XA2XB2P?P?142?PSPDPaPa%K4,42X;;PEPD142DEeM:`P:P:142:M<a9b@>1F?D12:D15:[[R@\KAO?D3VOX1N12:[!{D$!xC0<PQO1P@!xK$V!xK$!zB'2AG2ZEg00TW1H2:!xX$Ec!xN,g00Yg\>P4b6b<!x,%b>b<CdP\e%<1#?eR\CIE]11_]!vv%e16EI%J3E:PB%J8E:11B`!sA'3CGe1001PHPIP1P\CIE:16E016EF'3eCkE:W=X@2X?2o"). Qed.
  Lemma swrap32_of_u64_sub : ltac2:(zQ "c0!rb!hn1!h9!s1!v0!hg5!s7!j0!p7!r0!sd!va>1a$2>1b$2>0@2$6@2$8@1$a@2$3+2+hf@2$1^2^1@2$9@2$1^2^1@2$3+2+hf@3$7$2@2$b@1$0#i0@2$1@2$5@1$0#k0@2$4@1$0#k0^3@2$5@1$0#k0@2$4@1$0#k0^2@2$1^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##7\h04__p1h16__sat1h24__x1h34__x2h41zh52Hah67__arithh74__ffh8!sW%0h98__varmaph:5__with;1Hh<1ah=1bp;1p;2p;3p;4p;6p;7p;8g000Nj16Tg0013j1GTg003nj18Tg0053j2KTg00]Tj1eTg00aKj20Tg008Qj22Tg007Nj25!s8$mj27Tg00^1j1:Tg00_5j2=!s/$\j2HTg00`Dj3dTg00:Tj2bTg00;5j2;Tg00@ij1\Tg00Aij1ZTg00BIj2Y!s/$gj1XTg00CEj4W!s/$cj1VTg00DAj1R!s/$lj2Q!t1$hj3PTg00bKj2NTg00Gcj2?!u3$hj3MTg00EOj4>!sJ$nj6LTg00F:j1JTg00HFj2I!s/$hj2OTg00ITj3E!s/$nj3STg00JMj4TTg00cRj4UTg01<fj2cTg00eWj2FTg00f=j2BTg016Lj1a!v}$Qj21!v>$Oj24Tg01MSj3DTg00[oj6]Tg01J8j1CTg00LYj69Tg01EQj4[Tg00Nfj7^Tg00OJj7_Tg00PQj8`Tg00QSR0f1R1f0R23Ep=3P1g00RXR3g00S7R4P4g00SWR5P2g00T7F^p=@f2R6P3P4P4P5P1P2F_p=<f3R7!s;+6P1P2G`p=Ag00U>R8#6R9#GR:%88#!s$$R;#GR<'KR=#eR>1012R?'215?='7P0%69#6#6#6R?#:R@1061RA'=1076RB,32X4012>ARC15A=RD1H:<REg00Q5RF/5:RG12F<15F=[RH[RI12F:RJg00gVRKAd:<1UW5R<12F=\K^5JRJ!un$Uc1bF:';PGeO1RGPHp-0RKg00VIRL#\RM%ZLRLP01Y06P1%X0CWRN%V0RO%R0RPP01Q0:%:;5P0R;,N0g00R11?081?095M0R9C>,@PR8PP!vH'f4R3ELR:5<P%J4R4P8CA1IP5R5P2P6g00XgR8g00YGRQ';1O26=E8QdAS0F1CTRFb7b9b:X20X30W01021RQ,2>/761016R8,2>[^20^30^0KP2f6RRf5RS'0RT/5=PSPRP3O4b6b1b8b1PCePEPIP<PJPGPHPMPLPNPOPPP0P9g00X@P;!u9%;9<P:P4P;CAP5P!tU0X0K15Q=,76158=!tL/12>T!tA4DeCU17CDe,cA%6?#:R?1F?6'BRD1F?1,B?R?'0RC,=@P@PCPAP0%a@R3,1D11?3RR'0/13RS11B3!y2'RTP014@6R>14@DRK,02/13/3BX40!s@$1R814@7/!s>11A3RBPT1;0B11631113!t'$AD613E]10>8!sU%e14@?%C1E9PK%C6E910KR!sA'3SBe11C3ADD?3E914@C14@A'3eC[E9W;X=0X<0o"). Qed.
  Lemma swrap32_of_u64_rsub : ltac2:(zQ "c0!hn1!rb!h9!s1!s7!j0!p7!r0!sd!v0!va!hg5>1k$2>1b$2>0@2$4@2$6@1$8@2$3+2+hf@2$0^2^1@2$7@2$0^2^1@2$3+2+hf@3$5$2@2$a@1$1#i0@2$0^3@2$b@1$1#k0@2$9@1$1#k0^2@2$0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##6}h04__p1h16__sat1h24__x1h34__x2h41zh52Hah67__arithh74__ffh8!sW%0h98__varmaph:5__with;1Hh<1bh=1kp;1p;2p;3p;4p;6p;7p;8g000Nj15Tg0013j1DTg003nj17Tg0053j2HTg00]Tj1eTg00aKj21Tg008Qj22Tg007Nj23!s8$mj26Tg00^1j19Tg00_5j2B!s/$\j2ETg00`Dj3dTg00:Tj2]Tg00;5j2:Tg00@ij1YTg00Aij1WTg00BIj2V!s/$gj1UTg00CEj4T!s/$cj1PTg00DAj1N!s/$lj2M!t1$hj3LTg00bKj2KTg00Gcj2=!u3$hj3JTg00EOj4>!sJ$nj6ITg00F:j1GTg00HFj2F!s/$hj2OTg00ITj3@!s/$nj3QTg00JMj4RTg00cRj4STg01<fj2cTg00eWj2bTg00f=j2aTg016Lj1\!v}$Qj20!v>$Oj28Tg01MSj3CTg00[oj6ZTg01J8j1[Tg00LYj6;Tg01EQj4XTg00Nfj7^Tg00OJj7_Tg00PQj8`Tg00QSR0f1R1f0R23@p=4P1g00RXR3g00S7R4P4g00SWR5P2g00T7F^p=<f2R6P3P4P4P5P1P2F_p=?f3R7!s;+6P1P2G`p=Ag00U>R8#5R9#DR:%78#7#7#7R;#DR<'HR=#eR>1112R?'213?='6P0%59#5#5#5R?#9R@1161RA'B1176RB,42X4012>ARC13A=RD1E:<REg00Q5RF/3:RG12F<13F=[RH[RI12F:RJg00gVRKAd:<1UW5R<12F=\K^5JRJ!un$Uc1]F:':PGeO1RGPHp-0RKg00VIRL#YRM%WLRLP01V06P1%U0CTRN%P0RO%N0RPP01M0:%9;5L0R;,K0g00R11=081=095J0R9C>,<PR8PP!vH'f4R3EIR:5?P%G4R4P8CA1FP5R5P2P6g00XgR8g00YGRQ':1O26=@8QdAQ0F1CRRFb7b9b:X20X30W01121RQ,2>/661116R8,2>[^20^30^0KP2f6RRf5RS'1RT/3=PSPRP3O4b6b1b8b1PCePEPIP<PJPGPHPMPLPNPOPPP0P9g00X@P;!u9%;9?P:P4P;CAP5P!tU0X0K13Q=,66138=!tL/12>T!tA4DeCS16CDe,cA%5?#9R?1b?1'aR?,16RD,B@P@PDPAP0%\@RC,06R310?C'1/0CRR10BC!y&'RSP018@1RT107C/12/0C/4BX40P010ACRBPS1:0B101C,13/0CAC61CEZ113T!sR%e18@?%[1E;14RBe10DCAC6?CE;18@D18@A'4eCXE;W;X<0X=0o"). Qed.
  Ltac norm_s32 ::=
    repeat match goal with
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?a) + bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_2 a b) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?a) - bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_sub a b) by lia
    | |- context [bv_swrap 32 (?k - bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_rsub k b) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) + ?k)] => rewrite (swrap32_of_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b) * ?k)] => rewrite (swrap32_mul_u64 b k) by lia
    | |- context [bv_swrap 32 (bv_unsigned (Z_to_bv 64 ?b))] => rewrite (swrap32_of_u64_0 b) by lia
    | |- context [sx32 (Z_to_bv 64 ?b)] => rewrite (sx32_ssmall b) by lia
    | |- context [bv_swrap 32 ?x] => first [rewrite (swrap32_id x) by lia | rewrite (swrap32_id_m64 x) by lia]
    | |- context [Z.lxor ?w 18446744073709551615] => rewrite (lxor_m1_64 w) by lia
    | |- context [bv_unsigned (b8 ?x)] => rewrite (b8_unsigned x) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 1)] => rewrite (land1_small a) by lia
    | |- context [Z_to_bv 64 (Z.land ?a 7)] => rewrite (land7_mod8 a) by lia
    end.
  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
  Lemma land223_range : ltac2:(zQ "50!hne!p7!s7!h9!r0>1x$3>0@2$1Z^1@2$2@2$1Z@2$0^2+tf@2$4@2$0^2+tf+hg0").
Proof.
ltac2:(KReplay.run1 (kr_t_W_bpesc0 ()) [] "h07__arithh14__ffh28__varmaph35__with42Hah56__sat1h64__x1h72Hxh86__sat0h91xh:1zp;1p;2p;4p;3p;8p;5p;6p;7g003nj11Tg000Nj10Tg0013j14Tg01;ej2:Tg007Nj23Tg008mj28Tg0053j2BTg00@ij1@Tg00Aij1?Tg00Bgj1>Tg00Ccj1<Tg00DAj1;Tg00Dlj27Tg00EOj46Tg00HFj2TTg00;5j29Tg00Hhj2STg00ITj3RTg00Inj3QTg00JMj4KTg00_\j2ATg00`Dj3CTg00:Tj2DTg00^1j1ETg00`hj3FTg00cRj4GTg00BIj2HTg00Gcj2ITg00F:j1JTg00PQj8=Tg01N3j5LTg01O=j2MTg00LYj6NTg008Qj2OTg00Nfj7PTg00Q5R0f0R1'Op=2f1R2g00RXR3g00S7R4P4g00SWR5P1g00T7FPp=5g00QSR6%21R7P6g00U>R8#1#0#1#1#1#1#1#4R9/:2%08R:#0#0R;#0#0#0#0#0#4,31,87X:6P9P2%4;R<%29R=%4:R:/B<R>,39R?g00VIR@#@RA%?@R@%>6RB%<6RC%;6RDP61760REg00R1RF1769RGC6'51TD5RHP1f2RIg00XgRJg00YGRK'91S1I=RJKdAQ602CKRKb1b2b3P=P1b0P=e1A:<130:RJ%2<130>[RL[%2:RMg00gVRNAC:<2UW4%2>\N^4MP2g00Uc1D0:'9PJeO1PLPAP@PBPCP6PGg00X@176:%E;5F6C6,5DPHPKb1b2b3P?P1b0b5b8b5P?eCG18=?ePAP@1H62PCPDP3P4P4P5P6PEPF1I68C6,5DRD%J4PDG=PHPKb1b2b3X66%22RK\7^66P1PIP2O2b0PKeDL1:291M29ENW7W9o"). Qed.
  Lemma land255_range : ltac2:(zQ "50!hne!p7!s7!h9!r0>1x$3>0@2$1Z^1@2$2@2$1Z@2$0^2+vf@2$4@2$0^2+vf+hg0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##1Rh07__arithh14__ffh28__varmaph35__with42Hah56__sat1h64__x1h72Hxh8!s;%0h91xh:1zp;1p;2p;4p;3p;8p;5p;6p;7g003nj11Tg0013j13Tg01;ej29Tg000Nj10Tg007Nj24Tg008mj28Tg0053j2BTg00@ij1@Tg00Aij1?Tg00Bgj1>Tg00Ccj1<Tg00DAj1;!s/$lj27Tg00EOj46Tg00HFj2TTg00;5j2:!s8$hj2STg00ITj3R!s/$nj3QTg00JMj4KTg00_\j2ATg00`Dj3CTg00:Tj2DTg00^1j1E!sA$hj3FTg00cRj4G!tg$Ij2HTg00Gcj2ITg00F:j1JTg00PQj8=Tg01N3j5LTg01O=j2MTg00LYj6N!ur$Qj2OTg00Nfj7PTg00Q5R0f0R1'Op=2f1R2g00RXR3g00S7R4P4g00SWR5P1g00T7FPp=5g00QSR6%21R7P6g00U>R8#1!s$03R9/92%08R:#0#0R;#0!s$+3,41,87X:6P9P2%3;R<%29R=%3:R:/B<R>,49R?g00VIR@#@RA%?@R@%>6RB%<6RC%;6RDP61760REg00R1RF1769RGC6'51TD5RHP1f2RIg00XgRJg00YGRK':1S1I=RJKdAQ602CKRKb1b2b3P=P1b0P=e1A:<140:RJ%2<140>[RL[%2:RMg00gVRNAC:<2UW4%2>\N^4MP2g00Uc1D0:':PJeO1PLPAP@PBPCP6PGg00X@176:%E;5F6C6,5DPHP!tF'?P1b0b5b8b5P?eCG18=?ePAP@1H62PCPDP3P4P4P5P6PEPF1I68!si$RD%J4PDG=!sr,X66%22RK\7^66P1PIP2O2b0PKeDL19291M29ENW7W9o"). Qed.
  Ltac wrange w := try (let H := fresh "WR" in pose proof (bv_unsigned_in_range _ w) as H; unfold bv_modulus in H;
                        change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in H).
  Ltac zpos x := lazymatch x with bv_unsigned ?w => wrange w | _ => idtac end.
  Lemma land223_255 : ltac2:(zQ "30!hne!h9!j0>1x$1@3$2$1@2$0^1+tf@2$0@2$0^1+vf+tf").
Proof.
ltac2:(KReplay.run1 (kr_t_W_bpesc0 ()) [] "h01xh11zp;1p;2p;3p;6g003nj12Tg0013j13Tg000Nj14Tg01;ej21Tg00ITj38Tg00;5j27Tg01O`j35Tg00[oj66Tf0R0#2#2p=0g00QSR1P1g00U>#2R2#0#0#0#3R3%42#2#0#0#3R2'1,10R4f1/12=810X1117141103/12A5032E6W0o"). Qed.
  Lemma lor_m1_l : ltac2:(zQ "60!h9!s7!j0!p7!hof!r0>1y$0>0@2$1@2$3Z^1@2$5^1+hggggggggggggggg0@3$2$0@2$4+vvvvvvvvvvvvvvvf^2+vvvvvvvvvvvvvvvf").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##B0p'0h04__x1h17__arithh24__ffh38__varmaph45__with54__p1h62Hyh71bh81Hh92Hah:1Lh;6__sat1h<4__x2h=1si001sh>1yh?2Hnh@2LGhA2NZhB!sR%0hC1ei011ehD1ni021nhE1zi031lp;1p;2p;3p;4p;6p;7p;8g000Nj11Tg0013j1ATg007Nj20Tg008mj2;Tg003nj12Tg01PDj2J!s/$aj25Tg01QBj2>Tg00ITj37!s8$_j2p!se$Qj29Tg01RFR0j2MTg00;5j2BTg01;Gj1aTg00@ij1`Tg00Aij1^Tg00BIj2PTg00Ccj1[Tg00DAj1Z!s/$lj2@Tg00Gcj2KTg00F:j1XTg00HFj2U!s/$hj2T!t`$nj3STg00JMj4HTg00cRj4I!t`$fj3RTg00LYj6Cj7uTg00[oj6QTg01SMj2wTg0061j1G!s8$mj18!tj$gj1vTg0053j2tTg00EOj4F!tX$\j6oTg00bnj6nTg01TKj3hTg00_\j2gTg00`Dj3fTg00:Tj2cTg00^1j1d!sA$hj3eTg01U1j4b!vJ$Oj1LTg00=Vj2ETg00N=j3OTg00>?j2i!vS$Ij3j!vJ$Ej4k!se$Lj4lTg01V5j3m!s/$]j3]Tg01W?j3q!sn$fj7rTg00PQj8\Tg00OJj7sTg00Q5R1f0R2'9p=6%12#1#1#1p=_!s2$p=W!s:+!s$'p=:%22#2p=Y!s-$#!s2$V!s2+!s$'p=<g00QSR3f1R4g00R1P2CFp=?P!s4$XR5g00S7R6P6g00SWR7P2g00T7Frp=3f3R8P5P6P6P7f2R9P4P2G\p=4P3!sf$X@!st%=A7321p=DP9!sU'P4P2Fsp=N%62R:g00U>R;#1R<#1#_R=#W#:!s$0AR>,02R?';R@%2;#Y#V#<!s$0ARA/J!tD$gRB15A41584'>15A997B2X7B%A=RC,p4104CRD19C4RE'MP0109C19C9RF15A8RGf5RH/58'>=7BGP2108C1B3ARG%aCRI=73ARJP3PIf6RK,52RLf8RM/5KRN!sY$LXE3RLPBg00YGRO1>2N=!tO%RP1BBORQ15IHRR%6HRS10HC!{\$VIRU#`RV%^URW1P34RX%[3RY%Z3RZ1@31R[1K3;R;'?,3ZR\%X6R]P\C41UZ7R^P2P9PQ1T29=7BOdAS314ROCHR_b2b3b4X03%64R`\:^03P2PKPHO2b1PSePVPWPXPYPZ1@3CRa,=;,3ZRbP]PbC4P^P!sh,102CRcPD[!sj'9O2RDb1PTeCI1;STe9RCHECPAP2EQb8W:P2O119C8PGP!vQ$P!v6$1WbRLPPf7RP/w1%DPRI%GI'MP0%DMR0%G0f9R0#8RI/0CP2%D0!w7$1%84/0C^6@X>31911101>';PVPW%v3R@PY1=[a,3Z!u',101CRGP2b1PGe%81/0CeW6f:RGP2P0FuWCP2O1%GJ%A<RJ/tCRT,0GRSf;Rd#8/0C[%8G/0C10dT[p-0R!vM-PZ!{3+3P;g00TWP[CF,3ZEoP]!sF08EnR79NZ\R6P]1=[;,3ZC4!v|$!w~$POCH!w++W5%D2g00Yg[1;`91019[[^03^5eP210d>PdP4PGO4b19hGC1gJC101JRG%6CRd101T[RO[%6JRQg00gVR5AfJC4UW9%6T\5^9Q!}S$Uc1c1J'BPGeO1PO!xu0>!xs%9NZ7P]1@3J%d=5e3!s<%!y'2X5e1;4?104T!tt+f>RT#6PTf=O3b1b;bBb;PSeCbWAP2O1n20011000002!x4$11102b=%8P/0CPBPL1>L2!|Y$7B1BBLPNPMPK!wA-6P!{b$!tW5:4P`!vK-0>P0PMO3b1%6Meg00W5R0#LR>#L,E31E3>1E305O35O3g00WT'i=jUVPWP31P39P4P@Ck!t@$bP]PZ1K3<R<,?!y{$]1=;<!x7,!tW-<31098\F\c^03^<3P2PPPIP4P8O4b1%8M/0KeClECb@PRPd19CHRR!uT$@PY1?!{&2Pd!z~$d!}`/?a!}[$ZP]P!wV319C2PE!}Y$Db1PR!}Q$dRe9m!}Q5!wO33!s'$b=1JA8/54A]A84ECX?:XD37qAW6X>3o"). Qed.
  Lemma lor_m1_r : ltac2:(zQ "60!h9!s7!j0!p7!hof!r0>1x$0>0@2$1@2$3Z^1@2$5^1+hggggggggggggggg0@3$2$0@2$4^2+vvvvvvvvvvvvvvvf+vvvvvvvvvvvvvvvf").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##&Ch02Hxh11xh21zp;2p;1p;3p;6g008Qj2>Tg0013j14Tg007Nj26Tg008mj2=Tg003nj10Tg01PDj25Tg00ITj38Tg01XBj29Tg01YKj2:Tg00LYj6<Tg000Nj11Tf0R0#1!s$1p=2%00#0p=;!s-$#!s2$7!s2+!s$'p=3g00QSR1g00Q5/>0g00U>R2#!s$34,60'=P1%02#;#7#3!s$04R2f1R3'5A8102X21193015321:32E<W0W1o"). Qed.
  Lemma lor_bound32 : ltac2:(zQ "51!s7!p7!r0!h9!hof&@2$0@2$1Z^2@2$2^2+hggggggg0>1x$3>1y$3>0~0>0~0@2$0@2$1Z@2$4^4^3@2$2@2$4^4^3+hggggggg0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##%,h02Hxh12Hyh21xh31yp;2p;1p;5g008Qj27Tg000Nj10Tg0013j12Tg007Nj26Tg008mj25Tg01Ymj54Tf0R0#!s$&p=1%0!s-$3g00QSR1g00Q5f1R2'7g00U>#0#1R3#0#3#1!s$-2,62'5R4f3f2%23P2P0D4X14W0X31W2o"). Qed.
  Lemma shiftr_small0 : ltac2:(zQ "70!h9!p7!s7!j0!r0!s1!hp5>1x$0>1n$0>0@2$1Z^1>0@2$2@2$1Z^3@2$4^3@2$5+2^2@3$3$0@2$6^4^3Z").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##3}h06__sat1h14__x1h24__p1h37__arithh44__ffh5!sN%0h68__varmaph75__with82Hah94__x2h:2Hnh;2Hxh<1nh=1xh>1zp;1p;2p;3p;4p;6p;7p;8g000Nj1XTg0013j1DTg0053j22Tg007Nj20Tg008mj23Tg0021j2ETg00ITj36Tg00_\j2BTg00`Dj3ATg00:Tj2@Tg00;5j2;Tg00@ij1=Tg00Aij1WTg00BIj2<Tg00Ccj1UTg00DAj1O!s/$lj2NTg00Gcj2:Tg00EOj49Tg00F:j1CTg00HFj2F!s/$hj2G!t^$nj3HTg00JMj4I!t1$gj1J!t1$Ej4KTg00cRj4?Tg01[6j3LTg004Sj2MTg00L0j3>!s/$Yj6P!ui$Qj2QTg00Nfj7RTg00bnj6STg00OJj7TTg00PQj8VTg00Q5R0f0R1'Qp=1f1R2g00RXR3g00S7R4P4g00SWR5P1g00T7FRp=7P2P3P4P4P5P1ESp=8f2R6!s9+2P1FTp=5f3R7!s;+6P2P1GVp=4g00QSR3%11R8%16R9g00U>R:#XR;#DR</22,06'3P312<6R=,E7A6310X>3%17R>107=R?1B<6R@100<RAf4RB,2<,00\>[RC%1<RDg00gVREf5RF=A<2UW8RG12<FRH#1\E^8DRDP2g00Uc1@0<';PAeO1RA%1B100H[RHp-0REg00VIRI#=RJ%WIRI1<32RK%U3RL%O3RMP31N30g00R11:3:R:C9,7MRN18M755M%C4R4PNC41FM5R5P1P6g00XgROg00YGRP';1G16=6OPdAH302CIR0b4b6b7X13W21382%12RP[^13^2EP1f7ROf6RQ,2<R<'0POPBO3b3b0b5b0P>eP@PCPGPDPAPHPJPIP31<36P2%J3CKPLPM18MBP3P:g00X@1:3;!u$%;55MP4P;C4P5P!tQ,X93X2E1012,361026!tW$9!tZ%%1OP<!tP$4!tP+?eC?13>?e9L7=1M76!t_4!tT$PNP!v6$!t;0PP\8^13P1PQPFO2!sz+9e9>76EPW;W:X<3W=o"). Qed.
  Lemma wrap32_small : ltac2:(zQ "70!h9!s7!j0!rb!p7!r0!ho5>1x$0>0@2$1@2$4Z^1@2$5^1+hggggggg0@3$2$0@2$6@1$3#i0^2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##2Jh04__p1h14__x1h22Hah37__arithh44__ffh56__sat1h68__varmaph75__with82Hxh9!sG%0h:1xp;1p;2p;4p;6p;3p;7p;8g000Nj10Tg0013j18Tg007Nj21Tg008mj23Tg00^1j1DTg0053j2<Tg00@ij1ATg00Aij1?Tg00BIj2>Tg00Ccj1=Tg00DAj1W!s/$lj26Tg00Gcj2VTg00EOj47Tg00bnj6UTg00F:j1FTg00HFj2CTg00;5j29!s8$hj2ETg00ITj3B!s/$nj3GTg00JMj4HTg00_\j2ITg00`Dj3JTg00:Tj2K!s8$hj3LTg00cRj4MTg01F`j1NTg016Lj1OTg01[Yj3P!ui$Qj2QTg00Nfj7RTg00OJj7STg00PQj8TTg00Q5R0f0R1'Qp=4%01#0#0#0p=2!s2$p=@f1R2g00RXR3g00S7R4P4g00SWR5P1g00T7FRp=5f2R6P3P4P4P5P2P1FSp=;f3R7!s;+6P2P1GTp=:g00QSR8%41R9g00U>R:#0R;#2R<#0#@#2!s$-8R=,11R>'3%D<R?%42R@%8;R;%8<R<'<RA,12RBp-0RCg00VIRD#ARE%?DRD1>82RF%=8RG%W8RHP81680g00R11V8:R:C7,5HRIPH!ts+7EUR75;H%F4R4PIC:1CH5R5P1P6g00XgRIg00YGR3'91E16=BI3dAG802CHR3b4b6b7X18W01392P@[^18^0CP1116=P6P2O3b3P@e1I;<110;R6%4<110A[R9[%4;!t+$gVRJAJ;<2UW2%4A\J^2IP2g00Uc1K0;'9P6eO1P9PEPDPFPGPHP8P:g00X@RG168=!uL$9;H7P4P8P:PG168;=L8?!s?$C:P5P!ty,X0C132>PB!tz+f5R1#4P1f4O3b3b5b9b5PBeCM13@Be%N?,<;,12,3@e%O?!s0&7P2W8W:o"). Qed.
  Definition hxeq : ltac2:(zQ "10!h9>1a$0>1b$0P") := ltac2:(zQ "20!h9!j0\1a$0\1b$0@3$1$0^2^1").
  Ltac hx_name_b t :=
    let b := fresh "bx" in let E := fresh "EQ" in
    pose proof (eq_refl t : hxeq t t) as E; set (b := t) in |- *; change (hxeq t b) in E; clearbody b.
  Ltac hx_name_h t :=
    let b := fresh "hx" in let E := fresh "EQ" in
    pose proof (eq_refl t : hxeq t t) as E; set (b := t) in |- *; change (hxeq t b) in E; clearbody b.
  Ltac hx_reuse R :=
    match goal with
    | E : hxeq ?t ?v |- _ => lazymatch R with context [t] => unfold hxeq in E; rewrite !E; change (hxeq t v) in E end
    end.
  (* [comment removed for export] *)
  Ltac pose_branges x :=
    repeat (match x with context [bv_unsigned ?b] =>
              lazymatch type of b with byte =>
                lazymatch goal with
                | _ : 0 <= bv_unsigned b < 256 |- _ => fail
                | _ => pose proof (byte_range b)
                end
              end
            end).
  Ltac hex_norm1 R :=
    first
    [ hx_reuse R
    | match R with
      | context [bv_unsigned (v_sltiu ?a ?b)] =>
          let u := fresh "u" in let H := fresh "U" in
          pose proof (sltiu_range a b) as H; set (u := bv_unsigned (v_sltiu a b)) in *; clearbody u
      | context [bv_unsigned (v_sltu ?a ?b)] =>
          let u := fresh "u" in let H := fresh "U" in
          pose proof (sltu_range a b) as H; set (u := bv_unsigned (v_sltu a b)) in *; clearbody u
      | context [Z.land ?x 255] =>
          first [ rewrite (land255_small x) by lia
                | zpos x; let H := fresh "BX" in pose proof (land255_range x ltac:(lia)) as H;
                  hx_name_b (Z.land x 255);
                  lazymatch goal with E : hxeq (Z.land x 255) ?b |- _ => unfold hxeq in E; rewrite E in H; change (hxeq (Z.land x 255) b) in E end ]
      | context [Z.land ?x 223] =>
          first [ let H := fresh "HX" in pose proof (land223_range x ltac:(lia)) as H;
                  first [ assert (x < 256)%Z by lia | fail 1 ];
                  match goal with T : (x < 256)%Z |- _ => clear T end;
                  hx_name_h (Z.land x 223);
                  lazymatch goal with E : hxeq (Z.land x 223) ?b |- _ => unfold hxeq in E; rewrite E in H; change (hxeq (Z.land x 223) b) in E end
                | rewrite (land223_255 x) ]
      | context [Z.lor 18446744073709551615 ?y] => rewrite (lor_m1_l y) by lia
      | context [Z.lor ?x 18446744073709551615] => rewrite (lor_m1_r x) by lia
      | context [Z.lor ?x ?y] =>
          pose_branges x; pose_branges y;
          let H := fresh "OR" in pose proof (lor_bound32 x y ltac:(lia) ltac:(lia)) as H;
          let o := fresh "ox" in set (o := Z.lor x y) in *; clearbody o
      | context [bv_wrap 32 ?y] => rewrite (wrap32_small y) by lia
      | context [bv_swrap 32 ?y] => rewrite (swrap32_id y) by lia
      | context [Z.shiftr ?x ?n] =>
          lazymatch n with 3%Z => fail | _ => idtac end;    (* [comment removed for export] *)
          pose_branges x;
          first [ rewrite (shiftr_small0 x n) by lia
                | first [ assert (0 <= x < 1099511627776)%Z by lia | fail 1 ];
                  match goal with T : (0 <= x < 1099511627776)%Z |- _ => clear T end;
                  rewrite (Z.shiftr_div_pow2 x n) by lia;
                  let v := eval vm_compute in (2^n)%Z in change (2^n)%Z with v ]
      | context [Z.shiftl ?x ?n] =>
          pose_branges x;
          first [ assert (-1099511627776 <= x < 1099511627776)%Z by lia | fail 1 ];
          match goal with T : (-1099511627776 <= x < 1099511627776)%Z |- _ => clear T end;
          rewrite (Z.shiftl_mul_pow2 x n) by lia;
          let v := eval vm_compute in (2^n)%Z in change (2^n)%Z with v
      end ].
  Ltac hex_norm :=
    repeat lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => hex_norm1 R end.

  (* [comment removed for export] *)
  Ltac prune_or K tac ::=
    lazymatch type of K with
    | boxP _ => tac
    | _ => first [ exfalso; unfold hxeq in *; lia | tac ]
    end.
  Ltac pose_branges_regs := try (lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => pose_branges R end).
  Ltac step1_hex := first [ achk | st1b | arm_inputs; st1b ]; pose_branges_regs; norm_lits; fold_sh8; norm_shpa; norm_s32; hex_norm; gen_data.
  Ltac step1_std := first [ achk | st1b | arm_inputs; st1b ]; norm_lits; fold_sh8; norm_shpa; norm_s32; gen_data.
  (* [comment removed for export] *)
  Lemma zext32_small : ltac2:(zQ "a0!rb!h9!s7!j0!p7!r0!hpe!hp5!v0!hg5>1x$1>0@2$2@2$4Z^1@2$5^1+hggggggg0@3$3$1@2$7@2$9@1$0#k0@2$8@1$0#k0@2$6^2+i0+i0^2").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##=kh04__x1h17__arithh24__ffh34__p1h48__varmaph55__with61zh72H0h82Hah96__sat1h:4__x2h;4__x3h<1Hh=2H1h>2H2h?2H3h@2HxhA!sU%0hB1qhC1rhD1xp;1p;2p;3p;4p;6p;7p;8g000Nj15Tg0013j1BTg007Nj22Tg008mj27Tg0053j2UTg006Jj21Tg00^1j1]Tg00eWj2OTg00f=j2NTg004Sj2CTg0021j2@!se$Pj2xTg00ITj3=!sn$1j1q!tC$Qj29!sS$Nj2S!sA$gj2e!tU$jj2d!tU$Qj2TTg009Hj2`!s/$nj2_Tg00:Tj2QTg00;5j2D!s/$Oj1HTg00=Vj2<Tg00>?j2A!s/$kj2P!sJ$nj1[Tg00<Lj2Z!s/$mj3YTg00?Wj2XTg00@@j3R!s/$ij1WTg00AIj3?!s/$ij1VTg00BIj2MTg00CEj4|!s/$cj1{Tg00DAj1z!s/$lj2;Tg003nj1yTg00Gcj2LTg00F:j1r!s/$\j6p!sA$@j3ITg00Onj3oTg00HFj2n!s/$hj2g!vb$nj3fTg00JMj4h!tU$gj1iTg00L0j3j!s/$Yj6JTg00bnj6kTg00_\j2lTg00`Dj3m!s/$hj3cTg00cRj4bTg01\Ej2aTg01]Pj2sTg01^0j3tTg00N=j3uTg00EOj4G!s8$fj7v!ty$Jj7wTg00PQj8^Tg00Q5R0f0R1'Tp=3%51#5#5#5p=6!s2$p=\g00QSR2f1R3;=1p=4Au231p=8P2P3g00R1P1CGp=>!s4%XR4g00S7R5P5g00SWR6P1g00T7Fvp=0!s[&X@!s[%Kf2R7P4P5P5P6P3P1Fwp=E!sK&TW!sK%Ff3R8!sK+7P3P1G^p=:%31R9g00U>R:#5R;#6R<#5R=#\#6!s$-BR>,21R?'7R@P2%B;RA%B<R<'URB,13%]=RC1OC1'N/C</47X62P2113>RD1C1!s8,@DB1417X621xD>A=2>0RB#q117>RE1@E>,1>19E>'S'4[1eE>120>RE118>RF/9>RG#312G>'7[1dF>12>0f4RG/1>RH/9>RI,2>1TI0'7[1`H>f5RH/1>RI/@>==20\B1_I>f6!s:%9>/4I\B1@I>P2f7/1>/9>P2PHg00UcRI1Q0>'DPEeO1P@g00VIR@g00W5RE#HRJ#HRK,<2RL1<2JRJ'81<2ERE/8Jg00WTRM'A'P%HK,<2%[:,Z2=Y2J1X2>RK=R2E'8'8/AM%W@RN5?@3?%V@ROP21M27P31M28C|%{2RP%z2RQ1;20RR%y:,L2RS'>,0Q1;2>RT,KS,0Q5EQ%r5RUPQ!s$$!xV&1FTR,0QEpPU1L2;R;=I2T1L2:R:9I2T=o2S'F,0QC:PU1F:;!s1$C:1nQ6R;P1P7g00XgRSg00YGRV'D1g17==SVdAf203ChRVb2b4b5X02X:2X;2%37127>RS'7g00Yg\B11>7/SG,4F[1478[[^02^:2^;2P1P7f:P8P3f8O5b1f9,47eb7bCbBb?b>b=b7b<1CD<PNPO%i2PP1;2<,>R,0QP;P!tJ&%3<RFP1b1PFeRF9jD<EJ1OCD,NC%3DR>%B=R=,UARB,2DRWp-0RX18EL/AM,PE=?@NPO1M23RLPPPQ1>R:,0!vb-P8EkR85EQPUAI2:TR6!tO%C:!tQ,X02W31793P>!uU$3XP1PSP7P3O3b1P>e1lA=120AR7%3=120B[RS[%3A!}1$gVRRAmA=3UW8%3B\R^89P31Q0A,DIP7eO1PSAR2KJ/8E/AM!u$%P!t|%K:T,0Q9EQ8PU1;2A=c2C,K6!tn5X3X173?PW!to+%3HPHPGO3b1b9bAb9PWeCb17>We,aDEJ1s3<At3<FEJW@XD2o"). Qed.
  Ltac norm_zext32 := repeat match goal with |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl ?x 32))) 32] => rewrite (zext32_small x) by lia end.
  Ltac step1_nodata := first [ achk | st1b | arm_inputs; st1b ]; norm_lits; fold_sh8; norm_shpa; norm_s32; norm_zext32.
  (* [comment removed for export] *)


(* [comment removed for export] *)
Lemma sh8_bound47 : ltac2:(zQ "60!p7!s7!n3!h9!p1!r0>1x$3>0@2$1@2$0Z^1@2$5^1+ogggggggggg0@2$1@2$0+nvvvogg0@1$2^2@2$0@2$4@1$2^2+1+hgggnvvvogg0").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##<\h04__p1h14__p2h24__x1h34__x2h44__x3h57__arithh64__ffh78__varmaph85__with92H0h:1zh;1Hh<2H1h=2H2h>2H3h?2Hxh@1qhA1rhB1xp;1p;2p;3p;4p;6p;7p;8g000Nj10Tg0013j19Tg007Nj24Tg008mj21Tg003nj1:Tg004Sj2[Tg002Nj23!sJ$Qj22Tg0053j2u!sA$1j2D!s8$Pj2qTg00ITj3<Tg0061j1i!s/$Jj2N!tC$Qj2@!s8$gj2a!tL$jj2`Tg009Hj2]!s/$nj2\Tg00:Tj2ZTg00;5j2M!s/$Oj1FTg00=Vj2CTg00?Wj2XTg00@@j3WTg00N=j3BTg00>?j2L!sA$ij1VTg00AIj3J!s/$ij1UTg00BIj2ITg00CEj4R!s/$cj1STg00DAj1TTg00Gcj2HTg00EOj4?Tg00F:j1t!sJ$lj2P!s8$\j6s!sS$@j3pTg00Onj3GTg00HFj2o!s/$hj2n!v>$nj3hTg00JMj4f!uN$nj1eTg00<Lj2d!s/$mj3cTg00cRj4g!ty$gj1bTg00L0j3j!s/$Yj6O!wI$kj1kTg00M7j1lTg00bnj6m!v+$fj7_!t^$Jj7^Tg00PQj8rTg00Q5R0f0R1'2p==%01#0p=>!s-$!s$/p=8%:1#:p=Y!s-$#:#:p=7!sN+p=Kf1R2g00RXR3g00S7R4P4g00SWR5P1Emp=Qg00QSR6/P1p=;P2P3P4P4P5P1g00T7F_p=5f2R7!s>+2P1F^p=Ef3R8!s;+7P2P1Grp=6P6P!t?$1P1C?p=A%=1R9g00U>R:#0R;#>R<#>#8R=#>#8!s$&9R>,41'1P6%::R?#9R@,[2RA%Y?#7!s$$0#>#K!sP$B'312B1%9:RC,31%7=!sI4='2'1X:6P6%9;/u@,D2131BRD,2B13DC/2=!sF$%9<R<,q2A<6<0RD#i1D7<,N<1@7<'39<67[1a7<140<RE1@8<RF#=14F<'1[1`8<14<0f4RF/@<RG,4<12G0'1[1]F<f5RG/D<=<60\D1\G<f6RH/@<=<6H\D1DH<P6f7/@<P6PGg00Uc1Z0<'MPEeO1141<,19137BR9,2BRE139C/2=R9p-0RIg00VIRJg00W5RK#FRL#FRM#F,C6RN1C6MRM1C6L1X6<1C6K5W65B6RK5B65B6g00WTRL'L%VJRO3J%UJRPP61I67P21I68CRRQ%S6RR%T6RS1QSGRGP61H6?R?g00X@RT%;<RUC?,5S5ES%t4RVPS!s$$!x~'6PUg00TWR41P60R3!sR$EsPV!so$;R;P41H6:R49p6U=G6?!sG$C6RUPVPS1A3;,5S1QSHRW5ESPV%;BRXAG64XRX'A!sQ$C6C61oS5R5P1P7g00XgR4g00YGRY'M1n17=<4YdAh602CfR0b6b7b8X26X36X46X0IW1147<RY,18g00Yg\D1N<7/3F9<68[RF%=8/1H138BR<,2B[[[^26^36^46^0I^1IP1f:RB/4>%=7RDP7PBP8P2f8R4f9RZO8b5PEe%e:,d6=c6M=B6K9B6N/LL=JJOPPPQPR!ud$?,5S=ESGPVPSP!uy$P6P;PT%;>!v7$9ESWPV%;C9G6X%;=!uy-P5P!uQ6X1I11D8148>,1H13<C/2=[\F!u85%=BPY!u1'P4P!u,%9eCg11E9eb9bAb@b>b=b<b9b;PAPOPP%b6PR%;@,A3,5S!tQ,%=@R0P1b5P0e9j2@EO%k2%l2EOW?XB6o"). Qed.

(* [comment removed for export] *)
Ltac shad_bounds ::=
  repeat match goal with
  | H : ro_cells _ _ (sh8 ?x) _ |- _ =>
      lazymatch goal with
      | _ : 2147450880 <= sh8 x /\ _ |- _ => fail
      | _ => pose proof (sh8_bound47 x ltac:(lia))
      end
  | H : rw_cells _ _ (sh8 ?x) _ |- _ =>
      lazymatch goal with
      | _ : 2147450880 <= sh8 x /\ _ |- _ => fail
      | _ => pose proof (sh8_bound47 x ltac:(lia))
      end
  | H : ro_cells _ _ (sh8 ?x + _) _ |- _ =>
      lazymatch goal with
      | _ : 2147450880 <= sh8 x /\ _ |- _ => fail
      | _ => pose proof (sh8_bound47 x ltac:(lia))
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AESCJT : Z := 0x256b0.
Definition esc_target : ltac2:(zQ "10!h9>1c$0$0") := ltac2:(zQ "30!hrf!h9!hs7\1c$1M0\0$0$1@2$2^1+if+hgnsl4M0\0$0$1@2$2^1+m6+hgnss4M0\0$0$1@2$2^1+m2+hgnsv8M0\0$0$1@2$2^1+lc+hgnticM0\0$0$1@2$2^1+me+hgntm0M0\0$0$1@2$2^1+n2+hgntp4M0\0$0$1@2$2^1+n4+hgnts8+hgnvr0").
Ltac ro_tbl_case4 MI :=
  match goal with |- ov_read_bytes _ ?m (Z_to_bv 64 ?a) 4%nat = Some (le4 (Z_to_bv 64 ?v)) =>
    let az := eval vm_compute in a in let vz := eval vm_compute in v in
    replace (Z_to_bv 64 a) with (Z_to_bv 64 az) by (apply bv_eq; vm_compute; reflexivity);
    replace v with vz by (vm_compute; reflexivity);
    let obs := eval vm_compute in (image_bytes asegs az 4%nat) in
    lazymatch obs with Some ?bs =>
      let RO := fresh "RO" in
      assert (RO : ro_cells asegs m az [CB 4%nat bs]) by (apply (ro_cells_image asegs m az bs MI); [vm_compute; reflexivity | lia | cbn; lia]);
      rewrite (ro_cells_read_at asegs m az [CB 4%nat bs] 0%nat (CB 4%nat bs) 4%nat (Z_to_bv 64 az) RO) by (first [reflexivity | cbn; reflexivity | unfold wa; f_equal; lia]);
      f_equal; apply byte_list_eq; vm_compute; reflexivity
    end
  end.
Lemma aescjt_read : ltac2:(zQ "h30!rb!hl5!hsd!ht5!ihe!im3!p7!hn1!v0!imc!s7!j0!h9!iqb!irc!isa!it1!p1!r5>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1c$c>0@2$h0$5^2>0@2$a@2$6+if^2@2$6^2+n4@3$b@1$3@1$2@1$1@1$0#8@4$d$5^4@2$8@1$0#k0@2$h1$4@2$h2+4@2$7^3+ifN4@2$9@1$2@1$1@1$0#8@1$f@2$8@1$0#k0@2$7@1$e^3$4").
Proof.
  intros m c MI HC.
  assert (K : exists k : nat, (k < 70)%nat /\ c = 47 + Z.of_nat k) by (exists (Z.to_nat (c - 47)); lia).
  destruct K as [k [Hk ->]].
  do 70 (destruct k as [|k]; [ro_tbl_case4 MI|]); lia.
Qed.
Lemma esc_target_cases : ltac2:(zQ "60!h9!j0!s7!irc!itc!hmc>1c$0@2$5@2$2@3$1$0@1$3^1+hgnsl4@3$1$0^1+if@2$5@2$2@3$1$0@1$3^1+hgnss4@3$1$0^1+m6@2$5@2$2@3$1$0@1$3^1+hgnsv8@3$1$0^1+m2@2$5@2$2@3$1$0@1$3^1+hgntic@3$1$0^1+lc@2$5@2$2@3$1$0@1$3^1+hgntm0@3$1$0^1+me@2$5@2$2@3$1$0@1$3^1+hgntp4@3$1$0^1+n2@2$5@2$2@3$1$0@1$3^1+hgnts8@3$1$0^1+n4@2$2@3$1$0@1$3^1+hgnvr0@2$2@1$4@3$1$0^1+if@2$2@1$4@3$1$0^1+m6@2$2@1$4@3$1$0^1+m2@2$2@1$4@3$1$0^1+lc@2$2@1$4@3$1$0^1+me@2$2@1$4@3$1$0^1+n2@1$4@3$1$0^1+n4").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##zpp'0h01Hh14__p1h24__x1h34__p2h44Heqbh54__p3h65Heqb0h7!s-$1h84__p4h9!s5$2h:!s-$3h;7__arithh<4__ffh=4__p5h>8__varmaph?5__with@!sY$4hA1bi001bhB!s7$5hC4__p6hD4__p7hE1mhF1nhG1xhH1yhI1cp%0p&0p;1p;2p;3p;4p;7p;6p;8g000Nj17Tg003nj1<Tg0013j1`Tg02;Fj22Tg00;5j2h!s8$cj2|!s8$nj1zTg00<Lj2y!s8$Oj1S!s8$mj3dTg00=Vj2cTg00@ij1sTg00Aij1pTg00BIj2oTg00Ccj1nTg00DAj1mTg00Gcj2lTg00F:j1kTg00HFj2j!s/$hj2iTg00Ink300Tg00JMj4~Tg0061j13Tg02<Cj2}Tg008mR0j21Tg01boj1w!s_$Tj3@Tg0115j29Tg00N=j3vTg00>?j2u!ts$Ij3X!ta$lj2tTg00EOj4b!sS$fj7aTg00OJj7eTg00bnj6rTg0155j7\Tg00PQj8g!u6$\j6{Tf0R1#<#<p=Ag00XgR2f2R3f1R4'2;@1p=K%71#7p=F%71#<p=O%<!s6$=%71#`p=8g00QSR5?@41p=0%33%34%31'1'1p=Gf4R6#3f3R7#3!sB%/1!sB$'1p=>f5R8=@56/17A@5!sB%9p=Lf6R9=@58/16A@573/14/9!sA$5g00YGR:9@21p=?1c51p=RAv541g00WT'up=Dg00VIR;?X41p=q1t51p=6P3g00RXR<g00S7R=P=g00SWR>P5P4g00TWR?P1Cbg00T7R@Fap=PP6P<P=P=P>P7!s0+5P3P?P4CbP@FaP1Fep=EP4!sE+1Erp=NP8!s7+6P7P3!s4+4P1F\Ggp=J1134/91p=T!vP'p=[!vB-p=_%37!vS0,16p=C1167!sc&'9p=41167!sJ%,13'9p=Ig01Wb!vA%BA@241p=WA@541#3p=:!t\3p=^1941,93p=Y!ui0!sO2F\p=;!t8%p=H!sZ&,97,96p=Z!tQ+p=fAX;419X;39X;79X;6p=M!vB0{p=Q!t,2ep=V!w,-3P4P1Ggp=U114!s}%]!s0$93p=xg00U>R<#7R@#<#AR?#<#`RA,21P21h21RBAK4A1P2AK7A1P2P5P4%7@#F#O#A#AR@#7RC#7RD#7#=!s$$8REP2P5%<<RF#7RG#7RH#A#8RI,26RJ%AD!sS$F!sQ$K!sQ$OH#8RH,26%<D#A#F#8RD!s?$7?#8R?!s?$C!t5$L#O#O!s`$M!t3%G!t%$G,26%AL#F!sb$L!sA$=FRF#O#8RN!sf+F!to&O!sG&#8RF,26%=C#O!s`$C%<@#A!t0$F#8R@n010!s#$20000!s4h1!s41RPPE106ARQPPPK106IRRPPPD106HRSPPPM106?RTPPPL106GRUPPPO106NRVPPPC106FRWPPP@PQPRPSPTAGUVWD>ELF5F5F5]4P4123ARW#?P01241RV#?1034RU[RT1041RR1234RP#?RX[1073RY\X1|41P4n20!t}'1!uB$000XE5XF5RXPT^E5^F5RTP1P6PAP4O3PQp-0RQ%z<,y5S00g00W5RZ#SS01#RS025d51c5ZS03'D%s;S04'qRZ%p;R;1o54R[%n5R\%m5R]1l5<R<%6A5P]R^%k=R=P]P]P]%6ER_P_P^DE1N]7R_EJ1j]>R>P1P31h2:1i13#?dg00Q5>0054C~R:b<b>b?X25W1101AS0510EER`104A;T3[^25^1QP110EKRa109IRb10EDRc109HRd10EMRe109?Rf10ELRg109GRh10EORi109NRj10ECRk109FRl10E@Rm109AS06PbPd1[jl9_fhDCD4D4D4P9P4O3b;P`108AR`Pa108IRaPc108HRcPe108?RePg108GRgPi108NRiPk108FRkPmP`PaPcPePg1[ikD>DI!t$%eb4b0W4%BW127IP2PB1WJ!}z$9I!}z&P!}0$f7RJ/2HRWP!|~$12J?PM!s0&GPL!s0&NPO!s0&FPCP!{{xRkPE10JARiPkPK10JIRgPkPD10JHRePkPM10J?RcPkPL10JGR`PkPO10JNRmPkPC10JFRhPkP@PiPgPePcAG`mh!{m-6P4128IRk#?PXPTP1PJPI!zq$gP0%BV%3U[RU%3R%BPRP[%3Y\P1}!{j<H5XG5RPPU^H5^G5RUP1f9RYPAP9O31:YAPZP;P[P\P]%6I9P]<RRP=P]P_!{$%KRVPVPR!{$$6RV5^]EJP>P!zd,X1QX3Q101IS0710KKR0104I'1=Y37!zk&^3!zn$KDRff;Rl/0HRj10KMRd10l?Rb10KLRn10lGRo10KORp10lNRq10KCRr10lFRs10K@Rt10lARu10lIPjPbPo1[qs!yf'10KERs/1uPlP7O4b;Psf:Rs/0ARuP010sIR0Pf10sHRfPd10s?RdPn10sGRnPp10sNRp10sFRqPuP0PfPdAGnpqD>Ro,1t5Tr!zs-b6b0W6%Bk129H!zw%W!zw$YH!zw'!zh&s?RW!zj's!zj+s!zj+s!zjnRkPEPuPkPKP0PkPDPfPkPMPdPkPLPnPkPOPpPkPCPq!z@$o!z3+7P4f8Ro/2H!z6-sPH!z6$fPPPUP1f<RfPI!yM%fI!s:&>RqPAPlO31:q!ya0H!ya$p!ya+V!#5i&DRnPnPp!yg$8RnD;!yf8X5Q101HS0810DDRd104H;T69!yj0^5!ym$DMR0f@Ru/0?S0910DLRr10uGRt10DORb10uNRj10DCRv10uFRw10D@Rx10uARy10uIRz10uHS0:Q09AGtjwD>S0;'1!yl%DKR{/1z10DER|/1yPuP8O5b;P|f?R|/0AR}P{10|IR{Pd10|HRdP010|?R0Pr10|GRrPb10|NRbPv10|FRvPxP}%3dRdP0PrPb%3vDC,H{!#5n/b6b0b7b0W7!y}$Y?!y}/f?!y}'!yq$f=RW/2GS0<!yw'W!yw+W!yw`!#5G$WAR{!#5G$WIRv!#5G$WHRb!#5G$W?Rr!#5G$WGR0!#5G$WNR}!#5G$WFRx!z,${PvPbPrAG0}x!#5G,9P412l?S0=!z8+WP?!z8$r!y|%P|PHP9O3Pd!z4&ARdPI!z4%d!zH'CRrPAPuO310rAS0>#3S0?!zP/?!zP$x!zP0n!zR%MR}P}Px!zR$9R}5^]!zU=X8Q101?S0@P3P7P610MMS0A104?'1P8DZ!z^0^8!za$MLS0BfER0/0GRb10MOS0C100NRv10MCS0D100FR{10M@S0E100AS0F100IRk100HR~100?%3bS0G%3{7fv'H3_DID410MDRv/1~10MKR~/1k10MERkQ0F'1P0PJO6b;PkfDRk/!s{$P~10kIR~Pv10kHRvQ0A10k?S0AQ0B10kGS0BQ0C10kNR{Q0D10kFRbQ0EQ0F%3v!sW$Q0BP{%3bDC,H~!zs8b9b0W9Q0=#B12fGP2PBQ0</!z{%|G!z{'!zk&uNS0<!zn'u!znRR~PEPyP~PKPzP~PDQ0:P~PMQ09P~PLPtP~POPjP~PCPwP~P@Q0;!z:+:P412qGS0;!z:+uPG!z:$t!yn&BRtP?!#5L$t?!zN&kPHPlO3Pv!sJ&FRvPI!z:%vIS09#3S0:!sB&HR~PAP0O31:~!#5x/G!zN$w!zN4}!#6$&LRjPjPw!zT$JRjD;!zS@X=Q101GRz!zU%P810LLS0=104G;T9!zV5^=!zY$LOS0BfJRy/0N!{-$LC!z9$yF!zG$L@!z[$yA!zo$yIS0H10yHRb10y?R{1:yGS0I!y&$E#33f'HDCD410LMS0A/1{10LDS0E/1b10LKRbQ0H'110LER{Q0C'1PyPYO7b;P{fIR{!za$CPb10{IS0HQ0E10{HS0E!zd${!zd%=10{GS0=!zn${N!zn$F10{!ze$DQ0CQ!s`$#3!s^%Q!sP$!zl$'H!zk<b:b0W:Q0;#B12|N!zo1tN!zo'!zb&rFS0<!zeCR|PEQ0>P|PK10rIS!s1$D10rHS0;P|PM10r?S0HP|PL10rGS0BP|PO10rNRbP|PC10rFS0=P|P@Q0?Q0>Q0;!uR$BQ0=7GbDC!{/+@P412dN!#6C-rPN!{/$b!zs&0PGP9O3Q0G!zX&GRbP?!#6D$b!{@'{PHPuO3Q0E!sK&KR{PI!z}%{!#6i&MR{PAPy!s:$!{90N!{9${!{98j!{;%ORbPbP{!{;$oS0E5^]!{?EXCQ101NRb!{B,OOS0G104NS0B'1=Y9J!{H8^C!{K$OCS0HfORr/0FS0;10O@S0>!#8x$?!wc%A!w_%C10r?Rd10rGR|10rNQ0;'[D>DI10OLS0;/1|10OMS0D/1d10ODS0F!{0$10OKRdQ0A!s1$ER|Q0?'1PrPlO8b;P|fNR|!{F$?Pd10|I!{2$F10|H!sh$D10|?S0DQ0;10|GS0;Q0G10|NS0GQ0H10|FRd!xr$?!{;$F#3!s^%!y'$G%3d!{FDb@b0W@!#7;%tF!{J10F!{J'!{=4R2PE10vARBP2PKQ09P2PD10vHS!s1$M10v?S0<P2PL10vGS0=P2PO10vNRtP2PC10vFRdP2P@Q0:Q09Q0<Q0=%3dS0=,HtDC,HB!{0+BP412kF!#E^,vPFP4O3S0<!#>?&P~PNP9O3S091:~N!#6k'PyPGPlO3!vy$!zl'LR~P?PuO3S0G1:~?S0;!#?=,0O3!w;$F!sT&PR0PIPyO3S0?1:0!}l$!s@%RR0PAPrO3S0H1:!#4W$!{b-F!{b$<!{b;Q0E!#7~&CRZPZP<!{i$YS0JD;!{hHXDQ101FRZ!{k,CCR6104F;To9!{h>^D!{k$C@R9fTR0/0ARr100IRy100HR|100?R~100GRu100NRd100FRv'[3_DC10COS0K!{T$CLRT/1u10CMRX/1~10CDRB!{y$CKRt/1y10CER2/1rP0PWO9b;P2fSR2/0ARAPt102IRIPB102HRHPX102?RXPT102GRTQ0K102NRN102FR2PAPIPHPXAGTN2D>RF,195T6!{GBbBb0WB%BkPPPU!z$%!s0%9Q!y=%Q!y3+Q0GQ!x{%Q!xq+!|m$!xa$Q0HQ0CQ01#SRU#SRP#SRk#SR6#SR9#RQ00Q035d5RB'DRtPt%Rk/DBRkP!s$%t!s$&!s6&Q02/DBP!sN$P/DBRPPPPP%RU/DBRUPU!sV'%R6/DB%S9#R/DBQ04DM!s$/!z-'1Q!z''1Q]{!#6q$1Q]w!#?6$1Q]x!#Fh$1Q]p!#ND$1Q]R!#U1$1Q]^R^!zg@Q0J!zj%@RjPjAV]{<9V]w9V]x9V]p9V]R9V]^DE!zz'CU!s$,!{-Eg00YgR:\ZQ0BP:[103G!s,$7?P:[P:\SP:\aQ06P:[PoPYPsPl10@@RsP:\iP:\gP:\eP:\cP:\`P:\mP:\h3]3]3]5xq9YfWDZ[!s#%!{w?@CRQ/1v10@ORv!{F$@LRd!{F$@MRu!{F$@DR~!{F$@KR|!{F$@ERy!{F&PlPYPJP8P7P4O?b;PyPAP|PIP~PHPuPXPdPTPvPN11sF9TQ2!zyHn0110001020101P1O1bBbAW@!s>6@bAW:!s>6:bAW9!s>69bAW7!s>67bAW6!s>66bAW4!s>64bA%w1R1PEQ05P1PKQ07P1PDQ08P1PMQ0@P1PLPzP1POPbP1PCPZP1P@Q05Q07Q08Q0@AGzbZ!#Om+eXI5o"). Qed.

(* [comment removed for export] *)
Definition saved13 : ltac2:(zQ "40!rb!hl5!hsd!jhe>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0@1$2$3") := ltac2:(zQ "60!jhe!ji6!rb!jie!hl5!jj4\2ra@1$4@1$2#k0\2s0@1$4@1$2#k0\2s1@1$4@1$2#k0\2s2@1$4@1$2#k0\2s3@1$4@1$2#k0\2s4@1$4@1$2#k0\2s5@1$4@1$2#k0\2s6@1$4@1$2#k0\2s7@1$4@1$2#k0\2s8@1$4@1$2#k0\2s9@1$4@1$2#k0\3s10@1$4@1$2#k0\3s11@1$4@1$2#k0@3$1$0@1$3^1@3$1$0@1$3^2@3$1$0@1$3^3@3$1$0@1$3^4@3$1$0@1$3^5@3$1$0@1$3^6@3$1$0@1$3^7@3$1$0@1$3^8@3$1$0@1$3^9@3$1$0@1$3^a@3$1$0@1$3^b@3$1$0@1$3^c@3$1$0@1$3^d@1$5$0").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pecore : ltac2:(zQ "40!h9!rb!jn8!hl5>1r$2>3sp'@1$3@1$1#k0>3s0v$0>2ff$0>1c$0P") := ltac2:(zQ "h30!rb!hl5!j0!s7!v0!h9!jne!jo5!joc!jp4!jpb!jq2!jq9!jr0!jr7!jre!jn8!n3!p1\1r$h0\3sp'@1$1@1$0#k0\3s0v$5\2ff$5\1c$5@2$3@3$2@1$1@1$0#k0@1$f^5^4@2$3@3$2@1$1@1$0#k0@1$7^5^4@2$3@3$2@1$1@1$0#k0@1$6^5@2$4@1$0#k0^3@2$3@3$2@1$1@1$0#k0@1$9^5@2$4@1$0#k0@1$h1^2@2$3@3$2@1$1@1$0#k0@1$a^5@2$4@1$0#k0+9@2$3@3$2@1$1@1$0#k0@1$b^5@2$4@1$0#k0+nvvvogg0@2$3@3$2@1$1@1$0#k0@1$c^5@2$4@1$0#k0^1@2$3@3$2@1$1@1$0#k0@1$d^5@2$4@1$0#k0@2$h2^2+i0@2$3@3$2@1$1@1$0#k0@1$e^5@2$4@1$0#k0+1@3$2@1$1@1$0#k0@1$8^5@2$4@1$0#k0+vvvvvvvvvvvvvnvf").
(* [comment removed for export] *)
Ltac open_pecore PC := box_post; destruct PC as (?C1 & ?C2 & ?C3 & ?C4 & ?C5 & ?C6 & ?C7 & ?C8 & ?C9 & ?C10).

(* [comment removed for export] *)
Definition peframe : ltac2:(zQ "50!rb!hl5!h9!hsd!kg2>1m$4>3sp'@1$1@1$0#k0>3j40@1$3@1$1@1$0#8>2pa@1$1@1$0#k0>2ta@1$1@1$0#k0>1e$2>3isk$2>2ff$2>3j16@1$3@1$1@1$0#8P") := ltac2:(zQ "h10!rb!jhe!ji6!jie!v0!hl5!p1!hg5!h9!hsd!kg9!jj4!im3!kg2!kka!hn7!hn1\1m$d\3sp'@1$5@1$0#k0\3j40@1$9@1$5@1$0#8\2pa@1$5@1$0#k0\2ta@1$5@1$0#k0\1e$8\3isk$8\2ff$8\3j16@1$9@1$5@1$0#8@4$e$c^9@2$7@1$0#k0^8@3$2$1@2$aNi8^7@3$2$1@1$3@2$4@1$0#k0+vvvd@3$2$1@1$3@2$4@1$0#k0Z@3$2$1@1$3@2$4@1$0#k0@2$6@2$7@1$0#k0^6+qc@3$2$1@1$3@2$4@1$0#k0@2$f^3+d@3$2$1@1$3@2$4@1$0#k0+vvvvvvvvvsqgikg0@3$2$1@1$3@2$4@1$0#k0^4@3$2$1@1$3@2$4@1$0#k0@2$6@2$7@1$0#k0^6+l8@3$2$1@1$3@2$4@1$0#k0+nvvvvvve@3$2$1@1$3@2$4@1$0#k0@2$6@2$7@1$0#k0^6+q8@3$2$1@1$3@2$4@1$0#k0^3@3$2$1@1$3^5@3$2$1@1$3@2$4@1$0#k0^2@3$2$1@1$3@2$4@1$0#k0^2@3$2$1@1$3^6@3$2$1@1$3@2$4@1$0#k0@2$h0+vvvvvvvvvvvvvvvf@2$6^2+i0@3$2$1@2$aNh0^1@3$2$1@1$3@2$4@1$0#k0^2@1$b$1").
(* [comment removed for export] *)
Definition pesize : ltac2:(zQ "20!h9!kg2>1m$1>2ff$0>2sz$0P") := ltac2:(zQ "b0!h9!jhe!ji6!jj4!rb!im3!kg2!jie!kka!p1!v0\1m$6\2ff$0\2sz$0@4$8$5^3@2$9^2+hi0@3$2$1@1$7@2$a@1$4#k0^1@1$3$1").
(* [comment removed for export] *)
Definition pecells : ltac2:(zQ "50!rb!hl5!hsd!h9!kg2>1m$4>2pa@1$1@1$0#k0>1e$3>2sc@1$2@1$1@1$0#8>3u1w@1$1@1$0#k0>3u2w@1$1@1$0#k0P") := ltac2:(zQ "h50!jhe!rb!ji6!jj4!im3!p1!hl5!hg5!s7!n3!kl6!klc!km2!kka!kq9!hsd!h9!kg2!jie!kg9!v0\1m$h1\2pa@1$6@1$1#k0\1e$h0\2sc@1$f@1$6@1$1#8\3u1w@1$6@1$1#k0\3u2w@1$6@1$1#k0@2$8@4$d$4^6@2$5@2$7@1$1#k0^5+q0@3$2$0@2$h3N8^3@3$2$0@1$b^2@3$2$0@1$b^1@1$3$0@2$8@4$d$4^6@2$5@2$7@1$1#k0^5+r8@3$2$0@1$h2@2$h4@1$1#k0^4@1$3$0@2$8@4$c$4^6@2$5@1$9@2$7@1$1#k0^5+h5@3$2$0@1$a@1$eZ@1$3$0@4$c$4^6@2$5@1$9@2$7@1$1#k0^5+h7@3$2$0@1$a@1$eZ@1$3$0").
Ltac open_pecells PM := box_post; destruct PM as (SCR & END & PS21 & PS23).
(* [comment removed for export] *)
Definition petot : ltac2:(zQ "40!rb!h9!kg2!hl5>1m$2>2ta@1$3@1$0#k0>3tot$1P") := ltac2:(zQ "h10!rb!jhe!ji6!jj4!im3!hg5!s7!h9!n3!kg2!kl6!jie!km2!kka!kq9!v0!hl5\1m$9\2ta@1$h0@1$0#k0\3tot$7@2$6@4$d$4^3@2$5@1$0#k0^2@3$2$1@1$b@2$f@1$0#k0^1@1$3$1@4$c$4^3@1$8@2$5@1$0#k0^2@3$2$1@1$a@1$eZ@1$3$1").
Ltac open_petot PT := box_post; destruct PT as (TOT & TSH).
(* [comment removed for export] *)
Definition ptsh : ltac2:(zQ "20!h9!kg2>1m$1>2ff$0P") := ltac2:(zQ "f0!rb!h9!p1!hl5!imc!ht5!j0!n3!im3!kg2!kqf!kr6!kq9!p7!r0\1m$9\2ff$1>1x$1>0@2$d@2$2^2+i0^1>0@2$e^2@2$2^3+hi8@3$6@1$5@1$3@1$0#8@3$a$8^5@1$b@1$7^3@2$4@1$3@1$0#8@1$cZ").
(* [comment removed for export] *)
Definition pectx {HCEIL : HeapCeil} (sp' : word) (s0v : Z) (pa ta : word) (ff fsb lo e p0 : Z) : Prop :=
  aceil <= lo /\ lo <= bv_unsigned sp' /\ bv_unsigned sp' + 288 <= s0v /\ (bv_unsigned sp' = s0v - 288 \/ bv_unsigned sp' = s0v - 304) /\
  s0v <= bv_unsigned ta /\ bv_unsigned ta + 8 <= AAPP_HI /\ bv_unsigned ta mod 8 = 0 /\
  aapp (bv_unsigned pa) 280 /\ bv_unsigned pa mod 16 = 0 /\ fsb + AFS_HDR <= bv_unsigned pa /\ bv_unsigned pa + 280 <= fsb + AFS_SIZE /\
  aapp ff 512 /\ ff mod 32 = 0 /\ fsb + AFS_HDR <= ff /\ ff + 512 <= fsb + AFS_SIZE /\
  (bv_unsigned pa + 280 <= ff \/ ff + 512 <= bv_unsigned pa) /\
  AIMG_TOP <= fsb /\ fsb + AFS_SIZE <= aceil /\
  0 < p0 /\ p0 <= e /\ e <= aceil /\ (e + 16 <= fsb \/ fsb + AFS_SIZE + 16 <= p0) /\
  (fsb + AFS_SIZE <= ALOWSH_LO \/ AHI_LO <= fsb).
Ltac open_pectx PX := box_post; destruct PX as (CEIL & ROOM & S0A & S0B & TA1 & TA2 & TA8 & APP & PA16 & PAF1 & PAF2 & APF & FF32 & FFF1 & FFF2 & PAFF & FSB1 & FSB2 &
                                    P00 & P0E & EHI & INF & FSIDE); unfold ALOWSH_LO, AHI_LO, AFS_SIZE in FSIDE.
Lemma ptsh_rd : ltac2:(zQ "h70!rb!hl5!hsd!p1!p7!ht5!h9!n3!imc!ji6!jj4!j0!iqb!krc!im3!kg2!lg2!lk9!ll0!ll9!kq9!r0!v0>1m$f>2mc>0@1$1@1$0#k0@1$5@1$1@1$0#8>1W@1$2$h1>2ff$6>1x$6>0@2$d^5^2>0@3$h2^4^6^5>0@2$h3^5@1$7^3>0@2$4@2$3^5+i0^4>0@2$h5^5@2$3^6+hi8>0@2$4Z^7>0@2$4@2$3^8+hi8$h0@3$b@1$5@1$2@1$1@1$0#8@4$c$e^b@2$h6@1$0#k0@1$7^8N1@2$8@1$2@1$1@1$0#8@3$9@1$1@1$0#8@1$h4Z@1$a@1$1@1$0#8").
Proof.
ltac2:(KReplay.run1z (kr_t_W_bpesc0 ()) [] "##?vh04__x1h14__x2h22Hah37__arithh44__ffh56__sat4h68__varmaph75__with84__p1h9!sI%3h:!s/%6h;2F0h<2FHh=1Hh>2MUh?3OUTh@1PhA1WhB2X1hC2X2hD!sZ%5hE2ffhF1mhG2mchH1ohI1xp;1p;2p;3p;4p;6p;7p;8g000Nj10Tg00^1j1ATg00ibj1KTg01^Yj1sTg00Aij1STg02<dj2eTg02=ij3aTg002kj1>Tg02>lj2^Tg0013j16Tg003nj13!sJ$Nj2=Tg007Nj22Tg00eWj2mTg02@1j1lTg0053j2ETg00_\j2CTg00`Dj3GTg00:Tj2_Tg00;5j2O!s/$Oj1NTg00=Vj2DTg00N=j3MTg00>?j2]Tg00@ij1\!u3$Ij3[Tg00BIj2L!s/$gj1ZTg00CEj4Y!s/$cj1XTg00DAj1W!s/$lj2JTg00Gcj2ITg00F:j1rTg00Onj3@Tg00HFj2q!s/$hj2pTg00ITj3V!s/$nj3oTg00JMj4U!uE$hj3HTg008Qj2;Tg00cRj4R!s8$mj2?Tg02A0j2kTg023\j1gTg02B9j3QTg01gMj2dTg00bnj6fTg02C8j7cTg00LYj6iTg02DAj4jTg00EOj4T!v5$fj7bTg00PQj8n!u3$Jj7`Tf0R0#0#0p=Bf2R1f1R2'=/;0p=5g00Q5R3!s3$1%0!sM$#0p=7%30#3#3#3p=9g00QSR4P2g00R1P0CTp=:!s4%XR5g00S7R6P6g00SWR7P0g00T7Fbp=41J40p=<f3R8P5P6P6P7P1P2P0Gnp=8P!sy%X@!sy%F!tB$p=hP1!sS+2P0F`p=Pg02EPg00U>R9#0R:#0R;#0R<#BR=#0R>#AR?#K%A<#KR<#sR@[g02FR#Sf4RA/e2f5RB=a8A%>1,^A%6=R==5A8%3;#0#3#0#B#6R;,=B,2Af6RC#1f7RDg02GS75;f:RE%>DRF,m?%l3RG%1DRH%6:RI%39RJ#7RK#6RL'ERM,2DRN%9:RO#6RP,CIRQ123IRR%1P1EIPRS,23[RT[RU%1IRVg00gVRWAGIP2UW2RP%1S\W^2VRX!v<$Uc1_3I'ORYPReRZO1R[PTg00VIR\g00W5R]#NR^#N,D41D4^1D4]5M45M4g00WT']%\\R]3[R^%S\R\P41L41P2%Z4CYR_%X4R`%W4Ra1J43Rb1I4:R:':,4a%r6RcPa%<=Rd9@4:1I49Re!sA$Pc1:be,4aRbC8C81qa7RfP0P1g00XgRgg00YGRh'ORi1p01=VghdAo432RhCURgb4b6b7X04X14%12RjA51=2%11[[^04^14P0f<Rkf;RlPBPDO4b3b5b9b5PHe1CIL%1L123M[Rm\RAGIL2VWX2V%1M!vV$PQPUPPPXP[PTPAPZO1PmP^P\P_P`Pa%<;9@4:R^%<IRm%AO5H4!uJ&Pa1Fe^,4aR^Pc%AK9H4m,Fe,4aC8C8PfP!u/01=2;RK/;S1=1;,22RS121M!u8-?f>PDf9RM!u6$:!u8%bDb:PNeCR1?HNe,kD%hJ#9!s$$0#B#7!s$$6RJ/;F%69R9%7>#7!sG&9!sG+3#6RN55F'?P@g028\RFf8RH#>RO#gRZ7Qk1d<G9V@0XH@PDPHP]!uv'A@4ed/::,4aR:PcP:!uP5A50=2A52=1!uC+PMPEPBO3b3A5M=He!sv,P^PcP^!v=620KPS!sg,EPMPAO3b31=M;,2HeO3AQFlZPEPkPlPOPCPB%1O%6>R>,EIRB,2Op-0ROP]P\1L42RC!x,%J/:e,4aPa!#3&'8EfR85PaPcPb!tW$0P1PiPhCURh!ta+W81;J0/?2Pj!tc$8OP0%>MRM?59NPMP2!tj$CI>%1>123B[R3!ys$>!ys'B!ys%2PYO1P3!uw$!t`&99@4e%<N!y]$9Pa8PcAH4m?!yR'PfP!tV,X8OA509N,?2122B!tZ-kRk,;JPk!vE%!yE%CRFcEib=CjW<W;WCWBW?W>W@XI4XE4WAWGWFo"). Qed.
(* [comment removed for export] *)
Ltac outside_sh_tac x :=
  cbn [outside fst snd]; pose proof (sh8_bound47 x ltac:(unfold AAPP_HI in *; lia)); lia.
Ltac solve_load_anum ::=
  match goal with
  | |- context [ov_read_bytes ?segs ?mc ?a 1%nat] =>
      let E := addr_expr a in
      lazymatch goal with MU : munch ?W ?m0 mc |- _ =>
        lazymatch E with
        | sh8 ?x =>
            first
              [ lazymatch goal with TS : ptsh m0 ?ff |- _ =>
                  lazymatch x with context [ff] => idtac end;     (* [comment removed for export] *)
                  replace (ov_read_bytes segs mc a 1%nat) with (Some [b8 0])
                    by (symmetry; exact (ptsh_rd m0 mc W ff x TS MU ltac:(outside_sh_tac x) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold AAPP_HI in *; lia)))
                end
              | lazymatch goal with SHB : pshb m0 ?q ?e |- _ =>
                  pose_shb_facts SHB x;
                  replace (ov_read_bytes segs mc a 1%nat) with (Some [b8 (shb m0 x)])
                    by (symmetry; pose proof (sh8_bound x ltac:(lia)); exact (pshb_rd m0 mc W q e x SHB MU ltac:(outside_sh_tac x) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))
                end ]
        | _ =>
            lazymatch goal with INB : pinb m0 ?q ?e ?inb |- _ =>
              replace (ov_read_bytes segs mc a 1%nat) with (Some [inb E])
                by (symmetry; exact (pinb_rd m0 mc W q e inb E INB MU ltac:(outside_tac) ltac:(lia) ltac:(lia)))
            end
        end
      end
  end; load_post.
Ltac solve_load ::= first [ solve_load_base | solve_load_anum | solve_load_image ].

Ltac seg_unfold ::=
  lazymatch goal with
  | |- pecore _ _ _ _ _ => unfold pecore
  | |- peframe _ _ _ _ _ _ _ _ _ => unfold peframe
  | |- pesize _ _ _ => unfold pesize
  | |- pecells _ _ _ _ _ _ => unfold pecells
  | |- petot _ _ _ => unfold petot
  end.
Ltac print_hyps ::=
  try (match goal with H : ?T |- _ =>
         lazymatch T with
         | boxP ?P => idtac "  " H ": BOX" P
         | rw_cells _ _ _ _ => idtac "  " H ":" T
         | ro_cells _ _ _ _ => idtac "  " H ":" T
         | @eq Z _ _ => idtac "  " H ":" T
         | Z.lt _ _ => idtac "  " H ":" T
         | Z.le _ _ => idtac "  " H ":" T
         | not _ => idtac "  " H ":" T
         | _ /\ _ => idtac "  " H ":" T
         | _ \/ _ => idtac "  " H ":" T
         | munch _ _ _ => idtac "  " H ":" T
         | stk _ _ _ _ => idtac "  " H ":" T
         | _ => fail
         end; fail end).
(* [comment removed for export] *)
Ltac useg_begin r ::=
  intro_rv r; subst; unfold peframe, pesize, petot in *; unfold seg_post, pecore, peframe, pesize, pecells, petot; hide_post;
  lazymatch goal with |- evt _ _ (MS (mkR _ ?sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
    pose proof (bv_unsigned_in_range _ sp) as RSP; unfold bv_modulus in RSP; cbn in RSP end;
  try (lazymatch goal with |- context [bv_unsigned ?pa + 160] =>
    lazymatch type of pa with word => pose proof (bv_unsigned_in_range _ pa) as RA0; unfold bv_modulus in RA0; cbn in RA0 end end);
  acb;
  try (lazymatch goal with APP : aapp _ 280 |- _ =>
         pose proof (aapp_bounds _ _ APP ltac:(lia)) as (APB1 & APB2 & APB3 & APB4 & APB5); unfold AIMG_TOP in APB1; unfold AAPP_HI in APB3 end);
  try (lazymatch goal with APF : aapp _ 512 |- _ =>
         pose proof (aapp_bounds _ _ APF ltac:(lia)) as (AFB1 & AFB2 & AFB3 & AFB4 & AFB5); unfold AIMG_TOP in AFB1; unfold AAPP_HI in AFB3 end);
  try (unfold AFS_HDR, AFS_SIZE, AIMG_TOP, AAPP_HI in *|-);
  try (lazymatch goal with PA16 : bv_unsigned ?pa mod 16 = 0 |- _ => let k := fresh "kpa" in destruct (mod0_lin _ 16 ltac:(lia) PA16) as [k EPA]; clear PA16 end);
  try (lazymatch goal with TA8 : bv_unsigned ?ta mod 8 = 0 |- _ => let k := fresh "kta" in destruct (mod0_lin _ 8 ltac:(lia) TA8) as [k ETA]; clear TA8 end);
  try (lazymatch goal with FF32 : ?ff mod 32 = 0 |- _ => let k := fresh "kff" in destruct (mod0_lin _ 32 ltac:(lia) FF32) as [k EFF]; clear FF32 end);
  shad_bounds.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac achk ::=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    lazymatch pc with
    | 1077380 => chkjoin 11 1077384   (* [comment removed for export] *)
    | 1077432 => chkjoin 12 1077436   (* [comment removed for export] *)
    | 1077452 => chkjoin 13 1077456   (* [comment removed for export] *)
    | 1077820 => chkjoin 12 1077824   (* [comment removed for export] *)
    | 1077864 => chkjoin 12 1077868   (* [comment removed for export] *)
    | 1077908 => chkjoin 12 1077912   (* [comment removed for export] *)
    | 1077928 => chkjoin 13 1077932   (* [comment removed for export] *)
    | 1078188 => chkjoin 12 1078192   (* [comment removed for export] *)
    | 1078296 => chkjoin 14 1078300   (* [comment removed for export] *)
    | 1078400 => chkjoin 14 1078404   (* [comment removed for export] *)
    | 1078504 => chkjoin 14 1078508   (* [comment removed for export] *)
    | 1079028 => chkjoin 11 1079032   (* [comment removed for export] *)
    | 1079084 => chkjoin 12 1079088   (* [comment removed for export] *)
    | 1079128 => chkjoin 13 1079132   (* [comment removed for export] *)
    | 1079236 => chkjoin 14 1079240   (* [comment removed for export] *)
    | 1079336 => chkjoin 14 1079340   (* [comment removed for export] *)
    | 1079436 => chkjoin 14 1079440   (* [comment removed for export] *)
    | 1080344 => chkjoin 11 1080348   (* [comment removed for export] *)
    (* [comment removed for export] *)
    | 1084012 => chkjoin 15 1084016   (* [comment removed for export] *)
    | 1084048 => chkjoin 16 1084052   (* [comment removed for export] *)
    | 1084088 => chkjoin 15 1084092   (* [comment removed for export] *)
    | 1084136 => chkjoin 17 1084140   (* [comment removed for export] *)
    | 1084172 => chkjoin 17 1084176   (* [comment removed for export] *)
    | 1084216 => chkjoin 15 1084220   (* [comment removed for export] *)
    | 1084252 => chkjoin 17 1084256   (* [comment removed for export] *)
    | 1084288 => chkjoin 17 1084292   (* [comment removed for export] *)
    | 1084332 => chkjoin 17 1084336   (* [comment removed for export] *)
    | 1084376 => chkjoin 15 1084380   (* [comment removed for export] *)
    end
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
