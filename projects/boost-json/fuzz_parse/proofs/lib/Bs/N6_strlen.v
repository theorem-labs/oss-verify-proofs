(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset F_strlen.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import N8Store.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_N6_strlen () := KReplay.lz_vm "#$AKK47Corelib7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00!t4G1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI!sw+4Init9Datatypes6op!tE#00C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib3Mem7mem_invC13~~~!um>Z02C!um@7Z_to_bvK!tUS5Cells4cell04!tV3!uc24list!vW#!tX?;bv_unsignedC56Stdlib6ZArith6BinInt1Z3sub!sC<2le!t1AD!t1-_in_rang!sYB:bv_modulus!tF>t!xV25Logic3and00!xq<4prod!xoV5Frame:munch_refl!wD%!snZ5!sn$!si`:wmono!tY-!xw<3nat02!vg<6of_natC!vk78iff!t1%!sd;>pow_pos_nonneg!yZ=pow!sC<:!sk#!sg%I!{5A0K4!sj&9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr02!sIE1!sIE4C!sI55Tauto8B!t[&K!w_72eq!~9#!sb4:Z!uC+=Z!sn$CheckerC!v8<4find!sqAC!sq0_sou!sX8;ZifyClasses;rew_!yT%v!{HZ9stk_carve!{G%I!v#9x00c!t/O2Bs9N6_strlen<tryinit!{%#t!}F`3mkR!}?B!#9u&2!t1T8PropExec7seg_rom!tyZ6MState2MS!#:cE3!z}E!sI7!|a:1!~y=addK!#=u?5Instr5i!s+#08K!#>IG4tre!#>vK4sext!sQA3Sem5alu64!x+]8alu_addi!x,Z8StepFast8sf_congT!x5'!v\L7!#A1W3le8!u&&!#=O?6bv!uV#!vh;?!s<26BvBase=!#AE#le_bytesK!wMD4core01K!#=z@1K!tTJ>!t#$!sE+>machine_resul!#Ax#!t6'5Lists7!s+#Def5skipn!vnT4!x3#Arw_cells_cb_spli!#4'Z!yr+9b!w@#!{-$!spY!tf$D!#C0'!#Ey%!x=$!xh&!#>_6eq_tran!#C-<9add_assoc!sg86eq_sym!{q]6sf_ad1!|`c=!sm$dr_ztobv!stc@sf_store8_direct!swc7sf!#EL^!tg0!~g#all!to%!#;:Z!#KO#;!z{'_ok!so`8!{l1I!#A%:0!{<Y>!||+b!#@I#!ty_:!so%siz!vZ&!#O'_1!tZ`5c!tU,!siZ7!tU#_a!#3;_!#4{+!yi$!x{]!#41$!#Sm%!ss&c!#8c#!sw_!xl,write!zgb!vM#up!yZ'!#@b;leb!#GHA6eq_iff!sLB9and_morph!sOB7!#H?%!ta34Znat5Nat2Z9i!#Ne&K!#K<;G!#C6&3!sJF8!}_9or!}_V7S!x]#Dj:chunk_disj!wpZ!sp'!zU,frame_d!sw&!uOF5!y5U!#I{#6inside!u/b8!uy%in!zi`6!|H`!tZ'>!#X@$!|H$!t`^!v<$;!#WY$!}</!#C%X<!t]%to_mem!uQ\<stk!uO3!#]`@!#AJ&obliga!s:#_!#_FA9bv_!#_DA6shiftl!u=T!#Oz+v_auipc!#5z^F!#C~6_r!v4'!#D$9in!sJ#!uwDconcat!uW^b!uW/!#L[M!#So]6v!#Ng-!zeY=ov_read!#LF$!#M'Q@!#L~&!wV#word!#daDextract!#V~C1!v5T!#Oj#sxb!wH'!#`2?2!t,XAsext!u9'!up$!{6_@!#8J'!wG$a!#HOc<sf_load_goal!zGT6!#W,H9!#n}#_set!tw]?!#IX,!u##!tzT>I!#S>h0!tBN5!v>I6!{K#qbC!z><negb!xRabranch_!#6L[!#ZA31!#6B=6!#6B$!sB89False!sE$!xz`!xr#!#Q<1!#:$:7add_0_r!}%Z!#90&lit_self!#<AF!x@#not!#\DE!u~V!#ct%6ret!x?]!sk&;!sk%_fol!|aU!#aiT!#Ag%stk_releas!#Ag'!#I{?5mkrel!#mH7!#un#1K!#jb:!#8bT4!#cX#evt_don!#7S_8!#7S&!skZ!#kG%stk!sg`5!#Eu#!w-H3inj!wQEapp!#OjB!sK$2!#KXE4!#Ve_5!we[!xR#3evt!{Y'!$'SB1!#kcN!#>gX2wa!#6Q2!#en06firstn!#6T77f_equal!w8F6!tlT7CodeTab;!{{#step_!#6q&I!x'_0!x'V2Bs5ASegs5asegs!x,'!v0'!#rL51I!sD?0!{/68!{/#Inst7Inj_Z_Z!#}R;!$#h#0!#s2C3Op203!#{X;5eKind!#~_<uni!t49!se%4ki!#5X5!sf31!t-=bool!$3t-!sF81!#9WZ5Wrd6!$1J%I!#9QL0!#C4Y=!#C4&s!tK#!uM>!x&$!#9-84True!uhR!zW+7ct!#E~#!zYC!$7j+3I!tS=!$'b6!$$O,;!#@x$!tk$!zGK1!#=wGaluop!xdV!#32&8ct_entry!#?;Mmsize04!y<A!#v#+0!vV85!#E6#!$<+>1N!uzJ!t^%1!#|-D2w0!#CK[w0_!#m6'!tdG;!#I@%cond!$?K-!}l82!u2G1!u2]1!u2,".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm2dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeq95bvmap01Z37Corelib4Init5Logicta3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~v45asegshfbbv_unsignedk14prodta2ex46Stdlib6ZArith6BinInt1Zhl13subk14Nonek14consk13nilk14pairta2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hp03mkRhp05munchhp03stkhp05wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~huc2MShuc6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ij97mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ine7seg_romhf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~it24cellit22C179OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9N6_strlen~~~~~~jhcctryinit_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~jmb3evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jqd8rw_cellshl12le" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac call_pure SPEC ::=
  eapply evt_cut; [ eapply SPEC | ];
  [ .. | let ms' := fresh "ms'" in let PO := fresh "POST" in
         intros ms' PO;
         (let T := type of PO in let h := head_of T in try unfold h in PO);
         destruct_exs PO; subst ms';
         try (lazymatch goal with
              | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
                  replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
              end) ].

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition tryinit_post : ltac2:(zQ "50!h9!jc!l9!p9!sf>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>0$3P") := ltac2:(zQ "ha1!h9!jc!t7!ue!hif!hj7!l9!hk5!hkc!p9!hm9!hn0!hn7!hne!ho4!hob!sf!hsc!ht3!htc!hu3!ii9!iif!in3!ird!is8&>0@1$1@1$0#k0@1$6@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2t0@1$1@1$0#k0\2t1@1$1@1$0#k0\2t2@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2a2@1$1@1$0#k0\2a3@1$1@1$0#k0\2a4@1$1@1$0#k0\2a5@1$1@1$0#k0\2a6@1$1@1$0#k0\2a7@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\2t3@1$1@1$0#k0\2t4@1$1@1$0#k0\2t5@1$1@1$0#k0\2t6@1$1@1$0#k0\1F@2$h0@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1m~0\3ms'$9@2$8@1$1@1$0#k0\2a1@1$1@1$0#k0@2$8~0\2m'~0@2$3@3$f$9^3@7$h5@hf$h1^i3^i2^i1^i0^hf^he^hd^hc^hb@2$h9@1$0#k0+1^2^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6@1$h6^i3^5@1$b@1$1@1$0#k0^1@1$h8$4@2$3@3$h2@3$c@2$7$2$2@4$e$2$2@2$a@2$5@1$0#k0^i2+h0@2$5@1$0#k0^i2@1$d@2$7$2$2^4^1@2$3@3$h4$4^4^1@2$3@2$h7$4^1@4$h3$4^1@2$a@2$5@1$0#k0^i2+h0@2$5@1$0#k0^i2").
Lemma tryinit_body : ltac2:(zQ "h60!h9!jc!hif!jge!is8!hj7!hn7!jh6!hm9!hn0!hne!l9!sf!jlb!jq6!hsc!htc!ii9!in3!ird!ju8!jv4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$c@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@2$h2$2^1>0@4$h4$2^2+hrtul8@3$6$3@1$7@2$4@1$0#8+1@3$6$3@1$7@2$4@1$0#8+1@1$a$3>0@4$h0$2^3@2$8@2$5@1$0#k0^i3+h0@2$5@1$0#k0^i3>0@2$h5+hgggnvvvogg0@2$8@2$5@1$0#k0^i4+h0@3$e$2@i0$d^i6^i5^i4^i3^i2^i1^i0^hf^he^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5@7$h1@hf$f^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7@2$4@1$0#k0+pnupc^6@1$9@1$1@1$0#k0^5@1$h3$2").
Proof.
ltac2:(KReplay.run1z (kr_t_N6_strlen ()) [] "#%,fp'0h04__x1h11bi001bh21xi011xh31zh47__arithh54__ffh67__sat12h7!s0&3h88__varmaph95__with:1th;1Kh<2STh=4junkh>2FRh?1Hh@2MUhA3ST0hB4__p1hC3sfEhD2C5hE2MIhF2WMhG2a1hH1mhI2m'hJ1yhK2CHhL2HBhM3HB0hN2HahO4HeqmhP2LOhQ3TCkhR3TCshS2bsi022bshT4cstrhU1nhV3DJchW1FhX3INchY3SPRhZ3ST1h[1ah\2a0h]2a2h^2a3h_2a4h`2a5ha2a6hb2a7hc1ehd2fche2gphf2m0hg2m1hh3ms'hi1ohj2rahk2s0hl2s1hm3s10hn3s11ho2s2hp2s3hq2s4hr2s5hs2s6ht2s7hu2s8hv2s9hw2sphx2t0hy2t1hz2t2h{2t3h|2t4h}2t5h~2t6i032tpp%0p%1p&0p&1p;1p;2p;3p;4p;7p;Pp;Op;5p;:p;6p;<p;;p;8p;Bp;@p;?p;9p;Ag0000j16Tg000Uj1iTg0013k10[!s0$Vj19Tg002;k21v!s0$gS00k10:Tg003Ik20ITg004Lj1B!s/$jj25k115Tg005Pk11uTg006Tk10KTg0074j27!s/$^R0j2!sn$8;R1j2>!s1$Wk21?Tg009Jk1!tL%:3k20P!s0$OR2j2F!s1$jk20OTg00;Jk21!sy$<Rj3\Tg00=Uk2!uL%>]k10ATg00?<R3j1N!s1$\k10eTg00@:k21n!s0$bk21mTg00A?k31k!s0$ck10^Tg00BCk21j!s0$ak11gTg00C?k11b!s0$jk21_Tg00DMk20;Tg00E0k31!t[$ESk21!vn$F5j2!sC$FOk21VTg00G;k31S!s0$Zk41QTg00HLk40!tY$I7k71!w#$J>R4j2q!s1$XlPYTg00KelOoTg00Lfk10!uP$MHk11@Tg00NPj78Tg00OQk10!tW$Ook30!t:$PRk40RTg00Q=R5j21!s1$Zk40ETg00RFk11!sc$S3j3Z!s/$^k30DTg00TFk30CTg00UOj5xTg00VXk40!v<$WDk10!y\$XCj3!sV$Xhk20!vO$Yek503Tg00ZNj4!w$$Znj2wTg00\6k30!yX$\Tm:0fTg00]bj3tTg00^lj2`Tg00`=j6!y\$`[k302Tg00a>k40!xl$aZk50!ur$bak50!y[$com<0cTg00e@k10!uJ$fHm;0!w~$gYk31sTg00hbk31rTg00ihj34k11!yJ$jBk51!u$$kMj!sP%lUj1<Tg00mYj!xD%n\k204Tg00oam:12Tg010ok711Tg012@m;10Tg013Kk30~Tg014Qk20}!s0$nk30|Tg015Tk60{Tg016=k40z!s0$dk10xTg017Ik6!}T$17mk81fTg018Qk20Y!s0$kk41aTg01:5mB0uTg01;Fk71`!s0$jk31^Tg01<nk31]Tg01>6j1cTg01?:m@0rTg01@Hk60wTg01AQj3pTg01BUm?0ZTg01Cak20=Tg01DTk20XTg01E<k21!sD$E\k21!tX$Fdk21!sD$H7j6G!s/$Uk51WTg01I=k21UTg01JEk21TTg01K1j2!ub$L8k40JTg01M=k10nTg01N=k40!sa$Nfj2!uW$OHk11RTg01PGj3h!s/$gk11PTg01R4m<!~@$1SAk51MTg01TNk50VTg01U:k50!tC$Ujm;0!tW$W:k51H!s0$fk11!tN$Xnk41!u1$YZk31KTg01ZGk11L!s0$em91FTg01\2k41ETg01];k61O!s0$Wk20lTg01^6m:0oTg01_Fk10!vn$_gk10kTg01a4k20Q!s0$Yj3_Tg01b>j1!xn$cCk11DTg01dMk31CTg01e9k81BTg01fBm<0s!s0$gk40!tb$gBk40t!s0$\k41>Tg01hak4!xQ%ifk41!x&$jgk31dTg01kjk41eTg01lMm<!{7$1m2mB0y!s0$Xk71!vz$n<k20!sv$o@k31;Tg020@k30_!s0$cj4QTg021Pk10MTg022Nk30a!s0$mk61:Tg023Jk71p!s0$nmA1qTf0R6#9#9p=X%66#9p=E%96#6p=A%66#6#6#Bp=Pg0259R7f2R8f1R9=h763hp=Tg026=R:P8P9P6H1cp=IP!s4+=p=?!sk'6p=S%9!t9$#9p>05g027?R;/>6p=Wf3R<g027]R=P=P8P9Ck;h6p=VB1d:96p=m&0A6$0Ap=r1;=6p=CP=P=g028;P6H1ep>0dg028_S01P=!s$$3P3f5R3f4R>P<!ta%N<1<p>1t!sH&!s$%0P6P9P8P0P<P>P3f6R0f7R?f8R@f9RANB0yp>1o!sR$1P?P1P0P3P!sz-0sp>0`P=P9g029>P6H0Rp>09!s6%eS02g02:DR1P1g02:dS03P6g02;DK1hp=jg02;dRBg02<DS04746p>0620>8!w-$p>0H%6!wM$RB1;:96p>00A4=96p=]P=!tY,EGp=n!w7$p>0F20=96:0_<8p=@%B6-0=9!s5&bg02<dRC/a6p=0PCPC!sk%CQP9P6CQp=3PCP81aC!s5&J!sH&C!t7%CQCQp==g02=hRDP=!s:$k,a8,;<p=H!sM,p=2g02>TRE/w6p=L&0M9=p86p>0hB0a896-0><p=vB0a><8-0>3Ah7965h7p=f1a76p=^Q01/;6p=u1789/16,5<p=g!uo/J1:p=yB0a<89-0>>!vU%14!sW&p=M1196$0Mp>0<%c69p89p>1l1189$0M%c65p<p=e!y-05!y-&5!y-%P0P?P@P!x~&0]P8Q02P1P1Q03P9P6K1pp>0v!sy&=p<6p=}!vy$!yE$CQ!v]3|!sC$!sE/!wF-UB0_9;6p>01116;p=lP:!t^&<g02?[R5!tc/f:RFg02@:S05f;RGN?0Zp>0q1196,58p=d!xo&p>0G1F96,F8p=~P:g02@V!t#'!sx/PFPGf<S06f=S07f>S08NA1qp=Og02AZRH#6RI#6S09#6RJ#6RK#6S0:#6S0;#iRL$0[RM%9IS0<#iRN01vMQ0:#iS0=$0[%iJS0>$0[RO$0:\MRP20I:6S0?%9HS0@#6RQ#9S0A#9#X#E#X#AS0B#6#A#X#PRRQ0>%BHS0C'5S0D$1uS0EQ0E&0K7RS3TS0F5I9fRRT,7LRU%BKRV':=?8UQ0;#6S0G#6S0H#6S0I#S$05!s%+#S!s$$PRUfSRW,7L/:V'>fTRX-1?L17LXRY#W&19L-0PY'F20O==S0JfUS0K,7LRY/:VPYQ0J$0KS0LCVRY0173A\Y33216:01m00P>fWRY,7LRZ/:V=??ZP:P@fXRZ,7LR[/:VR\P[&0A5S0M$0A#r#r#rR]!s-%#rR^P6%N^R_,:[R`,>\1>\\P6X2=Ra1>96$0eXJ=X2=S0NP\P\%C\P`P\PaPaPa1:96$0d#CXH=XU=P[P[%C[P_PVPaPaQ01%N6#CW2P^PV%CVS0OJ1tS0PN:1oL0`%BIRIQ0;#BR[+1nS0Q20P;I%W[21mI[Rb-0P;[[S0R%WIRcg02B?S0SB1kI[9UWNS0TQ0S%Wb[^NcS0Ug02B[Rc!vM$V&0^cS0W21j=9S0X&1g=S0Y&1b=Rc21_=HS0Z20;=VS0[61\=RH009H'jQ03-1[cS0\P6P8Q04,;BR[21V68$06dB1S=;9H1QS0]b5b8b9X0=1:6VRd/>d^0=P6f[Re,7LRfO1b4b6b7H0mK1IA?@\`&0^OR`fYR\,7LRg/:_RhB0H^6SRi5IAX=`'q'FP21:gV=?AhfZRh!yQ$_=IFiX=`,q`PePhP\PZPYfVS0^Q0KPXPWfPRgfOR2fNRjfMRkfLRlfKRmfJRnfIRofHRpfGRqfFS0_fERrfDS0`fCRsfBS0afARtf@S0bf?S0cQ08Q07Q06PGPFMPY!tA,Q!t?+PTfQRuPgP2PjPkPlPmPnPoPpPqQ0_PrQ0`PsQ0aPtQ0bQ!sy'MOoQ06Q09#9S0d#6S0e#X$05#ES0f#6Rv#6#X#A#RRw,5LRxPG&0NMRyPF&1@:RzF8+00P61:fV1:f_5?GQ07f]Rf!vC%;I!vB'4P`Q08f^S0g!sA/f_S0hQ0gPff\R4!uM,!uG%P!uEPMPYQ!ss&P4!v@9!swH!v2$bPxQ0cPyQ08P!u\'Q0bf`S0i!u7+Q0QQ0RQ0TQ0UQ0VQ0WQ0XQ0YP=Q0Z&0\KRK-0;=60S=Rig02CGS0jPHH0R,jcQ0\Q!zr/16KS0k/]!zs&dS0l,7LRd!zt'faS0m,7LRH/1K1:HV']fbS0n!s9%:VB0H^<S9Is6X3=P911HKRHP6DnQ0aB0H^8S7IHfcS0o!sX'Q0`??6!sU$?!sU&9DnA?sHH1:dVQ0JP6feRH,7LRxQ0LCV?\rrX3=Q0811dKRrP8DnQ0JPrPd!sF$Q0`Q0`3\1:xV1>U!t%$t11xKRxP<Dn1>UxffRx,7LRt/:VfgRd,7LRr9?q!sR$s11tKR{P>DnQ0_??{tfhR{PdPxPHQ0lQ0oQ0nQ0mQ0i!xSSMPYS0pP!ss9!yNSMOoPoPwPpPyPqPzg02CnS0qPNPIPNQ0@#9#XS0r#9#X#SRw#6$0F#ARt#6#S#E#RC@!sQ%PtCb%6QS0s#iRQ%BwRwPQPwC@RwH0ES0tQ09#BRt&18CR|%0nP|%0hS0uP|D3Q0n#0S0vAJ|T|S0w%0xS0xP|Q0^#0P|Q0g#0S0yAJ|j|D3S0zD3%0{S0{AJ|Z|Q0i#0S0|AJ|g|Q0l#0S0}P|%0XP|%04S0~AJ|l|D3D3S10&0NCRCAJ|\|S11Q0m#0S12AJ|u|%0HS13P|Q0K#0P|%0fS14AJ|k!sb&511rKRk,5LR!t-$YP|Q0h#0S16AJ|2|D3S17Q0o#0S18AJ|W|S19%0eS1:AJ|m|S1;D=3JD3RmPo%9vS1<#6S1=#6Rv#PS1>,5LR2!wQ'F8P[g02DZS1?$0:R~20OD=S1@Q0tPtCHPMQ1;Q1:P|Q18Q19D3%0dS19Q17fiRD#0S17Q15!u/$PCQ0u=2||S0uQ0vQ0wQ0xQ0z!vk$%06S0wQ10D=PnP2PoPyPpPzF8#LX:MQ0qAZQLw80DdP}B0CdQwDxQ0pPmPoQ1>!yP-EbS1>!x}%%9JS0p!y5%Q0C!s'$C@S1;PQ%BJ!y2'S0tH0jS1APtPmPo%Av#RS1B,5LS1CPpPy%N]Rv,1kS1D&0i{60hqS1EPzF8S1FP[P~Q1@Q1A!v,$:PzPqQ0t9ZQLS1A9DL}S1GP]17L{Rm-0g]Q1Eg02FNS1E00OPS1HQ1EPPQ!v>%z11mKRm,5L#0!v'&15LtS109DL!v4$I03P6Ck'wX2PQ1F#LS1FP:PqPkP]POP]P?!s-%B0BO]?CvS0zPSEfR2P]Q0zQ1GP{!sU%B0H^?SR^P2P]P]P>P[&0^7S15/;2S1IN:0f&0:7R7Q0z#^';%u]S!sg$&0\JS1J,1rRJQ1DPMQ1G11kwS1D!vS$K15LJ!s<$PLPLP}PwCgQ1KQ0t9t}Q1`kwEKPM&1!sR$Q1D11KwS1G,1rR}P=P}Q1DB02rKwH07DyEKPrQ1JPKP]Q1J#CS1DI0@I0?N<0cQ1F$08N;0b!uy&!uD-B1s^]]$06eQ1IQ15B1r^]]742eN:0fAIqk2P:PpPm!vV&@!vV-@PSI14I14R2P6I13%Wm%s2#N,1m/>b'FP:PoAMLDKRm00<vR2fjRk#<R^PpQ05P:Po!s}+A!s}-ACvRm!wT$rP]Pm%[^P9%^mR},;7204r]=47}e%[m#uN:12K11B1lo2^-0I:P:PnAMLkKR^!t$&F!t$-FCvR2!t$$oP]P2fkRm#<R}P8%^2Rr!t,%o]=47re%[2#uQ05N;10PnP^PvP}CeB0~o]}7I^Q0O!t-&GflR^#<PSEf#s#N/]VP[fmR}#<#[#N,1v00}V$06AML}KRo#WR211o_S15/>bRr'F11oVS1I/>b,F2S1FP2PrP2PaPVO1S1L,1oRr/>bp-0RJ/;2A4J22e:0|22PaQ0NQ15Pr!#HX%1!#HX/S15PoPo%CoP_Q1LQ0PN:0]PbPb%Cb1]bbeS1ML0`J0{P>H0zQ1!vJ&Q08foRr#<S1FPSEfS1N#sR2$0x%N2#W!#?g;c!#Qx+20;=U009i,jc&0N120;=R20;=I60S=!s?&!sW/P<J1iS1O60vcL1f!#@61XBJQ0k,>U11RIS1P119K'>00Y8[^0=^BJP6frRU,7LS1Q/1KR2/1V/>RQ1QQ06O3!#@[$bTbMQ1P/>oQ1I/>R+0YS1IeQ1IePRPIPoPVH1aRoePoP:PjfnRo=MLKS1IPvQ1FCeS1P!|4$NPVP]Q1FPjPRQ0FPI!#V7$Q05%CIS1FP6PlNB0uQ1PQ0F7IR17LrS1P/1KRl#WRj11l_S1N/>bS1I'F11lV!xn$jS1QPjQ1IPjQ1L,1l!y/%1;JjA4Jjje:0|jj!xf&NQ1I!xg%Q15PlPl%Cl!xX3Q!xP+0!xP$Q!xP'bfqRj#<S1Q!xP%M#sS1L$0xQ1L#N!xSK9ii,jcS03Q0[:0S=iS0[Q0Z+09,jcK1`Q!x?%!x<8Q0k'>S1OQ0k/1VS0k/>6'F00Y9!xA'g02G7S02ftRi!xI$LO2!x8-0JPl!w$$LCVR1@1^lVeB1]1lVR1eP1P:PgfpR1,7LRl/1KS1PPvQ1Q#cS1IC}S1NQ1PQ1M!x:%QQ0JQ1PPl!su$S1PPgPg!#_~$Q05P6PGN@0r!sX$N7\gP:PuPuAMLjK00<vRg%<US1P#cS1NPnJ0wQ1N9pug,muP:PTP2PvfsRu#<S1MCeRgP2!wO'aQ1MPSEf!tU%M!sR$2P?P0P3Q05Q08N?0ZA?g22P:PW17LuRg!{H$Pv%<iS0aCeRT!su'!#Jk$!st'0aPWP2PgP@P?P0!st$6!st%T2gPXQ1L/1KPvfuRX#<S1L#cS0NC}PP1;P6S1RQ0KAMLXKPvfvRT#<S0K#cS1SC}94P6fwR2PTPXPiPuPUPjP1PrP^PmPkPD!#FpPMPYQ11Q17P|%0jS11Q12=2||S12%0XS0^P|Q13P|%0}!#C{$14P|F|S14FU%02S0gQ19!sW%9%0rS0hQ16=2||%0uS16P|Q18P|%0mS18P|Q1:P|F|D3S1:PCQ0{!s`$0{%01S0iQ0|!s`%iS0|P|Q!#Eu$^S0}P|Q0~!s`&0~17LTRh/1KRe,5LRgQ0x!sn%x%0oS0mP|Q0yP|D=S0y%0US0nQ0v!sH%v%0kS1TQ0u!#E9%WPZQ1BPYPyP9PzQ!#Bw&Q0;#AS0;CbS1BPNPwPNPwC@S1U20=Q;-01QRsH0jS1VPtP!sk$=#9S1=#PRW,5LRnPYPy%N5RY,1eS1W&0i160h9S1X!#Bv$Y!#Bv'V!#Bv'9AZQLsS1V9DLgS1ZP]20g]lQ1XQ!#Bc&0uQ1TP|!xE$v%0TS0vQ0yFUfxRl#0S0yQ0~PCQ17!wZ%7!xK$2Q0^Q14AML2KS14!#CB%:FUD3P\Q1CQ105DLPZ!#CB2Y#LS1YP:P9Pe!|B'_CvRZ%<2S0_;TSR\P5PZQ1ZP1PG%^Z,;7Q0zQ1ZPeQ1WPMQ1Z%leRZ,5LS1WPg!s8$17Lg#l,5LQ1WAtgQs1`e;EKPMQ1KPZ%lKS1W,1hRgP=PgPZB02hK;!#BI&hPKPKP5%CKS1Z!#BF-Y!#BF+9PeP\PGI13%We%s\#N,1e!#AM&8Q1400<YRbQ1QQ07!#AE$8Q14!}~&qCvRq%<lRe!uW'qQ1Q#[Q06%^qRh!#@:$\5=47he%[q!#AA'Q1I9p8b!#AB%<AMLlKRb!s|&pCvRpfyRq#<Rh!t#'pQ1PQ07%^pRZ!s}-Ze%[p!#A9+<PbPYQ1NC}Q1P:0~\57IbQ0OQ1MfzS0O#<S1P;TS!#A:'Q0a!#A7$Y!#A7%P:P0f{Rb=MLKR\PYQ0NC}RpP\Q1Lf|R\#<;TSPVP5Q1LP0!#<G&8P9P6Q05Q1F!vF$6NB0uQ0F9IpRP:P?17L\S1F/1KRpPYQ1SC}RZPpQ0Kf}Rg!sz,0KQ0JPp!sm$LCVRpP4P?!#=M'Q0!#8/%A\p4ZP:PfP@AMLgK!wk$pQ0_#cRZPGJ0wAp@pZ,mfPAf~Rf!uC$ZPYPeCeRpPZp+01@R4#<=TeSPVPePAPZPZ!#r?%GN<0qA?pZZPF17L4Rp/1!se%hCeS0_!sf%ARe#<=ThSPVPhPFPZPp!#s%%!sf$Q0_??ZpPGAMLeKPYQ1PCePPQ1RQ06p+01BS1R=MLKPY%<bCe94P6PMQ0<#6S1P#6S0_#iRZPZQ0e#E#AS0e#BRpPZPpC@Rp+0XQ0s#B+1ZR0-1YnS0sQ0B#9#E#E#PS0B,5LRh94M6X1MS1FPMAdL0WQ1F1;Mh17Ln9dL0S1F21XW0EGQ1F=4MheQ0s!s-&=Q0=PZPQPp15Q;I1W7ZL9DLnS0=21UnpEGQ0=PhPMe54Mp+01ES0sp+01DRnp+01CRZQ1RPeP4PfPgP\PqPlP!#:&4oP}!#:-8MPYS0oQ0xQ0v!#V:$0xQ0m!#7D$mD3%0ZS1FQ0n!s8%nQ0O#0S0KP|Q1TP|D=S1TQ0s#0S1S!#8~%S0|%0\S1LQ0}!s6%}32S0N%0eS0aQ0i!s;%iQ0yQ0{32S1MF|S1NPCQ0^=2||R0%0gS0^Q13!sQ$1332S1IQ1R#0S1QQ11!s=%1%0qS14Q1732S1Y32S0zPLPLPnPKCg#0S1C!#;C%S16%0bS1:Q18!s6%832S12!#Y^$Q0h!ta%hQ0gQ1932S0u32D=PHPWQ0lPyP8PzPNQ1P#BS1PPN!yE%E#RC@01TpRpPtQ!u7%zQ!tC$%0hS0eQ18Q0~Q0uD3S0uD=S1XPHQ1=#A#RS1=,5LR!t-,F8!#9x%Pp!#Xv&9Q0gP|!si$hD3S19%0nS1[Q12p+01FS1\#0S1]!#X`$1^PC!#<F+!x@$m32S1_Q1FQ1T32S1`PLPLQ0s!v='aQ0|Q0wQ0}!#BZ$D3D=PxPWPHPyP<!#YB,=PhP6DxQ0oQ!u9&!u,+Q0q!#<~$Q0r#6#X#SRW#6#A#ARp!#_]$E#PC@!v\$PNPpCbPQ%BWRWPQPWC@S0rH0ERW!v_&P015LRRp#0S1NQ13Q1QQ1YD3Q1CQ0uD=PHQ1<#9!#\q$0u#PS1C,5LS!t_-!vf,W!vf'!v8%!u`$m!v+%D3S1XQ!uw&e!uw-S1MD=PxQ1=!u{4qQ0r9ZQL80DhRWPpPMPW!z,$hQ0_$0F$0\RWCgQ0B=dLWQ0r:0ChQQ0B/`WEKDxPM20XQsS0B,zpS0r&0:MRWQ00P`PWP:P<P6Q0MH0JQ0>PLg02GT!}Q$>&0n6S0=H0W7ZLS1b,aMS1cPyn10110100021010200Q0D$1RS1d,aMRh34X1MS1ePMQ0B9dLRQ1e&0:`S1eQ0E#c,a`Q1e!tO'6Q!sz9=4WhWiPMQ1d1aM6=4WhX1M1;Wh!tv$Q!tq$Q0D&0KO5hO$0n!tw%!tZ$PEGP:P8Pp!uP%!s2$RQ0FP5Q0EQ0MPpP?Q0E#^RO,;7Q0F0045=47OeQ0M#uQ01Q0MQ0E#[34e20<RYRO,;MA4MpOeN<1NE!#[y$pQ0BCgROQ0B,`REG!vt,8PO!vt&!uU=e!sU-Q0r!sVF1V9DLpROAtpQs!uZ&OQ0MQ1bXS`S1bI1MRp!sR$PhPWe94WpQ1\Q0sPnP!#7X-Q0O!#7YOMPYQ1^Q0vQ1N!{4+Q1aQ1MFURp72CPxQ1C!z{'g02H2Q04PNQ0<#9#BS0<PNQ0G#AS0G#XCbRWQ1UPsI0VRhPtQ19Q1[Q16Q1d#0RRQ18D=Q1]Q0zPCPpD3PxQ0u#A#RS0u,5L!|3,Rp!},'h!#Gf'<!v2'Q1d!#GX&PN!|F$6Q0{Q0yP|Q0aQ0iD3S0{Q1SQ0Np+01GS1b#0S0MQ1`PCQ0g!#5+$g!uk$h!tp$2D3!#8=%Q1\!#5#&9Q0eQ13520!#3?%=S0eFUI0TPdQ1=!#G~%x!#G~$>!#G~$M%LpRpP6&08pN;0UPMg02H^RpPQQ0C!s'$C@RW-0XQRO'zQ0C,5LR<!#>3'=PM15L;Rh1z6O=4M<X1MPMAdL;OQ1=1;M<!z`$hPOCgS1=1`;OEGQ1==4M<e1zh!sZ$ePpg02ICEG!#i/%W80DpRhB0CpQWEGP<PMe94Mh!vk$!y^5b!y^PMPYS1=Q!w8&|Q0}72R!wp$`D3RHQ0e72CPdQ0uPxPyP>!#84%Q!#;A$I#9!#;A$Q0:-0GN-01NPW!#7l%PH!#;L%9P0%0<RH!#7k,D=RpPdQ1<#9RO#PS1<,5LS1Y!t3'!#7`57Q14P|!sg$1D3Q1]Q13920Rp+01HS17!xc&g!#;j$32S0z!y4%F|S12PCQ0y=2||RW!yP$i!yx%D3S0y!yP%b!yP&0:Q1XD=P{Q1YPdPyP3!#8G'PhP<P6DxQ1=P!u5%!v3,9#iRh20=h;+01PhPIPhPIC@PhQ0@#BPhQ0p#9RhCb%6h#SRh#S#S!vQ'20GNh-01NI1HRhPtPpPd%AO#RS0p,5LRO!v5,S0@!v8%?!|k%&1JEQ0@#L';!td'0p!sU'g02JH!~N$PNQ0_#A#XCb!x''1PC@Q0A#iRhQ0_#BS0_PhQ0_C@S0_H1GS0A!tX%PBPMQ1d>1KL<$1LRpQ0f#AS0f#A#PS1P,5LS0<Q0f#6S!s'$1?#PS09!x@$<n010!s#$20000!xQ7Q0APtCHQ!wk&Q0:Q0vPH!#=7,D=P{P6!wS0JMPBPMPpQ0_9ZhL9DLOQ109DLO!t?1Q1YPpQ0!#O4$9Pt!uY$Q1P#CQ09#CN91FH1EPpPB1;B6A4Bp6RhPBp+01KROp+01JR3p+01IRd!zB$!}&-!#H7'!}%I!|y$PQ0}Q1LP|!|~%!#uI$0}Q0i92WR%0OS0_Q0K!#5;$KQ1FQ0n32S1F!}J$_32S0pD3S1YPCQ1:!sM$1TQ1NQ16Q19Q0zD317L3R>/1KS0!#rj&4!sO%4PHQ11!|I$ID3S0:D=S0yPm!vi$9Q0<Q!wv3PkPyP@!$&T%^;hP9&06pS12P3P!v-4Q1R!v/PP{MPYS0AQ18!#xT%[Q16D3Q!}~&h72R%03S1:Q14!~W%32S18!u7%F|S1IPCQ0K!~/$n!v?%!uu$dR{/1KRh,5LRx#0S1NPWPH!~S0N!#HQ$kQ0<PDPyP?!uZ&g02K:!{5$454BPBQ0<PBPJP6Q02Q0Sn011!v<,XcBQ05Q04P6J1O!sH$200l6b?W2Q12Q02];dP6O1+0lW;Q0<94BpQ0AQ!tH%9!tH'Q1>!#=/%C!#]v$E#A$0F#ECbRpQ1BQ0tI0VRBPt!s`%1?!#JU$?!|q$B!u7,RJ!|b&PB!#<h'?Q1A9DLxRBP]PLQ0oPLQ0=H0WXS`S0=P3!#<}/pP6Q0yI0TPmQ1<!#;l%k!#;l$@!#;l'JRJP:P?Ph%<ZS1<%<3Rp;TSS0oP]P3PBQ0c%^p,;7PBQ1J,1{Rp11hvPMPB11hwRv!u/$A15Lp!s:$7LxRB=dLwQ1AQ0t9txQ1`hw!#\g&vQ1G!sk$P=PpPvB02{!#x/+{!#x/'!#x&&:0o&08JN;0U!w3+1?!w33!#Ko$d#9!#K\$Rw!$+5%IC@!#A:$JPtQ!yx%p!yx$!yI$NPkQ0f#9Rv#PS0f,5L!wD-!#A-'J!wD/V!wD$JP]Q0=PZ!w40w!w4/B!w4;pRp!w4%Q0oP5PZPJQ0cQ1<#^,;7PJPh11hYPMPJ%lhRY,5LR7Px!s6%B,5LP7AtxQs1`h!#`X'YQ1W,1{R7P=P7PY!vo$!#`U'{!#`U$Q!#`R'!vn%p!vn+!uz%!vn+!$0:+G!$/z2Q0GCbPQPVPQPVC@RIH0E!#S$$!vv&0}!vv$Pk%Av#R!y-$R5!vp,!#Re3YPCQ1T!#3/$32Rp!#5J$32R?Q0wQ0:D=PmP5!#4d+!$+/-I80DxR5PdPMP515L{RD!s2%%l{R;,5LRYPD!sB$1hVRD!vf%YPMP5AdLBVP7B0CxQI1`hV!vf'D11KV,1{RhP=PhPD!vg$V!vg'!sI$;P{&0p{DyEK&0kd!#Od$Q0B,z3R{g02KZR;-0QLRD9_L6%{ORh54MX1MPMP<!sN$O20QL65_L=4MhX1MP>15L620QL<RI!s='3=PMP3A_L6I!sM'M%{3RxA4M6!#Nd$MxA_L3I&1D3EG15L>&0k3EG%l>&0p>Dn!#P$$>=_LI=4MxeA_L{!s0%P;g02L?EG!{3%3R;At3QsEGA_L;DPx!#]%$Q1P!wg$P?Q1:!wR$RxPmPv!wT'Q0H!#A#&Q1;<1CsRsPtPxPmPh!wx,!xa's!xa'3Q!#oP$]P0Q!#8X%172RFUp+01LRt#0RsP?PCQ1L=2||R?!#<H$32R~!#T{%0i52WR[Q0_Q0KPH!#8z,D3D3P^P6PmPyPA!yG,!u]$O=_LD!#X<$P:P@Q0mQ0m%<n%<O;TSRSPFQ0b!#x_:Q03!#x,1Q1O^0=P6p+01MRh,7LRD!$>N&L1B!t,&sS#N'15?@17LOR@11@KRS/1_RA']Rm11SVRk,]@P=P=&1A=RxPaPx1]!$Jk,P@P@%C@PAPk!#{M+SPS%CSP_PV!#{L%N<0s!$A%?Q0jQ0[!$@m7Q0k,]6!uC+NRc,7LRS!$Ha,Pm17LtRm/1KRa/1_11DK=?G!$@\$PmP6DnA?FamP:p+01QRap+01PRmp+01ORFPcPhPtPOP3PdP<P9!#S57!#?M9MOoPj%{aP1PyP6PzF894E8Q0J17LmR8/:VRaP8!$A8&61mr6Q0?A?6a83~3~XIP,qPXGM,qMXhEQ0hQ0~P|!#_g%sQ1TQ16!z=$%0cRa!#c,&8!z^,8D3PC!#uN%R=Q0MQ0vQ0_Q1FD3RK%0hR_Q0|92?HQ0}P[D=D3Po%{cR[P}PyPGPzF8RkPMQ11Q1QP|!{[%PaA28R0FU%!#vC$!tb-PpFURpPCP|Q0a!#wB$WD3P_P~%0FR~P=PH!tQ-!{Y$1%{mR=PrPyQ07!}+$mP!w<0Q17!w?$!w<KPjMOoP1P!sz$!w=%54E!w<%FRL/:VR=PL!w<&o61mo!w<&=L!w<0R=Q1dPPQ0i!uB,P!vN&RFUP~PKPCPp!v+$H!w6'=D3Pr%{FR8PoPyQ0!tM$!uF4Q1bP<Q1d!uGKP1MOoPrP!s{$!uI0:SVR8PS!uD&}61m}!uD&8S!uD&PG!tL5Q1\!tO%!tMJPr!$Eq$!y-/z94Ek!tR$DVRVPD!tR&^GRy1m^GR[20I:GR:A?GVDRV'FRD'FRG'F1;EzPyPGQ0cP[PDQ08P:PVQ0`P6H0L!s%-tH0t1qM=eH1>!u:9!u5L!#Ib$MPY000keb<b?b>M?ObCM?O!s%%W;!#Gw%1020101P6O1b;b1M?OQ1=Q0@+00e!sQ%!s\$!sa'bCbObgbAb<bFb@bDbQbRbKbEbLM?ObObf!sA+XbDbV!sE,!tO$M?ObAbPb@b<b>b?W>X=`P9P6O2n20!#Lm&12!#`|%W?WZ!sD7!s/%b[!t7&YWPWAWDWEWHWdWWX~MX}MX|MX{MXnMXmMXvMXuMXtMXsMXrMXqMXpMXoMXbMXaMX`MX_MX^MX]MXGMX\MXlMXkMXzMXyMXxMZ03MXeMXwMWjo"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section STRLEN.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte) (lo : Z).
  Hypothesis STR : bytes_at asegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
  Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
  Hypothesis PAD : (- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack).
  Hypothesis ACC : accessible m (bv_unsigned a0) (Z.of_nat (length str) + 1).
  Hypothesis SV : shvis m (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1).
  Hypothesis ST0 : stk asegs m lo (bv_unsigned sp).
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - AINTRIN_STACK.
  Hypothesis MI : mem_inv asegs m.
  Hypothesis AC : ACONST m.
  (* [comment removed for export] *)
  Hypothesis N40 : Z.of_nat (length str) + 1 <= 2^40.
  Hypothesis INM : in_app_mem (bv_unsigned a0) (bv_unsigned a0 + Z.of_nat (length str) + 1).
  Hypothesis DJ : bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0.
  Hypothesis RSL : rw_cells asegs m ASTRLENP_CELL [C8 (Z_to_bv 64 AREAL_STRLEN)].
  Hypothesis CFI : rw_cells asegs m ACF_ISTRLEN_CELL [C1 (Z_to_bv 8 1)].

  Notation sa := (bv_unsigned a0).
  Notation len := (Z.of_nat (length str)).
  Notation POST := (astrlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m).
  Notation SP2 := (Z_to_bv 64 (bv_unsigned sp + -2144)).
  Notation SP4 := (Z_to_bv 64 (bv_unsigned sp + -2136)).
  Notation W := [(bv_unsigned sp - 4096, bv_unsigned sp)].
  (* [comment removed for export] *)
  Notation RST pc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x28 x29 x30 x31 mm :=
    (MS (mkR x1 SP2 gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17 a0 x19 SP4 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation FRAME mm := (rw_cells asegs mm (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac prep :=
    intros; acb; unfold AINTRIN_STACK, ASTRLENP_CELL, AREAL_STRLEN, ACF_ISTRLEN_CELL in *;
    pose proof INM as INM'; unfold in_app_mem, AHI_LO, AAPP_HI in INM'; rewrite ASHADOW_BASE_val in INM';
    pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; change (2 ^ Z.of_N 64) with (2^64) in SPR;
    pose proof (bv_unsigned_in_range 64 a0) as A0R; unfold bv_modulus in A0R; change (2 ^ Z.of_N 64) with (2^64) in A0R.

  (* [comment removed for export] *)
  Section JE.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 1778552 [C8 (Z_to_bv 64 1823096)].
    Hypothesis C1 : rw_cells asegs mm 1823096 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1778560 [C8 (Z_to_bv 64 1826408)].
    Hypothesis G3 : rw_cells asegs mm 1778568 [C8 (Z_to_bv 64 1826416)].
    Hypothesis G4 : rw_cells asegs mm 1778576 [C8 (Z_to_bv 64 1826400)].
    Hypothesis C4 : rw_cells asegs mm 1826400 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

    (* [comment removed for export] *)

    (* [comment removed for export] *)
  End JE.

  (* [comment removed for export] *)
  Section JR.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 1778552 [C8 (Z_to_bv 64 1823096)].
    Hypothesis C1 : rw_cells asegs mm 1823096 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1778560 [C8 (Z_to_bv 64 1826408)].
    Hypothesis G3 : rw_cells asegs mm 1778568 [C8 (Z_to_bv 64 1826416)].
    Hypothesis G4 : rw_cells asegs mm 1778576 [C8 (Z_to_bv 64 1826400)].
    Hypothesis C4 : rw_cells asegs mm 1826400 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

    (* [comment removed for export] *)
  End JR.

  (* [comment removed for export] *)
  Section JQ.
    Variables (mm : word -> option byte) (fjunk : list byte).
    Hypothesis MIm : mem_inv asegs mm.
    Hypothesis STRm : bytes_at asegs mm (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis FR1 : FRAME mm.
    Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -2144) [CB 2080 fjunk].
    Hypothesis STm : stk asegs mm lo (bv_unsigned sp + -2144).
    Hypothesis MU : munch W m mm.
    Hypothesis WM : wmono asegs m mm.
    Hypothesis G1 : rw_cells asegs mm 1778552 [C8 (Z_to_bv 64 1823096)].
    Hypothesis C1 : rw_cells asegs mm 1823096 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1778560 [C8 (Z_to_bv 64 1826408)].
    Hypothesis G3 : rw_cells asegs mm 1778568 [C8 (Z_to_bv 64 1826416)].
    Hypothesis G4 : rw_cells asegs mm 1778576 [C8 (Z_to_bv 64 1826400)].
    Hypothesis C4 : rw_cells asegs mm 1826400 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
    Hypothesis L64 : len + 1 <= 64.

    (* [comment removed for export] *)

    Section Loop.
      Variables (q1 : Z) (qj : list byte).
      Hypothesis QA : u8arr asegs mm (8 * q1) qj.
      Hypothesis QB : 8 * q1 <= sh sa /\ sh (sa + (len + 1) - 1) < 8 * q1 + Z.of_nat (length qj).
      Hypothesis SR12 : 2147450880 <= sh sa /\ sh (sa + (len + 1) - 1) < 17594333495296.
    End Loop.

    Hypothesis SVm : stk asegs mm (sh (hull_lo sa)) (sh (hull_hi (sa + (len + 1)))).

    (* [comment removed for export] *)
  End JQ.

End STRLEN.
(* [comment removed for export] *)
