(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Bytes ZBridge TacX SFModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface N6_tac N6_mem_is_zero N6_rip N6_quick N6_memset F_strlen.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import N8Store.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_N6_strlen () := KReplay.lz_vm "#$AKK47Corelib7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00!t4G1C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI!sw+4Init9Datatypes6op!tE#00C89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib3Mem7mem_invC13~~~!um>Z02C!um@7Z_to_bvK!tUS5Cells4cell04!tV3!uc24list!vW#!tX?;bv_unsignedC56Stdlib6ZArith6BinInt1Z3sub!sC<2le!t1AD!t1-_in_rang!sYB:bv_modulus!tF>t!xV25Logic3and00!xq<4prod!xoV5Frame:munch_refl!wD%!snZ5!sn$!si`:wmono!tY-!xw<3nat02!vg<6of_natC!vk78iff!t1%!sd;>pow_pos_nonneg!yZ=pow!sC<:!sk#!sg%I!{5A0K4!sj&9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr02!sIE1!sIE4C!sI55Tauto8B!t[&K!w_72eq!~9#!sb4:Z!uC+=Z!sn$CheckerC!v8<4find!sqAC!sq0_sou!sX8;ZifyClasses;rew_!yT%v!{HZ9stk_carve!{G%I!v#9x00c!t/O2As9N6_strlen<tryinit!{%#t!}F`3mkR!}?B!#9u&2!t1T8PropExec7seg_rom!tyZ6MState2MS!#:cE3!z}E!sI7!|a:1!~y=addK!#=u?5Instr5i!s+#08K!#>IG4tre!#>vK4sext!sQA3Sem5alu64!x+]8alu_addi!x,Z8StepFast8sf_congT!x5'!v\L7!#A1W3le8!u&&!#=O?6bv!uV#!vh;?!s<26BvBase=!#AE#le_bytesK!wMD4core01K!#=z@1K!tTJ>!t#$!sE+>machine_resul!#Ax#!t6'5Lists7!s+#Def5skipn!vnT4!x3#Arw_cells_cb_spli!#4'Z!yr+9b!w@#!{-$!spY!tf$D!#C0'!#Ey%!x=$!xh&!#>_6eq_tran!#C-<9add_assoc!sg86eq_sym!{q]6sf_ad1!|`c=!sm$dr_ztobv!stc@sf_store8_direct!swc7sf!#EL^!tg0!~g#all!to%!#;:Z!#KO#;!z{'_ok!so`8!{l1I!#A%:0!{<Y>!||+b!#@I#!ty_:!so%siz!vZ&!#O'_1!tZ`5c!tU,!siZ7!tU#_a!#3;_!#4{+!yi$!x{]!#41$!#Sm%!ss&c!#8c#!sw_!xl,write!zgb!vM#up!yZ'!#@b;leb!#GHA6eq_iff!sLB9and_morph!sOB7!#H?%!ta34Znat5Nat2Z9i!#Ne&K!#K<;G!#C6&3!sJF8!}_9or!}_V7S!x]#Dj:chunk_disj!wpZ!sp'!zU,frame_d!sw&!uOF5!y5U!#I{#6inside!u/b8!uy%in!zi`6!|H`!tZ'>!#X@$!|H$!t`^!v<$;!#WY$!}</!#C%X<!t]%to_mem!uQ\<stk!uO3!#]`@!#AJ&obliga!s:#_!#_FA9bv_!#_DA6shiftl!u=T!#Oz+v_auipc!#5z^F!#C~6_r!v4'!#D$9in!sJ#!uwDconcat!uW^b!uW/!#L[M!#So]6v!#Ng-!zeY=ov_read!#LF$!#M'Q@!#L~&!wV#word!#daDextract!#V~C1!v5T!#Oj#sxb!wH'!#`2?2!t,XAsext!u9'!up$!{6_@!#8J'!wG$a!#HOc<sf_load_goal!zGT6!#W,H9!#n}#_set!tw]?!#IX,!u##!tzT>I!#S>h0!tBN5!v>I6!{K#qbC!z><negb!xRabranch_!#6L[!#ZA31!#6B=6!#6B$!sB89False!sE$!xz`!xr#!#Q<1!#:$:7add_0_r!}%Z!#90&lit_self!#<AF!x@#not!#\DE!u~V!#ct%6ret!x?]!sk&;!sk%_fol!|aU!#aiT!#Ag%stk_releas!#Ag'!#I{?5mkrel!#mH7!#un#1K!#jb:!#8bT4!#cX#evt_don!#7S_8!#7S&!skZ!#kG%stk!sg`5!#Eu#!w-H3inj!wQEapp!#OjB!sK$2!#KXE4!#Ve_5!we[!xR#3evt!{Y'!$'SB1!#kcN!#>gX2wa!#6Q2!#en06firstn!#6T77f_equal!w8F6!tlT7CodeTab;!{{#step_!#6q&I!x'_0!x'V2As5ASegs5asegs!x,'!v0'!#rL51I!sD?0!{/68!{/#Inst7Inj_Z_Z!#}R;!$#h#0!#s2C3Op203!#{X;5eKind!#~_<uni!t49!se%4ki!#5X5!sf31!t-=bool!$3t-!sF81!#9WZ5Wrd6!$1J%I!#9QL0!#C4Y=!#C4&s!tK#!uM>!x&$!#9-84True!uhR!zW+7ct!#E~#!zYC!$7j+3I!tS=!$'b6!$$O,;!#@x$!tk$!zGK1!#=wGaluop!xdV!#32&8ct_entry!#?;Mmsize04!y<A!#v#+0!vV85!#E6#!$<+>1N!uzJ!t^%1!#|-D2w0!#CK[w0_!#m6'!tdG;!#I@%cond!$?K-!}l82!u2G1!u2]1!u2,".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm2dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeq95bvmap01Z37Corelib4Init5Logicta3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~v45asegshfbbv_unsignedk14prodta2ex46Stdlib6ZArith6BinInt1Zhl13subk14Nonek14consk13nilk14pairta2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hp03mkRhp05munchhp03stkhp05wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~huc2MShuc6ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ij97mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ine7seg_romhf7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~it24cellit22C179OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9N6_strlen~~~~~~jhcctryinit_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~jmb3evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~jqd8rw_cellshl12le" s.   (* [comment removed for export] *)
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
Lemma tryinit_body : ltac2:(zQ "h60!h9!jc!hif!jge!is8!hj7!hn7!jh6!hm9!hn0!hne!l9!sf!jlb!jq6!hsc!htc!ii9!in3!ird!ju8!jv4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$c@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@2$h2$2^1>0@4$h4$2^2+hsgvh8@3$6$3@1$7@2$4@1$0#8+1@3$6$3@1$7@2$4@1$0#8+1@1$a$3>0@4$h0$2^3@2$8@2$5@1$0#k0^i3+h0@2$5@1$0#k0^i3>0@2$h5+hgggnvvvogg0@2$8@2$5@1$0#k0^i4+h0@3$e$2@i0$d^i6^i5^i4^i3^i2^i1^i0^hf^he^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^5@7$h1@hf$f^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7@2$4@1$0#k0+pnuvc^6@1$9@1$1@1$0#k0^5@1$h3$2").
Proof.
ltac2:(KReplay.run1z (kr_t_N6_strlen ()) [] "#%,@p'0h04__x1h11bi001bh21xi011xh31zh47__arithh54__ffh67__sat12h7!s0&3h88__varmaph95__with:1th;1Kh<2STh=4junkh>2FRh?1Hh@2MUhA3ST0hB4__p1hC3sfEhD2C5hE2MIhF2WMhG2a1hH1mhI2m'hJ1yhK2CHhL2HBhM3HB0hN2HahO4HeqmhP2LOhQ3TCkhR3TCshS2bsi022bshT4cstrhU1nhV3DJchW1FhX3INchY3SPRhZ3ST1h[1ah\2a0h]2a2h^2a3h_2a4h`2a5ha2a6hb2a7hc1ehd2fche2gphf2m0hg2m1hh3ms'hi1ohj2rahk2s0hl2s1hm3s10hn3s11ho2s2hp2s3hq2s4hr2s5hs2s6ht2s7hu2s8hv2s9hw2sphx2t0hy2t1hz2t2h{2t3h|2t4h}2t5h~2t6i032tpp%0p%1p&0p&1p;1p;2p;3p;4p;7p;Pp;Op;5p;:p;6p;<p;;p;8p;Bp;@p;?p;9p;Ag0000j17Tg000Uj1dTg0013k10Y!s0$Vj1:Tg002;k21v!s0$gS00k10<Tg003Ik20ITg004Lj1A!s/$jj25k115Tg005Pk11lTg006Tk10MTg0074j26!s/$^R0j29Tg008;R1j2>!s1$Wk21!t'$9Jk11!sE$:3k20O!s0$OR2j2E!s1$jk20NTg00;Jk2!u9%<Rj3\Tg00=Uk21!t4$>]k10@Tg00?<R3j1!tR$?\k10cTg00@:k21o!s0$bk21mTg00A?k31k!s0$ck10[Tg00BCk21i!s0$ak11!sb$C?k11`!s0$jk21]Tg00DMk20!vQ$E0k31!t[$ESk21!vn$F5j2;!s/$Ok21TTg00G;k31R!s0$Zk41!vk$HLk40!vU$I7k71GTg00J>R4j2!tn$JXlPUTg00KelOnTg00Lfk10XTg00MHk11!ue$NPj78Tg00OQk10z!s0$ok30PTg00PRk40_Tg00Q=R5j21!s1$Zk40!vz$RFk11!sc$S3j3Z!s/$^k30CTg00TFk30BTg00UOj5xTg00VXk40hTg00WDk10gTg00XCj3D!s/$hk20eTg00Yek50!y/$ZNj4p!s/$nj2!yn$\6k30!yX$\Tm:0!zG$]bj3tTg00^lj2bTg00`=j6!xb$`[k303Tg00a>k40!tz$aZk50?Tg00bak50!ye$com<0!sa$e@k102Tg00fHm;0aTg00gYk31uTg00hbk31!t:$ihj34k1!{4%jBk51!s[$kMj1qTg00lUj!z^%mYj!xb%n\k20!zg$oam:11Tg010ok710Tg012@m;0~Tg013Kk30}Tg014Qk20|!s0$nk30{Tg015Tk60yTg016=k40v!s0$dk10uTg017Ik61j!s0$mk81hTg018Qk20Z!s0$kk41bTg01:5mB0rTg01;Fk71a!s0$jk31_Tg01<nk31^Tg01>6j1eTg01?:m@0qTg01@Hk60xTg01AQj3kTg01BUm?0WTg01Cak20;Tg01DTk20VTg01E<k21[!s0$\k21!tX$Fdk21XTg01H7j6F!s/$Uk51!sk$I=k21!sa$JEk21UTg01K1j2!ul$L8k40!sW$M=k10mTg01N=k40T!s0$fj2cTg01OHk11STg01PGj3g!s/$gk11QTg01R4m<1PTg01SAk51NTg01TNk50!sW$U:k50!sN$Ujm;0RTg01W:k51H!s0$fk11JTg01Xnk41KTg01YZk31LTg01ZGk11M!s0$em91!tv$\2k41ETg01];k61O!s0$Wk20!vZ$^6m:0wTg01_Fk10n!s0$gk10!x4$a4k20!uw$aYj3YTg01b>j1!xx$cCk11DTg01dMk31CTg01e9k81BTg01fBm<0p!s0$gk40!tv$gBk40i!s0$\k41?Tg01hak41dTg01ifk41>Tg01jgk3!xe%kjk41fTg01lMm<1=Tg01m2mB0s!s0$Xk71!vz$n<k20!v4$o@k31;Tg020@k30]!s0$cj4PTg021Pk10LTg022Nk30`!s0$mk61:Tg023Jk71p!s0$nmA1qTf0R6#7!s$%p=S%76#:p=G%:6#:p>0D%:6#7p=C%76#7p>04!s/$#7#Ap=Rg0259R7f2R8f1R9=g763gp=Tg026=R:P8P9P6H1dp=JP!s4+>p=?!t,$#:#:p=ig027?R;/>6p=Vf3R<g027]R=P=P8P9Cp;g6p=WB1e:96p=l&0@6$0@p=r1;=6p=BP=P=g028;P6H1fp>14g028_S01P=!s$$3P3f5R3f4R>P<!tT%N<1=p>1s!sH&!s$%0P6P9P8P0P<P>P3f6R0f7R?f8R@f9RANB0sp>1r!sR$1P?P1P0P3P!sz-0pp>0^P=P9g029>P6H0_p>06!s6%eS02g02:DR1P1g02:dS03P6g02;DK1gp=og02;dRBg02<DS04746p>0720J8!vy$p>0H%76#Ap=QB1;!v,$}A4=96p=[P=!tX,EFp=j20;96:0]<8p=@%A6-0;9!s5&ag02<dRC/c6p=0PCPC!sb%CPP9P6CPp=3PCP81cC!s5&K!sH&C!t-%CPCPp==g02=hRDP=!s:$p,c8,;<p=I!sM,p=2g02>TRE/v6p=L&0L9=k86p>0fB0`896-0J<p=zB0`><8-0J3Ag7965g7p=h1c76p=^Q01/;6p=u1689/16,5<p=f!uf/J1:p=|B0`<89-0J>!vK%13!sW&p=O1196$0Lp>0=%e69k89p>1n1189$0L%e65k<p=_!x|05!x|&5!x|%P0P?P@P!xt&0\P8Q02P1P1Q03P9P6K1pp>0t!sy&=k<6p>0!vz%!y<$CP!v^2>01!sD$!sF/!wH-XB0]9;6p=w116;p=sP:!t_&<g02?[R5!td/f:RFg02@:S05f;RGN?0Wp>0o1196,58p=`!xp&p>0G1E96,E8p=~P:g02@V!t#'!sx/PFPGf<S06f=S07f>S08NA1qp=Hg02AZRH#7RI#7S09#7RJ#7RK#7S0:#7S0;#dRL$0YRM%:IS0<#dRN01vMQ0:#dS0=$0Y%dJS0>$0YRO$0<\MRP20I:6S0?%:HS0@#:RQ#7#S#G$0D#C$04S0A$0D#RRRQ0>%AHS0B'5S0C$1lS0DQ0D&0M7RS3TS0E5J9fRRT,6LRU%AKRV'9=?8UQ0;#7S0F#7S0G#7S0H#S#i!s$&S!s$$RRUfSRW,6L/9V'>fTRX-1<L16LXRY#V&19L-0OY'E20N==S0IfUS0J,6LRY/9VPYQ0I$0MS0KCWRY0173A\Y33216:01l00P>fWRY,6LRZ/9V=??ZP:P@fXRZ,6LR[/9VR\P[&0@5S0L$0@#r#r#rR]!s-%#rR^P6%M^R_,9[R`,>\1>\\P6X2=Ra1>96$0cXJ=X2=S0MP\P\%B\P`P\PaPaPa1996$14#BXH=XU=P[P[%B[P_PVPaPaQ01%M6#BW2P^PV%BVS0NJ1sS0ON:1rL0^%AIRIQ0;#AR[+1oS0P20O;I%V[21mI[Rb-0O;[[S0Q%VIRcg02B?S0RB1kI[9UWNS0SQ0R%Vb[^NcS0Tg02B[Rc!vM$U&0[cS0V21i=9S0W&1c=S0X&1`=Rc21]=HS0Y20:=VS0Z61\=RH006H'oQ03-1YcS0[P6P8Q04,;BR[21T68$07dB1R=;9H1IS0\b5b8b9X0=196VRd/>d^0=P6f[Re,6LRfO1b4b6b7H0lK1GA?@\`&0[OR`fYR\,6LRg/9_RhB0H^6SRi5JAX=`'m'EP219gV=?AhfZRh!yQ$_=JFiX=`,m`PePhP\PZPYfVS0]Q0JPXPWfPRgfOR2fNRjfMRkfLRlfKRmfJRnfIRofHRpfGRqfFS0^fERrfDS0_fCRsfBS0`fARtf@S0af?S0bQ08Q07Q06PGPFMPU!tA,Q!t?+PTfQRuPgP2PjPkPlPmPnPoPpPqQ0^PrQ0_PsQ0`PtQ0aQ!sy'MOnQ06Q09#:S0c#GS0d#:#iRv#G#i#C#QRw,5LRxPG&0XMRyPF&1@:RzF8'}P619fV19f_5?GQ07f]Rf!v:%;J!v9'4P`Q08f^S0e!sA/f_S0fQ0ePff\R4!uD,!u>%P!u<PMPUQ!ss&P4!v79!swH!v%$aPxQ0bPyQ08P!u[&Q0af`S0g!u6+Q0PQ0QQ0SQ0TQ0UQ0VQ0WQ0XP=Q0Y&0zKRK-0:=60P=Rig02CGS0hPHH0_,ocQ0[Q!zh/16KS0i/[!zi&dS0j,6LRd!zj'faS0k,6LRH/1K19HV'[fbS0l!s9%9VB0H^<S9Js6X3=P911HKRHP6DjQ0`B0H^8S7JHfcS0m!sX'Q0_??6!sU$?!sU&9DjA?sHH19dVQ0IP6feRH,6LRxQ0KCW?\rrX3=Q0811dKRrP8DjQ0IPrPd!sF$Q0_Q0_3\19xV1>U!t%$t11xKRxP<Dj1>UxffRx,6LRt/9VfgRd,6LRr9?q!sR$s11tKR{P>DjQ0^??{tfhR{PdPxPHQ0jQ0mQ0lQ0kQ0g!xRSMPUS0nP!ss9!yMSMOnPoPwPpPyPqPzg02CnS0oPNPIPN%:Q#i#SRQ#7$04#CRw!#:|$#QC@!sH%PwCaQ0@#7S0p#7S0q#dRw%AQRQPwPQC@RQH0ES0rQ09#ARt&18CR|%0nP|%0hS0sP|D3Q0l#0S0tAK|T|S0u%0xS0vP|Q0]#0P|Q0e#0S0wAK|j|D3S0xD3%0{S0yAK|Z|Q0g#0S0zAK|g|Q0j#0S0{P|%0XP|%04S0|AK|l|D3D3S0}&0XCRCAK|\|S0~Q0k#0S10AK|u|%0HS11P|Q0J#0P|%0fS12AK|k!sb%1311rKRk,5LR}P|%0YP|Q0f#0S14AK|2|D3S15Q0m#0S16AK|W|S17%0eS18AK|m|S19D=3KD3RmPo%:v$04S1:#7S1;#7S1<#7Rv#RS1=,5LR2!wW'F8P[g02DZS1>$0<R~20ND=S1?Q0rPtCIPMQ19Q18P|Q16Q17D3%0dS17Q15fiRD#0S15Q1!u7%PCQ0s=2||S0sQ0tQ0uQ0vQ0x!vs$%06S0uQ0}D=PnP2PoPyPpPzF8#LX:MQ0oAZwLQ80CdP}B0BdwQDxQ0nPmPoQ1=!yV-EbS1=!yV'JS0n!yD%Q0B!s'$C@S19Pw%AJ!y:'S0rH0hS1@PtPmPo%Cv#QS1A,5LS1BPpPy%M]Rv,1kS1C&0g{60fqS1DPzF8S1EP[P~Q1?Q1@!v,$:PzPqQ0r9ZwLS1@9DL}S1FP]16L{Rm-0e]Q1Dg02FNS1D00NPS1GQ1DPPQ!v>%x11mKRm,5L#0!v'&15LtS0}9DL!v4$I05P6Cp'vX2PQ1E#LS1EP:PqPkP]POP]P?!s-%B0AO]?CzS0xPSEhR2P]Q0xQ1FP{!sU%B0H^?SR^P2P]P]P>P[&0[7S13/;2S1HN:0d&0<7R7Q0x#^';%u]S!sg$&0zJS1I,1rRJQ1CPMQ1F11kQS1C!vS$J15LJ!s<$PLPLP}PQCfQ1JQ0r9t}w1bkQENPM&1!sR$Q1C11KQS1F,1rR}P=P}Q1CB03rKQH08D|ENPrQ1IPKP]Q1I#BS1CI0?I0>N<0bQ1E$02N;0a!uy&!uD-B1u^]]$07eQ1HQ13B1t^]]742eN:0dAJqk2P:PpPm!vV&@!vV-@PSI13I13R2P6I12%Vm%q2#M,1m/>b'EP:PoAOLDKRm00=vR2fjRk#<R^PpQ05P:Po!s}+A!s}-ACzRm!wT$rP]Pm%]^P9%^mR},;7209r]=47}e%]m#uN:11K10B1no2^-0I:P:PnAOLkKR^!t$&F!t$-FCzR2!t$$oP]P2fkRm#<R}P8%^2Rr!t,%o]=47re%]2#uQ05N;0~PnP^PvP}C_B0}o]}7J^Q0N!t-&GflR^#<PSEh#q#M/[VP[fmR}#<#]#M,1v00|V$07AOL}KRo#VR211o_S13/>bRr'E11oVS1H/>b,E2S1EP2PrP2PaPVO1S1K,1oRr/>bp-0RJ/;2A4J22e:0{22PaQ0MQ13Pr!#HT%1!#HT/S13PoPo%BoP_Q1KQ0ON:0\PbPb%Bb1[bbeS1LL0^J0yP>H0vQ1E!uJ%Q08foRr#<S1EPSEhS1M#qR2$0u%M2#V!#?m;c!#Qm+20:=U006i,oc&0X120:=R20:=I60P=!s?&!sW/P<J1jS1N60tcL1h!#@<1XBJQ0i,>U11RIS1O119K'>00Z8[^0=^BJP6frRU,6LS1P/1KR2/1V/>RQ1PQ06O3!#@a$bTbMQ1O/>oQ1H/>R+0ZS1HeQ1HePRPIPoPVH1bRoePoP:PjfnRo=OLKS1HPvQ1EC_S1O!|4$MPVP]Q1EPjPRQ0EPI!#V+$Q05%BIS1EP6PlNB0rQ1OQ0E7JR16LrS1O/1KRl#VRj11l_S1M/>bS1H'E11lV!xn$jS1PPjQ1HPjQ1K,1l!y/%1;JjA4Jjje:0{jj!xf&MQ1H!xg%Q13PlPl%Bl!xX3Q!xP+0!xP$P!xP'afqRj#<S1P!xP%L#qS1K$0uQ1K#M!xSK6ii,ocS03Q0Z:0P=iS0ZQ0Y+06,ocK1aQ!x?%!x<8Q0i'>S1NQ0i/1VS0i/>6'E00Z9!xA'g02G7S02ftRi!xI$KO2!x8-0IPl!w$$KCWR1@1_lVeB1^1lVR1eP1P:PgfpR1,6LRl/1KS1OPvQ1P#eS1HH00S1MQ1OQ1L!x;%PQ0IQ1OPl!sv$S1OPgPg!#_j$Q05P6PGN@0q!sX$M7\gP:PuPuAOLjK00=vRg%<US1O#eS1MPnJ0xQ1M9kug,luP:PTP2PvfsRu#<S1LC_RgP2!wP'`Q1LPSEh!tU%L!sR$2P?P0P3Q05Q08N?0WA?g22P:PW16LuRg!{I$Pv%<iS0`C_RT!su'!#Jq$!st'0`PWP2PgP@P?P0!st$6!st%T2gPXQ1K/1KPvfuRX#<S1K#eS0MH00PP1;P6S1QQ0JAOLXKPvfvRT#<S0J#eS1RH0094P6fwR2PTPXPiPuPUPjP1PrP^PmPkPD!#FyPMPUQ0~Q15P|%0jS0~Q10=2||S10%0XS0]P|Q11P|%0}!#D-$12P|K01S12FX%02S0eQ17!sX%7%0rS0fQ14=2||%0uS14P|Q16P|%0mS16P|Q18!se$D3S18PCQ0y!sa$0y%01S0gQ0z!sa%iS0zP|Q!#F&$^S0{P|Q0|!sa'0|16LTRh/1KRe,5LRgQ0v!so%v%0oS0kP|Q0wP|D=S0w%0US0lQ0t!sH%t%0kS1SQ0s!#EG%WPZQ1APYPyP9PzQ!#B}&Q0;#CS0;CaS1APNPQPNPQC@S1T20;w;,wwRsH0hS1UPtP!sj$<#:S1<#RRW,5LRnPYPy%M5RY,1eS1V&0g160f9S1W!#B{$X!#B{'U!#B{'9AZwLsS1U9DLgS1YP]20e]lQ1WQ!#Bh&0sQ1SP|!xG$t%0TS0tQ0wFXfxRl#0S0wQ0|PCQ15!w[%5!xM$0Q0]Q12AOL2KS12!#CG$18FXD3P\Q1BQ0}5DLPZ!#CG2X#LS1XP:P9Pe!|F'^CzRZ%<2S0^;TSR\P5PZQ1YP1PG%^Z,;7Q0xQ1YPeQ1VPMQ1Y%seRZ,5LS1VPg!s8$16Lg#s,5LQ1VAtgws1be;ENPMQ1JPZ%sKS1V,1hRgP=PgPZB03hK;!#BN&hPKPKP5%BKS1Y!#BK-X!#BK+9PeP\PGI12%Ve%q\#M,1e!#AR&8Q1200=YRbQ1PQ07!#AJ$8Q1!~&'qCzRq%<lRe!uW'qQ1P#]Q06%^qRh!#@?$\5=47he%]q!#AF'Q1H9k8b!#AG%<AOLlKRb!s|&pCzRpfyRq#<Rh!t#'pQ1OQ07%^pRZ!s}-Ze%]p!#A>+<PbPYQ1MH00Q1O:0}\57JbQ0NQ1LfzS0N#<S1O;TS!#A@'Q0`!#A=$Y!#A=%P:P0f{Rb=OLKR\PYQ0MH00RpP\Q1Kf|R\#<;TSPVP5Q1KP0!#<N&8P9P6Q05Q1E!vH$6NB0rQ0E9JpRP:P?16L\S1E/1KRpPYQ1RH00RZPpQ0Jf}Rg!s{,0JQ0IPp!sn$KCWRpP4P?!#=U'Q0!#86%A\p4ZP:PfP@AOLgK!wn$pQ0^#eRZPGJ0xAk@pZ,lfPAf~Rf!uE$ZPYPeC_RpPZp+01@R4#<=TeSPVPePAPZPZ!#r2%GN<0oA?pZZPF16L4Rp/1!se%hC_S0^!sf%ARe#<=ThSPVPhPFPZPp!#rt%!sf$Q0^??ZpPGAOLeKPYQ1OC_PPQ1QQ06p+01BS1Q=OLKPY%<bC_94P6PMQ0<#7S1O#7S0^#dRZPZQ0d#7!#_h$ARpPZPpC@Rp+0VQ0q#A+1[R0-1ZnS0qQ0A#G#RS0A,5LRh94M6X1MS1EPMA`L0WQ1E1;Mh16Ln9`L0S1E21XW0EFQ1E=4MheQ0q!s-&=Q0=PZPwPp15w;I1W7ZL9DLnS0=21VnpEFQ0=PhPMe54Mp+01ES0qp+01DRnp+01CRZQ1QPeP4PfPgP\PqPlP!#:'4oP}!#:/8MPUS0mQ0vQ0t!#VF$0vQ0k!#7B$kD3%0ZS1EQ0l!s8%lQ0N#0S0JP|Q1SP|D=S1SQ0q#0S1R!#8}%S0z%0\S1KQ0{!s6%{32S0M%0eS0`Q0g!s;%gQ0wQ0y32S1LK01S1MPCQ0]=2||R0%0gS0]Q11!sR$1132S1HQ1Q#0S1PQ0~!si%~%0qS12Q1532S1X32S0xPLPLPnPKCf#0S1B!#;D%S14%0bS18Q16!s6%632S10!#Yk$Q0f!sw%fQ0eQ1732S0s32D=PHPWQ0jPyP8PzPNQ1O#AS1OPNQ0d#G!#\J$01UpRpPtQ!u7%xQ!tC$%0hS0dQ16Q0|Q0sD3S0sD=S1WPHQ1<#C#QS1<,5LR!t-,F8!#9x%Pp!#X{&7Q0eP|!si$fD3S17%0nS1ZQ10p+01FS1[#0S1\!#Xe$1]PC!#<E+!xA$k32S1^Q1EQ1S32S1_PLPLQ0q!v='`Q0zQ0uQ0{!#B^$D3D=PxPWPHPyP<!#YG,=PhP6DxQ0mQ!u9&!u,+Q0o!#<}$Q0:#C#CRW!#_g$G#RC@!vR$PNPWCaPwPVPwPVC@S1<H0ERW!vR&P015LRRp#!#Ea$1Q1PQ1XD3Q1BQ0sD=PHQ1;#:!#\i$0s#RS1B,5LS1!vY7W!vY'!v'%!uS$k!uw%D3S0mQ!uj&d!uj-S1LD=Px!uP$!un2oQ1<9ZwLS0=80ChRWPpPMPW!y{$hPVCfQ0A=`LVQ1<:0BhwQ0A/bVENDxPM20VwsS0A,ypS1a&0<MRhQ00P`PhP:P<P6Q0LH0FQ0>PLg02GTS1bQ0>&0m6S1cH0T7ZLS1d,cMS1ePyn10110100021010200Q0C$1SS1f,cMRW34X1MS1gPMQ0A9`LRQ1g&0<`S1gQ0D#e,c`Q1g!tO'6Q!sz9=4hWWiPMQ1f1cM6=4hWX1M1;hW!tv$Q!tq$Q0C&0MO5gO$0m!tw%!tZ$QEFP:P8Pp!uP%!s2$RQ0EP5Q0DQ0LPpP?Q0D#^RO,;7Q0E0095=47OeQ0L#uQ01Q0LQ0D#]34e20=RYRO,;MA4MpOeN<1PE!#[k$pQ0ACfROQ0A,bREF!vt,8PO!vt&!uU=e!sU-Q1a!sVF1U9DLpROAtpws!uZ&OQ0LQ1dXS`S1dI1NRp!sR$PWPhe94hpQ1[Q0qPnP!#7F-Q0N!#7GOMPUQ1]Q0tQ1M!{-+Q1`Q1LFXRp72CPxQ1B!zu'g02H2Q04PNQ0<#:#AS0<PNQ0F#CS0F$0DCaRhQ1TPsI0S!}6%7Q1ZQ14Q1f#0RRQ16D=Q1\Q0xPCPpD3PxQ0s#C#QS0s,5L!|-,Rp!}$1:PzP<!v3'Q1f!#GF&PNPM!z,$0yQ0wP|Q0`Q0gD3S0yQ1RQ0Mp+01GS1d#0S0LQ1_PCQ0e!#4r$e!ul$f!tp$0D3!#8'%Q1[!#4m&7Q0dQ11520!#3:%=S0dFXI0QPdQ1W!#Gl%x!#Gl$>!#Gl$M%LpRpP6&02pN;0RPMg02H^RpPwQ0B!s'$C@Rh-0VwRO'yQ0B,5LR<!#=z'WPM15L;RW1y6O=4M<X1MPMA`L;OQ1W1;M<!za$WPOCfS1W1b;OEFQ1W=4M<e1yW!sZ$ePpg02ICEF!#hz%h80CpRWB0BpwhEFP<PMe94MW!vk$!y_5b!y_PMPUS1WQ!w8&zQ0{72R!wp$_D3RHQ0d72CPdQ0sPxPyP>!#7z%Q!#;/$H#:!#;/$Q0:-0GN,wNPhH0ERhPtPH!#;9%7P0%0<RH!#7e,D=RpPdQ1;#:RO#RS1;,5LS1X!t2'!#7Z+h!#7Z&5Q12P|Q1PQ0~D3Q1\Q11920Rp+01HS15!xb&e!#;W$32S0x!y3%K01S10PCQ0w=2||Rh!yP$g!yx%D3S0w!yP%d!yP&0:Q0mD=P{Q1XPdPyP3!#8B'PWP<P6DxQ1WP!u6%!v3,9#dRW20;W;'wPWPIPWPIC@PWQ0@#APWQ0n#:RWCa%7W#SRW#S#S!vP&20GNW,wNI1HRWPtPpPd%CO#QS0n,5LRO!v3,S0@!v6%>!|h%&1JEQ0@#L';!ta'0n!sU'g02JH!~L$PNQ0^#C!~B$!x%'1OC@Q0p#:#dRWQ0^#AS0^PWQ0^C@S0^H1KS0p!t[%PBPMQ1f>1LL<$1MRpQ1:#:S1:#C#RS1O,5LS0<Q!#ra$!s'$>#RS09!xA$;n010!s#$20000!xR7Q0pPtCIQ!wk&Q0:Q0tPH!#=2,D=P{P6!wS0JMPBPMPpQ0^9ZWL9DLOQ0}9DLO!t?1Q1XPpQ0nQ1OQ09Pt!uY$Q1O#BQ09#BN91FH1EPpPB1;B6A4Bp6RWPBp+01KROp+01JR3p+01IRd!zC$!}&-!#G~'!}%I!|y$OQ0{Q1KP|!|~%!#u<$0{Q0g92hR%0OS0^Q0J!#5;$JQ1EQ0l32S1E!}J$^32S0nD3S1XPCQ18!sM$1SQ1MQ14Q17Q0xD316L3R>/1KS0k!#V<%2!sO%2PHQ0~!|J$HD3S0:D=S0wPm!vi$9Q0<Q!wv3PkPyP@!$&L$^;WP9&07pS10P3P!v,4Q1Q!v-PP{MPUS0pQ16!#xF%ZQ14D3Q!}~&f72R%03S18Q12!~W%32S16!u6%!~5$HPCQ0J!~/$l!v?%!uu$dR{/1K!#Zz$x#0S1MPhPH!~S0MD=S0mPkQ0<PDPyP?!uZ%g02K:S0<Q0454BPBQ0<PBPJP6Q02Q0Rn011!v;,XcBQ05Q04P6J1O!sH$200k6b?W2Q10Q02];dP6O1+0kW;Q0<94BpQ0pQ!tG%9!tG'Q1=!#=/%B!#]b$G#C$04#GCaRpQ1AQ0rI0SRBPt!s`%1>!#JB$>!|p$A!u6,RJ!|a&PB!#<g'?Q1@9DLxRBP]PLQ1bPLQ1cH0TXS`S1cP3!#<|/pP6Q0wI0QPmQ1;!#;k%k!#;k$@!#;k'JRJP:P?PW%<ZS1;%<3Rp;TSS1bP]P3PBQ0b%^p,;7PBQ1I,1{Rp11WvPMPB11WQRv!u/$@15Lp!s:$6LxRB=`LQQ1@Q0r9txw1bWQ!#\T&vQ1F!sk$P=PpPvB03{!#wy+{!#wy'!#wt&:0w&02JN;0R!w3+1>!w33!#K\$c#:!#KS$RQ!$+6%IC@!#A9$JPtQ!yw%n!yw$MD=S1MPkQ1:#:!$$p$:,5L!wD-!#A,'J!wD/U!wD$JP]Q1cPZ!w40Q!w4/A!w4;pRp!w4%Q1bP5PZPJQ0bQ1;#^,;7PJPW11WYPMPJ%sWRY,5LR7Px!s6%B,5LP7Atxws1bW!#`E'YQ1V,1{R7P=P7PY!vo$!#`B'{!#`B$Q!#`?'!vn%p!vn'!uz&!vn+!$02&Q0F!$/{2Q0FCaQ!#O8$I!vm-0{!vm$Pk%Cv#!x}%Rp!vg,!ve'I!#>:&XPCQ1S!~~%32RI!#5@$32R?Q0uQ0:D=PmPp!#4Z+!#N_'0=80CxRpPdPMPp15L{RD!s2%%s{R5,5LR;PD!sB$1WVRD,5LRYP;PMPpA`LBVPY!#N{$!zN$V!v]'D11K!v^$WP=PWPD!v^$V!v^'!sI$5P{&0n{D|EN&0jd!#O[$Q0A,y3R{g02KZR5-0ULRD9YL6%{ORW54MX1MPMP<!sN$O20UL65YL=4MWX1MP>15L620UL<Rx!s='3=PMP3AYL6x!sM'M%{3RYA4M6!#N[$MYAYL3x&1D3EF15L>&0j3EF%s>&0n>Dj!#Ow$>=YLx=4MYeAYL{!s0%P5g02L?EF!{&%3R5At3wsEFAYL5DPY!#\f$Q1O!wg$P?Q18!wR$RYPmPv!wT'Q0G!#@v%Q19<1CsRsPtPYPmPW!ww,!x`'s!x`'1Q!#o5$\P0Q!#8N$0~72RFXp+01LRt#0RsP?PCQ1K=2||R?!#<=$32R~!#Tk%0g52hR[Q0^Q0JPH!#8o,D3D3P^P6PmPyPA!yF,!u\$O=YLDPWP6DxP:P@Q0kQ0k%<n%<O;TSRSPFQ0a!#xG:Q03!#wm1Q1N^0=P6p+01MRW,6LRD!$><&L1B!t,&qS#M'15?@16LOR@11@KRS/1_RA'[Rm11SVRk,[@P=P=&1A=RYPaPY1[!$JO,P@P@%B@PAPk!#{5+SPS%BSP_PV!#{4%N<0p!$@o?Q0hQ0Z!$@[7Q0i,[6!uC+NRc,6LRS!$HE,Pm16LtRm/1KRa/1_11DK=?G!$@J$PmP6DjA?FamP:p+01QRap+01PRmp+01ORFPcPWPtPOP3PdP<P9!#S'7!#?C9MOnPj%{aP1PyP6PzF894E8Q0I16LmR8/9VRaP8!$@~&61lr6Q0?A?6a83~3~XIP,mPXGM,mMXhEQ0fQ0|P|!#_J%sQ1SQ14!z=$%0cRa!#bh&8!z^,6D3PC!#u0%R=Q0LQ0tQ0^Q1ED3RK%0WR_Q0z92?HQ0{P[D=D3Po%{cR[P}PyPGPzF8RkPMQ0~Q1PP|!{[%PaA28R0FX%0m!#vT%!tb'PIFXRIPCP|Q0`!#v}$hD3P_P~%0FR~P=PH!tQ-!{Y$1%{mR=PrPyQ07!}+$mP!w<0Q15!w?$!w<KPjMOnP1P!sz$!w=%54E!w<%FRL/9VR=PL!w<&o61lo!w<&=L!w<0R=Q1fPPQ0g!uB,P!vN&RFXP~PKPCPI!v+$H!w6'=D3Pr%{FR8PoPyQ0!tM$!uF4Q1dP<Q1f!uGKP1MOnPrP!s{$!uI09SVR8PS!uD&}61l}!uD&8S!uD&PG!tL5Q1[!tO%!tMJPr!$E_$!y-/z94Ek!tR$DVRVPD!tR&^GRy1l^GR[20I:GR:A?GVDRV'ERD'ERG'E1;EzPyPGQ0bP[PDQ08P:PVQ0_P6H0K!s%-iH0i1mM=eH1?!u:9!u5L!#IX$MPU/}keb<b?b>M?HbCM?H!s%%W;!#Gl%1020101P6O1b;b1M?HQ1WQ0@'}e!sP%!s[$!s`'bCbObgbAb<bFb@bDbQbRbKbEbLM?HbObf!sA+XbDbV!sE,!tN$M?HbAbPb@b<b>b?W>X=`P9P6O2n20!#L`&12!#`p%W?WZ!sD7!s/%b[!t7&YWPWAWDWEWHWdWWX~MX}MX|MX{MXnMXmMXvMXuMXtMXsMXrMXqMXpMXoMXbMXaMX`MX_MX^MX]MXGMX\MXlMXkMXzMXyMXxMZ03MXeMXwMWjo"). Qed.


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
    Hypothesis G1 : rw_cells asegs mm 1791384 [C8 (Z_to_bv 64 1835576)].
    Hypothesis C1 : rw_cells asegs mm 1835576 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1791392 [C8 (Z_to_bv 64 1838888)].
    Hypothesis G3 : rw_cells asegs mm 1791400 [C8 (Z_to_bv 64 1838896)].
    Hypothesis G4 : rw_cells asegs mm 1791408 [C8 (Z_to_bv 64 1838880)].
    Hypothesis C4 : rw_cells asegs mm 1838880 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

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
    Hypothesis G1 : rw_cells asegs mm 1791384 [C8 (Z_to_bv 64 1835576)].
    Hypothesis C1 : rw_cells asegs mm 1835576 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1791392 [C8 (Z_to_bv 64 1838888)].
    Hypothesis G3 : rw_cells asegs mm 1791400 [C8 (Z_to_bv 64 1838896)].
    Hypothesis G4 : rw_cells asegs mm 1791408 [C8 (Z_to_bv 64 1838880)].
    Hypothesis C4 : rw_cells asegs mm 1838880 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

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
    Hypothesis G1 : rw_cells asegs mm 1791384 [C8 (Z_to_bv 64 1835576)].
    Hypothesis C1 : rw_cells asegs mm 1835576 [C8 (Z_to_bv 64 2147450880)].
    Hypothesis G2 : rw_cells asegs mm 1791392 [C8 (Z_to_bv 64 1838888)].
    Hypothesis G3 : rw_cells asegs mm 1791400 [C8 (Z_to_bv 64 1838896)].
    Hypothesis G4 : rw_cells asegs mm 1791408 [C8 (Z_to_bv 64 1838880)].
    Hypothesis C4 : rw_cells asegs mm 1838880 [C8 (Z_to_bv 64 (2 ^ 47 - 1)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
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
