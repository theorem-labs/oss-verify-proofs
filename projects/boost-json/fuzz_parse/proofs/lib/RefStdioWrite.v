(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic
  ExitSim ShapeAlg Nodes LibWritev Frame RefMemcpyLib
  RefStdioDefs RefStdioWrite_run1 RefStdioWrite_run2 Ref_code_df8e4_e0344 SumWalkTac.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefStdioWrite () := KReplay.lz_vm "#$T@C4ELinuxProcessSemantics?!s<22Fs2FsC47Corelib5Lists7!s+#Def3mapC46Std!sA+4!s+#:firstn_nil!sa,4Init5Logic8eq_ind_rI79OSSVerify6Proofs:boost_json:fuzz_parse3lib8ShapeAlg8realizes00C13~~~K!t319Datatypes4list01C!t5X6t_emit!t1%!siYA!tx'_nonempty!st_=!t_%!vu#_eq!sp_8t_eq_sym!v^&!wMb3!sm%I!ykJ3Run6config00!u7Y4TSe!w`6!s`96images5Plain1M?loaded_segments!vgV4Scfg=hunspell_scfg!uyQ5State5event00!|n;5skipnC!{D;6length!sF<3ap!}U89!s}$_appI!|GA0!sF25Peano2le!u%/!s@$3Nat3subI!~M72eq00C5!tW&6ZArith6BinInt1Z6of_nat!sF<!s}#!sC=max!sC34Znat5Nat2Z7inj_iff!#4477iff!{j#K!u&;1!v[+9micromega;ZifyClasses5mkrel!tj<2le!sgB7rew!tm$!u8=9i!#3B#neg!t6<8max_spec!tX>t!w_83and!xS5!uv%or00!v8,7Numbers7BinNums1Z03K!uS57EnvRing3Pol01!#7=;3nat02!sf6=!sc#M!s4'5Psatz!sOM4!sOK6!sO6:ZM!wi,!v]$!~c$!tL#!|2@!tl76VarMap1!sDC3I!sD?0I!uEC7Formula!wp#!wR<5PExpr!wT/!x;38positive!t}8!sn22!snG1!snE!wsE!uT+!st75Tauto8G!sJ'6!wm<6option02C!sl<B!sl&C!y,@=Z!sT$CheckerC!x%<4find!sqAC!sq0_sou!sX8!#32-;!#32%_rev!#4}76!#B3$!smB6mkapp2!vpF4!sJF3!sJF5!sJF8I!#31?!#4Q,!#475!#9Q+5!}n$8!#:D#Na!#:3'!#6]=;inj_sub_!#9>@6!sM#!#7u7!u@%5eKind!#<<<unit!}[8!se%4kind!#6-=!sf%!#6NA1!#7T?1I!zO@!#5I/0!~AG3!#6BM1!~JD3Op2!y@8!sM6!stJ3!wU=bool!u\/!sF81!#Aq6=!#Aq%ll!#?=;5proj!wS?N02I45stdpp9bitvector;definitions2bv00C!sI@;bv_unsigned!#AS<add!y'@2!sa=pow!#HhPPropExec9u64_range!#G~%!#C~;eq_dec!vb83no!#@@26Specif7sum!x,%!v?A7Z_to_bv!#Cc7!#A-#1!#C~8or!v5>>pow_po!#BqC:!sN#!sJ%!#>??!#;nE3!sIE7!#6`E7!x<P7StepTac6u_Z2bv!#Sl7!vN,!#SfP5Hoare3at_!#MI&!s}64True!#Eq95Fals!#KI#!#N&85Riscv7Prelude5bvmapc!tpO=RefStdioWrite2RI!#P0UB!sj0_run2;sw_regs_bu!#VSW!|p'4getr!sg&8!sgN3Lib2Nd;and_elimF11!xG'!#4<B!|:9!wk%1!#6f;!#BX&0!z:SoreOk9mem_grow!#TOV!sk'>!sk+_refl!sp%!x{_LM!x%_3rdn!|[8!vS51!t0Y7rdn_ex!yw'!#W5I>!|A$!sE+8s!v\#_ok!w:X=!sd'_mono!tW`@word_to_le_bytes!t_QCat!v2#6w!sb%!tX&!{068!#H#$fl!#GdA3inj!sIB9!|m#morph!sOCnot!sO&!uKWD!#[C$_N!v=0!zZU5Frame6in_rng!sf\>!w%%_outside!}h^<!sp&!~Xc?!~X,tran!xl+!wZ@5!#M4#!sK68!sK#Inst7Inj_Z_Z!#?d@4BvWf!}wZseg_rom!#4Yc6LM_!#3u'!#O|Beq!#FN$!sL@8or!zoV!#;P57sw_done!#6I^4mks!#<5V!t]7!yA#sw2!st%!#nRO6CatSim6mstep!#nN'!#d49x!#idZ9rz_!t0%!#93&!#k/T1!ya_!{?#sh!zQd;rz!#o$'!zV'!|U?5bv_eq!y6Y6v_addi!wW3!#NL5!#iB2!#i\&tK!#l;V2!#9W79!#F2#_ind!v]_LM_!#=0'!{`h:!#Ei#try_a!xKd:LM_!#7b$8!#4jdRI!#GLY7Seq!xm#?rdn!t]&_hit8!sqV:SumWalkTac@!st-out_Z!su&!#R:;to!#o:#!t=O<RefMemcpyLib9!t?#!#r\$!|6&!zII6BvBase;!#An&!tSS9Lib!wH$v=!si-!uf+!#X`5<!#?n%!t{%!#_p=!#UF&!~+Yregupd!y#WGrChainAgr_reg_neq_of_eqb!ssV!#X4+getr_sam!#:b&3!#4v$7tac!w^#<!t0#ual_help!}\c8sw_c2!#~1'!}Z_!#7o$!#6~,!tii!#=aW!z&,?rz_w!s0$1_wal!#8j'!#M997!zQ#ind!x%Y:!x%$other!}|9!#fv3t!sH>8!#gg$cc!#Dc>@!#{%$!|\'!#:qQDRef_code_df8e4_e03447W_dfb50!w>V!sv9F!svrE!sv0!#<8O9TASK_SIZE!#eyA2!{q^8pc!tp#d0!z'8!#mQ#add!#5#>;le_gt_cas!#QNY>!#9L0!zLD2id!#7$6:!#7$%ap!#]}^7u_at_l!~#k2!~#-!td^<!$-%'!tiY!#A&?b!tmd5loop1!u\o!#jU3!#u&6!zW/!$-s9!sI#!vGa1!#M,%!uU&!#M,O<!st'Defs7s!#jR#t0!#3cV!#7]'5!#IF#!sh%K!tZe!uLhfi!$4y#!uLU!sp09ssp_cells!#6'V5m_fds!#6_Qfd_lookup!#LQP7FdEntry01!t>Q8m_halte!#{h=prod!#lA<!u=:m_vm_lazy!wCP!#n?$6ret!#M^X!#5E+>!#uB#oundtrip'!#9@7!$&{+sym!#3&]=!zx&_of_!#hS&!#4hb2!smd7LM!#jw,!#3xb;sw_enter!$Eu+!#Mx:8sub_diag!#F@g1!$G6X!#F@8zero!v-h!tj'n!#;@h18!v}'!#5R%!#3nPModel00I!#38X!$19=!$,&+0!#G>iac!#UFV!#G><!svoE!sv/!#F>d4!sp&".
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~0dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~k68realizes69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~ocfloaded_segments37Corelib4Init9Datatypest43nil3h5LinuxProcessSemanticsfLinuxProcessSem3Runv26config3h5LinuxProcessSemanticsfLinuxProcessSem5Statehi75eventk64TSetk66t_emit37Corelib7Numbers7BinNumshme4Npos35stdpp9bitvectorbdefinitionshofbbv_unsignedhme1Z37Corelib4Init5Logichs02eq46Stdlib6ZArith6BinInt1Zhta3add69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Hoare~~~~~~hv93at_hta2lehta3powhs03andhs02orhof2bvt46optionhta3subhs03not69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~imf9mem_growshta2lt3h5LinuxProcessSemantics5Riscv7Preludeirc5bvmaphs01I69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~iv04getrhof2BVhof4BvWfhof7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3libdRefStdioWrite4Loop~~~~~~jkc2RI69OSSVerify6Proofsaboost_jsonafuzz_parse3libh2RefStdioWrite_run2~~~~~~jp7bsw_regs_butt44listt44Someiv03rdnhta6of_natt43natjkc2LMt44boolt44true3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticski58store_okki5h0word_to_le_bytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~knd6wbytesv25mkCfgiv04mkstiv07seg_romiv06v_addit46length37Corelib4Init5Peanokuf2lekuf2lt37Corelib5Lists7ListDeflgf3maplgf5skipnhi77WriteEv37Corelib4Init3Natlk13addt43app69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefStdioDefs~~~~~~lm07sw_post69OSSVerify6Proofsaboost_jsonafuzz_parse3libdRefStdioWrite~~~~~~lqa2LM69OSSVerify6Proofsaboost_jsonafuzz_parse3libh2RefStdioWrite_run1~~~~~~lv07mem_sw1jp77mem_sw2t44prodhi77FdEntryt44Nonehi79FdChannelhi75Modelhi79fd_lookuphi75m_fdshi78m_haltedhi79m_vm_lazyhv96ret_oklm09ssp_cellslm07sw_file" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma rz_emit_nil : ltac2:(zQ "80!j7!o1!s2!uc!hhe!hl5!hle!hm5>1c$4>1K$6>0@4$1$2$0^2^1@4$1$2$0^3@2$7@1$3$5^2").
Proof.
ltac2:(KReplay.run1 (kr_t_RefStdioWrite ()) ["FPX1"] "h01Hh11Kh21cp;4p;1p;2p;5p;3p;7p10000p4p70p1000^p4p7210p8p1001:p4p710p1001Yp4p710p8g0027j46Tg003>j15Tg003^j20Tg004aj51Tg005oj24Tg0079j32Tg008>j73Tg009Eg00::g00;;R0g00<BR1f1R2f0R3C6P0P1f2R4P2g00=H#5/02R5P3P0P1P4P2P3D1,429252F3W0W1W2o"). Qed.

Lemma skipn_app_le : forall {A} (k : nat) (l1 l2 : list A),
  (k <= length l1)%nat -> skipn k (l1 ++ l2) = skipn k l1 ++ l2.
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["FPX1"] "##:Eh04__p1h14__p2h24__x1h34__x2h44__x3h51nh61Ah71Hh82H3h92Hkh:3Hk0h;7__arithh<4__ffh=8__varmaph>5__with?4cstrh@5cstr0hA1khB1lhC2l1hD2l2hE1mhF1xhG1yhH2z3p;1p;2p;3p;<p;4p;7p;6p;Bp;8p200R0g00>>R1p4p710p8P!s7$\R2!s70?<R3!s71YR4!s7'g00@7j13TP2j22Tg00@WR2j2BTP1j34Tg00A1j2JTP3j38!s5$Hj30j1>!s2$bR3j11Tg00BBj25!s/$_j29Tg00C<j2L!s/$_j3KTg00D<j27!s/$Vl<HTg00E;R1j26!s1$Wj4\Tg00F>j1E!s/$cj2YTg00GEj2C!s/$aj2:Tg00H<j2A!s/$Vj1XTg00I4j2W!s/$Uj1@Tg00J4j2G!s/$]j3VTg00KFj3U!s/$oj2TTg003>j1NTg00L[j3MTg00M;j2?!s/$Yj4OTg00N7j1P!s/$Uj1QTg00O@j2R!s/$cj1STg00PHj2=!s/$kj1mTg00QPj3lTg00R3j4<!s/$^j7jTg00SBj1i!s/$dj2_Tg00TFj2^Tg00U2j3`!s/$Qj4aTg00VCj4b!s/$nj6cTP4j4dTg001Yj6eTg00WJlBfTg00X0j7[!s/$Tj6ZTg00Y8j7g!s/$\j8hTg00Z@R4P4P4g00Z_R5P5P5g00[=P3P3P3f6R6g00[]f5R7f4R8f3R9f2R:f1R;f0R<MBfp=kP4P5P2P3P1g00\DP7P8P9P:P;P<M<Hp=]P;g00\fR1g00]ER2P2g00]eR=P<g00^EF[p=;P;P1P2P2P=P<EZp=IP:!s7+;P<Fgp=DP9!s9+!t,$Ghp=F%3;%3:129;,B:%38R>A489:128:R?,J9R@=48;588%37RAA4789=87:RB70<XB>g00^eR>=04@RCg00_DRD%19RE%1?RF'5,9DRG505P4P5%>4P3%>5%1;%1<505A04;<1L;<3KXG4XF4P>PD175DP@PG15;<,9DXE5X55P9PE175ERGP?PF175FR@FkM<H1B9?16EFR3P9PEP!sE$P@E]P<C\P3%E8%18,6D1268R3#E%13,6D%16f7R3/27#1'5R@,YD1CD@19D@RF=05@':16@DA05FD':'A%13f8R3/26#1!uI$P5p-0RFg00_bR@g00`NR?#X,W5%@>#@,G55V51G5>5U5g00a3'T%N@3M%3@P51?5:P;1?59CO%P5%Q5R@P@!wa+51R5D!x[$a_%S?,=5RG%m!s-$E5l5C<,;@1I@75D@1I@6P51=5?R?g00bFRHP1!sG$5D@Fj%i2R2P@P5PGg00bmPE!sB$P2P5P1PHP?!s5$CFCF1_@=P<P:g00cT!uG$d4R='71^<:=0@=dA`5D;Cab<b=b>X25X35X45X0FW115;:,CD/:9A05<D,:8'A16!s4$D:[[^25^35^45^0F^1FP<f9#1RFf:/23#1R3'5R=/6DA05;=P3PFP;P:P7O7b;bHb8b@b?b:CbPCP4P>%36A467!zb$6<9586A86>930X5417AB1279,J8P<Ecb7A88:;9489!|^'CdEeW9WDWCXA4X60o"). Qed.

Lemma skipn_app_ge : forall {A} (k : nat) (l1 l2 : list A),
  (length l1 <= k)%nat -> skipn k (l1 ++ l2) = skipn (k - length l1) l2.
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["FPX1"] "##'kh01lh11Ah22Hkh31kh42l1h52l2p;1p;2p;3p;4p;6p200R0g00>>R1p4p710p8P0g001YR2!s70>\R3!s70?<R4!s70dTR5!s7'g00@7j12TP3j25Tg00@Wj23TP1j30Tg00A1j28TP4j34!s5$Hj31Tg003>j17Tg00D<j2<TP5j3;Tg00e6j49TP2j66Tg00?Yj4:Tg00Z@f1R2#2f2R5#2f3R4/52/35f4R1#2R3A0145R61515R7,84=012R8541f5R9#2R:f0R;1594R<,81=095R=31X03P3%71R>A49;==1:=X031<38P61374A0914%7951:[A136>13<1[A;145P;C9E6A41529014P1P4P5P2C:E6W2W5W4W3X10o"). Qed.

(* [comment removed for export] *)
Lemma u_at_le : ltac2:(zQ "b0!ho7!hqc!hrb!ht4!hv2!ij1!ij8!ije!ik5!ikc!il2>1b@1$a@1$0#k0>1k$2>0@2$6Z^1>0@2$6@2$4@2$1@1$0#k0^3^2@2$7+2+k0@2$9@3$3$2@2$1@1$0#k0@2$5^4^3@2$4@2$1@1$0#k0^4^3@2$8@3$3$2@2$1@1$0#k0@2$5^4^3Z@3$3$2@2$4@2$1@1$0#k0^4^3@2$7+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["FPX1"] "##9Kp'0h04__x1h14__x2h22Hah37__arithh44__ffh54__p1h66__sat0h7!s/%1h88__varmaph95__with:1zh;1Eh<1Hh=2Hkh>3Hleh?2NEh@1bhA1khB1si001si011ei021np;1p;2p;6p;4p;3p;7p;8g00Ocj15Tg00eQj1j!s/$oj1YTg00fRj20Tg00g<j21!s/$Yj1GTg00h7j2XTg00E;j2=!s8$Tj1TTg00GEj27!s/$aj26Tg00iZj2ITg00j:j1?!s/$SR0j2fTg00k3j2;Tg00H<j2HTg00D<j2@Tg001Yj6F!sJ$Yj4ZTg00l4j3W!s/$Nj2VTg00m6j3UTg00IUj1DTg00J4j2<Tg00KFj3B!s/$oj2STg003>j1QTg00L[j3NTg00@7j1LTg00M;j2K!sw$Zj1M!s8$Yj4JTg00N7j1O!s/$Uj1PTg00PHj2CTg00n8j3RTg00O@j2E!s8$[j3iTg00R3j4ATg00o>j6hTg00SBj1gTg00XTj6eTg00Y8j7b!sA$dj2_Tg00TFj2^Tg00AHj3>Tg00U2j3]!s/$Qj4`!sw$bj3aTg010dj3\Tg011>j2c!t$$0j7d!t$$\j8[Tg00_DR1f0R2'=p=3g00Z_R3f1R4;>2p=2A>321p=9P4g00\fR5g00]ER6P6g00]eR7P2g00^EFdp=4P3!sM$bmP2CAp=:f3R8P5P6P6P7f2R9P4P2G[p=8g00`NR:#5R;#5!s$'R<#jR=#Y%3210=9/14%G;R>%G<R<'XR?'=%T810=8R@#317@?'6f4RA,0=/18RB/I?12B?RB%?B'fP0f5R0!sB$A/2!s<%f6RB!s8$0R0,;=,0=RC/20%9C120?R0'6'HP2f7RC!sL$BRD!sL&E/2DRF%9ERG12D?RH'6RIPGPHP3P?1;=2,0=#9X:31@311;=?!s6$dPDP2EFP2CZ3WX;0P2O1%?0P3PDf8!tj&C,22!s^%DPE1V><RE171>%3<171?[[RH%3>RGg012;RJAU><4UW2R<%3?\J^2GRGp-0RJg00_bRKg00^eRL#DRM#D,<31<3M1<3L5B35B3g00a3'S%QKRL3N%LKRKP31K39P4%M3CJRM%O3RN%P3ROPO!w~'P31C3:R:1C3;R;5R3RPg00bF1E3>=i3=R>CA,4OEhRQ%g6RRP!sb-1E31RS/::,4!sx/AEeFbPRPO1:S;,4OPR1:SP,4OC8C8C81_O7R7P2P9g00cTRSg00d4R;'@1^29=>S;dA]314C`R1b4b8b9X03X13W51124/2?g012W[R;%34/68%38118A#3[[[^03^13^5JP2f:,0=RJ/7?f9RAPJP8PBP0O6b3b6b7PEPHP<PGPLPKPMPNPOPQ!u$%P>!u$$P3PPg00a_P!uv%C8C8P7P!t_01149/=?1198/7?[\;!tM%P2P!t>%CO4!t<%5aDEF9\FIW?P2O1n200110000021110111102bBb<1c89,0=R=11@9R@'2%9=12@?'6'HeW>W=XA3W@o"). Qed.
End FPX1.

Section Loop.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variables (su f fd : Z) (l bufp bufsz can ret : word).
  Variables (e8 e9 e18 e19 e20 e21 e22 g3 g4 g23 g24 g25 g26 g27 : word).
  Variable mem1 : ltac2:(zQ "30!ho7!il2!il8>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Variable model : ltac2:(zQ "10!mn2$0").
  Variable K : ltac2:(zQ "10!hle$0").

  Hypothesis SUlo : ltac2:(zQ "20!hv2!ij8@2$1@2$0+hggggggg0+n0?2su").
  Hypothesis SUhi : ltac2:(zQ "10!ij8@2$0?2su+ogggggggggg0").
  Hypothesis Flo : ltac2:(zQ "10!ij8@2$0+vpgg0?1f").
  Hypothesis Fhi : ltac2:(zQ "20!hv2!ij8@2$1@2$0?1f+u8+hirmv8").
  Hypothesis FD : ltac2:(zQ "20!ir6!ik5@2$1@2$0Z?2fd@2$0?2fd+ogggggg0").
  Hypothesis Hfd : ltac2:(zQ "90!ho7!ml3!jk1!jv3!il8!ht4!mm5!mnb!mo8@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0?2fd@2$3$1@1$6@2$2@1$0#k0?2fd").
  (* LPS 75d69e00: a write to a channel needs the model's channel reader present
     (LibWritev.rz_writev1_wall / rz_writev2_wall premise, after fd_lookup); the top discharges it
     from Run.valid_input_channel_reader through init_model's m_channel_reader seed. *)
  Hypothesis Hrdr : m_channel_reader model = true.
  Hypothesis Hh : ltac2:(zQ "60!ho7!il2!mle!il8!ht4!mp1@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!ho7!il2!mkc!juc!uc!ht4!mpd&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hret : ltac2:(zQ "10!mqa@1$0?3ret").
  Hypothesis HKnil : ltac2:(zQ "20!uc!hl5@1?1K@1$0$1").
  Hypothesis SOK1 : ltac2:(zQ "80!kh7!khe!ht4!ho7!klc!s2!im1!jk1@3$2$0@4$4$5?4mem1@2$7@1$3#k0@2$6?2su+n0Nn0$1").
  Hypothesis M8 : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!im1!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?2su+8N8@2$3@1$1@1$2@1$0#8@2$6N8?3ret").
  Hypothesis M16 : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!im1!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?2su+h0N8@2$3@1$1@1$2@1$0#8@2$6N8?2e8").
  Hypothesis M24 : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!im1!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?2su+h8N8@2$3@1$1@1$2@1$0#8@2$6N8?2e9").
  Hypothesis M32 : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!im1!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?2su+i0N8@2$3@1$1@1$2@1$0#8@2$6N8?3e18").
  Hypothesis M40 : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!im1!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?2su+i8N8@2$3@1$1@1$2@1$0#8@2$6N8?3e19").
  Hypothesis M48 : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!im1!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?2su+j0N8@2$3@1$1@1$2@1$0#8@2$6N8?3e20").
  Hypothesis M56 : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!im1!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?2su+j8N8@2$3@1$1@1$2@1$0#8@2$6N8?3e21").
  Hypothesis M64 : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!im1!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?2su+k0N8@2$3@1$1@1$2@1$0#8@2$6N8?3e22").
  Hypothesis M72 : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!im1!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?2su+k8N8@2$3@1$1@1$2@1$0#8@2$6N8?3can").
  Hypothesis Mcan : ltac2:(zQ "a0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$9@1$0#k0+hirmv8N8@2$3@1$1@1$2@1$0#8@2$6N8?3can").
  Hypothesis Mbuf : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!hv2!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?1f+l8N8@2$3@1$1@1$2@1$0#8@2$6N8?4bufp").
  Hypothesis Mbsz : ltac2:(zQ "b0!ho7!juc!il2!jv3!il8!ht4!km8!jva!s2!hv2!jk1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?4mem1@2$a@1$0#k0@2$9?1f+m0N8@2$3@1$1@1$2@1$0#8@2$6N8?5bufsz").
  Hypothesis Mfd : ltac2:(zQ "b0!ho7!juc!jk1!il2!jv3!il8!ht4!km8!jva!s2!hv2@3$6@1$5@1$1@1$3@1$0#8@4$8$9?4mem1@2$2@1$0#k0@2$a?1f+n8N4@2$4@1$1@1$3@1$0#8@2$7N4@2$2@1$0#k0?2fd").

  (* [comment removed for export] *)
  Definition LM : ltac2:(zQ "30!ho7!il2!il8>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8P") := ltac2:(zQ "b0!ho7!il2!il8!ik5!im1!hqc!ht4!im8!iq9!ij8!ir6\1m>0@1$1@1$0#k0@1$2@1$1@1$0#8@2$3>1x@1$1@1$0#k0>0@1$7@2$3@2$9@2$4?2su+m8@2$5@1$0#k0^1@2$a@2$5@1$0#k0^1@2$4?2su+k8@3$6@1$2@1$1@1$0#8@1^3^2@1?4mem1^2@2$8?4mem1^1").

  (* [comment removed for export] *)
  Hypothesis HK : ltac2:(zQ "h20!ho7!il2!iub!ht4!jib!jj3!jj9!s2!il8!ks1!iu2!ks9!kt1!kh1!mk1!j7!o1!jk1>5regs'@2$a@1$0#5@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>0@3$3@1$1@1$0#k0@2$4^2@3$5@1$0#5+aKv$2@2$6@1$0#5+a?1l>0@3$3@1$1@1$0#k0@2$4^3@3$5@1$0#5+2Kv$2@2$6@1$0#5+2@2$h1@1$0#k0?2su>0@3$3@1$1@1$0#k0@2$4^4@3$5@1$0#5+1Kv$2@2$6@1$0#5+1?3ret>0@3$3@1$1@1$0#k0@2$4^5@3$5@1$0#5+8Kv$2@2$6@1$0#5+8?2e8>0@3$3@1$1@1$0#k0@2$4^6@3$5@1$0#5+9Kv$2@2$6@1$0#5+9?2e9>0@3$3@1$1@1$0#k0@2$4^7@3$5@1$0#5+h2Kv$2@2$6@1$0#5+h2?3e18>0@3$3@1$1@1$0#k0@2$4^8@3$5@1$0#5+h3Kv$2@2$6@1$0#5+h3?3e19>0@3$3@1$1@1$0#k0@2$4^9@3$5@1$0#5+h4Kv$2@2$6@1$0#5+h4?3e20>0@3$3@1$1@1$0#k0@2$4^a@3$5@1$0#5+h5Kv$2@2$6@1$0#5+h5?3e21>0@3$3@1$1@1$0#k0@2$4^b@3$5@1$0#5+h6Kv$2@2$6@1$0#5+h6?3e22>0@3$3@1$1@1$0#k0@2$4^c@3$5@1$0#5+h7Kv$2@2$6@1$0#5+h7?3g23>0@3$3@1$1@1$0#k0@2$4^d@3$5@1$0#5+h8Kv$2@2$6@1$0#5+h8?3g24>0@3$3@1$1@1$0#k0@2$4^e@3$5@1$0#5+h9Kv$2@2$6@1$0#5+h9?3g25>0@3$3@1$1@1$0#k0@2$4^f@3$5@1$0#5+haKv$2@2$6@1$0#5+ha?3g26>0@3$3@1$1@1$0#k0@2$4^h0@3$5@1$0#5+hbKv$2@2$6@1$0#5+hb?3g27>0@3$3@1$1@1$0#k0@2$4^h1@3$5@1$0#5+3Kv$2@2$6@1$0#5+3?2g3>0@3$3@1$1@1$0#k0@2$4^h2@3$5@1$0#5+4Kv$2@2$6@1$0#5+4?2g4>0@1$d^h2@4$h0$7$f@2$9@5$b?2fx^h4?3ret@4$e^h3?1f?4bufp?5bufsz@1$c$7?5model?1K").

  (* [comment removed for export] *)
  Definition RI : ltac2:(zQ "30!ho7!iu2!il2>4regs@2$1@1$0#5@1$2@1$0#k0P") := ltac2:(zQ "b0!ho7!il2!iub!ht4!jib!jj3!jj9!ik5!jk1!iu2!im1\4regs@2$9@1$0#5@1$1@1$0#k0@2$7@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+2Kv$2@2$6@1$0#5+2@2$8@1$0#k0@2$a?2su+n0@2$7@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+8Kv$2@2$6@1$0#5+8?1l@2$7@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+9Kv$2@2$6@1$0#5+9@2$8@1$0#k0?1f@2$7@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+h5Kv$2@2$6@1$0#5+h5@2$8@1$0#k0+hirmv8@2$7@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+3Kv$2@2$6@1$0#5+3?2g3@2$7@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+4Kv$2@2$6@1$0#5+4?2g4@2$7@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+h7Kv$2@2$6@1$0#5+h7?3g23@2$7@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+h8Kv$2@2$6@1$0#5+h8?3g24@2$7@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+h9Kv$2@2$6@1$0#5+h9?3g25@2$7@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+haKv$2@2$6@1$0#5+ha?3g26@3$3@1$1@1$0#k0@2$4^1@3$5@1$0#5+hbKv$2@2$6@1$0#5+hb?3g27").

  Lemma RI_but : ltac2:(zQ "50!ho7!iu2!jp1!il2!jtd>4regs@2$1@1$0#5@1$3@1$0#k0>5regs'@2$1@1$0#5@1$3@1$0#k0>0@1$2^2>0@2$4^3^2@1$2^3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["Loop"] "##>2h01bh12P2h23P21h33P23h43P24h53P25h63P26h73P27h82P3h92P4h:2P8h;2P9h<2R2h=3R21h>3R23h?3R24h@3R25hA3R26hB3R27hC2R3hD2R4hE2R8hF2R9hG5nd_i1hH!s-$2hI4regshJ5regs'p%0p;1p;2p;3p;6p;>p;4g00Ocj11Tg00Pkj13Tg00eQj1B!s/$oj1ETg0134j2I!s/$`j1=Tg014dj2HTg00gYj1?Tg00BBj2FTg00k3j2>Tg0166j24Tg00AHj32Tg00Gaj26Tg001Yj6CTg0177l>ATg018=j3G!se$Yj4@Tf1R0f0R1#?g018`3Gp=8f3R2f2R3/40;21p=0f4R41423140132p=514019223p=DA2230/61p=;1601,63p=:!s0&,62,64p=7f6R5f5R6P4P2P3P0P1C@C@p=<P5P!s;$1430P1ECp=9g00`NR7#1R8#3R9#BR:%18R;#1R<#1!s$$BR=#ER>'IR?%=01H30P>P218:8R8p,2su%37R7#3!sU&1#?'F,>=R@C0RA!sQ&<R<p,1lRBC!sc$%3;RC,8:RDp,1f,>=RE!s?&19#3,8:RF%1C!sy$3!s+2!s$%!t7&,>=R=C!t^'7RCp,2g3RG!s9+;R;p,2g4RH!tG'!t-&9p,3g23RI!tF'7!u{$J#1,8:RK!sD$4RL!s\'J,8:RJ!s<$5RM!s<'!sZ$,8:RN!s@$6RO!s@+,8:R:!s<$7R7C0%=3P>P4P<P!ux%6PDP!ui%5PFP!u9$f7S00PCP!u3$f8RPP;P!u+$f9RQP9P!tx$f:RRPKP!tf$f;RSPJP!t\$f<RTPNPOC0f=RU/4:RV=2>7P>PUP8f>RWP8D5RX!s6$<14W<RY!tL$UPDPWPDD5!s2$FPWPF!s2&CPWPC!s2&;PWP;!s2&9PWP9!s2&KPWPK!s2&JPWPJ!s2&NPWPN!s2$VPWP:CD%=UP>PYf?RYP<CDP>PYPDf@RV!tI&VPFfARZ!tK&ZPCfBR[!tM&[P;fCR\!tO&\P9fDR]!tQ&]PKfER^!tS&^PJfFR_!tU&_PNfGR_!tW&_P:fHR_/4:R`!vO$IRa/48RbP>P1P@14a<Rc=2>BRd14aDRe=2>ERf14aFRg=2>=Rh14aCRi=2>GRj14a;Rk=2>HRl14a9Rm=2>IRn14aKRo=2>LRp14aJRq=2>MRr14aNRs=2>ORt14a:Ra=2>7R:'6Ru'6Rv'6Rw'6Rx'6Ry'6Rz'6R{'6R|'6R}C;X0>P>PcP>fJRcP8P@C0R~A2>1B;:|!sC%e!sG$!yu$RB!uJ$EP{C;5:~!sF%gP~PB!sJ$!z7$REA2>1=PzD7!sF%i!sF$E!sH$!zO$R=!sl$GPyC;!sK'k!sK&=!sM$!zi$RGA2>1H;:x!sK'm!sK0!{&$RH!sr$IPwC;5:G!sP'o!sP+GPH!sT$!{L$RIA2>1LPvD7!sP'q!sP0I!sR$!{l$RL!t$$MPuC;!sU,s!sU2L!sW$!|9$RMA2>1O;::!sU,a!sU8!|\$A2>175:M!sS&A2>b@P}P^PdP|P]PfP{P\PhPzP[PjPyPZPlPxPVPnPwPYPpPvPWPrPuPUPtP:PTPSF<!s$'P`P1ECP_PNP0F9P_PJP3!s-$KP2!s-$9P4!s-$;P6!s-$CP5!s-$FQ0!sW%DPP!s-$<PQ!s-$8PRF9%=_eW7W6W5W4W3W9W8W2W;W:X1XPSM>AWBWAW@W?W>WDWCW=WFWEX<AP0M>AWHWGXJ?WIo"). Qed.

  Lemma LM_refl : LM mem1.
Proof.
ltac2:(KReplay.run1 (kr_t_RefStdioWrite ()) ["Loop"] "h01xp;1p;2p;3p;4g00Ocj10Tg00eQj13Tg00eoj12Tg00Pkj11Tg00gYj15Tg00BBj24Tg00fRj2<Tg00E;j2;Tg00GEj2:Tg00Gaj27Tg00j:j16Tg019<j18Tg00AHj39Tg019^j2@Tg00D<j2?Tg01:cj1>Tg00kYj4=Tg00`NR0#0#0R1#0R2#0#0#0#3R3#2R4p,2suR5%10#0#1#0#0#0#5'4f0,<3R3';%11#0#0#0#5,45,:3'7#6R3%32#2#8R2p,4mem1R5f1O1R1;91[]01@551?21V3X04%>5C=o"). Qed.

  Lemma LM_rdn : ltac2:(zQ "h10!ho7!il2!juc!il8!ij8!hqc!jv3!ht4!jva!s2!hv2!kg1!im1!kgb!ikc!kh1!ije>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>1n$d>2bs@1$2@1$1@1$0#8>0@1$f^4>0@3$7@1$3@1$2@1$1@1$0#8@4$8$9?4mem1^4^3@2$6@1$2@1$1@1$0#8^2>0@2$4@2$a@2$5@1$0#k0^5@1$b^4@2$h0+2+k0>0@2$e@2$4@2$a@2$5@1$0#k0^6@1$b^5@2$c?2su+m8@2$4@2$c?2su+k8@2$5@1$0#k0^6@3$7@1$3@1$2@1$1@1$0#8@4$8$9^8^7^6@2$6@1$2@1$1@1$0#8^5").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["Loop"] "##:^h01xh12Hah24__x1h34__x2h44__x3h54__x4h61Dh71Eh81Gh91Hh:2H0h;3Hnwh<2Hxh=7__arithh>4__ffh?7__sat73h@!s0&4hA8__varmaphB5__withC1ahD2bshE4cstrhF1mhG1nhH1op;1p;2p;3p;4p;7p;6p;8g00Ocj11Tg00eQj1Q!s/$oj1ITg019<j1GTg00@7j1OTg01;mj1^Tg00Pkj1@Tg00gYj1?Tg00BBj26Tg00fRj23Tg00E;j20Tg00GEj28!s/$aR0j2>Tg00j:j1iTg00AHj35!t<$^j2MTg01=1j49Tg01>1j2D!sJ$bj12!t<$<j24Tg00h7j2ZTg00H<j2CTg00F>j1YTg00lNj2XTg00m6j3WTg00IUj1=Tg00J4j2:Tg00KFj3A!s/$oj2HTg003>j1VTg00L[j3K!se$Zj1UTg00M;j2F!s/$Yj4ETg00N7j1T!s/$Uj1S!v-$Hj2<Tg00n8j3RTg00R3j4BTg00SBj1hTg00O@j2NTg00QPj3J!sJ$^j7gTg00o>j6f!sS$dj2eTg00D<j2]Tg00TFj2_Tg00U2j3`!s/$Qj4\!v>$Sj7aTg001Yj6bTg00X0j7[Tg00Y8j7c!s/$\j8dTg00Z_R1f1R2g00bmf0R3CBp=;P2g00\fR4g00]ER5P5g00]eR6P3g00^EF[p=7f2R7P4P5P5P6P2P3Fcp=Pf3R8!s;+7P2P3Gdp=Lg00`NR9#1R:#1R;#1R<#1#1#1R=#QR>#IR?%Q<#IR<#GR@[g00Z@%O<R<%^8P0p,2suR0%@9#1RA#@!sa%#?RB'6RC13>3RD'0%@;!s?+;,60RE,8D'>#iRFf6RGP2O1p,4mem1RHP2O1RI55@[^0?f4RJ,MH%G<RKg00;;RLPHPJP8C91D<735f5RM,3>RN%2J'4%?:RO%?=R='ZRP'013>GRQ%2M'4/0C10EQ'CPLf8RQf7RRPG!sl$MRM55K[[[P3PQP2O1=5@I\F^0?1MHRPLPHP!sQ$=5KM13>Q%2R'4/0Pf9RR,3>RM%2Q!t-'M'CPKPLPHf:RMPR!t-$R95K3XHKP7PLf;RKP!s?$PLPRPKPHPMP213>KRH/0D%2M,4H!v:$PGP2%YKg00_DRD%2K'01XO=18DO10D=18DP[[10DORKg012;RHAWO=2UW110DP\H^1!sb$b!vV$^eRH#=RP#=R=#=RO,:11:1=R=1:1P5A15A1g00a3RP'H%=!sE&H9A1=5A1/HP%VK5KK3K%OKP1P1%U1RKP71F1JCEP2P11F18PJPKCECE%T1%S1RK%@:,<1RP1<1:R:';,7KP1P:g00a_R=1<1A9R1PRACB,7K5PK%h5RHPKPK!zb'1<19R91N1B5J1RO,;A,7K1N1;9J19R9/;P,7KFgPH!sY-;O:!t6&P=P9!t%'EfCLCL1eK6P3P7g00cT!v5$d4R6']1_37=5K6dA`1D2C\b>bAbBX21X31X41X5110721478,82'>148J162B'0162;/08'C167B/08167;,88'>g012W[[[^21^31^41^51P3f?#2f@,3>PNP0PJPGO6b=b?b@bEO2W<X0?FaEbW6W;W9W8W!}X$O2n20010!s#$12!s/&W:WDWGXC?WFo"). Qed.

  Lemma LM_store_ok : ltac2:(zQ "a0!ho7!il2!kh7!khe!ht4!klc!s2!kgb!il8!kh1>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1a@1$1@1$0#k0>1n$7>0@1$9^3>0@3$4$2@4$5$6?4mem1^3^2$3@3$4$2@4$5$6^5^4^3$3").
Proof.
ltac2:(KReplay.run1 (kr_t_RefStdioWrite ()) ["Loop"] "h01xh11Eh21Gh31Hh42H0h51ah61mh71np;1p;2p;3p;4p;7g00Ocj10Tg00eQj19Tg00eoj16Tg019<j1=Tg01;mj1ATg00Pkj11Tg00gYj17Tg00BBj25Tg00fRj2?Tg00E;j2>Tg00GEj2<Tg00GaR0j2;Tg00j:j1:Tg00AHj34Tg019^j28Tg01?Wj43Tg01@Wj7@Tg00cTf0R1g00d434p=2g00`NR2#0#0R3#0R4#0#0#0#9R5#6R6%94#6#=R4[g00Z@f2R7#AP0p,2suR0%12#0#1#0#0#0#7'51?51R5'>%13#0#0#0#7,50,<5';#:R5f5R0f1R3O1p,4mem1R2P3O1R8544[^06f3R9,82g00;;R:P2P9P7C3#2P:P0f4P9C3#2[P1f7R9P3O1=448\5^06f6R5,82P:P2P5P0C3#2P:P5P2f8P9P3P1F@W3W2W1P3P1O2n2001000000120000000W4W7X56W6o"). Qed.

  Lemma LM_wbytes8 : ltac2:(zQ "b0!ho7!il2!kh1!ij8!im1!il8!hrb!km8!kr7!hv2!jk1>1m>0@1$1@1$0#k0@1$5@1$1@1$0#8>1a$6>1v@1$1@1$0#k0>0@1$2^3>0@2$3@2$4?2su+m8^3>0@2$3@2$9^4+8@2$4?2su+k8@1$2@3$8^6@2$a@1$0#k0^5@2$7N8^4").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["Loop"] "##EHh04__x1h14__x2h21xh37__arithh44__ffh58__varmaph65__with71nh82Hah97__sat73h:!s0&4h;4__x3h<1mh=1yh>1zh?1Eh@1GhA1HhB3HhihC3HlohD2HxhE1ahF1ohG1vp&0p;1p;2p;3p;4p;<p;6p;5p;Bp;7p;8g00Ocj11Tg00eQj1\!s/$oj1QTg019<k102Tg01;mj1[Tg00Pkj1DTg00gYj18Tg00BBj29Tg00fRj2ATg00E;R0j20Tg00GER1j23!s1$aR2j2;Tg00j:j1=Tg00AHj3C!t8$^j2N!s}$<R3j22Tg00k3j2ETg00IUj17Tg01A`j2KTg01Bhj3Vj4o!sj$bR4j1JTg01Cjj1ITg01DHj4gTg00DVl<T!s8$kj6cTg01ETj3bTg00J4j2?Tg00Koj2HTg003>j1aTg00L[j3GTg00@7j1`Tg00M;j2P!s/$Yj4RTg00N7j1_!s/$Uk10!v_$PHj2OTg00QPj3FTg00SBk10!v#$n8j3Z!s9$dj2~!ti$<j2YTg00TFj2}Tg00U2j3y!s/$Qj4xTg00VCj4XTg00mZj1sTg00O@j2WTg00lNj2rTg00h7j2q!sJ$6j3p!t:$[j3nTg00obj3mTg001Yj6@Tg00>\j2lTg01F=j2kTg01GMj3jTg01HMj6iTg01IUj3tTg01J]j5u!wP$Yj4hTg01Khl<vTg00WJlBw!v[$Fj3fTg00R3j4STg00X0j7UTg00Y8j7z!tU$>j6{!s8$\j8|Tf0R5#1#1p=Bg00Z_R6/Y5p=<g00Z@R7P6!s$$4P4f5R4f4R8f3R9f2R:f1R;P5M<vp=e!sL&!s$%3P5P;P:P3P9P8P4f6R3f7R<f8R=f9R>MBwp=dAf6;5p=>1W65p=:P:g00\fR?g00]ER@P@g00]eRAP6P;g00bmP5CSg00^ERBFUp=4!s?&a_P5CSp=MP;P?P@P@PAP5P!sI$LP:!s9+;P5Fzp=^!sL/E{p=]P9!s7+:P;P5G|p=6%1!v1$#1p=5g00`NR?#1RB#1RC#1RD#1#BRE#\RF#QRG%\D#QRH$02RI[%[:P2p,2suR2%D?RJ#1#!sV$#8RK'9RL1AF5RM'0%DC!s=&C,92RN,3M';#=RMP4P;O1p,4mem1ROP;O1RP5CI[^2G1NO910L9%8DRD,28/0N1EF4g00^eRQ#7RR#7RS#7RT#7RU#7!s$%RV/K85V3#[[[P5P<P;O1=CIP\M!sy%310L312<D/0Nf;RNf:RL,EFR31KV>RWP;CoRX!sW,EF=R=1KV<R<5V>RP,NOPIPNP;O1POP:O19CI5XFIP4P;P5O2PXPWPNP3P;P7PV1EFN,AFRX1AF:RI'0%J5RY,2XRX,3I';#=X77P6PL105I%JVRZ,25R[!sB'>61AF;R\,0LR]12LZR^,3\R_';R`#=Ra12LDRb,3\Rc,;]Rd#=P]P_P]Pc%I]!z\$1P5X26R]P113;5#IX=6X26P\P\%<\P^PbP]!s$$6P6g01LM12;5Cg#<X<6X76PLPL%<LPZPDP]P]%<YX27PVPD%<DEeM:dRYM<TEc9b`dg00_bRd1?6URU1?6T1?6QRQ'>'>g00a3RT'H1?6SRS1?6RRR'>,>U/HT%adRU5Gd3G%`dR`P61P6:RZP;1P69CR%_6R\&016R11O6JRc%:KR_5F6Re1O6BRf541%:CRg9F6cRc,Mf,L15^1,]1&00@R@P11O6?R?%:D5Z6Rh=41cP@P1A41e?P@A41?f1Mfh!s]+C6C6C61~1ARAP5!}a$cTReg00d4Rc'Y1}5:=Cec!uh$DRc=y6;CxReb4b5b6X06X16X;619:K/0;19:C,3;';g012WRi[12;D199C'0198K/0:1098129D,38';Pi[[[[^06^16^;6P5P2!z,%P9P8O6b3CXPae1AF3Ra1>RQ,>S/HT=GdURUP`P6PZP;%s6CRRZP\P1AF6f_=41?P@P1%BE#5!s$,R_#8Rd#:%DJ#5#8RJ#:5Z6=41fP@1W6c=41?C6C6PAP!uR019;K/0512dJ!u4$c:!u#'!t|$NP8p,4SUloO4b3%8BRB%8ERE'rR813cB10cE1qBERN,3c[[RJ10cBRdg012;RKApBE;UW8RE10cN\K^8dRdPUP`P!uF+g941hRg!uH$1_#B!uF&8R_#:941fRfP@%:B=n6FRF,M?,L1!u=825D19;C'0RC10:_R_13:N!uA/f=P4!uA$hiO4R4b3b9b:5mLR2E@1lHWRW1kV>RHE@%JW9j;3#=e!~S$0XN!~5+[NX>610^NR[10bN!}K$0P]P010!}F-^PbPYPNPN%<NM<TP8PJPEP!uo-P!uf$Pf!zo$hF!uG9:D/0N\_\C!u:&!u%&CXP[ePaP2E@PWPHE@EiE@XDMX2GPOP>PPP:At<>=DuChWBWCW@W?!#4{$n20010!s#$12!s/&WAXGGXE6W<o"). Qed.

  (* [comment removed for export] *)
  Lemma finish : ltac2:(zQ "f0!ho7!il2!s2!il8!iub!ks1!iu2!ks9!kt1!kh1!jp1!j7!o1!jj3!jj9>4regs@2$6@1$0#5@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>0@1$a^2>0@1$9^2@4$c$2$b@2$5@5$7?2fx^4Kd@3$d@1$0#k0+tvqt4Kv$4@2$e@1$0#k0+tvqt4@1$1@1$0#k0^3@1$8$2?5model?1K").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["Loop"] "#$zQp'0h04__x1h17__arithh24__ffh38__varmaph45__with57__sat73h6!s0&4h71Hh81bh94__p1h:4__x2h;1xi001xh<2Hah=6!sT$0h>!s/%1h?1mh@5regs'hA1zhB3LMmhC2Q1hD3Q10hE3Q18hF3Q19hG2Q2hH3Q20hI3Q21hJ3Q22hK3Q23hL3Q24hM3Q25hN3Q26hO3Q27hP2Q3hQ2Q4hR2Q8hS2Q9hT2R2hU3R21hV3R23hW3R24hX3R25hY3R26hZ3R27h[2R3h\2R4h]2R8h^2R9h_3RIrh`3RUNha1ehb1nhc4regshd!u@$2he1yp%0p&0p;1p;2p;3p;4p;8p;6p;Wp;5p;:p;>p;<p;Bp;7g00Ocj17Tg00Pkj1BTg00eQj1k!s/$oj1vTg0134k20XTg019<k10Q!s:$`k10JTg01;mk10ETg00gYj1<Tg00BBj28Tg00k3j2FTg01M1j2ATg018=j3S!s8$Tk10GTg0166j23Tg00AHj3:Tg00IUj1ZTg01A`j2P!sA$bR0j1u!t4$<R1j26Tg00h7k20=Tg00E;R2j22Tg01Cjj1rTg01DHk40!sv$lNk202Tg00GEj2GTg00m6j3~Tg003>k10WTg00@7k10VTg00M;j2}Tg00N7k10U!s0$Uk10T!vG$Hj2|Tg00SBk10!tl$n[k30O!s:$dk20NTg00D<j2mTg00TFk20MTg00U2k30I!s0$Qk40HTg00fRj2!sV$O@j2lTg00obj3!sU$H<j29Tg01NXj8L!u'$Zk10DTg01O`k30BTg01PFj6xTg00J4j2jTg00KFj3t!s/$ok20@Tg00L[k30?!uQ$Yk40<!s_$nmW0;Tg01R<j5ITg01S=j4bTg01TKj3eTg01UNS00k20!x<$1Yj6\!s<$hm:05Tg0177m>04Tg01Vnj2yTg0027j4zTg01Khm<0!xG$WJmB0K!v4$Vm<0!uB$R3j4_Tg00X0j7]Tg00QPj3q!vm$8k301Tg00Y\j8pTg00VCk400!s^$^j7{!s^$Tk60S!xC$aR3j2JTf1R4f0R5g018`R63Sp=@%75#7p=^%75#<p=Rf3R7f2R8/34;:5p=4%75#Bp=i%B!sO$f%B!s6$cg00;;R9g00<BS01f6R:f5R;f4R<P7P8DI/y4P5Czp=?g00Z_R=/m5p=Cg00Z@R>P=!s$$0P0P;P!sX$P4P5N<03p>06!sD&!s$%1P5P4P8P1P7P<P;P:f7S02f8R1f9R0NB0Kp=O!sP$2Q02P2P:!sy2Lp==g00_DR2/25p=E!uk$!s$/p=g!s:+p>0R1l=5p=UP8g00\fR?g00]ER@P@g00]eRAP=P4g00bmRBP5C_g00^ERCF]p=`Aq=45p=nB01!s/$DP;P?P@P@PA!tc&!s4'=P4P!se$PCF]Gpp=>1684!tp$K!s[?g00a_RD!s`/TP=Q0!uo-H00P4P5E\p=;12781245'9p>0F!v9,%r5Exp=Q1l=59q=4p=[P:!t6+!tN,=P<PBP7!t;%!u5;F{p=X16<7/2!t;'=W!sS2!u$+p>0CP4!sB+5J0Sp=wP<!s8+7!s^-8PBP4!tK&5F{p=o!sE-!xP$Gpp=d1284/95p>0A1678/2!s4$=s137813455:<p=513<713845:;/J5p=0AS<78,3;=::4!s8$V1J45,J8p>09A:78!s<$>0>A::;<!s7''Jp=h!sO&,J7,J<p=aP9Q011y8!{\%>0713459:78p=Y13849:<7!t1$H1378=:<!t?%1g00`NS03#7S04#BR?#kRCQ04#7RB#7RD#7S05#7S06#7RE#kRF#vRG+0XS07%kD#v$0Q\G&0J4&0E4PGP7Q04#<RH,@CS08p,2suRIQ03#BRJ#BS09#7S0:#^S0;#RRK'8,FFC4S0<PGP7%<DRD,@CRLp,1lS0=C!sy$%BBS0>#<S0?,@CRMp,1fRN,FFRO!sG&7?S0@#B#<S0A,@CRPQ0>#7S0B#B#i#f#c#i#c#c#^#RRQ,FFS0C!s`&<JS0!tA$Rp,2g3S0E!s?'BS0F,@CRBp,2g4S0G!t['?S0H!t:%I,@CR?p,3g23S0J!t['JRJ#7RS#7S0K#<RT,@CRU!sL$4S0L!sm'S#<S0M,@CRS!sB$5S0N!sB'!sh$S0O#<S0P,@CRV!sI$6S0Q!sI/<S0R,@CRW!sD$7S0SC4p,2fxRXP7%cJ!un$i#f!s$$RS0TP6Q0T,AFd5SFPGeS0UP8&0G9RJp,5modelRYp,1KRZF?Q0<13<LS0VQ0=5:G13;MS0W=:GOPGP:PPQ!vc%Q02PRQ0EC4131BS0XQ0G!sU$0?S0YQ0J5:GPGf:R:PUQ!uu%f;ROPSQ0NC4f<R[/3VS0ZQ0Q5:Gf=R\/3WS0[Q0S5:GPXf>S0\P\PJPIPNQ0=p,4bufpS0]p,5bufszS0^p,3canS0_p,3retR]p,2e8R^p,2e9R_p,3e18R`!s-$9Rap,3e20Rb!s-$1Rc!s-$2RdP:P0P1Q02p,4SUloS0`!s0$hiR:p,3FloS0ap,3FhiS0bp,4HretP\18IDRe,FFRfg00^eS0c#ZS0d#ZS0e#Z!s$,Rg1Pg]POp,2M8Pe%ugRh,65S0f%<ERi-0=HRj'2XA=S0g16ehRk/2j16eDRl/2jP5X;=Rm1245#rXe=X;=RnPkPlPm!s$$=P=g01LM1645H0:#CX?=Xb=S0hPePe%CePhPDPmPm%u5#CX;>PgPD%CDJ06S0iM:OS0jPjPj%CjR>G=202HiRo1G2H%Ei1G2j[[Rp%EHRqg012;RrA~Hi4UW<Rs%Ej\r^<qRqg00_bS0k$0WRrQ0k$0VRt1}=4Ru&0U=Rv&0T=RwQ03,|=Rx%^E#g#g#gRE#^$0R#g#RRy#U5`wRz&0P@R@Pw%UDR{,nxS0l/D{S0m%UH>0O=FR|E>20NwARAP5P8g00cTR}g00d4R~'m20M58=:}~dB0I=24H0HR~b2b3b4X0=125yRy184DR}?KDj[^0=P5PIP:O2R:b1b5b61NFfS0nPrPtPuPvPw%<ERE#U%UK'DS0o=`wxS0pP@Pw1l=2R2Q0lE>PAP!t5-6EKS0q/25RE%E}!t4'Q0`O2S0rb1PoPpPsPq!t3,PzP@PwQ0lP|ET!ss1G}j\y^0=P!to&5MeS0sG;PeQ0fQ0O#7#RS0O,8IR}Q0B!s5%f,8IRKP5H0FXA=Rf12k}S0t12KeRe'912l}S0u/9eQ0tPeQ0uPePmP!yq$Q0jP}P}%C}RlG=PeEQ!tu-wQ0mQ0O#US0m!we$jPwQ0f,[xReQ0lFX!u2185DRkPDQ0O,85S0lQ0f!s/$uPkDW!v5&O1S0tb1Q0nQ0sG;GLP\Q05#<S05,8IRk,FFS0sPg1Pg^POp,3M16PkQ0g16khS0n!|>$kDS0v/2jPmPn!sp$v!|0%Q0hPkPk%CkPhPDQ!{Z&wPjPjP>G=!wO=5,[xS0x!z;$yP|!xP2Q05,84S0z?KD!wd1Q0s,N!u#$!sy+Q!yD%P2Q0x!sn4z#E\E^0=Q!y-Ax!y-4Q0z/G!y03kS0zG;PkPfQ0n/2}S0{12KkRk'9Q0v!s7$|/9kQ0{PkQ0|Pk!vN,Q0wP}P}PlG=Pk!xb3yQ0jPwPeQ0x!xQ2!v$$5!xS%lQ!xG+Q!xA%sQ0z!xA%18IT!x:&z!x:$_!x:%24!x:-s!x:+5!x:+sQ05!x:?x!x:C1[xTS0y!x8$w!x84184TS0v!x66z!x6$z!x68y!x64v!x6Iy!x66v!x68v!x6's!w}$n!x6,5!x6-n!x60sQ05Q0x!x6=w!x6+y!}a5T!x4;zQ0v!}O'6#<S06!}O,v!x;$`!x;%32!x;-z!x;+y!x;+zQ0y!}Ob6!}O-5!}O66!}O$s!x?6v!x?$v!}OJs!}O]s!x?8s!x?'z!x-%!x?,y!xP%!x?$|P!xD%!vN,!}O@5!}O>6!}O>v!#6j,@#7S0s#RS0v!xF,6!xF$a!xF%40!xF-x!}[6x!}[B!xFFv!xF$!}]%z!xF6v!xF$n!xF66!xF$6!}_Jn!}_]n!xF8n!xF'x!xF3!}_%{!xF,{!xF'x!x$$!xF>z!}_<!v$$!xF<6Q0n!xF'K!#KV%S0n!xF3b!xF&8!xF-v!}f6v!}fBz!xFEn!xF$w!}f<n!xF$x!xFRw!sn4x!xFIw!xF6x!xF8x!xF'v!#<72y!#<7;v!}f$z!}fGw!xF4n!xFAx!xF';#<S0;!xA,x!xA$c!xA%5!#AR-6!xA+n!xA+6Q0n!}ab;!xA$5!}a<;!xA$y!xA6x!xA$x!xA85!sn4y!xAI5!xA6y!xA8y!xA'6!x0$v!xA,n!xA-v!xA06Q0n!}aJ5!xA4;!xA>xQ0y!#AR'i!x:&y!x:$d!x:%64!#6u7;!#6u-;!x:?5!#AREiS0z!#AR<i!#6q8y!x6$y!x68z!#6qZz!#6qZ6!x6,;!x6-6!x60xQ0;Q05!#ARFz!#AR4iRi!x4+i!x4/y!#6o'1FFKS0nPgQ0_,PgS0!#F`%72PK!x4$Kh!#6Y$16KDRi!x3+yPi!x2,KPK%CK!#6aO1De!x+8Q0f,84Rk!x,6n!x,$n!x,6Pe!sl2%Ek!x&EPe!#Qm5k!x#3KR:G;PKPf!#6@$Ry12KKRk'912i}Rz/9kPyPkPz!wx'yPi!#6J?!ww'Pe!}-4u!ws'Q0u!wt/nP:!#6D&C!wo$POp,4McanPQ!wj$QhR:!wi$QDRe/2jR!tZ$P:Pe!wj,QPQ%CQ!wj/_!wj7&0D=S0nPv%UQRi!|q$t=`w|!ty,PkP5b1b=b>Q0C!wY$CPrPtQ0nPvA`w2i!sQ,%EQP5!wG1!sM$B0Cwi!sy-1GQj!s{'5MQS0uG;PQPf12:}Rk12KQRz'912e}Ry/9z!w5$yPz!u['Q0_!w6'p-0R:/mz:0BzzE!#7Y5wQ0tQ0j1ww7DoCd!wH0X9:Q0O,84>0Ae8!yW$^9:P5Pz!#XU$3b1Q0CQ0u!wT'H#7S0H#7#RRz,6NRE,FFS0uPgQ0],Pg!wm%bufPE!wm$Eh!wd$16EDR!#@<&PeP!#@:,EPE%CE!wk/C!|W=Q0:#B#^#RRk#U,Dx=`wiRiP@Pw%Uz,DxS0:!x-$j!|s4AK5kQRk164zRQ!#\A,NQ0bO2S0t!}%'u!xN$u!tB/9#c#^#f#^#g#RS09#U!#\J,P2Q0:!~049/25S09%EQ!t6,aO2S0a!}S8!u9$Q0:!}T6Qj\k!{~'!}U%ES0:G;PEPf12e}S0_12KERE'912y}RQ/9EQ0_PEPQPE!w5'Q0C!}U+EEQQ0kQ0e,j=Q0d!s+$c,j=5t=5t=g00a3+0@<0?rS0kPtP=1}=8P4Q0nH0<!|6$!u#,oQ04,|=Ry5`wS0o!z,'jQ0m,nyS0m1ww<S0jDoCd!z83:!z;%q/28Ry168z!#\m%7S0OP<Cs[!un$^:!zO&E!#h3$bQ0`O5b1Q0uQ0!#3&'K#RRE,6NRz,FFRePgQ0^!zL,szPz!zL$zhRg!zL$zDRQ!zL'gPQ!zL,zPz%Cz!zL,Rh!zK=!u{%%UE,DxRx/D{R{!z54164ER>?KD!x421NFeRe!#7~6!#R?49%E>[!sc$!yS>Px!yR6>!yR4zR>G;PzPf12g}Rf12Kz!#3n$Q}RK/9zPfPzPK!#3n%gPQPh!yN+z!yN$!#4}%!xq-!xc%P{Q0mQ!xX>168E!xP$P<Cs\y!xK1z!xK1PeP>G;GLNW0;Q07Q07PXf?R>Q0UQ0\PJDIPXP5P]Q0\PNQ0]Q0^CbPJDI5e9PGP5Q0@#<ReP61ACed5SCQ!#t_%5PCPH!s=$Hd1FFIRI!s;%Q03#<R!s@'P]!sQ&D!s7$DdP^!sM'?P6Q0?,ACdP_!s:'B#<R!sP+`!s<'>#B#<Rz!s>$zdPa!s>'s#<R:!s<$:dPb!s<'AP6Q0A!s~$c!s:'H#<R=!sP$=dPd!uN%DP6Q0D,ACd5SCRkP>Pk!s?%FP6Q0F!s?6IP6Q0I!s?4!s~$Td9SCTRTP>PT!sT%MP6Q0M!sT'!s?-PP6Q0P!s?6RP6Q0R!s?'6P>P6D5E0!s$,FV!s$3409W@+08Q00!xL+@R6Q0T,@FRFP>PJDIRT!xR%P>!xQ81@CeRe!xF$R!u`&8PIC4Ry!sD&HRHP]C4RE!ud$LP^C4R8!s2$MP_C4R~!sN&DRDP`C4RA!s6&zRzPaC4R{!s6&:R:PbC4Rw!sb$PPcC4R@!sB&=R=PdC4RC135RRi136RRv5:GPG135BRt136BRl!s4$?R}136?Rh!s4$URQ136URg!s4$SRn136SRm!s4$VRK136VRf135WRj136WR|5:GH0>FhFhDaDaDaW@B07TYZP5!v]%BRTPFfARx!|',Px!vW5kPyPEP8P~PAP{PwP@PCPGPiPTPRCYPGPtPTPBPGP}PTP?PGPQPTPUPGPnPTPSPGPKPTPVPGPjPTPWCYDH!s$+!td$P3PXfCRjPFPT!tW&4P]PT!x074PeQ0=PGP4!x$$!s8$H!}0$4PL!}#$4PM!|s$4PD!|e$4Pz!|U$4P:!|G$4PP!|;$4P=!|,$4PRPjPR!s0$BPj!u?$4P?Pj!uA$4PUPj!uC$4PSPj!uE$4PVPj!uG$4PWPjPW!zx1D1!s$5PXfDRTPFPjPJPYPZF?P5PXfERK!uk-7!uk;<!uk'<!uk'<!uk%Q0VP^PG13<!uj%<!uj&<!uj&<!uj&<!uj&<!uj&<PRfFR7!ul$<PBP7!ul$<P?P7!ul$<PUP7!ul$<PSP7!ul$<PVP7!ul$<PWP7!ul=Fh!uj&3PGP;!u1$C4PGP;!u3';!wx&;!wx%Q0WP_PG13;!u3%;!u3&;!u3&;!u3&;!u3&;PRfG!u3&;!u3+;!u3+;!u3+;!u3+;!u3+;!u3?!u1+XfHR<PFP7!wu-GQ02!uD,1!uD'1!uD&1!z>&1!z>&1!wR&1!uE&1!uE&1!uE&1!uE&1PRfJRePRPGQ0XPe!uD$1P?Pe!uD$1PUPe!uD$1PSPe!uD$1PVPe!uD$1PWPe!uD/DH!z?7!wQ$0!#5B%PGP0!u&&0!u&&0!u&&0!u&&0!u&&0!u&&0!u&&0!u&&0PRfK!u&%P0PB!u'%Q0Y!u&&0!u&+0!u&+0!u&+0!u&1DH!|C7PXfLR1PFPe!wH/PO!u:,[!u:&[!u:&[!u:&[!u:&[!u:&[!u:&[!u:&[!u:&[PRfNRI!u:$[PBPI!w?$[P?PI!u;$[PUPI!u;$[PSPIPSPGQ0ZPI!u:$[PWPIPWD5!u4%!~W9!w<$\PHP]!u#$\!tw&\!tw&\!tw&\!tw&\!tw&\!tw&\!tw&\PRfO!tw&\!tw+\!tw+\!tw+\!tw'P\PV!tx%Q0[PIPWCY!#4P<PXfPR[PFPI!w10>!u/+6!u/&6!u/&6!u/&6!u/&6!u/&6!u/&6!u/&vfRRv!u,$lPv!u'$hPv!u%$gPv!u#$mPv!t}$fPv!vu$|Pv!#8o1H!vq6x!#=-$!s0$!t`%x!t`&x!t`&x!t`&x!t`&x!t`&xPRfS!tb&xPB!td&xP?!tf&xPU!th&xPS!tj&xPV!tl&xPWPv!#8<>PXfTR|PFPv!vh0j!t~+T!t~&T!t~&T!t~&T!t~&T!t~&T!t~&TPRfVR^!t~$TPBP^!t~$TP?P^!t~$TPUP^!t~$TPSP^!t~$TPVP^!t~$TPWP^!t~@3PGPK!#@h$!s0$!td%K!td&K!td&K!td&K!td&KPRfW!td&K!td+K!td+K!td+K!td+K!td+K!tdAPXfXRTPFP^!vb07!tt+!#;&NZR_!#;&'_!#;&'_!#;&'_!#;&'_!#;&'_!#;&'_!tt>3PGfIR_PDP`!td$_!t\&_!t\&_!t\&_!t\&_PRf[R<!t\$_PB!t`$G!tX$<!t\$_PU!t`$G!tX$<!t\$_PV!t`$GP_PWP<!t\;PXf\RMPFP<!vP0e!tj+!#9xF^R`!tj$1PBP`!#9y'`!#9y'`!#9y'`!#9y'`!#9y'`!tj<3PGfMR`PzPa!tZ$`!tR&`!tR&`!tR&`PRf_R1/3RRD!s5$B!tY$G!tQ$1!tU$`PU!tY$G!tQ$1!tU$`PV!tY$GP`PWP1!tU1!v?-`RePFP1!v?0I!tc+!#8q>bRa!#8q'a!#8q'a!#8q'a!#8q'a!t`$[PVPa!#8r'a!v79!v5$QRaP:Pb!tP$a!tH&a!tH&aPRfcR[!tH$aPB13[BRz!s2$?!tN$G!tF$[!tJ$aPS!tN$G!tF$[!tJ$aPWP[!tJ/D1!tJ%PXfdRIPFP[!v&0v!tX+|!tX&|!tX&|PRffRb!tX$|PBPb!uz$|P?Pb!tV$|PUPb!tV$|PSPb!tV$|PVPb!#7w%WPb!uz7!ux$URb!#M1$PGPb!t>&bPRfgR|!t>$bPB!tB$GPbP?13|?R:!s2$U!tD$G!t<$|!t@$bPV!tD$GPbPWP|!t@,D1!s+%PXfhRvPFP|!un0^!tN+!#6q-jRc!#6q'c!#6q'c!#6q'c!#6q'c!#6q'c!#6q'c!uf5!ud$YRcP=Pd!t<$cPRfkRT!t4$cPB!#MV%cP?!#MX%cPU13TURP!s2$S!#M^%cPV!#M`%cPWPT!t6'!uZ%E0PXflR^!#Jo$!uZ-<!tD+MPRfnRd!tD$MPBPd!tD$MP?Pd!tD$MPUPd!uR$MPSPd!tB$MPVPd!tB$MPWPd!uR3!uP$]RdPRfoRMPRD5PG!s~$M!t&$dP?!t-$G!s~$M!t&$dPS13MSR=!s2$V!t0$GPdPWPM!t+%!uF-pR<PFPM!uF0DfqRD!#Q0%ePBfrR!t:%e!t:+e!t:+ePS!uB$GPe!t8+e!t8,!u<0aRMPBfsRePB!u<$M!#HR'M!#FN'M!#FN'MPV13eVRT!v8&ePWD5!u0-tR|!#F<0fuRe/3BR[9:GzPGPIP?fvRz!t/$IPUPz!t/$IPSPz!t/$IPVPz!u#$IPWPz!u#/!t}$eRzP?fwRIP?!t}$z!#D5'z!#D5'z!#D5&Pz!#F/&!to+x!#Cx3:fyR:P?!vw$vPUfzR!sv%v!sv+v!sv+v!sv23PGfiRvPUf{R1PU!t`$v!#7M'v!#7M'v!#7M-PXf|R7!#7?3Pf}RPPU!tV$^PSf~RL!sl$^PVPL!sl$^PWPL!sl+3PGfmR^PSp+01@RjPS!tM$^!#TU'^!#TU+PXp+01A!#T81GP=p+01BPS!tC$<PVp+01CR=!#>J'=!se&3PGPD!sE%DR3PV!t8$DPWP3PWD5!t+%ER=PFP3!t-0Tp+01FPV!t-$|PWp+01GR|!s[$9Q01!s`%HR9!#4Q$DIPXPeP]P|!#Uf0PYPZp,2Hhp,5HlazyPDp,2HKPeP|P^PvPzPMPdPcPbPaP`!#S]$9?Q0J9:G5X8GPP13e?P\E\!s@$UQ0L!s@'713eUP0!s@&SQ0N!s@'113eSP;!s@&VQ0Q!s@'I13eVP4!s@&WQ0S!s@':13eWP5!s@&RQ0E!s@'j13eRPK!s@&BQ0G!s@'LP[PxE\P=ODN:05WOWNP4P5O2n20010!s#$12!s/&W7WM!sD@L!sD@K!sD@Q!sD+1!sD6P!sD@J!sD@I!sD@H!sD@F!sD@E!sD@S!sD@R!sD@C!sD@G!sD@D!sD@`!sD@d!sD7!s0%baWZWYWXWWWVW\W[WUW^W]WTP4N>04WBW_W?Wco"). Qed.

  Lemma finish_nil : ltac2:(zQ "h20!ho7!il2!s2!uc!il8!iub!ks1!hl5!iu2!ks9!kt1!kh1!jp1!j7!o1!hm5!jj3!jj9>4regs@2$8@1$0#5@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$4@1$1@1$0#8>0@1$c^2>0@1$b^2@4$e$2$d@2$6@5$9?2fx^4Kd@3$h0@1$0#k0+tvqt4Kv$5@2$h1@1$0#k0+tvqt4@1$1@1$0#k0^3@1$a$2?5model@2$f@1$3$7?1K").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["Loop"] "##&`h01mh14regsp;1p;2p;3p;5p;4g00Ocj10Tg00Pkj11Tg00eQj12!s/$oj13Tg0134j2>Tg019<j1;!s8$`j1:Tg01;mj15Tg00gYj16Tg018=j37Tg01MTj14Tg01R<j58Tg01Vnj29Tg01Wcj4=Tg01Xkj3<Tg00`NR0#0R1#1#2%01!s1$0!s$$2R2#3R3'>%21#3#;\3f1R3#:%53p,2fxf3R1%10#0#1!s$-0!s&&!s0,0#0#6g018`572f2R2g00;;#4D8p,5model'9p,1KP1P2P3f0C=3<UUW0W1o"). Qed.


  (* [comment removed for export] *)
  Lemma pc_dfbd0 : ltac2:(zQ "70!ho7!il2!iub!jj3!jj9!ht4!ktc@3$5@1$1@1$0#k0@2$6Kd@3$3@1$0#k0+tvrl0Kv$2@2$4@1$0#k0+tvrl0@1$1@1$0#k0+4Kd@3$3@1$0#k0+tvrl4Kv$2@2$4@1$0#k0+tvrl4@1$1@1$0#k0").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["Loop"] "##'Jh02b1h12b2h21nh31Hp;1p;3p;2g00eoj14Tg00AHj33Tg00fRj22Tg01Z8j37Tg00Ocj10Tg00eQj1:Tg00Pkj11Tg00gYj15Tg018=j36!s\$\j29Tg00D<j28Tg01[_R0f0R1#4R2f1R3#4R4g00Gaf2R5#4?331g00Z_R6f3R7/25127333R8[12531251536%47?353[R9f4#4?375\8A7531P1n20010!s#$12!s-%0W1W0W2P9^14^02^20P1g00`NR1#0#0R0#!s$':R2%11#0#1!s$-0!s++!s&$!s[%#0#5g018`R4562%50'9R0!sb%0#5R1=624R4186112201224536dO4b3o"). Qed.

  (* [comment removed for export] *)
  Lemma loop1 : ltac2:(zQ "i70!ho7!il2!ku6!jk1!juc!ht4!kg1!iub!s2!jj3!jj9!il8!jib!ij8!im1!jv3!jva!hqc!kgb!lg3!km8!hv2!ik5!ikc!lg9!li6!lid!ks1!lj6!hl5!iu2!ks9!kt1!kh1!jp1!j7!o1!hm5!ije>1n$h2>4regs@2$he@1$0#5@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>1k$h2>1b@1$1@1$0#k0>2bs@1$4@1$1@1$0#8>0@2$h3@2$2@1$1@1$0#8^1^6>0@1$i2^6>0@1$i1^6>0@3$5@1$1@1$0#k0@2$c^8@3$9@1$0#5+aKv$7@2$a@1$0#5+a@2$3@1$0#k0@1$6^6>0@3$5@1$1@1$0#k0@2$c^9@3$9@1$0#5+h6Kv$7@2$a@1$0#5+h6@2$3@1$0#k0@1$6@2$2@1$1@1$0#8^5>0@3$5@1$1@1$0#k0@2$c^a@3$9@1$0#5+h2Kv$7@2$a@1$0#5+h2@2$3@1$0#k0+1>0@3$5@1$1@1$0#k0@2$c^b@3$9@1$0#5+h3Kv$7@2$a@1$0#5+h3@2$3@1$0#k0@2$e?2su+l8>0@2$h6@2$h3N1^a@2$h8^a@2$2@1$1@1$0#8^8>0@3$5@1$b@1$4@1$1@1$0#8@4$h0$8^c@2$3@1$0#k0@2$e?2su+l8N8@2$f@1$4@1$1@1$0#8@2$h4N8^a>0@3$5@1$b@1$4@1$1@1$0#8@4$h0$8^d@2$3@1$0#k0@2$e?2su+l0N8@2$f@1$4@1$1@1$0#8@2$h4N8@2$3@1$0#k0@1$6@2$2@1$1@1$0#8^a>0@3$5@1$b@1$4@1$1@1$0#8@4$h0$8?4mem1^c@2$2@1$1@1$0#8^b@2$f@1$4@1$1@1$0#8^b>0@2$h7@2$d@2$h5@2$h1@1$0#k0^d@1$6@2$2@1$1@1$0#8^c@2$e?2su+n0@2$d?2su@2$h1@1$0#k0^d>0@2$d@2$h5@2$h1@1$0#k0^e@1$6@2$2@1$1@1$0#8^d+ogggggggggg0>0@2$d@1$6@2$2@1$1@1$0#8^e@2$i6+2+he@4$i4$8$i3@2$hb@5$hf?2fx^h3Kd@3$9@1$0#k0+tvrm0Kv$7@2$a@1$0#k0+tvrm0@1$1@1$0#k0^h2@1$i0$8?5model@2$i5@4$h9@1$1@1$0#8$hd@1$hc@2$3@1$0#k0?2fd@3$ha@1$1@1$0#8^h1^f?1K").
Proof.
    induction n as [|n IH]; intros regs m k b bs LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb Mb Mn Bbs DISJ NW M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b) as Hb.
    destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 88) 1 (Z.of_nat k)
                (Z.of_nat (length bs)) (Z.of_nat (length bs)) b)
      as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
    { eapply LM_store_ok; [exact LMm | exact SOK1]. }
    { replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact Mn. }
    { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
    replace (su - 88 + 8)%Z with (su - 80)%Z by lia.
    set (m' := wbytes (wbytes m _ _) _ _).
    assert (LMm' : LM m').
    { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
    assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
    eapply (rz_writev1_wall RSEGS regs1 (0xdfb50 : word) m' model W_dfb50 fd
              (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b + Z.of_nat k))
              (Z_to_bv 64 (Z.of_nat (length bs) - Z.of_nat k)) (skipn k bs) K);
      [ exact F_dfb50 | exact E_dfb50 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
      | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
    - subst m'. rdn_solve.
    - subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
    - rewrite word_to_nat_Z by lia.
      replace (Z.to_nat (Z.of_nat (length bs) - Z.of_nat k)) with (length bs - k)%nat by lia.
      subst m'. repeat rdn_peel1.
      change (Z_to_bv 64 (bv_unsigned b + Z.of_nat k)) with (at_ b (Z.of_nat k)).
      apply (rdn_skipn RSEGS m (length bs) b bs k); [|lia].
      eapply LM_rdn; [exact LMm | exact Bbs | lia | lia].
    - unfold TASK_SIZE. u_norm. lia.
    - unfold TASK_SIZE. u_norm. lia.
    - u_norm. lia.
    - u_norm. lia.
    - intros k' K1 K2. rewrite pc_dfbd0. rewrite length_skipn in K2.
      destruct (Nat.eq_dec k' (length bs - k)) as [EQ|NE].
      + destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite Q22. f_equal. lia. }
        { lia. }
        eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k' (skipn k bs))) by (rewrite length_skipn; lia).
        apply finish_nil; [| exact LMm'].
        eapply RI_but; [exact RI1|].
        revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      + destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                    (Z.of_nat (length bs) - Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact Q22. }
        { lia. }
        { lia. }
        { lia. }
        eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (IH regs2 m' k' (at_ b (Z.of_nat k)) (skipn k bs)).
        * rewrite length_skipn. lia.
        * eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * exact LMm'.
        * exact P10.
        * rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
        * rewrite P18. gres. exact Q18.
        * rewrite P19. gres. exact Q20.
        * rewrite length_skipn. lia.
        * subst m'. unfold at_. rdn_solve.
        * subst m'. rewrite length_skipn.
          replace (Z.of_nat (length bs - k)) with (Z.of_nat (length bs) - Z.of_nat k)%Z by lia. rdn_solve.
        * rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs) b bs k); [exact Bbs|lia].
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * unfold at_. rewrite length_skipn. u_norm. lia.
        * rewrite length_skipn. lia.
  Qed.


  (* [comment removed for export] *)
  Lemma loop2 : ltac2:(zQ "i99!ho7!il2!ku6!juc!kg1!jk1!ht4!s2!il8!ij8!im1!jv3!jva!hv2!hqc!iub!jj3!jj9!km8!jib!kgb!ikc!ll3!lg3!lla!ik5!lg9!li6!lid!ks1!lj6!hl5!iu2!ks9!kt1!kh1!jp1!j7!o1!hm5!ije&@2$b@1$3@1$1@1$0#8@2$h2N8^c&@2$5@1$0#k0@1$4@2$2@1$1@1$0#8^c&@2$h2N8~1&@2$b@1$3@1$1@1$0#8~2&@2$d@2$e@1$0#k0^h2@1$4@2$2@1$1@1$0#8^h1&@2$9~4@2$a?2su+n0&@2$h5~5@2$9?2su@2$e@1$0#k0^h2&@2$d@2$e@1$0#k0^h3@1$4@2$2@1$1@1$0#8^h2&@2$9~7+ogggggggggg0>1n$h4>4regs@2$i0@1$0#5@1$1@1$0#k0>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>1k$h4>2b0@1$1@1$0#k0>3bs0@1$3@1$1@1$0#8>2b1@1$1@1$0#k0>3bs1@1$3@1$1@1$0#8>0@2$h7@2$h6@2$2@1$1@1$0#8^3@2$2@1$1@1$0#8^1^8>0@1$i4^8>0@1$i3^8>0@3$6@1$1@1$0#k0@2$h3^a@3$h0@1$0#5+aKv$f@2$h1@1$0#5+a@2$5@1$0#k0@1$4^8>0@3$6@1$1@1$0#k0@2$h3^b@3$h0@1$0#5+h6Kv$f@2$h1@1$0#5+h6@2$5@1$0#k0@2$d@1$4@2$2@1$1@1$0#8^7@1$4@2$2@1$1@1$0#8^5>0@3$6@1$1@1$0#k0@2$h3^c@3$h0@1$0#5+h2Kv$f@2$h1@1$0#5+h2@2$5@1$0#k0+2>0@3$6@1$1@1$0#k0@2$h3^d@3$h0@1$0#5+h3Kv$f@2$h1@1$0#5+h3@2$5@1$0#k0@2$a?2su+m8>0@2$h9@2$h7N1^c@2$ha^c@2$h6@2$2@1$1@1$0#8^a@2$2@1$1@1$0#8^8>0@3$6@1$8@1$3@1$1@1$0#8@4$c$7^e@2$5@1$0#k0@2$a?2su+m8N8~0>0@3$6@1$8@1$3@1$1@1$0#8@4$c$7^f@2$5@1$0#k0@2$a?2su+m0N8~3>0@3$6@1$8@1$3@1$1@1$0#8@4$c$7^h0@2$5@1$0#k0@2$a?2su+l8N8~0>0@3$6@1$8@1$3@1$1@1$0#8@4$c$7^h1@2$5@1$0#k0@2$a?2su+l0N8~3>0@3$6@1$8@1$3@1$1@1$0#8@4$c$7?4mem1^h0@2$2@1$1@1$0#8^f@2$b@1$3@1$1@1$0#8^f>0@3$6@1$8@1$3@1$1@1$0#8@4$c$7?4mem1^f@2$2@1$1@1$0#8^e@2$b@1$3@1$1@1$0#8^e>0~6>0~8>0~6>0~8>0@2$9@2$d@1$4@2$2@1$1@1$0#8^h5@1$4@2$2@1$1@1$0#8^h3@2$i8+2+he@4$i6$7$i5@2$hd@5$i1?2fx^haKd@3$h0@1$0#k0+tvrm0Kv$f@2$h1@1$0#k0+tvrm0@1$1@1$0#k0^h9@1$i2$7?5model@2$i7@4$hb@1$1@1$0#8$hf@1$he@2$5@1$0#k0?2fd@3$hc@1$1@1$0#8^h8@3$h8@1$1@1$0#8^h6^h4?1K").
  Proof.
    induction n as [|n IH]; intros regs m k b0 bs0 b1 bs1 LEN RIr LMm Ha0 Hs6 Hs2 Hs3 Kb
      Mb0 Mn0 Mb1 Mn1 Bbs0 Bbs1 DISJ0 NW0 DISJ1 NW1 M30.
    { exfalso. lia. }
    pose proof RIr as RIr'.
    destruct RIr as (R2 & R8 & R9 & R21 & R3 & R4 & R23 & R24 & R25 & R26 & R27).
    pose proof (u64_range b0) as Hb0. pose proof (u64_range b1) as Hb1.
    destruct (Nat.le_gt_cases k (length bs0)) as [LE|GT].
    - (* [comment removed for export] *)
      destruct (sw_retry_a regs m (seg_rom RSEGS) su f fd (su - 104) 2 (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b0)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 8)%Z with (su - 96)%Z by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_le k bs0 bs1 LE).
      eapply (rz_writev2_wall RSEGS regs1 (0xdfb50 : word) m' model W_dfb50 fd
                (Z_to_bv 64 (su - 104)) (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k))
                (Z_to_bv 64 (Z.of_nat (length bs0) - Z.of_nat k))
                b1 (Z_to_bv 64 (Z.of_nat (length bs1))) (skipn k bs0) bs1 K);
        [ exact F_dfb50 | exact E_dfb50 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. rdn_solve.
      + subst m'. u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. repeat rdn_peel1. exact Mb1.
      + subst m'. u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. repeat rdn_peel1. exact Mn1.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs0) - Z.of_nat k)) with (length bs0 - k)%nat by lia.
        destruct (Nat.eq_dec k (length bs0)) as [EK|NK].
        { replace (length bs0 - k)%nat with 0%nat by lia.
          rewrite (proj1 (skipn_all_iff k bs0)) by lia. reflexivity. }
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b0 + Z.of_nat k)) with (at_ b0 (Z.of_nat k)).
        apply (rdn_skipn RSEGS m (length bs0) b0 bs0 k); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs0 | lia | lia].
      + rewrite word_to_nat_Z by lia. rewrite Nat2Z.id.
        subst m'. repeat rdn_peel1.
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_dfbd0. rewrite length_app, length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs0 - k + length bs1)) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn k bs0 ++ bs1))) by (rewrite length_app, length_skipn; lia).
          apply finish_nil; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (IH regs2 m' k' (at_ b0 (Z.of_nat k)) (skipn k bs0) b1 bs1).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs0 - k)) with (Z.of_nat (length bs0) - Z.of_nat k)%Z by lia. rdn_solve.
          -- subst m'. repeat rdn_peel1. exact Mb1.
          -- subst m'. repeat rdn_peel1. exact Mn1.
          -- rewrite length_skipn. apply (rdn_skipn RSEGS mem1 (length bs0) b0 bs0 k); [exact Bbs0|lia].
          -- exact Bbs1.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- pose proof (u_at_le b0 (Z.of_nat k) ltac:(lia) ltac:(lia)). rewrite length_skipn. lia.
          -- exact DISJ1.
          -- exact NW1.
          -- rewrite length_skipn. lia.
    - (* [comment removed for export] *)
      destruct (sw_retry_b regs m (seg_rom RSEGS) su f fd (su - 104) (Z.of_nat k)
                  (Z.of_nat (length bs0)) (Z.of_nat (length bs1))
                  (Z.of_nat (length bs0) + Z.of_nat (length bs1)) b1)
        as (regs1 & RUN & Q17 & Q10 & Q11 & Q12 & Q18 & Q19 & Q20 & Q22 & QB); try assumption; try lia.
      { eapply LM_store_ok; [exact LMm | exact SOK1]. }
      { replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact Mn0. }
      { replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact Mb1. }
      { replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact Mn1. }
      { eapply LM_rdn; [exact LMm | exact Mfd | u_norm; lia | u_norm; lia]. }
      eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN |]. clear RUN.
      replace (su - 104 + 16)%Z with (su - 88)%Z in * by lia.
      replace (su - 104 + 24)%Z with (su - 80)%Z by lia.
      replace (Z.of_nat k - Z.of_nat (length bs0))%Z with (Z.of_nat (k - length bs0)) by lia.
      set (m' := wbytes (wbytes m _ _) _ _).
      assert (LMm' : LM m').
      { subst m'. apply LM_wbytes8; [apply LM_wbytes8; [exact LMm| lia | lia] | lia | lia]. }
      assert (RI1 : RI regs1) by (eapply RI_but; [exact RIr' | exact QB]).
      rewrite (skipn_app_ge k bs0 bs1) by lia.
      eapply (rz_writev1_wall RSEGS regs1 (0xdfb50 : word) m' model W_dfb50 fd
                (Z_to_bv 64 (su - 88)) (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0)))
                (Z_to_bv 64 (Z.of_nat (length bs1) - Z.of_nat (k - length bs0)))
                (skipn (k - length bs0) bs1) K);
        [ exact F_dfb50 | exact E_dfb50 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact Q17 | exact Q10 | exact Q11 | exact Q12 | | | | | | | | exact HKnil | ].
      + subst m'. rdn_solve.
      + subst m'. u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rdn_solve.
      + rewrite word_to_nat_Z by lia.
        replace (Z.to_nat (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))) with (length bs1 - (k - length bs0))%nat by lia.
        subst m'. repeat rdn_peel1.
        change (Z_to_bv 64 (bv_unsigned b1 + Z.of_nat (k - length bs0))) with (at_ b1 (Z.of_nat (k - length bs0))).
        apply (rdn_skipn RSEGS m (length bs1) b1 bs1 (k - length bs0)); [|lia].
        eapply LM_rdn; [exact LMm | exact Bbs1 | lia | lia].
      + unfold TASK_SIZE. u_norm. lia.
      + unfold TASK_SIZE. u_norm. lia.
      + u_norm. lia.
      + u_norm. lia.
      + intros k' K1 K2. rewrite pc_dfbd0. rewrite length_skipn in K2.
        destruct (Nat.eq_dec k' (length bs1 - (k - length bs0))) as [EQ|NE].
        * destruct (sw_c2_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k'))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. rewrite Q22. f_equal. lia. }
          { lia. }
          eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          rewrite (proj1 (skipn_all_iff k' (skipn (k - length bs0) bs1))) by (rewrite length_skipn; lia).
          apply finish_nil; [| exact LMm'].
          eapply RI_but; [exact RI1|].
          revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        * destruct (sw_c2_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k'))) m' (seg_rom RSEGS) (Z.of_nat k')
                      (Z.of_nat (length bs0) + Z.of_nat (length bs1) - Z.of_nat k))
            as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
          { gres. reflexivity. }
          { gres. exact Q22. }
          { lia. }
          { lia. }
          { lia. }
          eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
          apply (loop1 (length bs1) regs2 m' k' (at_ b1 (Z.of_nat (k - length bs0))) (skipn (k - length bs0) bs1)).
          -- rewrite length_skipn. lia.
          -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
          -- exact LMm'.
          -- exact P10.
          -- rewrite P22. gres. rewrite Q22. rewrite length_skipn. f_equal. lia.
          -- rewrite P18. gres. exact Q18.
          -- rewrite P19. gres. exact Q20.
          -- rewrite length_skipn. lia.
          -- subst m'. unfold at_. rdn_solve.
          -- subst m'. rewrite length_skipn.
             replace (Z.of_nat (length bs1 - (k - length bs0))) with (Z.of_nat (length bs1) - Z.of_nat (k - length bs0))%Z by lia.
             rdn_solve.
          -- rewrite length_skipn.
             apply (rdn_skipn RSEGS mem1 (length bs1) b1 bs1 (k - length bs0)); [exact Bbs1|lia].
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- unfold at_. rewrite length_skipn. u_norm. lia.
          -- rewrite length_skipn. lia.
  Qed.

End Loop.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac wout1 :=
  rewrite wbytes_outside;
  [ | unfold in_rng; rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia
    | rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; u_norm; lia ].

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma sw_post_of_LM : ltac2:(zQ "a1!ho7!il2!hrb!ij8!il8!hv2!lpf!lua!mj6!mk1&>0@1$1@1$0#k0@1$4@1$1@1$0#8>3mem~0>1m~0>2su$2>1f$2>2ra@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>3can@1$1@1$0#k0>2wb$2>1n$2>1s@1$1@1$0#k0>1l@1$1@1$0#k0>4bufp@1$1@1$0#k0>5bufsz@1$1@1$0#k0>0@2$3@2$5+hggggggg0+n0^h1>0@2$3^h2+ogggggggggg0>0@2$3+vpgg0^h2>0@2$3@2$5^h3+u8+hirmv8>0@3$7^h5@f$8^h7^h5^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^h6@6$6^h8^h6^h5^7^6@4$9^h7^h5^7^6").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["FPX2"] "#%-Gh04__x1h17__arithh26__sat7h3!s/%8h44__ffh58__varmaph65__with71nh84__x2h91xh:1oh;1zh<2Hah=1mh>1yh?1Eh@3FhihA3FlohB1GhC1HhD2HxhE3Hx1hF3Hx2hG3Hx3hH4SUhihI4SUlohJ4bufphK5bufszhL3canhM1fhN1lhO3memhP2rahQ1shR2s0hS2s1hT2s2hU2s3hV2s4hW2s5hX2s6hY2suhZ2wbp%0p%1p&0p;1p;2p;?p;3p;@p;4p;6p;5p;7p;;p;<p;Bp;8g00Ocj19Tg00eQk10A!s0$ok10:Tg019<k105Tg00gYj1^Tg00Pkj1L!s8$<R0j21Tg00E;R1j20Tg02GTl?um@00Tg01;mk30[Tg00BBj26Tg00fRj28Tg00AHj3]!t2$^j2tTg01S=k40;k50HTg02Hbk60MTg00hTk10J!s0$7k20ITg00k3j2;Tg00IUj1cTg02Ilk201Tg01A`j2=Tg01Bhj37j4!sW$D<j2f!tF$bR2j1sTg00GER3j23!s1$aR4j22Tg01Cjk10!s0$DHk40`Tg00lNk20ZTg00m6k30YTg003>k10XTg00@7k10?Tg00M;k20>!sN$Zk10W!s:$Yk40VTg00N7k10U!s0$Uk10T!vm$Hk20<Tg00SBk10R!s0$dk20QTg00TFk20PTg00U2k30O!s0$Qk40NTg00O@k20!x&$n[k30KTg00obj3FTg00>\j2HTg01F=j2PTg01HMj6!sJ$1Yj6?Tg01:ck10GTg01J]k504Tg01>1j2oTg01b\j5vTg00H<j2[Tg01O`j3yTg01PFj6|!v@$kj6!uy$VCj4kTg01cgj7wTg02Jnm;0ETg00j:j1jTg01Khm<0DTg00WJmB0C!w^$Vm<0!wt$ETk30STg00QPk30BTg00R3j4hTg00X0j7gTg00Y8j7i!u_$>k60!x&$n8k30a!sC$\j8nTg01GMk30@Tg01IUk30_Tg01=1k40]!s|$^k70\Tf0R5#9#9p=_%9!s0$!s$,p=m%95#^p=a!sB+p>0F%L5#9p=lf2R6f1R7'1/05p=df3R8/061375'2#jp=41375,26#jp>08g00_DR9!sH+p=`1675,;6,88p=Wg00Z_R:/f5p=>g00Z@R;P:!s$$2P2f5R2f4R<P8P6P7P5N<0Dp>0^!sH&!s$%0P5P7P6P0P8P<P2f6S00f7R0f8S01f9S02NB0Cp=E!sT$3P0P3Q00P2P!s}/=p=Q!s<-&027P5EX60S0p=J1095p=D209:5p=BB0B:75p=SP6g00\fR3g00]ER=P=g00]eR>P:P7g00bmR?P5Chg00^ER@Fgp=AP6P3P=P=P!sK'a_RAP5ChP!sF$CP8!sF+!sP,7P5FiJ03p=~P:P7P!s|$p=ZB0a!tX$@P0!sR'!u<'!sa'!su9@Fg!sy&Gnp=Y1067/25p>0L108!wr+GP2!sZ+!vL%!u1-!tS%P@FgGnp=:!sQ@A!sQ/UP:P0Q00%j2%j!sR$CkP7P5E?p=MP;!w^,E?p=5%s5:0@67#jp=T!x1$1P0P1!x18<!t$&!s@'!s~,N!tU,p=r!v307!s2+5P@FgFip=q!v^0!sI0!vP&p!{L&p>071;75,86p={!s~25Gnp=RB0@675!{u$6!{b&p=V!tt+B0_675I04p=Og00;;S03!sd%H0]p=bP:!v/1z12!tH%=\!y73p=x!s91K0\p=}!uC2!sY0Fip=eg00`NR3#9R@#9RA#9R1#9R?#9RB#9RC$0ARD$0:RE&0A1$0:RF$05RG[S04Q04%_C#m#m#mRH#^RI%L3RJ#LRK#9RL#_RM#aRN'1S05f@S06'0fAS07%_H$0F#m#aS08'0%LK#L#_#l#_!s:%9Q07'0fBS0:%LL#_#aS0;%lARA#l#L!s&+!s$'!sF$<3dfDS0=fFRLQ0=Q0:Q07Q06f?S0>f>S0?f=S0@f<S0Af;S0Bf:RKQ02Q01!yL$M?ufES0C40[P4%9JRJ!t$'D,6L18D5R4P4%9A#aS0E,6LC4fHRAP7O1fIRHfGS0FQ0CQ0=fCS0G!tN+Q0>Q0?Q0@Q0AQ0BPKQ02P7N@005]G[^9EQ!s^&!sYA!tu$M?u/tLPAPLQ0C!u+$!sc%!s1$H0;J0MP5Q0D,6AP4P4Q0E,6AC4fJRO!tv$KRPPHQ0F!sf$!vC$!tC=!tq/PO!tB&!sZBK!to$HPPPHPA!u`%O!s/&H0;S0H16ONP4P4POC4%^BRB18D7R45dO%_JRJ#9RQ#^S0I,1O8084%^MRM18D6R45dP%^CRC,1P8084&0J818D8R8%^@R400ICRR7`8PGfOR8fMS0J/1BRS,;DS0Kg00^e#c!s$1RT!u5%+01S0L'=S0M37S0NQ0J%L@RU#9#_S0O#^RV'1RW!sp$PQ0>,=TS0QP<CIS0RfQS0SP2O19]G5X:GRXPGP8Q0KQ0M!sI%TP!s9$P<O1S0UPXPGfPS0VfNRYfLS0WPPPOPHPA!w]:P<N@00S0XPXPGQ0V%^1R1,6YRZ,;DR[Q0W!t^$Y37S0Z%^?S0[,6YR?!t}$\1=TPS0]37S0^%^JS0_,6YRJ!sC$`1=TOS0a37S0b16YBR\!s>$c1=THS0d37S0e16YVR]!s>$f1=TAS0g37S0hQ0I,6YR^!s@$iQ0F!tT$j37S0k16YMR_!s@$l1=TLS0m37S0n16YCR`!s>$oQ0C!sX$p37S0q!zg$YRa!sB$rQ0=!sB$s37S0t!{5$YRb!sB$uQ0G!s/$v!sH$w37S0x%aQS0y,6YRQ!sB$zQ0:!s/${!sK$|37S0}%LU!~+%~,6YRU,;DS10Q07,=TS11!wq$12!w&%xQ0zQ0|!s:%3!s:%tQ0uQ0w!s:%4!s:%qQ0rQ0s!s:%5!s:%nQ0oQ0p!s:%6!s:%kQ0lQ0m!s:%7!s:%hQ0iQ0j!s:%8!s:%eQ0fQ0g!s:%9!s:%bQ0cQ0d!s:%:!s:%^Q0`Q0a!s:%;!s:%ZQ0\Q0]!s:%<!yB&P[Q0YP<CIRc!s8'<O1S1=PXQ1=,fGPcQ0Y!sO$P<PTPDPDP8P1CWRc18D2RXPX%s5Rd,1cS1>C4X7;PZP5P!s>$TRc,15S1?C4X;:Re18D<Rf,0ZRg11ZcS1@,3fRh'2Ri11Z1Rj,3fRk,2gRlPiPlPgPhPgPkPgP5X9:Rg1375Rk$02X>:X9:RhPfPf%>fRlQ1@PjPg!s$$:P:g01LM1175H0`#>X=:X7:RiPZPZ%>ZPcP1PgPg%>dX9;PTP1%>1J0^RmM:ES1AGQGJ20Z4CRn1394%DC139R[[Ro%D4Rpg012;RqB0Y4C7UW<Rr%DR\q^<pRpg00_bRq$0XRs&0?qRqP:20>:6P7&0W:H0VRt&0U:Ru&0T:RvPvPv20<:3R3%BNRw'S20<:@R@5AvACv@3C~Rx&0R=R=P!sS$%B1Ry,S3Rz/Z@1@zyS1B9Cv@GY20Qv>R>P5P6g00cTR{g00d4R|'f20P56=]{|dB0O:97H0NR|b4b5b6X0:X8:165N@0L7kg012WRk[RN1671R{P6P611{1S1CCGPk[[^0:^8:P518D0S1DQ0SQ00O3R}b1b2b318D[S1EPnPoPrPpPsPq20>:7R~PuPv%BI/@w=Av3S1FP=Pv209:9R9PzE:P>P!ta,Q05/05Rw%D{[^0:P5!t6$6O2S05!t7%!t0/P!t'$Q08#B9Av3RIP=PvPz%B4>0K:DR4EU!t+28,05Rz13{R!t,->O2R{!t+%5FZS0SGMQ1EPfPfQ1E/1cS08C4eQ0Y,HFS0YQ0W,PTS0WD5Q0Y9T<[ePTQ1>/0R!{j$Q1?/0RX;:RZQ1@/0R10jRPg1075!{#,[!zv$Q1APRPR%>RRjG<!uQ5P!uH$Q1BP4!vG31C/0R\z^0:P!u2&Q1EQ0SGNQ08/0Re!}s$WD5EKE?Q1<Q0]!~g%!~',Q0[CWS0ZPXPXQ0Z/1dS0Z!~#%?Pe10?fS1<11?cS0W,3fS0Y'2S08Q!s;$1S0S,3fS1E'2S1CQ08Q1C!t6$YQ1<Q1EQ1<!}}$fPfPlQ0WQ0S!}]&iP?P?%>?!}E$!}1%<GQGJ!uv0t!uv$xP!{e&Q0[#B,S3S1E/Z@Q1E/@yS0Y!{h%!v80X8:Q0[,67S1CP6P6Q1C/11S08!{-$\N!{/&!zv&Q0\,8DS1B!yn6!zi%P9Q1E!wD5#D\w^!zo$!zV;!x''EP!zF41C/3!x'15F?S1CGMQ1B!z7%B/1cS1E!z7$]!z7$]1PTPS1AD5!#7u$5T<ePTQ0Z!z7&?PZQ0W/0RQ0S/0RPgP[!w=%Q1<PRPRP!yy?0Y!yy5!y^$!yy2BQ1CGNQ1E!yy%]Q1A!yy';Q0a!#9v$!yy/_CWR?PXPX11?dS0^!yv%JPe10JfR?11JcS1;!y`$A'2S0]11J1S1E!s8$C,2?S1B!t6$BP?Q1AP?Q1CP?!yp-1;Q1E!yp+JPJ%>J!yp-C!ypE_!yp&A!yp$A/@!#6Z+!yp5_,67R?!#5u$?1S0]!ym:`,8DS08!ym@A!w82%D?!ykKA!yk413?!yi3JS1AGMQ08!yi$08/1cS0Y!yi$a,HFR?1PTOS0aD5Q0`=T<?!yf$^!yf&JPZQ1;/0R!x\%!yf$!w3$Q1C!yfD!#4a60]!yf408Q1AGNQ0Y/0ReP?Q0a!ye':Q0d!#@q$!ye,PB!yd1b!yd%\Pe10\!yd$\cS1:,3fS0a'2S0Y11\1S1A!s8$8,2?RJQ0YPJ!t8$P?Q08!yb1:Q1A!yb+\P\%>\!yb,08!ybC%BBS0a,S3R?/Z@1@?!#4R<167BRJ!y^%J!y^>c!#4MCP?!y]4J!y]IP?!y\6J!y\3\!#4G4RJ!y[$d!y['HS0dD5Q0c!y[+b!y[&\PZQ1:!y[$A!y[+:Q1AQ08!#4CX]!#4C:10J!yY%d!yY'9Q0g!#G`$!yY-V!yY1e!yY%]Pe10]!yY$]cS19!yG$d'2S1C11]1S1B,3fRJ,2?R\Q1CP\!t7$P?PJ!yW19Q1B!yW+]P]%>]!yW-d!yWEVS1C!yW1]!yW<V!yW/Y!yW:f,8DR\!yV~!yVC]S08GMP\PfPf11\!yS'g!yS'AS0gD5Q0f!yS+e!yS&]PZQ19!yS$B!yS+9Q1BQ0d!ySE]!yS6Y!yS3P\Q08!yR-g!yR'8Q0j!#NH$!#:l-I!yS1h!yS%^Pe10^!yS$^cS18!yS$g'2S0811^1RJ,3fR\,2?R]Q08P]!t7$P?P\!yR18PJ!yQ+^P^%>^!yQ-g!#:fDI#BS08!#4+GQ0I,67R\!yU%\!#4-=i,8DR]!yUQ\!yU^\!yU3^S0dGMP]!yU%]cR\!yU$j!yU$Q0F,PTS1BD5Q0i!yW+h!yW&^PZQ18/0R10J!yU&8PJQ0g!#4%iP]Q0dGN10\!yT$1B!yT'7Q0m!#U2$!yT,PM!yS1k!yS%_Pe10_!yS$_cR\,3fS17'2S1B11_1R]!#3~'^Q1BP^P?Q17!#3~2P\P]!yQ+_P_%>_!yQ,17!#3|DMS1B!yO1d!#3|;M!#:UFl,8DR^!#3|~!#3|A_S0YGMP^!yM%^!#3|&m!#3|&L!#3|%l!yK+k!yK&_PZ10\R10]!yI$P\P]Q17!yHEd!yHH^Q0Y!#3v66Q0p!#[h$!yH-C!yH1n!yH%`Pe10`!yH$`cRJ!yH$6'2R^11`!yG&\,2?R_P^P_P?Q16!#3r2PJ!yF-`P`%>`!yF-6!yFECS0g!#@uJC!#3m+R_!yE:o!yEV!#3lo`S0]!yE0!#3l$p!#3l%C,PT!#@r%o!yG+n!yG&`PZ10J!yG,JP]Q16!#3iV10_!yE5]!#3g+!#@i+5Q0s!#bC$!#:=-E!yF1q!yF%aPe10a!yF$a!#3h$R^'2R_11a!#3f-`P_P`P?P^!#3d?aPa%>a!yD-5!#:7DE#!#3cHQ0E,67!#3eFr!#3e~!#3eFa!#3e2`!yF$s,HFR_Q0=,PTS16D5Q0r=T<_!yF$q!yF&a!#3g65!#3gr`ReP_Q16!yH'4Q0w!#hy$!yH/DCWR_!yH%_dS0t!yH%bPe10bfR_11bcR`,3fS14!#3h$b!#3h+_RaP^PaP_Q14P_P\P_!yJ-`!yJ-bPb%>b!yJ-4!yJAQ0D!yH%_=Av@S16Pv1@_yS0Y,r@CqDp!yO5D,67R\/06S0]11\1Ra8076!yR8u!yRD_!#3r[_!#3rFb!#@`$!#3r2w!yR&v,PTS0vD5Q0u!yR+t!yR&bPZ10`!yR,`P]Q14!#3rXa!yP5!#@['_Q0v!yP'3Q0|!#o_$!yP/y!yP/R_!yO%QPe10QfR\11QcR^,3fS0x'2Ra11Q!yO&`,2\RbPaPbP\Q0xP\P`P\!yO-^!yO-QPQ%>Q!yO,0x!#3sDy!yQ%\/Z@1@\yS13!#3s:y,67R`!#3s$`1Rb!#3r9z,8DRa!yF?\!yF4`!yFJ\!yF6`!yF3QS0vGMPa!yF%a!#3r&|,HFR\Q0{!yF${D5Q0z=T<\ePT10_!yD$QPZ10^!yD,^P]Q0x!yDD13!yD6b!yD2aQ0v!#3n&\Q0{!yD'2Q11Q0}Q10!yD/~CWR\!yD%\dR\!yD%UPe10UfR`11UcRa,3fRb'2R]11U1!yS$RQ,2`R_P]P_P`PbP`PQP`!yB-aP^!yB+UPU%>U!yB,12!yBE~!yB%`!yB$`yS0{!yB;~,67RQ!yB%Q!yB<10,8DR_!yB?`!yB4Q!yBJ`!yB6Q!yB3U!yB%_!yB%_cRQC4eQ11,HFR`Q07,PTR]D5Q10=T<`!yA$\!yA$UPZ10aR10^!yA%aP^Q12!yAD0{!yAF_!yA&QReP`P]!y@&!y:$Q1137R]Q0O#aR`!#}=&R_Q06,=TRbP<CIPb!xo$!yd+P`CWR]!yc%]dS0O!#4&0]!#4&+10'2S0}!wy$!yu$U,2]R\Q0}!#<c$0P]PUP]!#4+/a!#4+;10!#G?D`,S3R]!yf$]yS0}!#G<;`RU!yd%U1S0v!ye818D_!#ZX@]!yc4U!ycJ]!yc6U!#4#55!#ZX/UC4e1HFbR]Q06,PTRwD5AT<_]ePTQ0O!#:B%!#3|'a!#3|&aQ10!yaE}!#@n5v!#ZO65GN10UReP]Pw!yc'XQ1=5]GeQ0UQ00P<!wm=Q16Pv1r@?!#?08]@076J!wU6O2E?Q0TQ0MP8Q0KP<PT11YB9{DDR}!zL%}dR}!zK%SPe10SfRN11S!#Nb$R?'2Rx11S1Rw,3fR],2NRUPxPUPNP?PNP]PN!#N`/w!zG+SPS%>S!zG,0T!zG:vPvQ0a,@3RN=Av@R]Q08,@39Cv@C~S08!zf&]Pv1@NyR]!#B,9115BP7P7Q0I,15!zZ$R?117B!zr,Rx!#~U0Q1DQ0VP2O3S0a!#<$&K,8DR2!{#609#B=Av3R\P=AAv9NS0]CR!tU0S16Q09/05R{%DU[^0:S00P5Q0VQ0?O2S0U!#~N<;#B,@3Q0<#B5AvRzP=ACvN4S0X!t3305Q0;Q0<5d5RI13UR!t7%<!t7&@O2R!t6&5FSRaGMP2!{s%2cR^C4eQ0M,HFRQQ0L,PTR_D5Q0K=T<QePT10}!{u$S!#P,&w!#P,&wQ0T!{u>z!v3$]4S0T!t~4K10xR\I!tt$LP!uz'2PaGN10^RePQP_!{y'RQ0QQ0NQ0P!zj&V!zj$!#C;3WPe10WfRQ11W!#67$Ra'2R211W1Rx,3fRw,2QRJP2PJPQPaPQPwPQ!#63/x!zj+WPW%>W!zj-R!zj9Q!zL+vQ1C,@3RQ/Z@1@QyRw!#63917VRa!z?%a1RJ!z?$\?!z@%Q!z4,P,8DR?!vv6!z'&QS0a!z'4C%Da\{!vu$8Q!yr=!wb$CvQ4S0M!wb4;13a!wb'v!wb'5FWS0}GMP?!yO%?cRa!yO$Q,HFR2Q0>,PTRSD5Q0P%s2R}606<!#CI,W!#6K&x!#6K&xQ0R!yTDw4S0R!u\4010J!tp'O!yT+?Q0}GN10aReP2PS!yU'NQ0PQ0Q37RaQ0J/1MR?,;DRJQ!$@-$Q0QPaPJ!yq&M!yq$Y!yq%YdRY!$+v/Re!uo$X!yq'x11?!#Ch%W,2eR_PxP_PePaPePWPe!yq-X!#Ch,!$+d1Rl!#5\=1B,@3Rt=Av@RhQ0g!#5\'!z3&hPv1@tyRy!#5Y<MP7P7115!$4o$117MR@!z<%@1Rh!#5U7<O3!#=Q'JRk!zB=tS0V!wd4D%D@!zB&g!zBEt4S0U!sj4B13@!xP'P!zB,?R@GMPk!zA%kcRfC4!xZ&B06<J}!z/$Y!$+u&10X!#D7+XP^Pl!z-Dy4S0N!{x4}10h!t\&1F!z-+kP@GN10f!z,/P8Q0J!$GY$P<I0H!#=d%bDWGWFWEX9EPP11ABRG,;DR<Q02-01KS1=,=TR857ORS11AVR2,;DRf1=TKR@37Rk11AMRA,;DRU=7k@RhPPPSPkPPPOPSPPP!$KyKM?uRLPOPPAVDH1S0>Q0j57PR4Q0[9VDHS0[Q0m37RlQ0_!s7%_Q0p37R^AVDHBS06Q0s37RXAVDHVS07Q0G,=TS0G37RZQ0I!s[%IQ0:!s=$:37R?AVDHMS0=!#GM$YAVDHCS0C;7bRCQ0E!sY%E!}\%JQ0D!s7%DQ0?,;D,=TR}37R{Q0y9VDHR9Q0@!s>&337ReQ0~!s>$WQ0A,=TRa37R_AVDH`R`Q0B,=TRx57_PPPeP_PPP{PePPPJP{PPPCPJPPPYPCPPP?PYPPPZP?PPPXPZPPP^PXPPPlP^PPP4Pl!w/$4&0GPQ0jPPQ0>FOQ0mP4Q0[FOQ0pPlQ0_FOQ0sP^Q06FOQ0GPXQ07FOQ0:PZQ0IFOQ11P?Q0=FOPbPYQ0CFOQ0QPCQ0EFOP}PJQ0DFOP3P{P9FO!#3S$FOPxP_P`FO1tPLeP5I04P8POP<FOP@PSPf!s-$kPUFOQ0H,tPe&0?FRL$05R`Abk<TR_Q0B001K,=T,oL9]`5X:`RWP`AbS<TPWQ03POP<Q1=PGAd51RX;:S1=!|:'Q0KQ0LP5PPQ01O2RO!#3%'<RWQ16Q00P5PHP0O2S00b1!s^,5Q0<P!sU&5FGDzAdW1ReDvP_Q03!u5$2PGPTPT11HBR_?`_RS0<11_cRW/0RR011HVRe?`eRS0511edRa/0R10We10a_'[3\3\X7;A`GGRRa11GcR9/0RR{A`22RR3112cRJ/0RR}1092S1610JGS0L'[S0K'2S0B'2RC'2RY'2S0D11G1Rb/0RR?1121RZ/0RRX10b2S0E10ZGS0Q'[S0C'2R^,23Rl'2R4,2aPaPYPaP4p-0R4/fa9yaaS0=P{PCP?PlPgP[P9Pb!#8Z'GPG%>GS11!#?P,I!#4T&S0:P3Q0BP3P^1f439y33S0BP}Q0KPXQ0C!#Bf%Z!su+2P2%>2S0C!su-K!su,7!wm$LQ!|y$!tZ'Q0IP2P2Q0CG<!sw'Q0KPGPGQ11G<E|EX!s$%!#648!#8\$PvQ0]Q0X5xvS0XPvQ0TPvQ0aQ0M!s9$MPvQ0RAAv]QAAvwN5}vDeDeC!#=s2Q09/07R^116BRB?`BRS0911B1Rl/0RRC116VRV?`VRS0a11V1RY/0RS0]10lV10YB!x{%[\I^0:!zk&Q02O3S02!z@%CkQ0De1HF@S0D1PTKS01D5FwE?Abh<T!zP%kPA!zP%Q0<11HMRH?`HRS0Q11HdRd!tA$E10WH10d!z>$7\0!z?$AA!zm$AcR_/0RRW109AS0<10_!z,&16'2S0G'2S06,2{S0s,2aS0_11A1RF/0RRP10bAS0p10FGS0['[S0m'2S0>,20S0j,2?S0A!z&$Q0sPaQ0AQ0=P{Q06P?Q0jQ0:P0Q0GP0Q0>1f409y00R4PWQ16PPQ0m!xS$_PF!yL+APA%>ARi!yK+Rm!yJ'RjQ0<!yI$pQ0[!yI/APAPi!yH&_PFPm!yGV!y>,VQ0U5xvRGPvQ0NAAv]tAAvy!y=?116MRM?`MRR611M1RN/0RR]10lM10N!xv$7\C\^!xx$Q!xl/_eQ0DQ!xd'Q0H?b<T1oL85]`eP`AbkfT1oLx!#5y%Q03PSPfPKP2Q!#5e,10Q0OP!#5\+fRSQ!$Iw$!#5T0;Q0v!#5T+2DzAdS1ReDvAbhf!z,-2!z,%511ecRc/!#Le%E10cH10de!#5;'10JAR;10_2Rd'[Re,2WRc,20RH,2}Rh,23RS10ZARx10F2R8'[R<,2PRC,20RB,2XRl,23P3PhP3PlQ0BP}PHPXPBQ07P0PcP0PCP4PWPePPP<PjP;PdPxP8!~z/!xk5!#3H&!xkM!~p%PvP!xb+w!xb$Q!xb=aQ0]10YM10NV'[9\6]3\!xO5PS!xN5!x?$@RL5]`eQ03PkPUPKPA!x>/0}Q1F!x>-URDQ1DQ0g!x>11BQ0P!x>,ADzAdD!x>$!t7$UT=]`LeN;0EWBW?P7P5O2n20010!s#$12!s/&WCW@WAWHWIXKEXJEXNEXQEX7:XZ:XLEXXEXWEXVEXUEXTEXSEXREXPEXM:XY:W=WOo"). Qed.

Lemma pc_dfb48 : ltac2:(zQ "70!ho7!il2!iub!jj3!jj9!ht4!ktc@3$5@1$1@1$0#k0@2$6Kd@3$3@1$0#k0+tvqs8Kv$2@2$4@1$0#k0+tvqs8@1$1@1$0#k0+4Kd@3$3@1$0#k0+tvqscKv$2@2$4@1$0#k0+tvqsc@1$1@1$0#k0").
Proof.
ltac2:(KReplay.run1z (kr_t_RefStdioWrite ()) ["FPX2"] "##'Fh02b1h12b2h21nh31Hp;1p;3p;2g00eoj15Tg00AHj33Tg00fRj21Tg01Z8j3:Tg00eQj1;Tg00Pkj10Tg00Ocj12Tg00gYj16Tg018=j37!s\$\j29Tg00D<j28Tf0R0#2#2p=4g01[_R1%50R2f1R3#5R4g00Gaf2R5#5?330g00Z_R6f3R7/15117333R8[11531150536%57?353[R9f4#5?375\8A:530P0n20010!s#$12!s-%0W1W0W2P9^14^02^21P0g00`NR0#4R1#4#4#;R2%00#2#0!s$-2!s&&0#4#!u8%4#6g018`R4572%61'9R1%00#4#6R0=724R4186011211124536dO4b3o"). Qed.

Theorem ref_stdio_write :
  forall (regs : bvmap 5 word) (mem : word -> option byte) (model : Model) (su f wb wp fd : Z)
         (s l bufp bufsz can ret : word) (pending extra : list byte) (K : TSet),
  getr regs 2 = Z_to_bv 64 su -> getr regs 10 = Z_to_bv 64 f ->
  getr regs 11 = s -> getr regs 12 = l -> getr regs 1 = ret ->
  (4294967296 + 112 <= su)%Z -> (su <= 140737488355328)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (su - 112)) 112 = true ->
  (1019904 <= f)%Z -> (f + 232 <= 1226488)%Z ->
  sw_file mem f wb wp fd bufp bufsz ->
  ssp_cells mem can ->
  (0 < fd < 2147483648)%Z ->
  fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
  (* LPS 75d69e00: a write to a channel needs the model's channel reader present
     (LibWritev.rz_writev1_wall / rz_writev2_wall premise, after fd_lookup). *)
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  (0 <= wb <= wp)%Z -> (wp <= 140737488355328)%Z ->
  (wp - wb)%Z = Z.of_nat (length pending) ->
  bv_unsigned l = Z.of_nat (length extra) ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112)%Z \/ (su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112)%Z \/ (su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 140737488355328)%Z ->
  rdn RSEGS mem (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS mem s (length extra) = Some extra ->
  ret_ok ret ->
  K [] ->
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte),
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     sw_post mem su f bufp bufsz mem' ->
     realizes RSEGS (mkCfg (mkst regs' ret mem' (seg_rom RSEGS)) model) K) ->
  realizes RSEGS (mkCfg (mkst regs (916032 : word) mem (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
Proof.
  intros regs mem model su f wb wp fd s l bufp bufsz can ret pending extra K
         Hsp Ha0 Ha1 Ha2 Hra SUlo SUhi SOK Flo Fhi SWF SSP FD Hfd Hrdr Hh Hlazy WBP WPhi
         LENP LENE M30 DISJP DISJE SNW RDP RDE Hret HKnil HK.
  pose proof (u64_range s) as Hs. pose proof (u64_range l) as Hl.
  pose proof SWF as SWF'. pose proof SSP as SSP'.
  destruct SWF as [Fwp Fwb Ffd Fbuf Fbsz]. destruct SSP as [Ggot Gcan].
  zaddr Fwp; zaddr Fwb; zaddr Ffd; zaddr Fbuf; zaddr Fbsz.
  assert (HlZ : l = Z_to_bv 64 (Z.of_nat (length extra))).
  { rewrite <- LENE. symmetry. apply u64_roundtrip'. }
  (* [comment removed for export] *)
  set (mem1 := mem_sw1 mem su ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                       (getr regs 20) (getr regs 21) (getr regs 22) can wb (wp - wb) s l).
  assert (SOK1 : store_ok RSEGS mem1 (Z_to_bv 64 (su - 112)) 112%nat = true).
  { subst mem1; unfold mem_sw1. store_ok_peel. exact SOK. }
  assert (M8 : rdn RSEGS mem1 (Z_to_bv 64 (su - 8)) 8%nat = Some (word_to_le_bytes 8 ret)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M16 : rdn RSEGS mem1 (Z_to_bv 64 (su - 16)) 8%nat = Some (word_to_le_bytes 8 (getr regs 8))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M24 : rdn RSEGS mem1 (Z_to_bv 64 (su - 24)) 8%nat = Some (word_to_le_bytes 8 (getr regs 9))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M32 : rdn RSEGS mem1 (Z_to_bv 64 (su - 32)) 8%nat = Some (word_to_le_bytes 8 (getr regs 18))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M40 : rdn RSEGS mem1 (Z_to_bv 64 (su - 40)) 8%nat = Some (word_to_le_bytes 8 (getr regs 19))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M48 : rdn RSEGS mem1 (Z_to_bv 64 (su - 48)) 8%nat = Some (word_to_le_bytes 8 (getr regs 20))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M56 : rdn RSEGS mem1 (Z_to_bv 64 (su - 56)) 8%nat = Some (word_to_le_bytes 8 (getr regs 21))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M64 : rdn RSEGS mem1 (Z_to_bv 64 (su - 64)) 8%nat = Some (word_to_le_bytes 8 (getr regs 22))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M72 : rdn RSEGS mem1 (Z_to_bv 64 (su - 72)) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M104 : rdn RSEGS mem1 (Z_to_bv 64 (su - 104)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 wb))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M96 : rdn RSEGS mem1 (Z_to_bv 64 (su - 96)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 (wp - wb)))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M88 : rdn RSEGS mem1 (Z_to_bv 64 (su - 88)) 8%nat = Some (word_to_le_bytes 8 s)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (M80 : rdn RSEGS mem1 (Z_to_bv 64 (su - 80)) 8%nat = Some (word_to_le_bytes 8 l)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mcan : rdn RSEGS mem1 (Z_to_bv 64 0x12b6f8) 8%nat = Some (word_to_le_bytes 8 can)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbuf : rdn RSEGS mem1 (Z_to_bv 64 (f + 88)) 8%nat = Some (word_to_le_bytes 8 bufp)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mbsz : rdn RSEGS mem1 (Z_to_bv 64 (f + 96)) 8%nat = Some (word_to_le_bytes 8 bufsz)) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Mfd : rdn RSEGS mem1 (Z_to_bv 64 (f + 120)) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 fd))) by (subst mem1; unfold mem_sw1; rdn_solve).
  assert (Bp : rdn RSEGS mem1 (Z_to_bv 64 wb) (length pending) = Some pending).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDP. }
  assert (Be : rdn RSEGS mem1 s (length extra) = Some extra).
  { subst mem1; unfold mem_sw1. repeat rdn_peel1. exact RDE. }
  (* [comment removed for export] *)
  assert (HK' : forall regs' m,
     getr regs' 10 = l -> getr regs' 2 = Z_to_bv 64 su -> getr regs' 1 = ret ->
     getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
     getr regs' 18 = getr regs 18 -> getr regs' 19 = getr regs 19 -> getr regs' 20 = getr regs 20 ->
     getr regs' 21 = getr regs 21 -> getr regs' 22 = getr regs 22 -> getr regs' 23 = getr regs 23 ->
     getr regs' 24 = getr regs 24 -> getr regs' 25 = getr regs 25 -> getr regs' 26 = getr regs 26 ->
     getr regs' 27 = getr regs 27 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
     LM su mem1 m ->
     realizes RSEGS (mkCfg (mkst regs' ret (mem_sw2 m f bufp bufsz) (seg_rom RSEGS)) model) K).
  { intros. apply HK. all: try assumption.
    eapply sw_post_of_LM; [exact SUlo | exact SUhi | exact Flo | exact Fhi | ].
    match goal with H : LM _ _ _ |- _ => exact H end. }
  pose proof (finish_nil su f l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi Hh Hlazy Hret M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz HK') as FIN.
  pose proof (loop1 su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L1.
  pose proof (loop2 su f fd l bufp bufsz can ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 3) (getr regs 4) (getr regs 23)
                (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) mem1 model K
                SUlo SUhi Flo Fhi FD Hfd Hrdr Hh Hlazy Hret HKnil SOK1 M8 M16 M24 M32 M40 M48 M56 M64 M72 Mcan Mbuf Mbsz Mfd HK') as L2.
  pose proof (LM_refl su mem1) as LM1.
  destruct (Z.eq_dec wb wp) as [EQ|NEQ].
  - (* [comment removed for export] *)
    destruct pending as [|p0 pending']; [| cbn [length] in LENP; lia]. cbn [app].
    subst wb.
    destruct (sw_enter_eq regs mem (seg_rom RSEGS) su f wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1.
    lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?M _) _) _ =>
      replace M with mem1 by (subst mem1; rewrite Z.sub_diag; reflexivity) end.
    rewrite Z.sub_diag in M96.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    destruct extra as [|x0 extra'].
    + (* [comment removed for export] *)
      cbn [length] in HlZ. change (Z.of_nat 0) with 0%Z in HlZ. cbn [map].
      eapply (rz_writev1_zero RSEGS regs1 (0xdfac8 : word) mem1 model W_dfac8 fd (Z_to_bv 64 (su - 88)) s (t_emit [] K));
        [ exact F_dfac8 | exact E_dfac8 | exact Hh | exact Hlazy | exact Hfd | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | unfold TASK_SIZE; u_norm; lia | unfold TASK_SIZE; lia | ].
      { u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. rewrite <- HlZ. exact M80. }
      rewrite pc_dfb48.
      destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 0)) mem1 (seg_rom RSEGS) 0)
        as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
      { gres. reflexivity. }
      { gres. rewrite R22. exact HlZ. }
      { lia. }
      eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
      apply FIN; [|exact LM1].
      eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
    + (* [comment removed for export] *)
      eapply (rz_writev1_wall RSEGS regs1 (0xdfac8 : word) mem1 model W_dfac8 fd
                (Z_to_bv 64 (su - 88)) s l (x0 :: extra') K);
        [ exact F_dfac8 | exact E_dfac8 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
        | exact R17 | exact R10 | exact R11 | exact R12 | exact M88 | | | | | | | exact HKnil | ].
      * u_norm. replace (su - 88 + 8)%Z with (su - 80)%Z by lia. exact M80.
      * unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
      * unfold TASK_SIZE. u_norm. lia.
      * unfold TASK_SIZE. lia.
      * cbn [length] in LENE. lia.
      * lia.
      * intros k K1 K2. rewrite pc_dfb48.
        destruct (Nat.eq_dec k (length (x0 :: extra'))) as [EK|NK].
        -- destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. f_equal. lia. }
           { lia. }
           eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           rewrite (proj1 (skipn_all_iff k (x0 :: extra'))) by lia. cbn [map].
           apply FIN; [|exact LM1].
           eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                       (Z.of_nat (length (x0 :: extra'))))
             as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
           { gres. reflexivity. }
           { gres. rewrite R22, HlZ. reflexivity. }
           { lia. }
           { lia. }
           { lia. }
           eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
           apply (L1 (length (x0 :: extra')) regs2 mem1 k s (x0 :: extra')); try lia.
           ++ eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
           ++ exact LM1.
           ++ exact P10.
           ++ rewrite P22. gres. rewrite R22, HlZ. reflexivity.
           ++ rewrite P18. gres. exact R18.
           ++ rewrite P19. gres. exact R19.
           ++ exact M88.
           ++ rewrite <- HlZ. exact M80.
           ++ exact Be.
  - (* [comment removed for export] *)
    destruct (sw_enter regs mem (seg_rom RSEGS) su f wb wp fd s l bufp bufsz can ret)
      as (regs1 & RUN1 & R17 & R10 & R11 & R12 & R2 & R8 & R9 & R18 & R19 & R21 & R22 & R3 & R4 & R23 & R24 & R25 & R26 & R27);
      try assumption; try lia.
    eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN1 |]. clear RUN1. fold mem1.
    assert (RI1 : RI su f l (getr regs 3) (getr regs 4) (getr regs 23) (getr regs 24) (getr regs 25)
                     (getr regs 26) (getr regs 27) regs1).
    { unfold RI. repeat split; assumption. }
    eapply (rz_writev2_wall RSEGS regs1 (0xdfac8 : word) mem1 model W_dfac8 fd
              (Z_to_bv 64 (su - 104)) (Z_to_bv 64 wb) (Z_to_bv 64 (wp - wb)) s l pending extra K);
      [ exact F_dfac8 | exact E_dfac8 | exact Hh | exact Hlazy | exact Hfd | exact Hrdr | exact FD
      | exact R17 | exact R10 | exact R11 | exact R12 | exact M104 | | | | | | | | | | | exact HKnil | ].
    + u_norm. replace (su - 104 + 8)%Z with (su - 96)%Z by lia. exact M96.
    + u_norm. replace (su - 104 + 16)%Z with (su - 88)%Z by lia. exact M88.
    + u_norm. replace (su - 104 + 24)%Z with (su - 80)%Z by lia. exact M80.
    + rewrite word_to_nat_Z by lia. replace (Z.to_nat (wp - wb)) with (length pending) by lia. exact Bp.
    + unfold word_to_nat. rewrite LENE, Nat2Z.id. exact Be.
    + unfold TASK_SIZE. u_norm. lia.
    + unfold TASK_SIZE. u_norm. lia.
    + unfold TASK_SIZE. u_norm. lia.
    + u_norm. lia.
    + u_norm. lia.
    + intros k K1 K2. rewrite pc_dfb48. rewrite length_app in K2.
      destruct (Nat.eq_dec k (length pending + length extra)) as [EK|NK].
      * destruct (sw_c1_eq (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. rewrite R22. f_equal. lia. }
        { lia. }
        eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        rewrite (proj1 (skipn_all_iff k (pending ++ extra))) by (rewrite length_app; lia). cbn [map].
        apply FIN; [|exact LM1].
        eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
      * destruct (sw_c1_ne (regupd regs1 10 (Z_to_bv 64 (Z.of_nat k))) mem1 (seg_rom RSEGS) (Z.of_nat k)
                    (wp - wb + bv_unsigned l))
          as (regs2 & RUN2 & P10 & P19 & P20 & P18 & P22 & PB).
        { gres. reflexivity. }
        { gres. exact R22. }
        { lia. }
        { lia. }
        { lia. }
        eapply rz_msteps; [exact Hh | exact Hlazy | exact RUN2 |]. clear RUN2.
        apply (L2 (length pending + length extra)%nat regs2 mem1 k (Z_to_bv 64 wb) pending s extra); try lia.
        -- eapply RI_but; [exact RI1|]. revert PB. unfold sw_regs_but. gres. intros PB. exact PB.
        -- exact LM1.
        -- exact P10.
        -- rewrite P22. gres. rewrite R22. f_equal. lia.
        -- rewrite P18. gres. exact R18.
        -- rewrite P19. gres. exact R19.
        -- exact M104.
        -- replace (Z.of_nat (length pending)) with (wp - wb)%Z by lia. exact M96.
        -- exact M88.
        -- rewrite <- HlZ. exact M80.
        -- exact Bp.
        -- exact Be.
        -- u_norm. lia.
        -- u_norm. lia.
Qed.
End FPX2.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
