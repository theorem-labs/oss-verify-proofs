(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EH/EhBridge.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EH/EhBridge.v. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Exec TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatSim XStoreOk XAxSymExec3 XAxSymExec3Sound XSegRun EhX_plain EhCut EhCut2 EhRegs EhIfaceDefs EhIface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER Require Import EhCut EhCut2 EhIfaceDefs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EhBridge.
Ltac2 kr_t_EhBridge () := KReplay.lz_vm "#$#$C47Corelib7Classes?Relation!s6)9Reflexive!sR.Program6Basics4flipC46Stdlib5Lists4!s+#8nil_cons!sa,4Init5Logic6eq_ind!sB88!sB(_r!s}+9micromega5Tauto5eKindI!sE;8GFormula00C4ELinuxProcessSemantics5Riscv7Prelude5bvmap!v.59Morphisms6Proper!sI?Krespectful_per_oblig!vl$_1!v?7:firstn_nilI89OSSVerify!t8#ofs:boost_json:fuzz_parse3lib2EH7XCatSim6msteps00C13~~~!smP3Lib4Exec!sk2K!sk`1!sk)!vF,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!vp#s2bv00I!yT19Datatypes6op!sL#!xm=?!s<2>!x}$!sE+>ms_svc_pending!tw,!t6:2!tX2!{.(2eq!tr#!tPZachine_result!u@\4!w]#K!tRi1!u~2!u\(3and01!yLa2!yL(C!{mZ:!sm(!#3W#!{o(!ugY=!ug*state00!t^P3Ref5RSegs5rsegs!{oM3!yT8!vv$0c9!v1Q8EhBridge6BRIDGE!v9*lib!t_3!zh0x01!yxZ7ms_r!uf#!txR6EhRegs4REGS6rshape!xt)!so^;!ud#_!st/!}r<3nat!}o5Peano2le00!x$G1C5!#7~(6ZArith6BinInt1Z6of_natC!#4s?7bv_wrapK!#5AC1!soA;bv_unsigned!ta<3eqb!t~=to!t~(!zH7not!s_<7eqb_neq!#7s=Z02!se<2le!zP:q!uk#!#=w3;Zify!#<i)and_morph!sOB7rew_iff!tT34Znat5Nat2Z9is_nonne!#8;<4list01!#9k;!sF(0K!tZ56VarMap1!z.$!sD>0!sD6=RingM!s4*7!#@g*!t567Env!sT#5PExpr01!sIE2!sI6!t?:!st7!#BL27!#C7;8B!sJ)!sH6:Z!t<+=Z!sT$Checke!#D,6!vJ)4f!#Dj#!sq?C!sq0_soun!|(>max!y3>7inj!yV$!zh77iff_sym!zBB5mkrel!tP<8max_spec!|8>t!#?L8or!#4[>1Z03!xw>3Pol!xJ8!xu15Psatz!yFF!sO)4!sOK6!sO6!x4.;!u{(!#8T#!#D_.!}18!tl7!|k,!u[7!sD,!vB7!{E36!xQB;!#3m(_rev!#6g<modulo!sF<9mod_small!#92AZ_to_bv!sLA@!sL)!#8l+!sU@4BvWf!#MIH6bv_eqb!#=CR;XAxSymExec33AX24ridx!#=@)!wHD!ym7!sJ3!x8G5!sJF8!~/Eapp!#8\<bool!}O/!sF8!#?f,!}o6!#LO<!#@K#0!#4a=6inj_le!}=D3Op2!#EW3!tt.uni!#:r8!vM(4ki!#It#!sfA!#=_68!vi#Inst@!#A`$!zf#!s,#!#?0.!uk7!t:.!vP6!#Ki84True01!#<L5!#3q:!uh7!vW6!uo>!xM$!#>k2!t](5Fals!#E8#!t^L!#7HD!t^$5!~=AD!~g._in_range!sYA:bv_!#4`#us!#5(<eq_dec!ub26Specif7sum!{q(!#S)9x00!tQA5!#3p#!#DT8or!#HR4!{l(Z2!{n#id!s^<!}1?N00!#5/R@!#5/,Sound4AX2S7regs_ok!#58$!#O3b9reg!#8j(!#M@c2gr!tci4regv!#TnX9XProp!vQ#4get!t^)!#9Hb6sr_get!ssjedeno!ss*!#;_?3Sem!x]#!tK#K!#;\be!#I7#!tE*!zf*!#as$7!s+#Def3nth!#WHPLib5Frame3mkR!t*3!#g):=eq_Tran!#RQ$!#d/>?eq_p!#dU#!s,#xy!sR?Mt!sy#_co_!#fk#v_impl!#O3$ism!{?_<mkR_of_!#UZ,I!wUb3env!#e:*!xIh!ss)!~ohcase!#\\(!#4ch4fla!|Nka!|N/!tlh6estar!sy*!{fS3Mem2wa!sd)!#Ov;pow!sC=ad!#PX<>pow_po!#VK)!sN<:!sN#!sJB7compar!#CK6!#Tv17!u~T2Nd:and_elimF3!#7eb=!#]_(64_mo!#eZ(!x\j!zJ#_u!}2i5sadd!}3+!#?v7!#DY$!#HG<:!wZ(is!#mt#!uYh5elenZ!#Lr(!uXi!#90)!y+S8!x?*3rdn!#;;@!#g<A@word_to_le_bytes!#pRC!#]EE3!z`]!uG,!#6rc!#5($_!#3K)!wyc6kentry!wz+!yjh9!s{(!#EP*!#5~W3le8!se^8!xf$_!#9A*!xo<length!#_C2!#kP(t!u1Ymr!#45)!#|h59nth_error!t*X:!u#(_!v=,!$$T7!#[P$fl!#VFA3inj!sg23Nat!#9\#!tlW<!w=*_!}z.!#Dp85skipn!sD;6!$$.$!#:=<add_0!$*+,!w$.;!$$j(all2!}#c;k!#3R#intro!xB2!vp96!#Z8#!#n2+5!u.$8!yg$!vx#!v|*!#foA!sI#!#W^=7Inj_Z_Z!#4BR8XCat!}e#D!y])N!#5}.!|~^5wr!|{.!#7\W5wview!#5$j7!tZ`8store_ok!v*X>!v*$_!sj+!#8Ih!#=@#_li!#ETZ!#N<(st!#7=)!#[e7proj!#||Z<find_segment!sjK<MemImageType<seg_writabl!#OU,!#]v2neg!#yD<9ltb!#o4#!#c(3!#Gl+ltb!#BD;7reflec!$.u#!tO;andb!}V+4Bool!s*$=!s>#_true!#x@6!tM.e!#{S=leb_!us4!$9o+!#rL.!tH,>!tH$fals!tIA!t+$g!#:vX7ro_add!#Xy)!t1;4of_N!$/*J!xl07S!yQ(00C6!tn,!tg96i!s\#s5PlainA!s+$!z8*_0!#H4)!smc!#AM)!smb!$3$)!smb!#M@)7!smP1M?loade!}O+!#85^7mem_in!#_Y(!#5(b=!yg)_!t~$!#4D=9!#i*#_ind!#8mj4!#Fon7know!#Fm+!#mY;!#qi/!#@~1Forall00!$BK7!sC(_!sf#!uvj!#Q=*!t<56Ex!s2#!#sE.!tz9!#{Y,!sG91!#Up`!wj*!$(/7f_equa!#zFA6bv!#B$#!#H7Wrdn_unfol!#IC)!|?Xwa_succ!si)3!t|(7tac!#;w$!u<(_hel!$I8,!#:/2nat!$>]#!#vpB!$5?3!sH.8!sH#!tX$!#DaSStoreOk9!~Z#grow!#3G)!#81V9seg!#EC(!seW8!se$ase!#<J<su!#<J<4to_N!#@kY?!#7/)!u4#_a!#<1T!#B^$5wmon!#Ji)!siY7outsid!#h.)!#@3;prod!#}>4!#A^,e!#A^)!~d62I!#NZ,!t$28lis!zP$!#yx<!tJ$!~^U!#Ez(iv!#sk)!w*Zmunch!#:Ch;!w4)_de!}|*!tcS6MStateC!$/6)!$/9.!trh>!yk$_of!}V0!#_g[7!|t#rom!tki6z!#~($!#X`;7f!#8}#b!t7d!#PO#!#D()!#tg:!$Xz#!#<R5in_map!$;p0!sa2seq!#a^D4!t+76!#CO#q!$\Y7!tD#!$\Y;3!t^0!#ty4Diff!#tm$subr!#v;)!t56>!w*)_!s.(!uy;ap!uy)!#X3@eq!sL#!#R1cin_!y3/!{mdstatics_!xw/!s{c@!s{+!#QM)!s}h7u64!#T{,!#uAc!#;\$!ssh5a_off!#3KY4Step8rw_cell!#48Z5C!sc#8!si$!#\E+!slY:!sl(siz!v=*!t\`w!v7[!sl(;!sl(!#_U.!#gJ6!}=#nil_r!$]1S!t5(4!t5#!#Qu)!$e0S!sj/!#6M)!yjSEhIfaceDefs6EHDEFS<EH_IMG_WORDS!s|l6eh_img!zl[TacX2wz!#p\(!vG_!#U;(!$^2ckimg!#h>.!#i8d!#QS$!yf#!sxi<!sx*!#:T#!{*<!#Ql)map!v3d!$)U$!#6.+!swcD!#4O)_C8!}C(!#3m*!t(cA!#mH$of!s~2!#nh7!vA)impl!xVlapp!#W/Bfs!$^k2!sC.sn!#S7QRefBRMalloc_i!}U#_stmt:RSSP_GUARD!~KY5EhCut3CUT6!{y#k!#sV)!sm\9!#4+1!{nd!sv+_eq!#RrP6BvBase=!#J0#!#q5)!t^c8!z8(!$5Uj2e!#`u(!$>Oh!#5vi9kwr!#w5/!svR7!#99(3EHI5!~a#!$(1Y!ym,3!#4Dk<!x/(litva!$F_i9!sy+!u]c7vCANARY!snc8flags!~,\6!so$24CUT29!sq$0!sr\!xz4!$)1)!snc!#h+Y!uR/:global!vG.!#7:e3me!#U*i=!#M++!#<$k7!~9#!zh\!v[0!tl,!{]dnewh!yxh9pool_liv!#NeY!y|4!#s])!vG^7!tb$!yyY!#ku25!#8|X!w~0!t]$!($O$!#uD(!suk!vK)!suk!#9+)!$3f?mo!$i(A?!#n^$!$iW,!$TSB3alu!sLE5alu64!(/`:!sN(5Instr!sP#op!$}9B6bv_su!$($+!#mu*div:Zminus!ucIsub!uc+!tmN!$7,c6wz!#rg#!#@^m!#||)!#>v\!t_+!#3\_hdr!#Yb/!#H4\!sp#!~i*!$3td!#Np$o!#X}(!#Ohd!$F7$!vR,!#4ZU;!#4Z*1!#>$Y!vL,4vHD!$\u)!sk^P2V!uFZ3Arr4u64!$*U[Arr:!sf#_sp!#<c+!(#K<ul!$Co6mul!#j1D5!s`7!#3V.!#j,.!$B[(!#tf+!$A86!#x3.!sF68sub_diag!(EQ>ap!#lw7!#_b*!#jB77!$EL#_!$*,8!sB(all2!t#8!sE)!tE9!$Hf)!sE#!up?!wN#!$D)A!sI#!#`=eeh_auxv_lis!y4)!$rRM!$zg6!((z77!sOK5!#Z7c!$Jz*!{\$nt!#xo(!}u]5vAUX!}vX!#Y(:!sv#_CELL!#3`dX16!#:@cvX!sjd4vUI!#[Gc!uD#!#FlY!sk02!#=Kc4vRN!uEZ!|r67PH_AD!#9>Z!#j+6PH_ENT!svpNUM!svXR!#M[,!#3O#!#?Bj:!#Wz$eli!#R*(!#6N6?!#e1(cons!#zJf=cell_of_!tK$!u?i8kwr!u=.!sudlit!#D9#!#CIi!su*!$[o3!$=D1repea!(GK<6shiftr!$md<!sF(_0_!#:Uf5zero!$Ey^!$\q+!#jg:!$RH,!#K_c<rdn!#n?q=!#\$)!zk#!#W^Y!vw62b!xv)!#ngc!wh$!#{I.!}Ri!vdq!xu,c!syk;!#d$$!w]/!#Yg_!#=2Y!#9~6eh_id!$.Y)!$JBR!#Xr:!#~y(".
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemantics0dmachine_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~k65rsegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~oa6msteps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~t06mstepst03evt07ms_regs89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6EhRegs4REGS~~~~~~hi36rshape37Corelib4Init9Datatypeshme4listhme3nat37Corelib7Numbers7BinNumshp54Npos89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hr63envhr64expr35stdpp9bitvectorbdefinitionsiga2bv37Corelib5Lists7ListDefiid3nthhr64ELithr66edenot37Corelib4Init5Logicild3andild2eq37Corelib4Init5Peanoine2le46Stdlib6ZArith6BinInt1Zip86of_natiga7Z_to_bvhme4boolhme5falseild1I3h5LinuxProcessSemantics5Riscv7Preludeitb6bv_eqbhr64ridxiga2BViga4BvWfild2exild2or89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhBridge6BRIDGE~~~~~~jid4regvitb5bvmap89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~jo37regs_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jta3mkRhi32grhp51Zhr66adenothr65saddrjo36estartjo34flat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~kkd2wajo35elenZip82leip82ltip83powhr62SAhme6optionhme4Some0h0word_to_le_byteshr65KWordjo39kentry_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~kua3rdnip83addkkd8bytes_atkkd3le8hr63KWrkkd5wr_atjta3stkhme4truekkd7ro_addrhr64KImgkkd7mem_invhr66kentryjo37know_okhme3apphme4conshme3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~lr29mem_growsjta5wmonohme4pairhme4prodjta3ivljta7outside36Stdlib5Lists4Listmi82Injta5munchhme4None05wviewiid3mapiid3seqjid6zrangejid6wview0mi87forallbild3notigabbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~mpc4cellmpc2C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~mu68rw_cells89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~nid9IMG_WORDS89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbEhIfaceDefs6EHDEFS~~~~~~nn9cEH_IMG_WORDSnid6img_knnn96eh_img3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasenu5dZ_to_le_byteshr64EVarhr62ev89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhIface3EHI~~~~~~oj35cell1nid8flags_kn79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Refh2RMalloc_iface_stmt~~~~~~oo9aRSSP_GUARD89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6EhCut24CUT2~~~~~~ou19flags0_knou1aglobals_knoj35cell4oj35cell879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~pkf2wzoo93memou1astatics_wrnid7newh_knou18PoolLiveou17pool_knoj39pool_liveoj35cell2ou18PoolIdleou1cPoolPristine3h5LinuxProcessSemantics5Riscv5Instrpv97ALU_ADD3h5LinuxProcessSemantics5Riscv3Semqi85alu64pv97ALU_SUBip83subnid3addnid6hdr_knoj39hdr_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~qo34u64smi89nth_errorip83mulnid7auxv_knnn9ceh_auxv_listoo9aRAUXV_CELLnn95zeroshme6lengthou1apool_statenn97eh_idle" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhIfaceDefs.EHDEFS. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ER.EhIfaceDefs.EHDEFS. Import EHI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BRIDGE.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH.EhBridge.BRIDGE.

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac kh ES C := eapply kword_at; [lia | apply ES | lia | cbn; lia | first [exact C | cbn [edenot]; unfold word_to_le_bytes; rewrite u64_lit by lia; exact C] ].
(* [comment removed for export] *)
Lemma auxv_kn_ok : forall (E : env) (M : bv 64 -> option (bv 8)) (av x16 x6 x11 x12 x23 rnd : Z),
  ev E 3 = wz av -> ev E 24 = wz x16 -> ev E 29 = wz x6 -> ev E 25 = wz x11 ->
  ev E 30 = wz x12 -> ev E 31 = wz x23 -> ev E 26 = wz rnd ->
  Mem.bytes_at rsegs M RAUXV_CELL (Mem.le8 (wz av)) ->
  auxv_words_ok M av x16 x6 x11 x12 x23 rnd ->
  0 <= av -> av + 464 <= 2^64 ->
  know_ok rsegs E M auxv_kn.
Proof.
  intros E M av x16 x6 x11 x12 x23 rnd E3 E24 E29 E25 E30 E31 E26 AC AW H0 H160.
  destruct AW as (Hlo & Hhi & AW).
  assert (ES : forall off, estart E (SA vAUXV off) = av + off).
  { intros off. apply estart_of; [cbn [edenot vAUXV]; rewrite E3; reflexivity | lia]. }
  assert (IT : IMG_TOP <= 2^32) by (unfold IMG_TOP; lia).
  unfold auxv_kn. cbv beta iota delta [AUXV_RSEQ] in AW |- *.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat match goal with H : exists _, _ |- _ => destruct H end.
  unfold wz, PH_ADDR, PH_ENT, PH_NUM, RAUXV_CELL in *.
  cbn [app].
  repeat (first
    [ apply know_ok_nil
    | apply know_ok_cons; [ first
        [ eapply kword8_of_bytes_at;
            [ first [ apply ES | apply estart_lit ]
            | cbn [edenot lit vAUXV vX16 vX6 vUID vX12 vX23 vRND];
              rewrite ?E3, ?E24, ?E29, ?E25, ?E30, ?E31, ?E26; rewrite ?Z.add_0_r; try unfold wz; eassumption ]
        | eapply kunk_of_bytes_at; [ apply ES | lia | lia | eassumption ] ] | ] ]).
Qed.


(* [comment removed for export] *)
Ltac kcell := first [ eapply lit_cell8; eassumption | eapply lit_cell; [eassumption | lia] ].
Ltac kn_split HK := unfold know_ok in HK; cbn [app] in HK;
  repeat match type of HK with Forall _ (_ :: _) => apply Forall_cons_iff in HK as [? HK] end.

End BRIDGE.
(* [comment removed for export] *)
