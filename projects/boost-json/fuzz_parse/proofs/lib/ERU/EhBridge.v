(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the CONFIG_RSEQ=true copy of this unit's EHU/EhBridge.v, generated: only the constants whose facts or premises name the auxv tail, over the vector with the AT_RSEQ pair (LPS 727298f3); every other name points at EHU/EhBridge.v. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr Exec TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require PropExec MState Mem Cells Step Frame.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatSim XStoreOk XAxSymExec3 XAxSymExec3Sound XSegRun EhRegs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require Import EhX_ubsan EhCut EhCut2 EhIfaceDefs EhIface.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU Require Import EhCut EhCut2 EhIfaceDefs.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU Require EhBridge.
Ltac2 kr_t_EhBridge () := KReplay.lz_vm "#$#$C47Corelib7Classes?Relation!s6)9Reflexive!sR.Program6Basics4flipC46Stdlib5Lists4!s+#8nil_cons!sa,4Init5Logic6eq_ind!sB88!sB(_r!s}+9micromega5Tauto5eKindI!sE;8GFormula00C4ELinuxProcessSemantics5Riscv7Prelude5bvmap!v.59Morphisms6Proper!sI?Krespectful_per_oblig!vl$_1!v?7:firstn_nilI89OSSVerify!t8#ofs:boost_json:fuzz_parse3lib2EH7XCatSim6msteps00C13~~~!smP3Lib4Exec!sk2K!sk`1!sk)!vF,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!vp#s2bv00I!yT19Datatypes6op!sL#!xm=?!s<2>!x}$!sE+>ms_svc_pending!tw,!t6:2!tX2!{.(2eq!tr#!tPZachine_result!u@\4!w]#K!tRi1!u~2!u\(3and01!yLa2!yL(C!{mZ:!sm(!#3W#!{o(!ugY=!ug*state00!t^P4RefU5RSegs5rsegs!{pM3!yU8!vw$0c9!vwOEHU8EhBridge6BRIDGE!v;*lib!t`3!zj0x01!yzZ7ms_r!ug#!tyO2EH6EhRegs4REGS6rshape!xv)!so^;!ud#_!st/!}t<3nat!}q5Peano2le00!x(G1C5!#8$(6ZArith6BinInt1Z6of_natC!#4u?7bv_wrapK!#5CC1!soA;bv_unsigned!ta<3eqb!t~=to!t~(!zI7not!s_<7eqb_neq!#7u=Z02!se<2le!zP:q!uk#!#=y3;Zify!#<k)and_morph!sOB7rew_iff!tT34Znat5Nat2Z9is_nonne!#8=<4list01!#9m;!sF(0K!tZ56VarMap1!z.$!sD>0!sD6=RingM!s4*7!#@i*!t567Env!sT#5PExpr01!sIE2!sI6!t?:!st7!#BN27!#C9;8B!sJ)!sH6:Z!t<+=Z!sT$Checke!#D/6!vJ)4f!#Dl#!sq?C!sq0_soun!|(>max!y3>7inj!yV$!zh77iff_sym!zBB5mkrel!tP<8max_spec!|8>t!#?N8or!#4[>1Z03!xw>3Pol!xJ8!xu15Psatz!yFF!sO)4!sOK6!sO6!x4.;!u{(!#8T#!#Da.!}18!tl7!|k,!u[7!sD,!vB7!{E36!xQB;!#3m(_rev!#6g<modulo!sF<9mod_small!#92AZ_to_bv!sLA@!sL)!#8l+!sU@4BvWf!#MKH6bv_eqb!#=CR;XAxSymExec33AX24ridx!#=@)!wHD!ym7!sJ3!x8G5!sJF8!~/Eapp!#8\<bool!}O/!sF8!#?f,!}o6!#LQ<!#@K#0!#4a=6inj_le!}=D3Op2!#EX3!tt.uni!#:r8!vM(4ki!#Iv#!sfA!#=_68!vi#Inst@!#A`$!zf#!s,#!#?0.!uk7!t:.!vP6!#Kk84True01!#<L5!#3q:!uh7!vW6!uo>!xM$!#>k2!t](5Fals!#E8#!t^L!#7HD!t^$5!~=AD!~g._in_range!sYA:bv_!#4`#us!#5(<eq_dec!ub26Specif7sum!{q(!#S+9x00!tQA5!#3p#!#DT8or!#HR4!{l(Z2!{n#id!s^<!}1?N00!#5/R@!#5/,Sound4AX2S7regs_ok!#58$!#O4c9reg!#8k(!#MAc2gr!tdj4regv!#TrX9XProp!vS#4get!t_)!#9Jb6sr_get!ssjedeno!ss*!#;a?3Sem!x_#!tK#K!#;^be!#I9#!tE*!zh*!#aw$7!s+#Def3nth!w8P3Lib5Frame3mkR!t*3!#g.:=eq_Tran!#RS$!#d3>?eq_p!#dY#!s,#xy!sR?Mt!sy#_co_!#fo#v_impl!#O5$ism!{@_<mkR_of_!#U\,I!wUb3env!#e>*!xIh!ss)!~qicase!#\`(!#4fh4fla!|Oka!|O/!tlh6estar!sy*!{gS3Mem2wa!sd)!#Oy;pow!sC=ad!#P[<>pow_po!#VN)!sN<:!sN#!sJB7compar!#CN6!#Ty17!u~T2Nd:and_elimF3!#7fb=!#]b(64_mo!#e_(!x\j!zJ#_u!}3i5sadd!}4+!#?y7!#D\$!#HJ<:!wZ(is!#my#!uYh5elenZ!#Lu(!uXi!#91)!y+S8!x?*3rdn!#;<@!#g?A@word_to_le_bytes!#pWC!#]HE3!z`]!uG,!#6sd!#5)$_!#3L)!wzc6kentry!w{+!ykh9!s{(!#ET*!#6#W3le8!se^8!xg$_!#9B*!xp<length!#_G2!#kT(t!u1Ymr!#46)!#|n59nth_error!t*X:!u#(_!v=,!$$Z7!#[T$fl!#VJA3inj!sg23Nat!#9]#!tlW<!w=*_!}{.!#Dr85skipn!sD;6!$$4$!#:><add_0!$*2,!w$.;!$$p(all2!}$d;k!#3T#intro!xC2!vq96!#Z=#!#n7+5!u/$8!yh$!vy#!v}*!#ftA!sI#!#Wc=7Inj_Z_Z!#4DR8XCat!}f#D!y^)N!#6#.!}#^5wr!||.!#7^W5wview!#5(j7!tZ`8store_ok!v*X>!v*$_!sj+!#8Ki!#=C#_li!#EWZ!#N@(st!#7?)!#[k7proj!#})Z<find_segment!sjK<MemImageType<seg_writabl!#OY,!#]|2neg!#yJ<9ltb!#o:#!#c/3!#Go+ltb!#BG;7reflec!$.}#!tO;andb!}W+4Bool!s*$=!s>#_true!#xF6!tM.e!#{Y=leb_!us4!$9w+!#rR.!tH,>!tH$fals!tIA!t+$g!#:xX7ro_add!#X})!t1;4of_N!$/3J!xl07S!yQ(00C6!tn,!tg96i!s\#s5UbsanA!s+$!z8*_0!#H7)!smc!#AO)!smb!$30)!smb!#MC)7!smP1M?loade!}O+!#86^7mem_in!#_](!#5)c=!yh)_!u#$!#4E=9!#i2#_ind!#8oj4!#Frn7know!#Fp+!#m`;!#qp/!#A(1Forall00!$BT7!sC(_!sf#!uvj!#QA*!t<56Ex!s2#!#sL.!tz9!#{`,!sG91!#Ut`!wj*!$(67f_equa!#zMA6bv!#B)#!#H:Wrdn_unfol!#IF)!|@Xwa_succ!si)3!t|(7tac!#;x$!u<(_hel!$IA,!#:02nat!$>f#!#vwB!$5F3!sH.8!sH#!tX$!#DcSStoreOk9!~[#grow!#3H)!#82V9seg!#EE(!seW8!se$ase!#<K<su!#<K<4to_N!#@lY?!#70)!u4#_a!#<2T!#B_$5wmon!#Jk)!siY7outsid!#h3)!#@4;prod!#}E4!#A_,e!#A_)!~d62I!#N],!t$28lis!zP$!#z#<!tJ$!~^U!#E{(iv!#sq)!w*Zmunch!#:Di;!w5)_de!}}*!tdS6MStateC!$/>)!$/A.!tsi>!ym$_of!}X0!#_m[7!|v#rom!tlj6z!#~3$!#Xf;7f!#9$#b!t8e!#PU#!#D.)!#tp:!$Y/#!#<V5in_map!$;{0!sa2seq!#afD4!t+76in_seq!$\f7!tD#!$\f;3!t^0!#u)4Diff!#tv$subr!#vD)!t56>!w+)_!s.(!uy;ap!uy)!#X9@eq!sL#!#R7din_!y5/!{qestatics_!xy/!s|d@!s|+!#QU)!s~i7u64!#U+,!#uMc!#;d$!ssh5a_off!#3QY4Step8rw_cell!#4>Z5C!sc#8!si$!#\O+!slY:!sl(siz!v=*!t\`w!v7[!sl(;!sl(!#__.!#gU6!}A#nil_r!$]BS!t5(4!t5#!#Q~)!$eAS!sj/!#6Q)!{VS;EhIfaceDefs6EHDEFS<EH_IMG_WORDS!s}m6eh_img!zn[TacX2wz!#pi(!vI_!#UF(!$^Ddkimg!#hK.!#iFe!#Q_$!yj#!syj<!sy*!#:]#!{0<!#Qy)map!v6e!$)g$!#64+!sxdD!#4V)_C8!}J(!#3t*!t)dA!#mZ$of!t#2!#n{7!vD)impl!x[mapp!#W@Bfs!$_*2!sC.sn!#SHP!$g|#BRMalloc_i!}]#_stmt:RSSP_GUARD!~TZ5EhCut3CUT6!|(#k!#sl)!sn]9!#471!{ve!sw+_eq!#S/P6BvBase=!#JD#!#qL)!t_d8!z>(!$5oj2e!#a4(!$>jh!#6)j9kwr!#wN/!swS7!#9G(3EHI5!~j#!$(LV!yr13!#4Ol<!x3(litva!$G#j9!sz+!u`d7vCANARY!sod8flags!~7]6!sp$24CUT29!sr$0!ss]!y(4!$)S)!sod!#hLV!uU3:global!vK.!#7Jf3me!#UKj=!#MH+!#<<l7!~F#!zq]!v_0!tn,!{genewh!z$i9pool_liv!#O+V!z+8!#t.)!vK_7!td$!z(X!#lF35!#97U!x*4!t^$!(()$!#uo(!svl!vN)!svl!#9@)!$4=?mo!$i\A?!#o2$!$j2,!$U+B3alu!sLE5alu64!(0=:!sN(5Instr!sP#op!$}lB6bv_su!$(U+!#nI*div:Zminus!ucIsub!uc+!tmN!$7\d6wz!#s<#!#@um!#}R)!#?3]!t`+!#3d`hdr!#Z1/!#HQ]!sq#!~p*!$4Ne!#O;$o!#YN(!#P4e!$Fl$!vV,!#4cU;!#4c*1!#>;Z!vO,4vHD!$]U)!sl_P2V!uHZ3Arr4u64!$+2[Arr:!sf#_sp!#<s+!($.<ul!$DN6mul!#jaD5!s`7!#3^.!#j].!$C:(!#uB+!$An6!#xg.!sF68sub_diag!(F6>ap!#mO7!#`6*!#jr77!$F*#_!$*a8!sB(all2!t#8!sE)!tE9!$IE)!sE#!up?!wN#!$D`A!sI#!#`ifeh_auxv_lis!y5)!$s6M!${K6!()^77!sOK5!#Z]d!$K[*!{^$nt!#yM(!}x^5vAUX!}yW!#YO<!sw#_CELL!#3eeX16!#:LdvX!ske4vUI!#[pd!uG#!#G$Z!sl02!#=[d4vRN!uH[!||67PH_AD!#9J[!#jb6PH_ENT!swqNUM!swXR!#Mw.!#3\#!#?Tk:!#XJ$eli!#RL(!#6]6?!#ed(cons!#{1g=cell_of_!tL$!uAj8kwr!u?.!svelit!#DP#!#C_j!sv*!$\a3!$>31repea!(HA<6shiftr!$nW<!sF(_0_!#:hg5zero!$Fj^!$]d+!#kF:!$S9,!#K{d<rdn!#nyr=!#\Q)!zq#!#X)Z!vz62b!xz)!#oJd!wl$!#|5.!}[j!vhr!x{,c!szl;!#dZ$!wb/!#Z5_!#=GZ!#:76eh_id!$/J)!$K:O!#Y?>!$#j(".
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemantics0dmachine_state79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~k65rsegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~ob6msteps79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~t16mstepst13evt07ms_regs89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH6EhRegs4REGS~~~~~~hi46rshape37Corelib4Init9Datatypeshmf4listhmf3nat37Corelib7Numbers7BinNumshp64Npos89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hr73envhr74expr35stdpp9bitvectorbdefinitionsigb2bv37Corelib5Lists7ListDefiie3nthhr74ELithr76edenot37Corelib4Init5Logicile3andile2eq37Corelib4Init5Peanoinf2le46Stdlib6ZArith6BinInt1Zip96of_natigb7Z_to_bvhmf4boolhmf5falseile1I3h5LinuxProcessSemantics5Riscv7Preludeitc6bv_eqbhr74ridxigb2BVigb4BvWfile2exile2or89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU8EhBridge6BRIDGE~~~~~~jie4regvitc5bvmap89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~jo57regs_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jtc3mkRhi42grhp61Zhr76adenothr75saddrjo56estartjo54flat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~kkf2wajo55elenZip92leip92ltip93powhr72SAhmf6optionhmf4Some0h0word_to_le_byteshr75KWordjo59kentry_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~kuc3rdnip93addkkf8bytes_atkkf3le8hr73KWrkkf5wr_atjtc3stkhmf4truekkf7ro_addrhr74KImgkkf7mem_invhr76kentryjo57know_okhmf3apphmf4conshmf3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~lr49mem_growsjtc5wmonohmf4pairhmf4prodjtc3ivljtc7outside36Stdlib5Lists4Listmia2Injtc5munchhmf4None05wviewiie3mapiie3seqjie6zrangejie6wview0mia7forallbile3notigbbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~mpe4cellmpe2C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~mu88rw_cells89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~nif9IMG_WORDS89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHUbEhIfaceDefs6EHDEFS~~~~~~nnccEH_IMG_WORDSnif6img_knnnc6eh_img3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasenu9dZ_to_le_byteshr74EVarhr72ev89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU7EhIface3EHI~~~~~~oj75cell1nif8flags_kn79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUh2RMalloc_iface_stmt~~~~~~ooeaRSSP_GUARD89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU6EhCut24CUT2~~~~~~ou79flags0_knou7aglobals_knoj75cell4oj75cell879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~pl62wzooe3memou7astatics_wrnif7newh_knou78PoolLiveou77pool_knoj79pool_liveoj75cell2ou78PoolIdleou7cPoolPristine3h5LinuxProcessSemantics5Riscv5Instrqg07ALU_ADD3h5LinuxProcessSemantics5Riscv3Semqif5alu64qg07ALU_SUBip93subnif3addnif6hdr_knoj79hdr_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~qoa4u64smia9nth_errorip93mulnif7auxv_knnncceh_auxv_listooeaRAUXV_CELLnnc5zeroshmf6lengthou7apool_statennc7eh_idle" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut.CUT. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhCut2.CUT2. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhIfaceDefs.EHDEFS. Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.ERU.EhIfaceDefs.EHDEFS. Import EHI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BRIDGE.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.EHU.EhBridge.BRIDGE.

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
