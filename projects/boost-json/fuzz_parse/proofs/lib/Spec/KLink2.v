(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafeP STree Malloc Prog KInv AllocTop VmKit MmNodes GapGrid KLink.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RelSpec RefNodes HeapCeil.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_KLink2 () := KReplay.lz_vm "#&,6C4ELinuxProcessSemantics?!s<22Fs4pathC47Corelib4Init5Logic8eq_ind_rC89OSSVerify6Proofs:boost_json:fuzz_parse3!sg#Spec6Malloc4aptrC13~~~I!sjT5STree5stree00!sl%!tv<trans!sD29Datatypes3fst!u;]o!u;+C46Stdlib5Lists4!s+#8nil_co!tL4!tj%6!vb%!wVN2Fs!sTK5State7PipeBuf!tk8map!tk&!sC57!sC#mapK!u/+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!wc;4prod!sF?list00!u872In!xEU4KInv3ehi!xB'!u1?;bv_unsignedC5!tP&6ZArith6BinInt1Z2le!wyQ;region_freeK!unA1K!ym72eq!s@4!s`32K!w8A1!u&Q:iv_overlap!|v<4negb!sD=andbI!uE;0!s@9or00K!s@;1!wY<3ad!wv=3ltb!sC<6ltb_geK!z,'9micromega6VarMap1!vy$!sD>3I!sD?0!sD6=RingM!s4'7Formula!uo#!sQ47Env!sT#5PExpr!tX8!sI23!~>G1K!tdL!sQ75Tauto8G!sJ'4!z:<6op!|g#!u/8!sl38C!sJ<B!sJ&!sH6:Z!u&+=Z!sT$CheckerC!w]<4f!#7J#!sq?C!sq0_sou!sX#!#8@9sym!zr<2!|-<8!}m#_ind!#5a<bool!{v4!sF31!sFB2!y#G3!}E85False!}b/!#8\3Z!~$:3and!{c8!w'-;!}B%!#7m#!#8@,!xl35eK!vD@unit!|K8!se%4kind!{XF3Op2!|L/!t581K!v%?!sDA2!#4P<pow!#9IQiv_subtract!#:q@D!#:q,_in_range!sYA:bv_modulus!#;K=t!uE=max!t0A7Z_to_bv!si=sub!#>A69in_app_or!sa<8ltb_spec!yH<8BoolSpec00!sl<4of_N!zQ6;ZifyClasses!#Ct#ff!#E|8iff_refl!sjB3inj!sIB9and_morph!sOB7rew!t_$!v9<min!v9$!x%>in!sC<>pow_pos_nonneg!sN<:!sN#!sJB7compar!#AF<3na!#<h8!}l15Psatz!#=9A!#:bF3!#<ID4!~=@!sg?3P!#7O$!uCI4!tYE1!sIE7!#GRO3Lib6M!#3b#<!#35'lit!#NG7!wl-snd!z,>ax!z,%!zvA5mkapp!|{C!sK$2!sqErel!w/K6!sO6!#:>:!#@PF5!sJF6!#<;=N!#:e7!t`;!#:qI!sMJ5!vx68!vx#Inst7Inj_Z_Z!#>%74True!#O8=:!~I%ison!#@[=!~N$1!#TeVSafeP4etwf!zk&!sj\assn!{W'!#<|N=maps!#<~+!#XJTKLink@!sl0_I!tY&!#MY9x00c!u_U!t7$2?!#>|,_!#Ry+!u-Z8frame_ok!sm[!#TQ#6ld_br!sj&K!sjY9brk_phase03!xz]!#[M#;round_up_pg!uN\Prog>dec_mmap_fixed!w1\Monad4msys!t]`9neg_errno!sm`6ps!wt,!yO[<ev_step_post!{S8!#PW40!#PyC1I!t]Z3KLB!#bX'!sj[BUD!|\bkb!{%%!#47V8m_v!z&#!#b2Q6vm!x<$!s[P<vm_start!saU9!|q$_top!#`^[l!z~W!#@s#Decode8!}I$len!#4c_9!#4c$reg!smdgroups!sm`8ld_metas!z@e!xG$!sma7kb_minv!sl[7MmNodes5m!sl_!tZ%6kb!z+$!#4]`!zt+_l!v:'!#b5;!#SF#o!t9[C!#9t,_al!#h^$!vfb2wz!#3Y&!#Co39SatDivModCZ_mod!#N|%!#O'Cdi!#V$#!#R`73no!#Uy=di!#US<=!tP#pos_b!#_]#!sM@!tt#!sM15!#F9$PreO!s/#1Z;!tt#0_r_ext!sL>!st#!sL'!#3[R9LiaTuning9zify_don!#7f%!#IFM3!#TD=ul!#[fQvm_reserved!zC[;kb!sj#v!|H,!#EG[A!#oh,_above!zI2!#tV-ex!s2#!#[E7>!sB&_!s-%!vO=leb!#vUQvm_!#<##!~0<leb_le!{Q85proj2!#g&7!#d6#!#r4:x!#qLR<!#x/%tains!~i]4pgup!z^<!#S177K!{zS5!t9%node0:!#4kb6mmsafe!smcDn!#EF#!#H]+!#^m#!s{b=!su%x_model!{?'!xE95Riscv7Prelude6bv_eqb!#3uS!#@R&!#I>#_o!u8&!#MKU!#J0#!v#%ans!#MKW!t^-<!t^'!#\#,7!sqN7Re!#em#;!v5%!#dm$!t``5no_cc!xO[!v=$5ps_fa!sidso!y/A!#IF9vm_limi!#VR[Cvm_only_with!#J:&!uBZ!sx%>went_In!#<d$!#F/`4!sr#!t]a7kb_ha!#Bn'!#MDR!sa#!#;h\5kb_!#\d\!uy%vm!sh]!uy,na!slgresv!uD`7ld!ska!|=$rban!#Fm&!#<#'!#>D$7!s+#Def3map!u`[8!yI#ceil!#4QU8HeapCeil5!sh/!tWZ:!#B?&!x&c9!so'n!vT3!#Xr2length!#b12Peano2le00!tP_!#Qxfbrk_disj!v-a!xP#!#Rg-!#GaSnoac!s;#!tO[;kb!u=#tinc!#pPCappI!#Fi55NoDup!wXa!#WAe4wcov!#3`dliv!#]gW=!#;G#ve_byte!wU\6ltotal!ykecou!#:Ob6l!skf8!vq$mi!#;=W<vm!#G$$bas!$?pR!#?,-!u2ZB!sj-!#?x0!#N9;of_na!#VK34Znat5Nat2Z9i!$#{'!vp[ehi_pai!$I1%!#RH\!#q{0!#pk]8AllocTopA!#\f+same_s!#]^&5!#y?'!#y7%6PosDef3Pos!#V1#!#R};opp!sC<4land!t&A!$Ad>7po!uv$!wO[D!#tJ-!#RI'!|<`F!#vW2_intro!}9bsum_g!#gg]!sm-m!sm,!}EP:!#5q+K!tNZ!#o[#1!u:[!#|#%9mspec_!#tJ]!#vt%D!#TH,answer!#yM^Prog4ps_m!tdb=is!#v1$_for!ss'!#=f;or!#]Q+4Bool!s'$:orb_true_!$9p<3eq!$K/<8!#Rp'!}0<sub_0!$YvV!#I2%!$=q#!x1c>!x1$!x'd!st&6!wA%!xq\!#pl#set!#o~`!sm$:!sm#!#Fbe9!{?e!t]$event!#|%,!}tcre!soc:!so%bin!$$ua1M!sfa5m!tRZ!#\%,=!$'>'n!#l;'!sr[8!sr'!#4y_7!$%e%!{+e!#zQf!sn&ph!wqa4m!z6+K!#3'Z2ev02!whZ!#ht$5n!vw,!$<rE7!$AtD5!#jwJ5K!#M#PSyscallEffect!$_|Svm_init_sp!tEQ6VmMaps!t>#!#o057f_equal!#3@[5!#3@#!#4,\!$k@$PGSZ!ya[!{;%!$8N+4!t[b9PROT_NONE!|u`5MAPFX!si%I!#3=X6P!x0$!$4H&!slZ!#m<,0!w&\!so2!}j'7!soPcfg=hunspell_scfg!~X[ITree4re!#Mf&I!{xP5Model!#Z>V!#BL$LEN_MAX!#6<[!#VK$BUDCAP!u6W!~0'!$HF<!$Gx#0!#S|=6inj_le!u3[8RESV!uz_7GapGrid6GRID_J!{FV!$7w3!{F-I!xGY4mled!sjb!#46,!$?6a@!#V:$ceiling!$3~+!#5,Z=!sv0!|FX!#F6#!$q\9!$Oq$1!sxQ7MemCopy00!#3PTE!#3P'!uO%forc!$6%\!x'$3wwZ!#4AY!zI'CEIL_MIN!smhA!#95[!#NB&ms!#97-C!#8FX;MAP_FIXED_!v='!xp79!$mI#!%%;#!#Rh?!$ew?7reflec!$~E9:in_!~J#!$eQ#!sE59in_or_ap!$E3Z8g_rem!$4R+!~b^qui!#GD\!#3Q22!#3Q`9!sl$_!$B&'!t_e1!sok5!uPaA!$IB&_!$Am&!tgV!$4a2;!}sa:!#PA#un!#PC'K!soZ9!#Zt#!#BN-!#M~_3!w1a@!w1+!$Ela!su%C!su+of!$Ffj@!$82%!wB$!$8-f<!sq&!$8,E!#Nt9!sd#!#3Y$!#nV[>!#4C&_sp!$k],!#5U4!%7M#!$jm-!#5q-app_assoc!$B;7!#zP#!t5'1!sIE2!#AUY6pwdisj!#ARb9!sm%!$dW'!#7OY5e!$$?+!we\;!#6[$!#8>,!uL[;vmwf!#9w0!wO66filt!%-b,!xS/!sA%!v5#!zdJ2Fs9!$<a%eq!u-\!~%+g!$Li<!$uf/!$v/C2!$H;<1!#8z[!#q%+!w'2!t903Nat3!#u\]:lbrk!$%'%!x}`=!#tU&!%Bv$!sr`<!sr+!~~#!yr1!wI,!$vM-;!%#8%_rev!tD[8!v%$cnt!w/=add!#Co7!$4\$!t|$!#Q|<7inj!#zOX!#;]%@!#8-%!#lF2!#L3P!sh#has!#QuZ!#=},!#5m&!ui=8!ui%c!%'N+5!sI$8!$7o#!vp#!vt'!vUB!w?$!u]O9TASK_SIZE!#<>\=!sj+_v!$1K'!#5:6!#I^$!#7}Y9bump!#s=#!#;rA!$[6R!t1%Prog?!#Cj#protect_rw!w~9!#x-+mod_!$']>7add!$_5$!wYPm_vm_lazy!s^QA!s^$materialized!$A@PRef!x=$H!ux+budget_ok!$&~/6!tcI3Sys2Mm8M!st&B!s}5!#IF_<!#6:U!sj,6eff!#zf]!{a'>!uK+!#D{-!su\B!#Fi%!s{'!#Fk'!#K3e1!|E=B!#D4$ap!#D8'!{:=6eq_d!#UA36!u<#if7sum!%Ez$!#BW[=nodup!#Uf$n!#CLb=m!$;\%_bump!#=Oemlen!srf;!#;O%!sp_!#;3%!|e,!#;51!#Pd_!#p|b7!#p|#RW!z2'!#j#OENOMEM!tJ\!sf#SYS!u8b5TWO6!u}\!#:P$!$+@%re!wXf1!z0a:ev_brk0!y5Y!#6z29!v6\Prog!$%%&_!$]Q]!$$:%up!%0Ocg!#OGW!#6b,7dec!%/bd>!$xp-ge!ssa?!x\%_grow1!#G#+!#@6;eqb_n!#P9\!t=/2!$5^]!#J~%ev!%5qa!{X+!#Qy#!t^'!#9<[@!sp'!#{p$!svd<!sv#!#Ki$!srd>!sr#!#8P&!#8Ig5!sjf6!xpecostb!smi!v4&!#O0Z7!{A#!#O--!t]T!#y~$MAPF!tXV!vz30!#4\`8!#4\%0!tYb<undef_rea!%I=#!wp\!%x4#9!%x4#_!$?N]!$0$$memb!#3>\!$4j%<!$A+$conseq!xa`8c!uM$!$G[^!t`$?!t`%pointwis!#8ka6t!%0-$!xnZ!#e:$cpath!$3@]!sk-!#@ha8BUD_mon!$UUbans!$WE#!sm%!#8'_!#O'#!$;G+!v=a!#s'[!&%w/1!slh!tZ&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14prodk14boolk14listk14true37Corelib4Init5Logicn52eq3h5LinuxProcessSemanticsfLinuxProcessSem5Stateoebregion_free79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~sa3ehi36Stdlib5Lists4Listhgc2In46Stdlib6ZArith6BinInt1Zhi52lehfbbv_unsigned01Zhi53addhi53powoebiv_subtractoedmaps_subtract79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~ho06PStaten53andoe5Modelsa5MAPFX79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~htc5EMmaphtc4PGSZhtc9PROT_NONEsa7BPGuardsa9brk_phasesa6ld_brksa4mled79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5KLink~~~~~~ile3BUDile3KLBilecev_step_postile8frame_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MSafeP~~~~~~is55mspechtcbround_up_pg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec7MmNodes~~~~~~jhb6mmsafeho07ev_stepho06ps_brkk13appk14pairn52exk14consk13fst37Corelib5Lists7ListDefjp83mapsa8g_removehgc5NoDupoe8m_vmmapsoe6vm_brkoecvm_start_brksa9ld_brkregk16optionsa9brk_quietile9phase_invhtc7EMunmapn52orsa9ld_groupssa9bump_metahtc9EMprotecthtc7PROT_RWhi53mulsa8ld_metassa9event_preile8ev_costbile8ev_costkhtc2ev" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Notation mspec := (MSafeP.mspec mmsafe).
Notation MP := (Monad.M PState).
Ltac kb_open K :=
  pose proof (kb_minv _ _ _ K) as Kminv; pose proof (kb_halt _ _ _ K) as Khalt; pose proof (kb_wf _ _ _ K) as Kwf; pose proof (kb_nawf _ _ _ K) as Knwf;
  pose proof (kb_resv _ _ _ K) as Kresv; pose proof (kb_top _ _ _ K) as Ktop; pose proof (kb_hceil _ _ _ K) as Khc; pose proof (kb_resv_top _ _ _ K) as Krtop; pose proof (kb_resv_wf _ _ _ K) as Krwf; pose proof (kb_resv_n _ _ _ K) as Krn;
  pose proof (kb_start _ _ _ K) as Kstart;
  pose proof (kb_groups _ _ _ K) as Kgrp; pose proof (kb_metas _ _ _ K) as Kmet; pose proof (kb_distinct _ _ _ K) as Kdis;
  pose proof (kb_brkreg _ _ _ K) as Kbreg; pose proof (kb_phase _ _ _ K) as Kph;
  pose proof (kb_live _ _ _ K) as Klive; pose proof (kb_count _ _ _ K) as Kcnt; pose proof (kb_limit _ _ _ K) as Klim;
  pose proof (kb_vdso_in _ _ _ K) as Kvdi; pose proof (kb_vdso_disj _ _ _ K) as Kvdd;
  pose proof (kb_rdr _ _ _ K) as Krdr.

Section HC.
Context {HC : HeapCeil}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_above : ltac2:(zQ "c1!h9!jc!l9!m0!m7!me!o9!rc!hg6!hhf!hjd!hk3&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$4~0>2aw@1$1@1$0#k0>2nw@1$1@1$0#k0>0>1e~0>0@3$9~0^1^4@2$a@1$8^2@2$b@1$0#k0^4@3$6$3@3$7^4^3^2$5").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink2 ()) ["HC"] "##:1p'0h01eh12awh22nwh31Hh41ah51li001lh64mapsh72H0h84__x1h94__x2h:4__x3h;1bi011bh<1xh=1yh>3He'h?2IHh@7__arithhA4__ffhB8__varmaphC5__withD2e'hE2szi022Ini032l'i041pp;1p;2p;3p;4p;7p;8p;6p;5p10000p4p70g000`R!s2$10R1p8p1001>!sB$R2p1002B!sC%p8P!s6$3H!sS&3p8P2P1!s>+fp4p7210R2!sl%4C!sl%4P3p8P4!sP$4P!sC&5G!sl&2g005dR4!s{3p1006@!sh$!s5+n!s507d!t?+P!s]08Ap4p7311!sQ$g008]j13Tg009Bj1\!s/$`j1PTg00:CR1j2H!s1$cR2j1@Tg00;Cj34!s/$Zj1>Tg00<[j20Tg00=Ej22!s/$aj38Tg00>[j1BTg00?;j2?!s/$Uj3DTg00@5j4C!s/$Uj4ATg00ANj1<!s/$lj29Tg00BJj35!s/$dj2VTg00C>j3U!s/$Xj27Tg00D5j26!s/$Rj2OTg00E2j2=!s/$Pj4L!s/$nj1KTg00FLj1ITg00G7j2:!s/$Zj3JTg00H=j1G!s/$bj4MTg00IMj7NTg00J1j1F!s/$Sj8QTg00K7j2R!s/$Yj2ETg00LEj3S!s/$dj4TTg00MVj4[TP4j6ZTg00N2j3YTP0j6W!s5$Lj5X!s/$nR0f0R4g00ONR335p=1g00OnR59504p=;g00PNR6#3R7#3!s$+\R8#PR9/H9R:#@R;P:f3R<94:4f1R=#>108<R>'2R?[^0:f2R@=8<=#1[^29^19RAX6;%B:94:4P!sI$1?03RBW3X29X19P1P9P9f5R1f4RC5D:RD!sQ,A8D@!sq,\A^5;P4!sV$6RDP1CCRE=D:CRF!sY,P0P3P<P@f7R?PDCA#</94#1X;0P4PEA5:EEp-0RG^5;^4:P2P:PGP4g00Q3A5:=<PCP<P4O2'Vn101!}[$020020!s4$3X5;X4:p?1001102PEPCO21?:E3UO2%>E108@'2P0108?RE108D'7,6>R>P5g00QPRGg00Qn16=4#;12=@R2[124=16@=#;[RH16<@#;\21O=4P4n200!tR%012!s-%0X=GW<PH^=G^<GP4108CRHf8R2,08RI/7EREg00RIRJ#B%@JPG1=G@P=1=G<CL%KG%IGRJg00S5RKg00STRLPLg00T4RMPJPKPLPLPMPG1:G61:G75JGg00TT%G6,:GCMg00U;FNR6%FLP6GQ1RJMP4P@PB1E4@#1dg00U[=SG=CTbAbBbCX8GX9GX:G174=/2@17=@/2<[^8G^9G^:!u<%1RGPIf9,08R8P@O4b@O3b7C[A505>P0P517GH,68,94#</93!xC%B16HEP4EZb7b3P@P=PDP1!xe%3#1eA8C@=P<P@P=A4:41!sH$9P9P2P?CC=5:=A4:=D;Y4O2W>XD:O3EWA8F@=#1e!zb'X?AX6;XE9X09P=P4O2!w^$104010121!y1$1X4:P4DXW6o"). Qed.

Lemma iv_subtract_ehi : ltac2:(zQ "b1!h9!jc!hjd!hk3!l9!hl1!hl4!hlb!hm2!hg6!hhf&@2$4@1$1@1$0#k0@1$1@1$0#k0>1a@1$1@1$0#k0>2sz@1$1@1$0#k0>2lo$5>2hi$5>1e~0>0@2$2@2$6@2$3@1$0#k0^5@2$3@1$0#k0^4@2$7+2+k0>0@2$2Z^4>0@2$2^4@2$7+2+k0>0@3$a~0^4@4$8^8^7^6^5@2$2@1$9^5@2$6@2$3@1$0#k0^9@2$3@1$0#k0^8").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink2 ()) ["HC"] "##^+p'0h02H2h16__sat4h24__x1h34__x2h44__x3h53Hinh64__p1h74__x4h87__arithh94__ffh:!si%3h;8__varmaph<5__with=2z2h>2H1h?1xh@1zhA2HahB1bi001bhC2b0hD1ehE1HhF2H0hG3HhihH3HlohI3HwfhJ1ahK2hihL2lohM1mhN1nhO2szhP1yp%0p&0p;1p;2p;4p;3p;5p;6p;<p;Bp;7p;8g008]j1LTg009Bk10I!s0$`k10;Tg00:Ck200Tg00<[j21Tg00V9j1p!s/$WR0j2XTg00=Ej23Tg00W4j4~Tg00;Cj35!s8$nj2xTg00Xak10HTg00YJR1j2!s|$Qnj2=!t7$cj1oTg00D5j2!tI$>[j1lTg00CXj22!s^$fj2<Tg00ZCj27!s/$ij24Tg00[Fk50!s9$BdS00j2E!s<$dj2eTg00\FS01j3d!sG$Jj3BTg00@5j4W!sD$jR2j1bTg00?;j2PTg00]Hj3a!s/$nj1yTg00^Lj4w!s/$oj6tTg00_Xj4sTg00`?k20F!s0$aj2rTg00a>k20!tS$afk30DTg00bJk20C!s0$kj1!v%$cJj2mTg00E2j2`Tg00d3k10A!s9$Pj4M!s/$nk10@Tg00FLk10?!sM$Qk60>Tg00G7j2OTg00H=j1kTg00e5j3ZTg00J1k10:!sK$Zj3STg00K7k209!s0$Yk208Tg00LEk306!s0$dk40!w}$eXk10!vy$f6k20!xK$fWj3gTg00g@j2f!s/$ck30!wb$hFj2]Tg000`j6\Tg003fj3hTg00iQj3iTg005dj6j!s8$nk20!yc$?Uj3N!yF$Zj1}Tg00jPm<0!xT$k5mB0!y3$k[l<|Tg00l@j3n!s/$ij2Y!uk$bj4JTg00IMj7QTg00mUj7qTg00n9j7{!u}$Sj8zTf2R3f1R4'2f0R5'3p=?g00U[R6/35p=:1445,r3p=>f6R7f5R8f4R9f3R:1734CW;N5p=A%}4!sU$CP9P:P31745CWp=Rg00QPR;/P5p=Fg00n]R<P;!s$$2P2P8!sU%P4P5N<0<p=v!sC&!s$%0P5P4P3P0P:P9P8P7f7R0f8R2f9R=NB0=p>0G!sP$1P0P1P7!sw/M<|p=uAB;45,=3p=61m;5p=GAn;45p=9g00RIR1g00o;R>,Y4;N5p>0BP;P4g00ogR?P5CJp=TP:g00S5R@g00STRAPAg00T4RB!t7$@PAPAPBP5g00U;RCFQFqp=V!sm&TTRD!sm%KP3!sR+;P4P!t+$PCFQp=UP:!sA+!sK,4PCFQP5Fqp=@!s=05F{p=[!su2D!su,_!su04P5Gzp=81Y3>1Y4>=N155N1p=^An;34/Y!s8$p=I!sw1g010NR>!s|,D!t5$!s7$p=cg00PNR>#LRC#LRD#L!s$%R?$0IRE$0;RF200FFRG11E911E:%pCRH%p?R?'XRI3?%::S0213:IP0!x$%C~95G:1xE2RJ11E2RK#:&0HE,0K'=RKPJPKPGg00NnRK%oGRJf:RL,1ERM/;2PGPFPFPLPE11E=RN?>2M%lGROFAPOn010!s#$20000RPPKPJ12MNRN,;0!s`%1<M0RQ,7EPE14NQP!s^7QP7P3I07A5G7PA5G7Q'EQ00PKPJf;RQ,1ERP/;=!tY&QPEA>M=P!sq795G!s]$12PMRM,!u5'1<P2RR!tS&MR!s`;f<RR!un%2PRS,C2P5!ss$;ML!tJ&RPEA>PLM!sh:2f=RP,1ERT/eQ10TQ13QT1;TQ3df>RU,1ERV/;RPKQ01f?RW,1ERX/0P13PXPKPJP4!t6%fARYPEf@RZ,1ER[11EYR\7>WPOFAR]!tG6PfBR^,1ER_/2\S03,CUS04]5P410[UA5GP]Q00!u9$^PEA>\Z_DR=BGUA5GUOS05fCR],1ER`/2_S06,CWS07P5!sX$]PEA>_Y`!sX$W!tp&DRa11EaRb9>`^S08,7ERcCWRdfERe,1ERf/2bRg,C5XDGS09P;Q08A?f5gX@;%:`Rh%bERi,XHRj,0`Rk'=10`I,=hRlPhPkPhP5X?;RkP?O1Rm,XHRn,0`p-0Ro/PhABohhe9ahhPk1045#yXP;X?;RhP`P`%F`PjPnPk!s$$;P;g01151X45Cw#FXM;XN;PHPH%FHPiPmPkPk%b5#FX?<PEP?%F?EvN:0GR<GuEtPLCsRmPl%:fRi10fjRp'=10fI,=iRqPiPpPi10fn1PoiABoiie9aii!u9$fPf%Ff!tZ$!sq%RCsR<PqfF,1ERn,4aRj-0FfS0:10fj1rfjRh;6f13jf?6hj'ES0;fGS0<,1ES0=9>neReP;20EH?Rh106HRj%:?106I[Rk[Ri%:HRpg011YRrB0DH?4UWAR?%:I\r^ApRpP4g012520C6H'PPjeO1RjPkg012[Rr#HRs#HRt#GS0>%Gs1m;rRr'9Rs'9S0?%l1Ru+0B%o1R1P;P;1`;9S0@P3&0A;S0ACMP41`;:S0BCMS0C&0@;Rv&0?;RwPwPw!#5a'7J0>S0DPw1O;CR@%k>,O;Rx'TCVPw!s<$DRD1O;>Ry5Z;Rz/KxAUw@zC@5[w&0:ARAAS;y@RzAS;yx5_wC8209wBRBP5P3g00ONR{,PK20853=BK{dB06;64H05R{b9b;b<X2;X3;X4;X7;X6oA694314:5R|/33?64|'E1243R|124:'3[^2;^3;^4;^7;^6oP5fK,1ER}fJS0EfL,1ER~'4'0S0FQ0EP}P9P~P8O6b8b1b:b1b=b0b0b011EcQ08PmPlP<PqQ0:Q0;PeP;PhPiP?PpPjPk&04>-03;S0;%HtRt#HR>#GRe5g;Rc%H>S0:#GR>Q0>/9rS0>,9eS0GQ0G%Gt/9rRt,9c;^u3I7IsP1Q0CPvPwPwQ!w:$Tyx!w-%AZ;D@S0C/KxQ0C9Uwy!w#$PA!ws$w1f;6R6/Kx1f;H>02;ERH9DwxC@PAPwADw@D!sQ%1K6yADwyHC@S0CC8C8C8PBP!w/<5314:4RD!w/$5D'EQ0210:I'=RD10:8PD[[!w65Q!vw'~P9P8P0PQO8!v{3']E\AhFFd,1EAi!s-%12b`RD3?e1CdDePZP5EjW0P5O1A5GWOg00Q3Rd1CYgP5!#6Z'0!sH%S08n20!s;'2110!s3&W5W>P5O113U[A5GPOPdQ07!sg05Rd!sJ%n2002!s=&1!sk/P3O1bCbBW5P5O1!#9d$=S!#<%'=R=!#:T%S=!#9j:12TMRM,eL10LM13ML1;LM3d12VT,;QPKQ0112XVRV,0R13VR!#9_-1<\URJ!t1%2\[/4JPOFARJ!t66PQ!#9G%2[XR[,0PA5GPJ!#9L%1<_WR_!sn$Q03/4!#9T%Q05Q!#9=&1<`ZR`!sI&6/4!#9E/1<bYRb,7ERY14DbRG,7ERWCWR`Q09P;Pb1<f^Rf,4g,7E,1E=?5gX@;P;PG!#9J&!|\'201n]Rf10n]1<n]Rg;6]13]n?6gn'ERgQ0=/<aRa!||1PuP1P;1`;3RnP4Q0BCMPvAS;@xR]=Z;y9S;y=_w]!{:614|5=?5|!zl+P5!z`%O3!~W6W!tv'PfPgP!tT2Q0>,9cRc19>cAIesu3^9IetP1P;PnP4P;Q0@P:Q0ACMCMRn!~0%Pw%kC,O;RC,cyAUwxCC@!~F+xyCV!~-/K6@ADw@HC@Rs!}y&Cz!sD%AZ;zxRz,K6ADwzHC@!}|B105:?63:A6935'E%:3103I'=Rz123:,0812:9R6/48Rx#:10xI'=!~37fIRx/3~RcPxP9!vX$!~8:,]GE\11EY!vaA;=g;>19er'9ReQ0:#H#G/9eQ0?=I>!vp$>tP1P!v\+1c@CAUwy!vU/y@!vU,!vF+]!s/$_w]HPAQ!#5;&!v?@4:?65:A6954'E1086A?98I%:9109!v+$\z!v-5PcPx!#59'7PQQ0<O9!v&5b!#5=$`!#5=%`,1E;?De1C`!#580Q!#4nD[PP!#4VPn211!sw11000b51C7NebFbEW5WGWHWIWDXK;XL;XOFWJo"). Qed.

Lemma maps_subtract_ehi : ltac2:(zQ "a1!h9!jc!l9!hjd!hlb!hl1!hg6!hhf!m7!hn0&@2$2@1$1@1$0#k0@1$1@1$0#k0>4maps@1$8~0>2lo$5>2hi$5>1e~0>0>2e0~0>0@3$7~0^1^5@2$3@1$6^2@2$4+2+k0>0@2$3Z^4>0@2$3^4@2$4+2+k0>0@3$7~0^4@3$9^7^6^5@2$3@1$6^5@2$4+2+k0").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink2 ()) ["HC"] "##:Yp'0h02e0h11Hh22Hah36__sat3h44__x1h54__x2h64__x3h72H0h82H1h93Hhih:3Hinh;3Hloh<3Hwfh=1Wh>7__arithh?4__ffh@!s{%2hA8__varmaphB5__withC1ahD1ehE2hihF2lohG4mapshH2szhI1xi001xi011bi021pp;1p;2p;3p;5p;4p;9p;7p;8p1001>p4p70R0p1013:p4p7210R1p8P!s9$4!sF$10R0p!sV$4C!sV%2P1p8P2P0p8g008]j13Tg009Bj1e!s/$`j1VTg00:CR0j2K!s1$cj1GTg00;Cj31!s/$Zj12Tg00V9j1D!s/$Wj2RTg00=Ej20Tg015Bj3JTg016>j5ITg003fj39Tg00iQj37Tg00W4j44Tg00QnR2j28Tg017MR1j2[Tg00@5j45!s:$gl9XTg00<[j26Tg00CXj2>Tg00a>j2WTg00YJj2E!s8$fj3UTg00bJj2TTg00?;j2C!s8$kj1@Tg00cJj2:Tg00l@j3B!s/$ij2OTg00>[j1N!s\$Uj3LTg00E2j2ATg00d3j1M!s8$Pj4;!s/$nj1PTg00FLj1QTg00G7j2=Tg00H=j1H!s8$Zj3STg00J1j1dTg00g@j2c!s/$cj3bTg00K7j2`!s/$Yj2_Tg00BJj3\Tg00LEj3Z!s/$dj4]!t$$bj4^Tg00IMj7Y!t$$Sj8a!vf$PR3f1R4g00TTf0R5C^p=?P4g00S5R6g00STR7P7g00T4R8P5g00U;FYp=<f3R9P6P7P7P8f2R6P4P5Gap=Fg00PNR:#3R;#3R<#3!s$%R=#eR>#VR?/K?R@#Gf4RA91@5%24%D;RB%D=R='RRC'0[^0@g00U[RD/09109Cf6REf5RF;JA91@9f7RGPEPFPAP5DIf8RH91@5A9??5RIA7??5RJPGPEC491@F'8X0@,[@P1P@f9R191@5PIPJPHPG!sH$E!sH$%2E/0CP5P0P?P?f<R0!sO'f;RJf:RI!sS$1'8%2I/0C[P5P?P?P4P5C5RIf?R151@A9??!tQ$If>RIf=RH!s\$0'8P2!sU$6P4C5R2f@RK!sU&2A7??2P1P!t/%H!t,%!t+&AP9C5fBRI51@!s7$FPAC5RH99??A7??HPIfA!s^$KPK!sG$EPFC5RHP4O2%2H/0CPGPEfDfCPIP5PKP1P4M9X%2I16>G16>E'>'01WB=1EDBRE10D=1EDC[RG[10DBRIg011YR1AUB=4UW210DC\1^2IP4g01251TDB'CPEeO1PGg00RIRGg012[RE#@RI#@,:31:3I1:3E5B35B3g00o;'O%NG3L%GGP3P31A36P9%M3RGC;P4!s7$9P9PGC;C;%P3%Q3RG1=3:R:1=3<%H;,=35S3R;'?,<G%d7R7PG1c3B=b3>RB,?;,<GP71?:B,<GCFCF1`G8P5P6g00NnRGg00ONR8'C1_56=\G8dAZ3D4C]b?bAbBX43X53X631>46,051>69/0C106C[[^43^53^63P516>J16>0fG#2PAPFO5b>b3b@b3b1b=W8W7P4P5O2n20010!s#$12!s/&W1XH?XC?!sH-102!sH%101101XI@!se7!s0%b0W:W9W;W<XD@XE3XF3WGo"). Qed.

(* THE SHAPE [ev_mprotect_ok] AND [ev_mmap_fixed_ok] USE.  The [bjhl_vdso_gate_*]
   lemmas below go through "the range is APART from every reserved entry", which
   nothing in [KLB] supplies for a heap page on its own: [kb_resv_top] bounds
   the ledger but does not separate an entry from a meta.  The route
   that works goes through the MAPPING instead: the page sits inside
   [went b (mmap_len l)], which [kb_metas] already puts in [vm_maps], so a range
   inside a mapping that misses every reserved entry misses the vDSO pair, which
   is in that ledger.
   PROVENANCE, cited BY BRANCH, read per hunk with git show on the branch below:
     a donor tree
       projects/openssl/pem/proofs/lib/Spec/KStep.v:139-149
         -> region_free_inside, statement and proof
   pem uses it at Spec/KStep.v:1482-1485 to discharge EXACTLY this obligation,
   with the same shape this tree needs ([aw], [nw], [went b nb] and the mapping
   membership that [kb_metas] yields).  It is a plain list lemma with no harness
   name, so it ports as hunks; the donor carries no address and no constant, so
   none was taken.
   USED TWICE below ([ev_mmap_fixed_ok]'s [Hrf] and, through
   [bjhl_vdso_gate_apart], [ev_mprotect_ok]'s eighth conjunct).  pem closes the
   same obligation with
   [kl_vdso : forall r, In r (vm_reserved h) -> forall e, In e (vm_maps h) ->
   edisj e r] (its Spec/KInv.v:214) and the vDSO inclusion carried in its
   TREE-LOCAL [minv] (its Lib/Nodes.v:524, projected by [minv_vdso]).  This tree
   carries both in [KLB] instead ([kb_vdso_disj] and [kb_vdso_in], Spec/KLink.v),
   because its [kb_minv] is LPS's [mminv] and no lane here owns that definition.
   MOVED from just above [ev_mprotect_ok] to here, unchanged, so that
   [ev_mmap_fixed_ok] can use it too. *)
Lemma bjhl_region_free_inside : forall l (lo n : word) e,
  (forall r, In r l -> edisj e r) ->
  elo e <= bv_unsigned lo -> bv_unsigned lo + bv_unsigned n <= ehi e ->
  region_free l lo n = true.
Proof.
  induction l as [|[a s] l IH]; intros lo n e H Hl Hh; [reflexivity|]. cbn [region_free].
  rewrite (IH lo n e (fun r Hr => H r (or_intror Hr)) Hl Hh), andb_true_r.
  pose proof (H (a, s) (or_introl eq_refl)) as D. unfold edisj, elo, ehi in *. cbn [fst snd] in D.
  unfold iv_overlap. apply negb_true_iff. apply andb_false_iff. destruct D as [D|D].
  - right. apply Z.ltb_ge. lia.
  - left. apply Z.ltb_ge. lia.
Qed.

Lemma ev_mmap_fixed_ok : ltac2:(zQ "h70!hl1!hrc!hs6!o9!hsc!ht4!iha!ii3!iib!hjd!ij8!ik2!ike!il7!ipb!iq2!iq9!ir9!jg3!jgc!jla!jm4!jmf>1L$d>1G>0$1>0$4P>2s0$1>3cur$0>2cb$0>2ck$0>0@1$h1^5>0@3$3$b@1$c^7@1$a^4>0@2$9Z^4>0@2$9Z^4=1a$0@1$h3^7@6$h2$h4$1$0\1s$1\2mo$4@2$2@3$3$1^2^b@2$2@4$f?2HC^d@1$h6^2^1@2$2@2^c^2^1@4$e^d^1^9^8@2$h5?2HC@4$6^1$7$8$5@7$h0?2HC^b@4$6^1$7$8$5^a^9^7^6").
(* Replay replaced by explicit text (rule 11); the zQ STATEMENT above is
   untouched, so no caller changes.  Spliced by g3notes/bjhl/splice.py, which
   anchors on the declaration line and refuses unless it occurs exactly once
   and the two following lines are "Proof." and a KReplay replay ending in
   "Qed." -- so the blob was replaced without ever being displayed.
   This lemma is in the eight because it builds a KLB by [constructor].
   PROVENANCE, cited BY BRANCH, read per hunk with git show:
     a donor tree
       projects/boost-beast/http_request/proofs/lib/Spec/KLink2.v
         -> ev_mmap_fixed_ok
   ONE DIFFERENCE, semantic rather than cosmetic, at the [Hrf] step: beast's
   tree has already had [kb_resv_top] made two-sided
   [ehi e <= start_brk \/ start_brk + 4 * PGSZ <= elo e], so it closes [Hrf]
   with [region_free_apart] and destructs the disjunction.  This tree still has
   the one-sided [ehi e <= bv_unsigned (vm_start_brk ..)], so the same step is
   [region_free_above] with a plain [pose proof] and no case split.  The old
   field shapes are kept deliberately until all eight constructing files are
   explicit, so the branch never goes red in six files at once.  Everything
   else is the donor's text; it carries no address or constant, so none was
   taken from it. *)
Proof.
  intros L G s0 cur cb ck HG Hph Hcb Hck a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb].
  set (L' := set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)).
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMmap a PGSZ PROT_NONE MAPFX) (dec_mmap_fixed a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ KLB L' (ps_brk s0) mo /\ x = FxDone /\ BUD L' mo cb ck)).
    intros s mo (-> & HK & HGs & HB).
    pose proof (kb_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
    pose proof (kb_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
    set (aw := MmNodes.wz a). set (nw := MmNodes.wz PGSZ).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Hrf : region_free (vm_reserved (m_vmmaps mo)) aw nw = true).
    (* [kb_resv_top] is now the [exists V] shape and no longer separates a
       reserved entry from this range.  The route that does is pem's
       (Spec/KStep.v:1482-1485): the MAP_FIXED range is the brk guard, which
       sits inside the tracked mapping [e0] that [kb_phase]'s BPGuard arm
       hands over, and [kb_vdso_disj] keeps every reserved entry apart from
       every tracked mapping. *)
    { apply (bjhl_region_free_inside _ _ _ e0).
      - intros r Hr. exact (kb_vdso_disj _ _ _ HK r Hr e0 He0).
      - rewrite Ua, Ha. exact He0l.
      - rewrite Ua, Un, Ha. unfold PGSZ in *. lia. }
    assert (Hmc : map_contains (vm_maps (m_vmmaps mo)) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    assert (SF : mmsafe (NMmap a PGSZ PROT_NONE MAPFX) mo).
    { cbn. right. change (pgup PGSZ) with PGSZ. fold aw nw. splits; auto;
        first [rewrite Ha, Ecur; exact S2 | unfold PGSZ in *; lia]. }
    split; [exact SF|].
    intros rsp mo' evs Hst.
    apply (nstep_mmap_fixed_iff mo) in Hst; [| exact MI| exact SF]. destruct Hst as (_ & -> & ->).
    change (pgup PGSZ) with PGSZ. fold aw nw.
    exists FxDone. split.
    { unfold dec_mmap_fixed. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. change (mmap_len PGSZ) with PGSZ. fold aw nw.
      subst aw nw. unfold MmNodes.wz. rewrite !bv_eqb_refl. cbn [andb]. rewrite errno_of_lit by (unfold PGSZ in *; lia). reflexivity. }
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs]|].
    pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    assert (HK' : KLB L' (ps_brk s0) (mmap_fx_model mo a PGSZ)).
    { subst L'. unfold mmap_fx_model. fold aw nw.
      kb_open HK. constructor; try exact Kresv; try exact Krtop; try exact Kvdi; try exact Kvdd; try exact Krdr;
        rewrite ?with_vmmaps_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?alloc_top_same_sp; auto.
      - intros e [<-|He]; [rewrite ehi_pair, Ua, Un; lia|]. eapply maps_subtract_ehi. 4: exact He. all: try exact Knwf. all: lia.
      - intros b0 l0 Hin. pose proof (Dgm b0 l0 (or_introl Hin)) as D.
        specialize (Kgrp b0 l0 Hin). destruct Kgrp as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      - intros b0 l0 k Hin. pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
        specialize (Kmet b0 l0 k Hin). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [right; eapply maps_subtract_In_intro; eauto| exact Hr].
      - intros b1 l1 E. injection E as <- <-. splits.
        + lia.
        + rewrite Ha, Ecur. exact S2.
        + lia.
        + reflexivity.
        + lia.
        + intros z Hz. exists e0. split; [exact He0|]. lia.
      - exists a, (2 * PGSZ). splits; [reflexivity| lia| lia].
      - unfold vm_live_bytes in *. cbn [vm_maps]. rewrite Klive. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg ld_groups ld_metas set_brkph set_brkreg]. rewrite Hph. reflexivity.
      - rewrite Kcnt. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg ld_groups ld_metas set_brkph set_brkreg]. rewrite Hph. unfold PGSZ. reflexivity. }
    splits; auto.
    destruct HB as (B0 & B1 & B2 & B3 & B4). unfold BUD. unfold mmap_fx_model. rewrite with_vmmaps_vmmaps. cbn [vm_limit].
    assert (E1 : ltotal L' = ltotal L) by (subst L'; unfold ltotal, lbrk_bytes; cbn [ld_brk ld_brkreg ld_groups ld_metas set_brkph set_brkreg]; rewrite Hph; reflexivity).
    assert (E2 : lcount L' = lcount L) by (subst L'; unfold lcount, lbrk_cnt; cbn [ld_brk ld_brkreg ld_groups ld_metas set_brkph set_brkreg]; rewrite Hph; unfold PGSZ; reflexivity).
    rewrite E1, E2. splits; auto. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & -> & HB). unfold ev_step_post, ans_cont, ev_costb, ev_costk, ev_fixed.
  cbn [answer_ok event_post]. change (Z.land MAPFX MAP_FIXED =? 0) with false. change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb]. cbv iota. fold L'.
  rewrite !Z.sub_0_r. splits; auto. unfold mmap_fixed_answer_ok. rewrite Z.eqb_refl. apply orb_true_r.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma g_remove_split : ltac2:(zQ "e0!hl1!l9!m7!jn9!jnf!o9!jo6!job!jp2!hs6!jqf!jr6!hhf!js1>1a$0>2l0$0>1l@1$2@2$1$0$0>1M@1$2$0>0@3$c@2$1$0$0@4$4$0$0^4^3^2>0@2$d$0@3$3$0@4$a@2$1$0$0$0@2$8$0$0^3^2@2$6@1$2@2$1$0$0\2l1@1$2@2$1$0$0@2$6@1$2@2$1$0$0\2l2@1$2@2$1$0$0@2$9@3$5@1$2@2$1$0$0^6@3$3@2$1$0$0^2@3$7@2$1$0$0@4$4$0$0^8^7^1@3$5@1$2@2$1$0$0@2$b^8^6@3$3@2$1$0$0^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink2 ()) ["HC"] "##^hp'0h02l2h12l1h21Hh33Hnih41li001lh53Hinh63Hndh71Eh81ei011eh94Hnd'h:2H0h;1xi021xh<3Hneh=2IHh>2x1h?2x2h@1AhA1BhB1fhC1yhD2H1hE1MhF1ahG2a0hH1bi031bhI2l0hJ1ri041rhK1zi051zi061ni071pp%0p;2p;1p;3p;6p;4p;5p;9p;:p;7p;;g00:CR0j2iTg00:cR1j1UTg00;Cj34Tg003fj2hj3ZTg02NSj33Tg017MR2j20Tg00>[j1WTg00?Uj35Tg00BJj32Tg02n^j2JTg005dj6^Tg03jfj2STg03I[j6LTg03kEj2]!s/$gR3j2\!sp$;j2DTg01f6j4R!s/$Qj4MTg000`j6Ol9dl:aj7`l;cTg02CJj4ITg03lJj5gTg00QnR4j2FTg00C>j3f!sC$ij5eTg01Z0j1QTg03mGj2:Tg00NLj5_Tg00@5j4TTg02O0R5j2Y!sr$PR6P6f1R7f0R8CTp=1f2R9P6P7P8CIp=>A3678,Y6p=<f5R:f4R;f3R<P6P6P9P7CT;5833p=Hf6R=?2:;1:97=2<8'Fp=P!s3'p=;f7R>A5<9793:;72=/F8p=AP<!sn&I=368956;p=C1:7895<9p=NA5;<9=2:7!sU$6!t\$9569p=XA4678#Qp==1Y68p=BA5678p=E!sz1p=@A2!s?$7A597893;<p=8!u7,=5<8p=?A2<9!t4%GA2:;<A297!u;$VA397892;<p=K!tC$p=[!u@$=2;8p=9!tc$p=b1i66R?#UR@%U6RAP?11;<RB=4?81h66RC=>?7RD/<9P@P;P?P7P?f8REP>P8EHRFP@PEP;A3?78RGFPX0@,0@X1@,0@[[X4@11<9RH%W?RI54?A>?CI/<7g00Q3RJP@PIP!si%IP!sd2P7n010!s#%W6W5P0P6P611=:!tj$<D;!t_-:RFf9RK'1RLP8P@PFP;PGC;GA!t^111>=RMA5?9754?A5?<99>?C/<:P@A5?=:RN!sw&;RO/1F!sr$OPN!sr7[^4@P811KERN!t`&>!t`-=RPf<RQ'1!sj$P!t^9A5?H794?LA5?B!tY&EP5P6P>P?PCP:PODCR592A7P@P?PLPE!t,&ARBf@RHP8EHg00NnRRP@1JFB!sG$LPBPECN!v^+20000=2@GE6!tN/RL[P8%W6RSA>?C<RT=X:KS0052AA>?C;RU=X=FRV92ASPAPSP1P6p-0P8g011YPJn1011!t/'2!wq&X8Ag03bdP5P8E^PJ1SL8b:W2P8O1W21=78%B7RL1E<9PP!u[$OPBDC52A1E;<f>RJ!s;$QfBR5!s=$PAPAP1P6PAP8P:P8!tD21051!tD$1E:;f?RS!se$PfCRWC@RX'EP8ELA2A;XPAP6!so$6P8P>P7!so==:PH!sm$JfDR1DCP7EL17=H17>BP817E5P6PW!sH$5fHRXC@92AKRY1=7F%BOP@P?fIRZ/1XR[fGR\!wz&PR]fOR^P8EHP!wu$Z]P\P?P[P]P\!wuE]9]3[XK6!tF$BP\!tD$EP8PYPA!s:$WPZC@RYfFS01/=8!tU$JRB/1ZR[PX!tS&QR_/1]R`P8D8!tT%B_!sC$[P_PX!tTE^9L]3X4AfE/=YA>?C1/<BfNR1,]\17\11J\1'\1JX^PRP317Z]!tV$MR3fLRX'1RYfKRL!t[&TR[fSRa'1S02!t_'P<PLP?PYP[PL!t]EP717B_RbP6fRRc11acRdP?P8PLPBC?54?!v8$LP_C@Re,E7#B!s7$XPcC@,=9!|d$:P]P^C?!tb&XRffWRg'1RhP8D8RiA2@^GRjCG!wS03]6]5X>611c_RkP?PcPBPZ!tA%a!wi&]DC#B1=[eg00BdRefURl/1311l[Rm52?A4?mX!tQ$f!tQ&iP!t62P9fVRj/1111jlRn52?P?P6!#5b$!{/$8n20011070001!{+&5X8?Ro11g^11gjS03P8EL17^j17]gRpP6Pf!w[$\RqP9Pa!uq$qf[RrP8C?Rs93?7RtP@PaPGEV!t\/X?6P@!sa$ZRu,1rRvPc!vU%PvP8D8A2@c!wg/PI!sU&YRv,1uRwP_A5?w8Rx93?IP@P_P?PIP8DK!s[$P]11vfRy=5?]RzA3?IzRz52@A3?I]RI92@]1D@z1D@ICRCMCMP_P8EO!#3c$b2W7P8O1A4?n3!vs$vP_P]!xF'PyP8D8S04P@P]!uN3P9P6!{2$RIP[Pg1[gI1[g[g007dRIp4p710RzP!s0$210RIP7\7R{%U9R|P4P;P<!#=Q$94<8P:P;P8O1P9A4=8<CGX;:,0:R}[!sN$8O1P7A4:89CGX;;,0;!sW$<P9CI94;7[R~P=!s9%CI94:9\}!t-'P8Dg!x^&!{z%1!#6s'C9W4WBWAW@P~^C9^4|^B{^AI^@zP8!yH$CP^PfP?AZ668/7vA4?8]'FX;?PhAZ66h/7fA4?h^1D6fP7CRCMO6b23fDeO1'SW5P8O1!tI-2110!z6$00W3W6W5PLP8P\Q01P:M9dW8P8O1%QbPe11LB=2?kA4?kZP@P?1113Rk!#4?&Pm!~W$@P?Pk1:lXPGD9!~A2\11XL=2?d!{a27!{a:PYQ02!{Y%3[RY!s\$oPkPmP7ELPY171lP6Pg11c8=2?y!tb%l<RlPaPt!tX$l1:qaRl!tZ5]7X?611_g=2?hP6Pv118v=2?w!~P$cPfC@Rw!#3m+aPvC@,=9f]Rh,7<#Q!{s$_RY,1=RkPgf`Ro/1YR0=5?8RL!}/$X!v&'ogRk!tP6<]3]6]7X>6A2?yyPu!t8$_Pg!#3s$rw17qq!t8&^Rw,1YR\Pj!w3&\!w3+\1:Yj!w3681D6h!xa$<!xG$7PcP7P8P3PQP>M:aW7P]P7P;F`VpU!}-%!}42dBPBP8P=O2P@P3!tG&nP8P@PjP3!#A=4P2P@P@P1!sP%Q03!sQ$gP1!sQ2!u,$`P^Pi!s0%1:f^!u77P@P]Q!~F$vP]!#E++!t5&_A3?9xP@Pu!s1%8!sF$!sx$m!xn+mPl!t$:aA3?;sP@PlP?P;P8DKCGP4P@P[P?P:P?PhPqP7C?DKP@PhP[A3?:7C;!s|$yPgP!xL%yPk!t-:jP?P>A5?\<!sh$?PEP?P0P;D8RkfaRy/1oRX!#EE%Y!#EE,eRDfdR4'1Rl!sn$D!#EG8fbR;/1yRs=4?7Pq!yQ$9Po!yQ$bTy,=h1<U;P@ffRUP:A3?JFRh!u5&s!#ES'iRTfhRaP8EH!s@%1:TE!uG5[]9!zj$5]=X4@A4?0kP?PKP?PXP:D8Rk!#Fo$w!sj$QP?fcRw,14RTPED8R!t;&PT!uF$4PE!uF7A4?XkPr!u>$?PF!tt$=D8PYDC!}9&?POP?PwP;P>EHPoC@,=qA>?CE/<y!vF$?PPP?PlPKD8A3?PK!ud$@!ts$?PHP?fgRl,1aRyPQ!td-y!|W+X1:a!us3A5?\JREP@P@11lURa=5?ORX93?SRy95?0RCP?A5?0SRqP?Pa!uY$?P01:lyA3?q8D9!u`$PF!y\$@PCA3?qXP@PLP?PqPODKCGX4!tv%\P?PUPDPFC?RD93?JROA3?EDRDD9!sG&hA3?EFRED91D@D1D@ECR1:UOP8EOCMCMW7W9!~L$5W=PgP8PjPQP[PWP5M;cW2P7P8O2!#9o/!s/&W2X0@!sE7102!sE%1!sE>b8!#9N?<!sB$102103104!sD%10111106bHbJW9W3PFP8EObDW:PK!s0$!#K2%b:!s+%W2P8P9P7O3W2W9W3X1AX;6!#<?&O4!t-%!s#&20041!s7/A2A8V!vc$NP>!xi&HPS!#I9+KH!s>$NPHP>!#F+D[X4AQ00O1P81DAVO1b2P@A5?M:RM!t+%11JP!x|$JPM!{W5e!wi%X4@X?6X>6!vy-!#;M&1!#;M%G?P7D_WEW4XI6XF6o"). Qed.

Lemma phase_quiet : ltac2:(zQ "h10!o9!jsa!hl1!ike!h9!hsc!jt5!jte!jud!il7!jc!jv9!l9!ik2!kg2!iq2!kge>1L$9>2L'$9>4pbrk$2>2mo$5>3mo'$5>0@4$f?2HC^5^3^2>0@1$e^6>0@3$0$d@1$3^6@1$3^7>0@3$0@1$b@2$c$2$2@1$8^7@1$8^8>0@3$0@1$a@1$4#k0@1$7@1$1^5@1$7@1$1^6>0@3$0@1$a@1$4#k0@1$6@1$1^6@1$6@1$1^7@4$h0@1$3^a^a^9^7").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink2 ()) ["HC"] "##CYp'0h01bi001bh11lh22E1h32Hqh43Kphh51eh61kh73curi013curh82E2h92E3h:2E4h;2HKh<1Lh=2L'h>2moh?3mo'h@1ohA4pbrki022phi031xp;4p;1p;3p;2p;5p;6g01D>j4]Tg03nMj1\Tg01:=j1?Tg00BJj30Tg00:Cj2JTg01C:j1VTg01M2j19Tg008]j1ATg009Bj1S!s/$`j1PTg01GKj17Tg01I7j1<Tg01HBj1;Tg01FDj5[Tg00J1j1XTg00<[j26Tg00V9j1UTg01_7j2TTg00CXj2:Tg01J2j1ITg00=Ej22Tg01dEj1HTg00;Cj3>!sJ$jj1R!s8$Zj1QTg00Qnj21Tg017Mj2@Tg00@5j4FTg01N9j1KTg01Kkj1M!ui$dj2BTg01O@j1E!ui$\j2OTg03oTj1ZTg03jfj2NTg01;Aj1WTg000`j6DTg040]j4YTf3R0f2R1f1R230f0R3'1p=8g00QPR4?023p=4f5R5f4R6=040A0412/13'1'1p==12!s4$p=G1123,11p=3!sI'p=C1@43p=5!s8',10p=Lg03]ER7g03U6R8p,2HCR9P6P1P2C]%\5g03^IR:%?5f6R;#?301J44R<#VR=%9;f7R>#930g00PN#AR?#A!s$+SR@#PRA%76#<%75RB#<30%;B%7;#;50AP9f:R9f8RBP>P5D[P:p-0RC%?9RDPA%7>RE#;RF%<ERE%99RG%X<RH50=C8%7BRB#<RI,6@,43RJ%;BRK,6@RLP3f9RMP3f;RN#9RO=0=HRPE=PJPL%U?g03K='TR?,:3RLPMPL%IB,2L1JAARB%7MRJ#H9>B3%R3RQ1:2?%Q3RR'27G2RS'1X5B'@P4P4P2P3CFRTf=RU#K5><%M2,:1RV/201:0?RW/21'BRX[^14^041J<4RYP<!sb$4!v~$F!sh$Zf>R[#E3>%M1,:0R\/261:6?R]/20'BR^[^64!sj%3353PE=P=f<R_#9R`1O<TRa%;J,6@Rb1:23Rc149c3CC8X14#5X04#5g011YRdn0110300050010101111010000P:%?NReP:PCP3A0AKIRf/1P%<JRP!w$&g14b3Rh14N3RiA0=`HR`'13314bLRb14NLRj%IJ%79!v_'/1SX5B,@B%K[9><TP!v$'f?Rk#E9>YZP!uR1GLRl73`53gP=%9URmP!uQ&14_cRn7CcRo!uN/P!uI%2!uI7X0:P=POP:PC%?_ROA0=3H,1fA0=2HRf,1i93ghA3jfl93gbP=P1PaP!t,M@=PAPI!vP$OPAPKP3P`C816@2RI!vN$A0=mHRm,1iRi73hA3jmlRm93gb%9[Rg=0=aRb/1o!uEKA!t4$!t>'3PPP`C8%<J!{h'PIP3PiCLPJPIPLPmCLPb16@1PcPnCL!t4MeP:!s$$CP3Pdg00Q3RePePdP!yV60!s^&%?U=0:2!s\$1PA%7_R_#;%<_%9k=0=HC8%7URU#<R_,6@Rn,43Rb%;URm,6@RIP3P[P3f@RJ#9Ri!}g$`E=Pb!u?$[PL%IURU%7[Rb!yp%RP!yr+fBRS#K9><TR!yw-C!yu%R!yw6^,1`!|P$A#9RYPa%;b,6@RX14kc7Cc!xn6!|@:PCP0PAPmP_!wO%!sm$b,43R_PXP3PkP3A0=YHRYE=P_PXPLPkPL11Y^E=P=%9SPa%7k#;!{E$J!tJ:!wl8]4]2]3P3g041e90:OPA%7NRN#;%<NA0=gHC8P3W4W2X3d%?[Rg%Z250:141nRnPIP1P[P1P`E=140bRbPXP0PkP0PYE=/N1!s_%eX74P3O1%W290:gPnPI1:1?RnP[Pn12nU12Q012WR53P!wQ%12V51:5?/21'B\T!w;%12\;1:;?Rn/20'B\Z!wU/3!xT%XPWPkPW12WU12Q612]!s{0;12n!sx1>1:>?!sv7!u77g03LA!vD$=PiPa14[c9CI!w31!vK'g042n!sR$3X4d!s9$!wM$001!xq6;P5P2O3b0PFP2EDPEP1EDPGP0EDPDP6!s+$9PMP>CYeb4W:W9W8W2W3W;X?8W>XA4X=7W<o"). Qed.

(* boost-json's [munmap_model] cuts the range out of [vm_maps] with [maps_subtract]
   (MmNodes.v:359); on a well-formed ledger holding exactly that entry, the cut is
   [map_remove] of its base. *)
Lemma maps_subtract_exact : forall maps aw nw,
  vmwf maps -> In (aw, nw) maps ->
  maps_subtract maps (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) = map_remove maps aw.
Proof.
  intros maps aw nw [WB WD] Hin.
  pose proof (WB _ Hin) as Wn. unfold elo, ehi in Wn. cbn [fst snd] in Wn.
  assert (Hrel : forall b s, In (b, s) maps -> (b = aw /\ s = nw)
            \/ (bv_unsigned b + bv_unsigned s <= bv_unsigned aw \/ bv_unsigned aw + bv_unsigned nw <= bv_unsigned b)).
  { intros b s Hb. destruct (pwdisj_In _ _ _ WD Hb Hin) as [E|Dj].
    - left. injection E as -> ->. split; reflexivity.
    - right. unfold edisj, elo, ehi in Dj. cbn [fst snd] in Dj. lia. }
  assert (Hpos : forall b s, In (b, s) maps -> 0 < bv_unsigned s).
  { intros b s Hb. pose proof (WB _ Hb) as W. unfold elo, ehi in W. cbn [fst snd] in W. lia. }
  clear WB WD Hin. unfold map_remove. revert Hrel Hpos.
  induction maps as [|[b s] r IH]; intros Hrel Hpos; [reflexivity|].
  cbn [maps_subtract List.filter fst].
  specialize (IH ltac:(intros b0 s0 H0; apply (Hrel b0 s0); right; exact H0)
                 ltac:(intros b0 s0 H0; apply (Hpos b0 s0); right; exact H0)).
  rewrite IH.
  pose proof (Hpos b s (or_introl eq_refl)) as Ps.
  destruct (Hrel b s (or_introl eq_refl)) as [[-> ->]|Dj].
  - rewrite bv_eqb_refl. cbn [negb]. unfold iv_subtract. cbv zeta.
    repeat match goal with |- context [(?x <? ?y)%Z] => destruct (Z.ltb_spec x y) end; try lia.
    reflexivity.
  - destruct (bv_eqb b aw) eqn:E.
    { exfalso. apply bv_eqb_eq in E. subst b. lia. }
    cbn [negb]. unfold iv_subtract. cbv zeta.
    repeat match goal with |- context [(?x <? ?y)%Z] => destruct (Z.ltb_spec x y) end; try lia; cbn [app].
    + rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
    + rewrite Z.max_l by lia. replace (bv_unsigned b + bv_unsigned s - bv_unsigned b) with (bv_unsigned s) by lia.
      rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* LPS 75d69e00: [nstep_munmap_iff] now takes an [AllocForced] instance (MmNodes
   Section Shapes), which the recorded replay applied positionally without. The replay
   is replaced by this explicit proof, adapted from boost-beast http_request
   Spec/KLink2.v ev_munmap_ok to boost-json's own [mmsafe] (5 conjuncts, MmNodes.v:89)
   and [munmap_model] (maps_subtract, through [maps_subtract_exact]); the statement is
   the one the replay's zQ encoded, binder for binder. The instance is resolved by
   typeclass search (Scfg.hunspell_alloc_forced). *)
Lemma ev_munmap_ok : forall L G s0 a l0 len cb ck, frame_ok G -> brk_quiet L -> In (a, l0) (ld_groups L) ->
  (len = l0 \/ len = round_up_pg l0) -> 0 <= cb -> 0 <= ck ->
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck)
        (ev_step (EMunmap a len))
        (ev_step_post L (EMunmap a len) G s0 cb ck).
Proof.
  intros L G s0 a l0 len cb ck HG Hq Hin Hlen Hcb Hck. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite <- mmap_len_round_up in Hlen.
  set (L' := set_groups (g_remove a (ld_groups L)) L).
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMunmap a len) (dec_munmap a len) _
             (fun x s mo => s = s0 /\ G s mo /\ KLB L' (ps_brk s0) mo /\ x = RgDone true /\ BUD L' mo cb ck)).
    intros s mo (-> & HK & HGs & HB).
    pose proof (kb_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
    set (n := mmap_len l0) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 n) in *.
    assert (Hnn : mmap_len n = n) by (subst n; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
    assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
    { destruct Hlen as [-> | ->]; [unfold LEN_MAX in A1; split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
    destruct Hlen3 as [Hlen1 Hlen2].
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
    assert (Hhas : map_has (vm_maps (m_vmmaps mo)) aw nw = true).
    { unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went, KInv.wz. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    assert (Hwent : went a n = (aw, nw)) by (unfold went, KInv.wz; fold aw nw; reflexivity).
    assert (MS : maps_subtract (vm_maps (m_vmmaps mo)) a (a + n) = map_remove (vm_maps (m_vmmaps mo)) aw).
    { rewrite <- Ua, <- Un. apply maps_subtract_exact; [exact (kb_wf _ _ _ HK)|]. rewrite <- Hwent. exact A5. }
    assert (SF : mmsafe (NMunmap a len) mo).
    { cbn. change (pgup len) with (mmap_len len). rewrite Hlen2, TASK_SIZE_val. unfold MmNodes.wz. fold aw nw.
      splits; auto; try lia. all: unfold PGSZ in A3; exact A3. }
    split; [exact SF|].
    intros rsp mo' evs Hst.
    apply (nstep_munmap_iff mo) in Hst; [| exact MI| exact SF]. destruct Hst as (_ & -> & ->).
    change (pgup len) with (mmap_len len). rewrite Hlen2. unfold MmNodes.wz. fold aw nw.
    exists (RgDone true). split.
    { unfold dec_munmap. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. rewrite Hlen2. fold aw nw.
      rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. rewrite !bv_eqb_refl. reflexivity. }
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs]|].
    pose proof (kb_distinct _ _ _ HK) as Kd.
    destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
    rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
    { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
    assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                     b + mmap_len l <= a \/ a + n <= b).
    { intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kb_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + n) by lia.
    assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
    { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. unfold KInv.wz in E. rewrite unsigned_lit, Ua in E by lia. exact E. }
    assert (HK' : KLB L' (ps_brk s0) (munmap_model mo a n)).
    { unfold munmap_model. unfold MmNodes.wz. fold aw. cbv zeta. rewrite MS.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) (munmap_model mo a n)) by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]).
      unfold munmap_model in Hph'. unfold MmNodes.wz in Hph'. fold aw in Hph'. cbv zeta in Hph'. rewrite MS in Hph'.
      subst L'. kb_open HK.
      (* [kb_vdso_disj]: a munmap only drops a mapping, so every mapping left is
         one the invariant already placed apart from the reserved ledger. *)
      assert (Hvdd : forall r, In r (vm_reserved (m_vmmaps mo)) ->
                       forall e, In e (map_remove (vm_maps (m_vmmaps mo)) aw) -> edisj e r)
        by (intros r Hr e He; exact (Kvdd r Hr e (map_remove_In _ _ _ He))).
      constructor; try exact Hph'; try exact Kresv; try exact Krtop; try exact Kvdi; try exact Hvdd; try exact Krdr; rewrite ?with_vmmaps_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?alloc_top_same_sp; auto.
      - apply vmwf_remove. exact Kwf.
      - intros e He. eapply maps_subtract_ehi. 4: exact He. all: try exact Knwf. all: lia.
      - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgrp b0 l1 Hin1). destruct Kgrp as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        unfold map_remove. apply filter_In. split; [exact G5|]. destruct (bv_eqb _ aw) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E.
        apply (Kfst b0 l1 Hne ltac:(pose proof (mmap_len_ge l1 G0); lia)). exact E.
      - intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kmet b0 l1 k Hin0). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + unfold map_remove. apply filter_In. split; [exact G7|]. destruct (bv_eqb _ aw) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E.
          apply (Kfst b0 l1 Hne ltac:(pose proof (mmap_len_ge l1 G0); lia)). exact E.
        + intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          destruct (iv_subtract_contains (fst e) (snd e) a (a + n) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(clear -D Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      - rewrite Ezz, map_app, <- app_assoc. exact Kd1.
      - intros b0 l1 E. specialize (Kbreg b0 l1 E). destruct Kbreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
        intros z Hz. destruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr].
        unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:Efst; [|reflexivity]. exfalso. apply bv_eqb_eq in Efst.
        unfold brk_disj in A6. specialize (A6 b0 l1 E).
        destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
        + rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
        + pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold KInv.wz in D. fold aw nw in D. rewrite Un in D. lia.
      - unfold vm_live_bytes in *. destruct (live_bytes_remove (vm_maps (m_vmmaps mo)) aw nw Kwf A5) as [-> _]. rewrite Klive, Un.
        unfold ltotal. cbn [ld_groups ld_metas set_groups]. rewrite Ezz, Eg, !sum_glen_app, sum_glen_cons. fold n.
        unfold lbrk_bytes. cbn [ld_brk ld_brkreg set_groups]. lia.
      - destruct (live_bytes_remove (vm_maps (m_vmmaps mo)) aw nw Kwf A5) as [_ ->].
        assert (LP : (1 <= length (vm_maps (m_vmmaps mo)))%nat) by (destruct (vm_maps (m_vmmaps mo)); [destruct A5| cbn; lia]).
        rewrite Nat2Z.inj_sub, Kcnt by exact LP. unfold lcount. cbn [ld_groups ld_metas set_groups]. rewrite Ezz, Eg, !app_length. cbn [length].
        unfold lbrk_cnt. cbn [ld_brk ld_brkreg set_groups]. lia. }
    splits; auto.
    destruct HB as (Q0 & Q1 & Q2 & Q3 & Q4). unfold BUD. unfold munmap_model. rewrite with_vmmaps_vmmaps. cbn [vm_limit].
    assert (E1 : ltotal L' <= ltotal L).
    { subst L'. unfold ltotal, lbrk_bytes. cbn [ld_brk ld_brkreg ld_groups ld_metas set_groups]. rewrite Ezz.
      replace (sum_glen (ld_groups L)) with (sum_glen (g1 ++ (a, l0) :: g2)) by (rewrite <- Eg; reflexivity).
      rewrite !sum_glen_app, sum_glen_cons. pose proof (mmap_len_ge l0 ltac:(lia)). lia. }
    assert (E2 : lcount L' <= lcount L).
    { subst L'. unfold lcount, lbrk_cnt. cbn [ld_brk ld_brkreg ld_groups ld_metas set_groups]. rewrite Ezz.
      replace (length (ld_groups L)) with (length (g1 ++ (a, l0) :: g2)) by (rewrite <- Eg; reflexivity).
      rewrite !app_length. cbn [length]. lia. }
    splits; auto; lia. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & -> & HB). unfold ev_step_post, ans_cont, ev_costb, ev_costk.
  cbn [answer_ok event_post]. fold L'. rewrite !Z.sub_0_r.
  splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
ltac2:(KReplay.run1z (kr_t_KLink2 ()) ["HC"] "##=[p'0h01Hh11Eh22H0h31yh41li001lh51xi011xh62Hyh72H1h82Hxh91eh:2H2h;3Hndh<1bi021bh=1Ah>1Bh?2IHh@1fhA2l0hB2x0hC1zp;1p;4p;2p;3p;6p;7p;5p200R0g00;CR1p4p710R2p8P0g02CJR3!s9%!s7%05dR4!sJ&5!s9&NLR6!sJ/4\2R7!s7'p201R8P2p8P8P!sq$2!sN$8P5p8P8g03I[R5!se+8P5!sJ-g000`R2!sD-7!sD02O0R9!sD'g00:cR:j13TP3j42TP9j25TP1j31Tg00BJj30Tg00>[j16Tg00?Uj34TP4j6=j78Tg03jfj29Tg01Z0j17TP5j6<!sP$;j2;TP7j6>TP2j6:TP6j5?Tf1R6P6[f2R2#3f3R7%37f4R5f5R4f6R1P4P5P2C2,54f7R3?127f8R;?125P3P5O1P3P7O150;f:R<?045[[[[]3]5W4!sb$7%64C2,55%619112%639132P1!sc$1!sc%3g00Q3R=A0<14P2n010!s#%W1W6W8W;X35X57%35P3P1P4!t`%1A1;27f9R>!t]$;!sx$;!sx%>f;R?!t]'^31^54P;P3P1A4;57C2,53A4>4591>2A4<1491<2P>!si$>!si%<P9P?f=R9#3R@f<RAP<O1f>RBP9PAP>C2549RC706f?RD?0;3RE[P7%3?RF%6?P<P;O1PAP?P<P3C254?RG30%3ARH%6AP?P>O1!sp$?P;C254ARA30P@%69P:PBp-0f0R9g011YP=n101!v1%2!s%$!s#$X9@g03bdPCP9E=P=19E9b2W0P9O1W0f@RE#3fAR=?169#7fBRC/56fCR@#3A4@72PCPEO1fDRIP@PCPDC254@30%3IA4I57P@P=O1fERJPIP@PEC254I30%3JREPEP:fFRKfGRL#3P9P4P9!tr2102100X9EA4J45PIPCO1PKPJPIP=C2R=54JP9E<A0E5=%3KR=PKP:PLfHR:P9P3P6!sv:=A4K14PJP@O1R@PL!sz$CC254KP6E<A0K1@PKPIO190L3P9PLPJO190:;fIR@P:PKO1fJRC#3fKR4PCP@PKC270>R=A146<#7fLRE/5?fNR??0LK]2]0[X<@%3@!sT$:PJC270;P9P=%34R=PEP4PCPLC2R;P4P@O1=1E9#7fMRM/56fORN?0:LRO]2]0X4=PCP:O1=14;#7PM!sd$:C2,5Eg00BdR;A0?CLA1?L@POPIA0N4:fPROPEPNP9O1PNP@O150OfRRL?06C]1X5OP?PEO1P?P:O150NP;fQR=?0M@RPA1=@ERQA0L?CRRPKfSRSPNPLPOO1PLP9O150SfU?0=6]1X3SP=PNO1RT=0LTfTRU/;OW1P4P9P2F8X0RP9O1A1LCMA0SN4P1PLP=P4O1PUPSPLPNC291S9X<LRR!s7$=P?P4P9E>PTP2E:O1'9W6P9O1n20!~G'2!s-$!s'$W1P@P9PIF8!{1%A1N:CP;A0OE:A1O:4A0=C@PJPLP?P=PEO1RJP=!u=%LA0UM!u<$LPO!tb$OP?O150=A0SEN!tz$JP!te,EP7!te$9E=!te$1PCP9PKF8X0P!w2$!xI%5P2P9PKO6X6Q!u/>8!sB>:W7P<P9E:b:W2P>!s0$!}b&b!s+&W7P9P2P6O3W7W2W0WAXBDP7P2P6P9O4n!{h%!t%&0041!|/+000A0H9AA0B31[X4FPGO1P91;HA!t#$!#6C'3X51W?W4XC7P9D?W4W@X>8X=0o"). Qed.

Lemma map_base_bump : ltac2:(zQ "72!hl1!l9!jp2!jqf!m7!o9!kj7&@3$2$0$0@3$2@2$1$0$0$0^1&\1m@2$1@2$1$0$0$0~0>1a$0>2ms@1$4@2$1@2$1$0$0$0@3$5@1$4$0@4$3@2$1@2$1$0$0$0$0~1@4$3@2$1@2$1$0$0$0@2$1@2$1$0$0$0@1$6^2^1@4$3@2$1@2$1$0$0$0$0~1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink2 ()) ["HC"] "##-\p'0h01lh11ah22a0h31bi001bh42b0h51kh61mh72msh81pi011ph91xh:1zi021zp;2p;1p;4p;3p;6g00:CR0j27Tg00:cj19Tg04\Mj23j1@Tg02CJj44Tg00BJj32Tg00@5j41Tg00V9j1=Tg00CXj26Tg01_7j2<Tg02n^j2;Tg00?;j2:Tg04]Tj6ATg008Aj6?Tg000`j6>Tg003fj38Tg00QPR1f1R2f0R3781781p=0P1P1P2P3C1p=51711R4/71R5#9%91R6P5P1f2R7/33,04X95R8P3C4P5P11043R9X65R:P2C49263X0!sW$P8P:P0P4P1f3R8!sa%=219P3P!t>$f7P4!tD'R0'3,041040521^:1P3g00PN#=R0/63g03K='<,67f:R9';g00NnR6P6P6P5P3!t2$4/58R61670C1!t#$6P7C1R6n010!s#$20000!t3%6521!s]%1587P2C1,04,:1R8P8n011!sV,b4!sL%7!tu%7,39!si%7521eX51X01X3!u<$O2n20011!t>$120102102X84!sC91102X25P3EA!vL$:P5P5%@2R2P3C4!v{$5!v=$:P3E?E>W7X11o"). Qed.

(* ---- bjhl: the revision's vDSO/vvar gate on [mmsafe (NMprotect _ _ _)] ----
   75d69e00's Sys/Mm/Mprotect.v answers [unmodeled] for an mprotect whose range
   meets the launch's vdso/vvar pair, so [MmNodes.mmsafe]'s NMprotect case now
   carries [region_free (vdso_reserved (m_kernel mo) (vdso_top h)) _ _ = true].
   [State.init_reserved] appends the pair to [vm_reserved] (75d69e00
   State.v:7716, with [vm_reserved_init_model] at :7844) and no step rewrites
   [vm_reserved] -- every next-state in Sys/Mm rebuilds [mkVmMapsFull] with the
   same [vm_reserved h] -- so the gate follows from the range being apart from
   the reserved ledger.  The lemmas below are the whole of that argument that
   does not depend on WHERE THE HEAP SITS; the placement fact itself belongs to
   the heap ledger and is deliberately not proved here.
   PROVENANCE, statement and proof, read per hunk with git show at the ref:
     a donor tree
       projects/boost-beast/http_request/proofs/lib/Spec/KLink2.v:45-61
         -> bjhl_region_free_apart (statement and proof)
       projects/boost-beast/http_request/proofs/lib/MmapSim.v:223-253
         -> bjhl_vdso_incl_reserved, bjhl_region_free_vdso_of_reserved
            (statement and proof)
   DIFFERENCES from the donor: the [bjhl_] prefix on each name (the donor's are
   unprefixed); the two MmapSim lemmas live here rather than in this tree's
   MmapSim.v, so that no file's import list moves and no import cycle appears;
   [bjhl_vdso_gate_apart] has no counterpart in the donor; and [vdso_top_eq],
   [vdso_incl_init_model] and [vdso_incl_with_vdso] are deliberately NOT ported
   here -- they belong beside the launch, with whoever discharges
   [bjhl_vdso_incl_reserved].  The donor carries no addresses and no constants,
   so none were taken from it; this tree's own are untouched.  One further
   difference, MEASURED rather than anticipated: the donor closes
   [region_free_apart]'s two branches with [apply andb_false_r] and
   [reflexivity] respectively, and NEITHER closes them here.  After the
   [rewrite IH] this tree's goal carries a trailing [&& true], so the first
   branch reduces outright while the second needs [andb_false_r] -- the
   opposite way round from the donor.  Both branches now end
   [rewrite ?andb_false_r; reflexivity], which closes either shape and so does
   not depend on which comparison [iv_overlap] puts first. *)
Lemma bjhl_region_free_apart : forall maps aw nw,
  (forall e, In e maps ->
     ehi e <= bv_unsigned aw \/ bv_unsigned aw + bv_unsigned nw <= elo e) ->
  region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold ehi, elo in H; cbn in H.
  destruct H as [H|H].
  - replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false
      by (symmetry; apply Z.ltb_ge; lia).
    rewrite ?andb_false_r; reflexivity.
  - replace (bv_unsigned e <? bv_unsigned aw + bv_unsigned nw) with false
      by (symmetry; apply Z.ltb_ge; lia).
    rewrite ?andb_false_r; reflexivity.
Qed.

(* The pair is part of the reserved ledger it was appended to.  Kept as a named
   predicate rather than inlined so the launch side can discharge it once, from
   [State.vm_reserved_init_model], and carry it. *)
Definition bjhl_vdso_incl_reserved (m : Model) : Prop :=
  incl (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m))) (vm_reserved (m_vmmaps m)).

Lemma bjhl_region_free_vdso_of_reserved : forall m addr n,
  bjhl_vdso_incl_reserved m ->
  region_free (vm_reserved (m_vmmaps m)) addr n = true ->
  region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m))) addr n = true.
Proof.
  intros m addr n Hinc Hrf. apply region_free_intro. intros a sz Hin.
  exact (region_free_In _ _ _ a sz Hrf (Hinc (a, sz) Hin)).
Qed.

(* THE LAST MILE the mprotect gate needs, stated so that the one fact still
   missing from the heap ledger -- that a ledger group is apart from every
   reserved entry -- discharges it directly.  A range apart from the whole
   reserved ledger is apart from the pair, because the pair is in that ledger.
   Nothing here assumes which side of the pair the heap lies on. *)
Lemma bjhl_vdso_gate_apart : forall m addr n,
  bjhl_vdso_incl_reserved m ->
  (forall e, In e (vm_reserved (m_vmmaps m)) ->
     ehi e <= bv_unsigned addr \/ bv_unsigned addr + bv_unsigned n <= elo e) ->
  region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m))) addr n = true.
Proof.
  intros m addr n Hinc Hap. apply bjhl_region_free_apart.
  intros [a sz] Hin. exact (Hap (a, sz) (Hinc (a, sz) Hin)).
Qed.

(* The same, taken through [kb_resv_top] instead: with every reserved entry
   ending at or below the brk start, a range at or above it misses the pair.
   This is the form [ev_mprotect_ok] can use the moment its range is known to
   begin at or above [vm_start_brk], and it needs no apartness premise. *)
Lemma bjhl_vdso_gate_above : forall m addr n,
  bjhl_vdso_incl_reserved m ->
  (forall e, In e (vm_reserved (m_vmmaps m)) -> ehi e <= bv_unsigned addr) ->
  region_free (vdso_reserved (m_kernel m) (vdso_top (m_vmmaps m))) addr n = true.
Proof.
  intros m addr n Hinc Hab. apply bjhl_vdso_gate_apart; [exact Hinc|].
  intros e He. left. exact (Hab e He).
Qed.

(* DISCHARGING [bjhl_vdso_incl_reserved] AT THE LAUNCH, in two pieces: a base
   case at [init_model] and a congruence that carries it across every step.
   TREE: boost-json/fuzz_parse.  No quantity here is a count, an index or an
   offset, so there is no unit to name.
   The congruence rather than one lemma per update, because the predicate reads
   only four projections -- [m_kernel], [vm_reserved], [vm_mmap_base] and
   [vm_init_sp].  [vdso_reserved] reads the first; [vdso_top h] is
   [page_round_down_Z (mmap_top h)], [mmap_top h] is
   [Z.min (bv_unsigned (vm_mmap_base h)) (page_round_down_Z (alloc_top h))] and
   [alloc_top h] is [bv_unsigned (vm_init_sp h) - stack_max_size]
   (75d69e00 State.v:3466, :3483, :3371).  Every next-state in Sys/Mm rebuilds
   [mkVmMapsFull] carrying those three ledger fields through verbatim, so a new
   update costs no new lemma here -- only the four equalities, each of which is
   [reflexivity] for a [with_vmmaps]-shaped update.
   PROVENANCE, cited BY BRANCH:
     a donor tree
       projects/boost-beast/http_request/proofs/lib/MmapSim.v:232-240
         -> bjhl_vdso_incl_init_model, statement and proof
       projects/boost-beast/http_request/proofs/lib/MmapSim.v:227-230, :242-244
         -> generalised into bjhl_vdso_incl_cong; the donor has [vdso_top_eq]
            over two ledger fields and [vdso_incl_with_vdso] for one update, and
            no congruence of this shape.  DIFFERENCES: the [bjhl_] prefix, and
            the congruence covers [m_kernel] and [vm_reserved] as well, which
            [vdso_top_eq] does not speak about. *)
Lemma bjhl_vdso_incl_cong : forall m m',
  m_kernel m' = m_kernel m ->
  vm_reserved (m_vmmaps m') = vm_reserved (m_vmmaps m) ->
  vm_mmap_base (m_vmmaps m') = vm_mmap_base (m_vmmaps m) ->
  vm_init_sp (m_vmmaps m') = vm_init_sp (m_vmmaps m) ->
  bjhl_vdso_incl_reserved m -> bjhl_vdso_incl_reserved m'.
Proof.
  intros m m' Ek Er Eb Es H. unfold bjhl_vdso_incl_reserved, vdso_top, mmap_top, alloc_top in *.
  rewrite Ek, Er, Eb, Es. exact H.
Qed.

Lemma bjhl_vdso_incl_init_model : forall reserved brk0 mbase sp lim inp,
  bjhl_vdso_incl_reserved (init_model reserved brk0 mbase sp lim inp).
Proof.
  intros reserved brk0 mbase sp lim inp. unfold bjhl_vdso_incl_reserved.
  rewrite vm_reserved_init_model.
  replace (m_kernel (init_model reserved brk0 mbase sp lim inp)) with (in_kernel inp)
    by reflexivity.
  intros e He. apply in_or_app. right. exact He.
Qed.

Lemma ev_mprotect_ok : ltac2:(zQ "ha0!hl1!hrc!ii3!l9!hs6!hl4!hjd!jnf!hsc!kk3!kl0!klb!o9!kg2!km2!il7!ipb!iq2!iq9!ir9!jg3!jgc!jla!jm4!jmf!hhf>1L$f>1G>0$1>0$8P>2s0$1>1b$0>1l$0>1k$0>2cb$0>2ck$0>0@1$h3^7>0@1$d^9>0@3$h9@2$3@2$3$0$0$0@4$7@2$3$0$0$0@4$7$0$0^7^6^5@1$e^a>0@2$6@2$b@2$5+2^6$2@1$h5^7>0@2$6Z^6>0@2$6Z^6=1a$0@2$5^b@2$b@2$5+1^9$2@6$h4$h6$1$0\1s$1\2mo$8@2$4@3$c$1^2^f@2$4@4$h1?2HC^h1@1$h8^2^1@2$4@2^h0^2^1@4$h0^h1^1^b^a@2$h7?2HC@3$9^1$2$a@7$h2?2HC^f@3$9^1$2$a^e^d^9^8").
(* Replay replaced by explicit text (rule 11g); the zQ STATEMENT above is
   UNTOUCHED, so no caller changes -- [ev_step_spec] below is still a replay and
   still applies this lemma with the same eight binders and six hypotheses
   (checked against the zQ itself: L G s0 b l k cb ck, then frame_ok, brk_quiet,
   the [In (b,l,k) (ld_metas L)], the [(2+k)*PGSZ <= round_up_pg l] bound, and
   the two budget bounds, then the [let a]).
   CAUSE, from the baseline round a farm round at this line:
   75d69e00's Sys/Mm/Mprotect.v answers [unmodeled] for an mprotect whose range
   meets the launch's vdso/vvar pair, so [MmNodes.mmsafe]'s NMprotect case
   (MmNodes.v:92-99) carries an EIGHTH conjunct
     region_free (vdso_reserved (m_kernel mo) (vdso_top h)) (wz addr) (wz (pgup len)) = true
   and the recorded replay builds the old seven.
   PROVENANCE, cited BY BRANCH, read per hunk with git show:
     a donor tree
       projects/boost-beast/http_request/proofs/lib/Spec/KLink2.v:329-411
         -> ev_mprotect_ok's proof, the plain-text twin in the other tree of the
            fork; its [KLB] field list, its [kb_metas] shape and its helper
            names are this tree's, which is why the bullet sequence transfers.
   DIFFERENCES, each forced: the donor has NOT threaded the eighth conjunct (its
   [SF] closes against its own [mmsafe] with [splits; auto], so the donor is red
   here in the same place); [Hvd] is therefore this tree's, built out of the two
   [KLB] fields this commit adds and [bjhl_vdso_gate_apart] above -- the range
   lies inside the tracked mapping [went b nb], every reserved entry is apart
   from that mapping ([kb_vdso_disj]), and the pair is in the reserved ledger
   ([kb_vdso_in]).  The [try exact Kvdi; try exact Kvdd] in the [constructor]
   discharges those two fields for the next state, which this step leaves alone
   ([mprotect_model] rewrites [vm_noaccess] only).  The donor carries no address
   and no constant, so none was taken from it. *)
Proof.
  intros L G s0 b l k cb ck HG Hq Hin Hk2 Hcb Hck a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite <- mmap_len_round_up in Hk2.
  set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
  eapply mspec_bind.
  { apply (mspec_sys mmsafe (NMprotect a PGSZ PROT_RW) (dec_mprotect_rw a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ KLB L' (ps_brk s0) mo /\ x = RgDone true /\ BUD L' mo cb ck)).
    intros s mo (-> & HK & HGs & HB). pose proof HB as (Q0 & Q1 & Q2 & Q3 & Q4). pose proof (kb_minv _ _ _ HK) as MI.
    pose proof (alloc_top_lt _ (kb_top _ _ _ HK)) as [[Htop0 HtopC] Htop47].
    pose proof (kb_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    set (nb := mmap_len l) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 PGSZ) in *.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Hcn : map_contains (vm_noaccess (m_vmmaps mo)) aw nw = true).
    { destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps (m_vmmaps mo)) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    (* the eighth conjunct: the protected page sits inside the tracked mapping
       [went b nb], which the ledger keeps apart from every reserved entry, and
       the vdso/vvar pair is one of those entries. *)
    assert (Hvd : region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) aw nw = true).
    { apply bjhl_vdso_gate_apart; [exact (kb_vdso_in _ _ _ HK)|].
      intros r Hr. pose proof (kb_vdso_disj _ _ _ HK r Hr (went b nb) A5) as D.
      unfold edisj, elo, ehi in D. unfold elo, ehi in B5, B6. unfold elo, ehi.
      rewrite Ua, Un. destruct D as [D|D]; [right| left]; unfold PGSZ in *; lia. }
    assert (SF : mmsafe (NMprotect a PGSZ PROT_RW) mo).
    { cbn. change (pgup PGSZ) with PGSZ. unfold MmNodes.wz. fold aw nw. splits; auto; try (unfold PGSZ in *; lia). }
    split; [exact SF|].
    assert (BOK : mprotect_budget_ok mo aw nw = true).
    (* this tree's [mminv] is the two-component conjunction, not the donor's
       three: [proj2 MI] is already [m_vm_materialized mo = []] *)
    { apply mprotect_budget_ok_intro; [exact (proj1 MI)| exact (proj2 MI)|]. rewrite (kb_live _ _ _ HK). unfold BUDCAP in *. lia. }
    intros rsp mo' evs Hst.
    apply (nstep_mprotect_iff mo) in Hst; [| exact SF]. change (pgup PGSZ) with PGSZ in Hst. unfold MmNodes.wz in Hst. fold aw nw in Hst.
    destruct Hst as (_ & [(He & _ & _)|(_ & -> & ->)]).
    { exfalso. rewrite BOK in He. discriminate He. }
    exists (RgDone true). split.
    { unfold dec_mprotect_rw, dec_mprotect. cbn [no_cc eff_copies eff_copyins eff_ret eff_writes eff_zeros eff_unmaps]. change (mmap_len PGSZ) with PGSZ. fold aw nw.
      rewrite (unsigned_lit 0) by lia. cbn [Z.eqb]. rewrite !bv_eqb_refl. reflexivity. }
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| apply vm_only_with_vmmaps| exact HGs]|].
    pose proof (kb_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
    assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
                     b0 + mmap_len l0 <= b \/ b + nb <= b0).
    { intros b0 l0 H Hne. pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kb_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    assert (HK' : KLB L' (ps_brk s0) (MmNodes.mprotect_model mo a PGSZ)).
    { unfold MmNodes.mprotect_model.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) (MmNodes.mprotect_model mo a PGSZ)) by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| reflexivity| reflexivity]).
      unfold MmNodes.mprotect_model in Hph'.
      subst L'. kb_open HK. constructor; try exact Hph'; try exact Kresv; try exact Krtop; try exact Kvdi; try exact Kvdd; try exact Krdr;
        rewrite ?with_vmmaps_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk vm_limit set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; rewrite ?alloc_top_same_sp; auto.
      - intros e He. eapply maps_subtract_ehi. 4: exact He. all: try exact Knwf. all: unfold PGSZ in *; lia.
      - intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
        specialize (Kmet b1 l1 k0 Hin1). destruct Kmet as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
        unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
        + assert (Eb0 : b0 = b).
          { destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
            pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
          subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
          splits; try assumption; try lia.
          intros q Hq1 Hq2. destruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh).
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b + q * PGSZ) (b + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(right; subst a; clear -Hq1; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
        + splits; try assumption.
          intros q Hq1 Hq2. destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          assert (We : ehi e <= 2^64) by (apply Knwf; exact He).
          assert (D : b0 + mmap_len l0 <= b \/ b + nb <= b0).
          { destruct (Z.eq_dec b0 b) as [->|Hne].
            { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
            exact (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne). }
          destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) Hlohi Hel ltac:(unfold PGSZ; lia) Heh We
                      ltac:(clear -D Hab Hq1 Hq2 G5; unfold PGSZ in *; nia)) as (e' & He' & Hr).
          exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      - rewrite map_base_bump. exact Kdis.
      - unfold vm_live_bytes in *. rewrite Klive. unfold ltotal. cbn [ld_groups ld_metas set_metas]. rewrite sum_mlen_bump. unfold lbrk_bytes. cbn [ld_brk ld_brkreg set_metas]. reflexivity.
      - rewrite Kcnt. unfold lcount. cbn [ld_groups ld_metas set_metas]. rewrite length_bump. unfold lbrk_cnt. cbn [ld_brk ld_brkreg set_metas]. reflexivity. }
    splits; auto.
    unfold BUD. unfold MmNodes.mprotect_model. rewrite with_vmmaps_vmmaps. cbn [vm_limit].
    assert (E1 : ltotal L' = ltotal L) by (subst L'; unfold ltotal, lbrk_bytes; cbn [ld_brk ld_brkreg ld_groups ld_metas set_metas]; rewrite sum_mlen_bump; reflexivity).
    assert (E2 : lcount L' = lcount L) by (subst L'; unfold lcount, lbrk_cnt; cbn [ld_brk ld_brkreg ld_groups ld_metas set_metas]; rewrite length_bump; reflexivity).
    rewrite E1, E2. splits; auto. }
  intros x. cbn beta. apply mspec_ret. intros s mo (-> & HGs & HK & -> & HB). unfold ev_step_post, ans_cont, ev_costb, ev_costk.
  cbn [answer_ok event_post]. fold L'. unfold mprotect_answer_ok. cbn [Z.eqb orb]. rewrite !Z.sub_0_r. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_step_spec : ltac2:(zQ "h30!hrc!hjd!hs6!hl1!hsc!o9!kmd!il7!ipb!iq2!kn9!ko5!iq9!ir9!jg3!kp1!jla!jm4!jmf>1L$7>1e$f>1G>0$0>0$4P>2s0$0>2cb$3>2ck$3>0@1$d^4>0@2$6^7^6>0@2$1@1$a^7^4>0@2$1@1$b^8^4>0@2$1Z^6>0@2$1Z^6@6$e$h0$0$3\1s$0\2mo$4@2$2@3$5$0^2^b@2$2@4$9?2HC^e@1$h2^2^1@2$2@2^c^2^1@4$8^e^1^a^9@2$h1?2HC^b@7$c?2HC^c^b^a^9^8^7").
Proof.
ltac2:(KReplay.run1z (kr_t_KLink2 ()) ["HC"] "#$kzp'0h01Hh13Hcbh21sh33Hckh41lh52moh61bi001bh71kh83curi013curh94Hpreh:1pi021ph;4addri03!s-$h<3mo'h=2_Hh>3leni043lenh?3Hphh@4__p1hA4__x1hB4__x2hC4__x3hD4proti05!s-$hE3reqhF2HqhG1ai061ahH1ei071ehI5flagsi08!s/%hJ1ri091rhK1EhL2H0hM2HKhN3HinhO4HlenhP3KphhQ2NEhR7__arithhS4__ffhT8__varmaphU5__withV4__x4hW4EcurhX1GhY2H1hZ2H2h[2H3h\2H4h]2HGh^4Hcb0h_4Hck0h`2Hkha5H!u=$b4Hreghc1Lhd2R1he2R2hf2R3hg2S1hh6__sat4hi2b0hj5c!vk%:!s/%hk2cbhl2ckhm4hinti0;!s-$hn2l0ho2s0hp3whyi0<!s,%=1ni0>1xp%0p%1p&0p&1p;1p;2p;7p;8p;4p;5p;3p;:p;6p;;p;=p;>g0196k11ZTg057?j2]Tg01@kj1GTg01Aoj72l:wTg058Fj1:Tg01:=j1BTg03oTk10FTg01<Jj1<Tg008]k104Tg00V9k109Tg00CXj23Tg00:Ck20=Tg01C:k114!s0$\j2fTg00BdS00j2DTg00QnR0j26Tg00=Ej20Tg02n^k20_Tg059Jk80{Tg03:Hk20yTg05:Sk10MTg01>ak40\Tg05;Wk10CTg05<_k20KTg03;Hk50GTg05=bk11UTg05>ek20YTg03B3k30kTg000`j8Zj6hk71?Tg03>_k20gk319Tg03kEk20f!s0$gS01k20eTg003fk31>Tg00iQk31!u`$EBk40ZTg01D>j4xTg01FDk517Tg009Bk11!u]$9`k115Tg01GKj1JTg01HBj!tn$1I7k10STg00J1k10aTg00<[j2OTg01J2j1gTg01dEj1a!s8$jk11!w6$;Zk112Tg017MS02k20QTg01Kkj1kTg01M2k10:!wC$Jj3!wr$5dk611Tg01PFk510Tg05?kk10~Tg00bkj1}Tg00cJj2vTg00eXk10!s9$f6k20|!s0$Wk30OTg00lik20^Tg00>[k10zTg00?Uk30]!x}$ck10xTg00E2k20NTg00d3k10w!s:$Pj4{!s/$nk10!t;$FLk10uTg00G7k20!va$H=k10[!s0$bk40!un$g@k20LTg03Eak30t!sX$Zk30JTg00K7k21Y!tY$;k20r!s:$Yk21XTg00LEk31W!s0$dk41VTg01_7k206Tg03jfk20?Tg01Z0j1iTg05A8m;1TTg05BFk20oTg01e[k40nTg02OLk81QTg02PTj3jTg01X^k21PTg01Uij2bTg01YOk21!x=$ZIk20!xd$Zfk21!v2$YJj2[Tg01[Mk21!{K$\4k21K!s0$Zk2!yF%]@k21I!wm$Jk21HTg01hkk2!~$$3FDk31!}b$^Kk21E!v<$=k61D!u1$gm=1CTg03C6j4@Tg03nMj1nTg01;Ak10!uW$D5j1qTg05E<m>1ATg05FEm:1@Tg048^j2pTg01N9j1|Tg05GUm>1BTg0524j3QTg05Ham>1<Tg05Iok308Tg05K3k10ETg05L7k11;Tg05M>k11:Tg03J8k60lTg00@5k40!v`$3:k518!{H$Ck30BTg01O@k10p!z3$@k31R!yc$Qk61!|G$IMk70b!|Q$Sk80qTf1R1$1;f0R2'0p=F&1:1/02p=Eg00U[R3!s3$Pf4R4f3R5f2R6P1P2H0Z'6p=8g03OVR7f6R8f5R939P4P5P6P1Cx/62'6p=;g01jXR:P7g00QPR;P520g61P2J0lp=4g03^IR<g041e792p>01A9;13/62p=Wg03K=R=-062p>0dA9;12p=5A9<61!sH$R20Q;2p=1P;P;!th%jp=A132=p=Sg03LAR>99<9&0:5=946!si$'6'6p=dA9;23p=>20_23p=HB0k7;2p>0I!t|$STR?!s{%I0Gp>0HP7g05NER@!t7%\p>0WP7P@!sK/XP7P7!s7/VP:!s7$!vV$J0lp>02A9<12p>0D131299;6p=uA97!s:$@!va0p=sP:P9B1945!sh$I18p=Y&042$04p=~&0:1=962p=oA95!v4%>0R&0S2,O1p=cA9;!vJ&?1612,66p=7136!xU%\10!sD&VB0B!sf&=m%|2:0B61p>0<P6!vx-e&0p!sA+;%g2,01p>00&0:6=95!tM&P1b2=p=l1[3!s8&`1[32p=tB1R!x1$XP;P1g00ogP2H03p=z!s5$S5S03P?P?g00T4S04P2J1Sp>0sP4Q!s@%Q04P5!s2-6g00U;R:K0bP1P2L0qp=^g00NnRAg00OnS05!yo%A1312/3=p==A9<2>p>0m1b2==9;3p>0510!v=%>1LP1!t0-2P:K0bp>0i!tG1!t='>0hg05OMS0699;2p=_g03MJS07!s5%Cg0538S0899;2,D1p=y1[31g03Ul,[!|4$NA9;2=p=Mg03NSS09!sQ$!w'$>Q!s_%p=`1D!xN'cQ!sI%p=T1312006=p=I&0p5:0B94!xb''6p=KAQ1=2p=rQ089Q2=p=Lg03]Eg05POR:g03U6R>p-0RB[\7&1Z51]891F85f7RC/E5%P9S0:Q0:P:f<R:/]2f9RD,F11E6DP1f>REp,2HCRFfARG%G1RHP2f?RIP1P2O2PGP2f=RJP:D8F;X5>X27PFP5PFPIP5PJP:f;RKf:RLF2C4]3]1]9PL%:2,]J%:1/FL%:6S0;/ELQ00f@RM#B$01,W5%BGRN&0F2RO%<2RPg00PNS0<$04S0=$09RQ$0dRR'3RS,543RX8;#1fBRT#BRU20=;;RV$14RWPT1A12S0>,fVS0?P91312RX#SS0@EdX4;#1X6;#1'DP1PMPFfCRYPHP2PG!uZ&YP2PIPE!uX/%:4RZPFPGPZPIPEPJP:F2C4P6%>4S0A&01N'6P0%>9&01UP1PTPFfERN!s~$Y!s~&N!t2$M!s~,S0BPF%:8!t%$YPZPGPMPIPEF2C4RZP2%>CS0CP;P3PAP;%H2P3PRn010!s#$20000S0D/0T!sE%1P3Q0<$09R[!sK3E/0TfHR\#BS0F$01P1P\PFfKR]PHP2fIR^!tr&]P2fGR_fFR`!tv/GPF%:5RaPFP^PaP_P`PNfDRaF2C4[]3]1XE;PAP;20_33Rb!tv5/0GPAP;PbP3P[!sA4%B_S0H$01PFP\P`PNPaPYPTP2L0{P1P_PFfJRc!vk$\!tw&cP2P`PN!ts,RdPA20y7;S0IPbP7P;P;P7P;&0M3Rbg05QSH0\&0C2-0K7&0I1V?+0HXJ;I0GS0J&1U7S0K%G2S0L00Y3-0WbP@Q0IP2&0C3-0K7B0k7;3!s^$&0IHS0Mn01106!uA'XG@+0XX27+0V!u[1PFP\%:3Rb!uT'F2Re402ePdPFPbPeC4eW?W3W1f8ReP2P8P9GZW0!ud%n20!st'12!s/&W0P2O1159S9RUO!{t$%BYRUPWPYQ0?P8Q!{U3Q00158!sU/a!sU$aQ0?PC!sU2PZP215C!sT,Q02P;%BNS0N15eS7ROX8;P1PaPFP_!wa$N!wa&_!{Z$T!yV/OPF%:eRUPFPNPU!xJ$GPMF2C4S0PP2Q0H15LS7ROP0Q0F&0F1+0D%<1S0Q=uKRQ!z?%:RO!z?$O!z?%P!z=$S0RP2%Bc&0F5!s[$4S0S=uERP;%<9S0T/3RROQ0D/0^Q0E/0^P1fNRSPFfQRU!{e$ORZ!u1&UP2fMRbfLRd!u5/UQ0;-0gFS0VPFPZQ0;PbPdP]PcF2402!{g-%HO!{c7\!sB$<8/3R#H!{i7\%<CS0W!tz$00f3%>O%HO+0e%<eS0X!s^%AQ01%<DS0Y/3R#>!|_$1!st5S0Z/0b!sD$6!#386[/0ZP1fSROPFfVRf!uz$TRg!uz&fP2fRRhPUD8F;S0\!#5Z'<J/3RS0]#:RiPFPgPiPhPUfPRiPZ!wP%^]1]3P1%<LS0_!tr$S0`%Pb%PZQ0\P020@6gPFfWRj%G6S0aP1fURkP6P1O2PjP1POPhD8Ds20=;7RlPF%<G!tC$b#:P5P6PFfZRm%<YS0c/3R#:fXRnPjPfPkB1>;71S0dB1=!s/$eP2M:wX<>X:lEYP220@4fP7PjPFf[RoQ0LP9fYRpP2P9O2PoP9PjPfH0ZRq'6DsP!tL$NS0f!t7$RrP1P8PFf^Rs%<!uS$:f\RtPoPmPpQ0dQ!t?0RuEY[!vU$Pm%GjP4PnPjP4O2PmP4PfPkD8DsP0PFPo%GnP9CxPpPnP9O2/6qPlPFPrPpP8PuEYP2PFf]Ru%GmPCCxPtPoPeO2PsPePmPpD8!tx%\!ta$PtPDPFfaRr%<!v@&_RqPsPuPt!ts4EYPFPq%GtPDP1I17P<PB%BqQ0=$04S0g#~#~S0h$16Rv$15S0i%JDS0j#UQ0j$0S&0aVRw9oWqH0R%JLS0k,cvS0l,52S0mQ0k#U,OvS0n/52%GuS0of`Rx=oWwS0p7?237Q0mQ0n132RRy'5Q0oQ0pQ0k#gS0q,0yQ0iQ0i+0=RzPzP2%JKS0r#a&132&1229\1R7V1S0sCmXHz+0QQ0>fbR{60<V%k1=\65A\5R6'DS0t[^4;^6;20=V;R|1A61=eV2R}fcR~40;%k6=\54A\4R5'DS0u[^7;!sY%37377?y37PW&0:r!uR$?Q0r#US0v!uX$w%GsS0x/5X7?XH0R!#6G+g011YS0yn0110>00050010101111!}O%P<%BxP<PBP2!uf$vQ0r$0SS0rQ0m=9WwS0m!w#$:S0v,cv!v|$iQ0v!v|&z!v|$qS0{AoW{wS0|!vy&iQ0z/5yQ0{Q0|Q0v-00y!ve%JS0v#aS0zQ!vY&-0QzQ0>fdRz60<VQ!vL+feS0t:0;|}Q!v0:P~!v'$!t\%%GxS0i!u}'P!u},Q!ux?X6<P2&0F^PNJ11Q0lQ0n!xz%7?^7?^5?^P0Q0r,Ov,5cQ0wQ0xQ0m7?c7?cg00Q3R<P2Q!v<&d%JES0w!t^&rAoWzw7?b7?bPFQ0t%G{S0mPIPCI10%JIRw,cvRX%lX%Uw,OvQ0g$09$0dRy%gw5\X5VX'W+0`P0%JMRX,cvRw#t%lw%UX,Ov%gX9\wy5Vw'WP<P2%JTS0x,cv#t%JY!t+&#l!t'%%gw9\Xy!sy$&0~O%<O,0Og00RIS0rg012[RX#}Ry#}Rw#}S0l,v;S0n1v;wS0pQ0<$0}-0|;S0o1v;yS0y60O;1v;XS0|'X'X'Xg00o;S0u+0^!y`$zS0>40]!s2$xS0sP;P;20N;6S0}P5&0w;RXC{P5!s<%5P1PXC{S0~C{&0v;S10&0u;RXPXP;Q0g-07;S0gg00TTS11!t`$[S0<!s>$12H03&0a?S13P!sX$20L;3Ryg010NS14Q0=$0[!sj%=H03Q!sN%Q0gQ0='z!s5'1220L;QQ0h#~#~#~$09Rw-0L;S0h60t;S1560J;/zyQ1320sX9D^!s$%Q04-1YXS16P2P6g00ONS17-0rA21X26Q1759AdB1W;31H1VS17bSbTbUXA;XB;XC;X@B1012%t5S181554206QwS19,35#>PC[[[[^A;^B;^C;^@BP2P<%J`,cvPk%<kP1P5PePcO8bRP<eb0W=Wg!#CL<!sF$W!sF>PbP+0?W=WM!#D9?9P2Eh!#D]@!#=^$Q0^eW1W3WKP2O1Q0`#i10[b10RZPAQ05P1PgPFPjPHP2Pk!sv%PjP2!#=0$!#AI+`PAQ0IP2Q0JQ0K%<IS0\/3RRv$0MQ0L00Yv+0W!#Gf%%<M/3R$0C-0K7Q0b$0IV?+0HQ!#GgOk%<ES0b!t4$#:POPhPUPiF2402X6APFPg!s8$JPiPZPSPDP2P1N;1TQ0]#HS1:Q1:$0A%>v#i[Q0]#>#i%Hv$0A[Q0]00o3P6H0nEh!vA+QP2O1n1021001090002111071110=P6P5O2b6bJW3W1PIP2PJP:GZW0W?!wM@8;!sE7!#5p$!#IK$Q0NPWPNQ0?Pe!#He1!#HT%`PWP`Q0?PD!sF0Q!#Gs$FPWP\Q0?PK!sD,!s_&^S0@PWP^1A62,fVP:1=62!sI$Q!#Gn$]S0RPWP]1A4!sG$E1=42EdP0%BdS0?$0mPWPd1A91S0P,fV1=91,5IH0PP1PdPFPZ!yP$b!yP&ZP2P]Pc!yP/NPF%:MRvPFPbPvP]PcP^P\F2C4P2%BSS0^!t3%Z1Ae4S0]!t3$e4,5TH0PP01AD9S1:,fV9oWi1=D9,5YP1PiPFPO!tJ$U!tJ&OP2PZPS!tJ-1;PF%:a!tJ$UPv!y=$bPd!tJ%1AKCS1<!t#%h1=:e,5`P;1=JDRWQ0D/0UQ0E/0UP1PfPFPp!t;$j!t;&p!|=$g!u_/EQ0VPFPjQ0;PkPgPOPh!#JM4W!#JM6iPAP;1=EL!#JK8i1=IKRW!#JF$W%HW+0e1=M:!#JA%1=GJ#>Q0Z/0kQ0[/0jP1PoPFPs!u$$t!u$&sP2!#Dn$F;S0[!#I\&1=NGRW#:!vB$tPvPmPpPnPj!#IW$Z!#IW$1=TE#>S01%Pk%PjQ0[!#IR$tPFPqQ0aP1Pu!#IK%q!tJ$mD8!#Gx$1=^NS0a!#ID&P{1=]_#:PxPqPsPu!#Ey6220@4sP7PqPFP~Q0LP9Pr!#I'%~P9PqPsH0ZS0V!#I+&1=b^#:S0;!#I$%fRv1=Z]#:PzP~P{Pr!t44S0D!#H}'{Q0{P4!t_$4O2P{P4PsPu!#H}'~Q0iP9CxPrPxP9O2Q0V'6PlPFQ0;PrP8Q0D!#I%$Q0tQ0!#I$$zP~PeO2PvPeP{Pr!#I$$13idS0m#S!tf$DPFfiS0D1=hS#:fgS0;PvQ0tPz!v17FQ0;%GzPD!{^$dPaL1Q&05iS0e10Rd%ldQ0mQ0j#gQ0j#a%SiQ0m3j3V'W37-0`iP0%tU&05US0m10Rb%lb13UbRlQ0qQ0k#a%SU;jl!sW%P<P2%tO&05gS0q10RiQ0e13giRlQ0v+00Q0z%Sg;jl3737P0&05kS0eQ0m13kURlQ0w!sK$w#a%Sk!sM$9VRUP<P2&05jQ0q13ngS0m%JGRl+00%al%Sn!u%%79VRgP010Rk!tD$pkRlQ0x!sw$x#a%Sp!sw$P<P210RjS0e%ln13tnRR%JNRl#g!st$t;jR3V'W21Puw%Pu%Pw1bqwRR#P[[21Osw%>wRl#i20Uqw-06w=uqR[21Nqw%twS0x1bx!sU$1[Rw'6[21Mxw1[w31brwRR,[w@1LR3[21Krw20U{w#>\l21J{w1b~w/5~\lg03bd21I~wRRePRP4g012521H3w+0rQ0xeO11bz!t5-Q0rQ0l#}RR,v;S0lQ0pQ0y'X'X21G;wQ0|61F;Q0o%}R,v;60O;Q0lQ0oQ0n!s3%!sS$'X'XQ0u+0^+1EQ!#D<%sP;P;Q0}P420N;4C{P4Q0~C{Q10PX!#Bs$!#j=&Q0h/zy-0iXJ1DQ13Q12Q0hQ0<$04-07;60t;Q0=60J;'z-0iXH0h!#CQ%P;Q15Q11Q0g!#Cu-=!#CA$!sH%PyQ14Q12!sG-12Q0g60J;Q0h!#Cp08!#Cp&!t2$6Q!#CG4V;X@BP<\l206w4=u15[Q19/06Q0AQ181349/3w#>PD[!#CS0V!#CV&20Uvw1bvwP{PvPCPLPEPTPOO:bRbLP<eb\b[bZbYbLb0bhP<eW=Wf!#>3>We!sD@d!#DO>!#D,qZ!#D,/1#i10[kQ0e!#D+&tPFPqPHP2Pu!su%PqP2!#7i$!#:y+5!#D+/1=_YR<!#D#'<!#D#+1=\a!#C}'a!#C}Xu1=`TR@#:!#Ya$Pn!#Cx,t!s8$NPGP!#[L$J!#C|%=1C%HWR?&0A?%>@#i[%>W#i%H@$0A[20oW!#Cs+Z!#CsLi!#Cs%_P2PNPaGZW0Wb!xH@!#D9@4!#D9?X6!#DXC!s@-211000!s'$!sB@3W1W9XE;P2O1!#z:$P2C@,]Y!#zI'@/FMP!#~;%C@/EMQ00%n`S00%>8%_5%C4/y41N993737Q0H&0T2RW15CPS0e%M8%C9R@00>437!#q^%P1P`PFP^!yn$_!yn&^!vd%!yn/HPFPCP8P9P4C@R?PFP_P?!#l}&!#q$%n_Q0C%_41y@91N88!#9k$%n\%_9%C8R@%`8S0C'D1NCC37,WeQ0GPFPDPePCP8!s~&^P?!#gl0ZP2%nc%_e%CDR?/yD1NLL37,WKP0%>:%_D%CLR</yL1NKK37Q0NPFPJP:PKPLC@RwPFPbPw!#FN-S0NP2%>EP;P3%_JRw%CERB%`E1NII40cRl'6Q1;PFP1!#rW$C@RXPFPUPX!#Eq-[X;;%_:%CJRX%`JRy'D1NEE37P0PwPl!sh%3!sh+l!sh$l!#F[0%_IP;Q06PAP;%q2S0KP3%kY!#EO7%q!#g{5Rl/0i%Ca/yaS0M1NNN!#:>$E!tJ$`PNP5C@RRPFPjPR!#Fm+!#r}&I;PA!tO$#qRRP3%kT!tI3ZPAP;PR!#Fn6Z%CY%`Y1Naa40cP0Q0MPw!tI-Q06!wG&jPw!tJ/P2%C`Rw/y`1N\\PFPmPnPjP^P\Pf!sN$IP1!#pz$N>1AWOWa!}#60!~'+3W1PMP2PEPJ!#qRCI!#78DWF!#r<BQ0F15ePRR%MCS0620>@9377RW!#qH+Q0@%MeS0F%CC%T8379?DP!sH%Q0ZP2Q0R%MLR@%Te77?9?KP7RWP0Q0?&0T1+0DQ0Q%MK%TD77<5?:Q0NP2Q0^&0T5!sD$S%ME%T:77X5?IP0Q0T,5M%MI%TJ77B!z;%G!z;+B!z;$B!z;1Q0W,5TP;Q0X%MYRB%CT00>GRX'6Q0`!{e$!~?$C@R<PFPkP<!#U3+!{e&MT%CG%TM!{[$BPX!s^$Q0_!s_+X!s_$X!s_/P2%MNP;P=!{;%NP3%k2!yr3g%C_RX%T`RB'6P1PpPFPtPHP2Pm!wd%PtP2PnPj!#y`,<PFQ0\P6P\P_C@RW!yo$W!#9y%k!{[%1X>!{Y$%qaP3%k=RW!tH3O20>wNP0PXPBP!sy&=!sy&<!sy$<!sy/P2%C^P;Q07%TcP1PuPFPx!tw$s!tw&xP2PtPo!$$F-Q0cP=P1P]!sz&sP<P!#nq%!vy%D;%T!s|$9!}V%KP3P!tx4m10lmP1PqPFP{!tA$x!tA&{!tM$u!tA1fP=Q07P6!#4:%xPl!#n>$Po!$+C&!~m+9#qRl!tA7p!~l$l!~l7pPq!st$a!u>%PMPkPgN:1@!}V$cP2P9P_!}V$c!}:<!~2,1P`P2PTK1?!~/BY!~/F!#[?b!#=I?I;XD;X>;X;;!#=N&O41p12,]I1p61/F:1p56/E:P0%nTPV1A92%|Y1542154P'DCm!#[Q%BPF1p94R3PFPYP3!$,N-P6%naR3PV1Ae2%|`15C2Q0e!sc-2P;PV1AD2%|_15e2/DR!sB$Q0HPF1pDeRRPFP_PR!#=N/2PV1AK2%|^15L215L!t^$P01A:1>0<Vc15K1Q0Q,5K'DP1PcPFPb!z&$]!z&&bP2P^P\!z&/1pJ:RPPFP]PPP^P\P_P`!#Zk&E5>0<Vd15E4Q0S,5E'DPSPdP]PMP9PI!#=<$PDP1P2PaPYN>1BWOWN!yC?Xn!x070!x0'!#7v?!x2%!x+%!sL$AQ612,]GAQ561/FEAQ456/EEP0P3%M4%`5P|P}P_Pe1I[2R3,36RP1IQ2RRQ0Q'0RlEKX7;#1!#aS+37Q0OPFAQ894RAPFPNPA!$&J-P6Q00Q06Q0C!t&$cPKPPP!sn7P0Q0F%`!sM%]P:!sM8'6Q0GPFAQLDe!t=$^PA!#B2-P2P;P=AQJ2K/F\AQE1:/E\!sy$UPT!sy8R=,6yQ0UPFAQM5E!s|$ZPA!$&L+!#?6&>;1r:L/F_1rJK/E_%`:!t#$iPG!tz:P0PyP=!t&$1rMER=!t%$=!t%/P2%`IP;Q081rY2/Eb1ra1/FZ!t$$jP\!t$6R\#1Q0`PF1r`5RZPFPkPZ!#:\/]1]3XD;%LT/Ed%LY/FS!sv$fP_!tx8!|o%\!s{$%L`R\!sz$\!#:w0!sh$pPc!sh3!sc%|1A51=eV2PmP]1353!sK/P1PnPFPo!|j$p!|j&oP2PjPf!|j/%LcRcPF!t4$j!#Ae$!tJ'Q0P!t+$tPb139!t+,!tL+86!sF$uPS1383%<6,0R!sJ$Q05PF%LSRSPFPuPS!#O9+!t$']!s`$qPi13e3Q0S!s`$P0Q1:=eV1>0;|x1I[1,3D1IQ1Q0T'05?UP1PxPFP~!uK$r!uK&~P2PqPs!uK1hRhPFPrPh!#bO$Pt!tI%Q1<=eV5>0;|{1I[4,3:1IQ4Q0X'05?gP01I[99ukJ1IQ9Q0Y'0P1Pz!#a+$HP2Q0!#e+%Q0;P2P~P{!tD1fRfPFQ0tPf!#b`$Px!tE%1I[C9ujIP;1I[e,3MRj%L2/E~%L1Q0t'F1IQKQ0\'0P1fjR~PFfmRrPHP2fkR!#Vp%PrP2Q0DfhRr!tC15RkPFPfPkQ0DPrQ0;Pv!zP,;;%Lj/E{1I[D,3G#L/Fz1IQLQ0b'0P~!sV%YPIPK!#bf%POPCP2PxPqN>1<W`W1W3Pn!#Rg+!#<T?N!#;_?7!#Re@!#S+_!tu$MP2P4!$;WDW3W1PKP2PePCGZX0@!#I4[!#8<$!#=E'!#=C$3g001>B08!#8G$B08!#8H$B08!#8I%1PYPFP`!{+$!#KQ%!#@,$PG!xI/B08945R9PFPaP9!#8-$PIF2C400?6!tK&m;Xj;W:!tJ,5RZ&0E2,]J&0E1/FL&0E6/ELP1PIPFPT!tD$!#\U%PT!#LU$!tD/&0E5R>PFPMP>!$FA$PK!tB1WpP2O1n01107000611103411031041051082!s4&3!s<,3010210:10;1010<!#Vw$O3W_W^!s~&]Xl;Xk;Xo7WXWHWco"). Qed.

(* [comment removed for export] *)
Lemma membed_spec {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (P : R -> Prop) (G : PState -> Model -> Prop) L s0 cb ck,
  frame_ok G -> ctree_ok L t Post -> tbound t cb ck P -> 0 <= cb -> 0 <= ck ->
  mspec (fun s mo => s = s0 /\ KLB L (ps_brk s) mo /\ G s mo /\ BUD L mo cb ck) (membed t)
        (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ P r /\ KLB L' (ps_brk s) mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0 /\ BUD L' mo 0 0).
Proof.
ltac2:(KReplay.run1z (kr_t_KLink2 ()) ["HC"] "#$GWp'0h02L'h11sh22moh31Hh41rh51zh63mo'h72s'h81Gh91Lh:1Ph;4Posth<2cbh=2ckh>2s0h?2HGh@2HKhA3HcbhB3HckhC3HokhD1RhE2TBhF7__arithhG4__x1hH1thI2B0hJ2B1hK2HBhL3HB'hM3HB1hN3HG'hO3HG1hP3HGshQ3HK1hR2HPhS3HPrhT4HanshU5HconthV3HfahW4Hfa'hX2HkhY2HmhZ3Hm'h[2Hph\4Hpreh]3Hsoh^4Hso'h_2IHh`3TB1ha3TB2hb3TBkhc2_Hhd4__ffhe8__varmaphf5__withg1ehh1khi3mo1hj2s1i001xp%0p%1p&0p;1p;4p;5p;2p;3p;7p;8p;9p;6p;<p;;p200R0g05ShR1p4p73110p8P0g05U0R2p4p72!s8'3J8R3!sK1385R4!s929>R5p4p741!sr,V4R6!t,2W@R7p4p7!s7+XFR8!sJ2YUR9!sJ'g0196k10XTP7j4]TP9j5STg01@kj19Tg01D>j4=Tg02kTj13Tg00:Ck20;Tg024Uj12Tg025Xj11Tg01EBj4LTg00QnR9j20Tg05ZZj5QTg00BJj34Tg05[_k307Tg00?;j2eTg00>[k104!t,$ck10WTg00E2k20V!s0$nk10UTg00FLk10STg00g@k20RTg00G7k20PTg00Hbk402Tg00J1k10MTg00mUk70I!s:$Sk80HTg00K7k20G!s0$Yk20DTg00LEk30C!s0$dk40BTg05\dm90ATg01fQk400Tg000`j6yTP4k70@Tg057?j2~Tg035fj3cTg036mj37Tg03>_j2lTP2j3^Tg05L7j1FTg00=Ej2RTg05M>j1_Tg05]kj2NTg00Zij2ZTg01Aok70?k80KTg05_2m<0>Tg02SXj1hTg00CXj2ETg01GKj1pTg026[j1gTg02Udj1nTg00YJj2m!u5$6j4rTg05`>m909Tg003Hj6{TP6m;0JTP8k708TP5m;0LTP1k706Tg002Bk30NTg017MS00k20OTP3k603Tg05aCk405Tg00IMk70QTg05bIj5|Tg03;Hk50TTg05POS01g00QPR3f0R140Np=}g00U[R5/R1p=Pg03OVR8f1R6;41p=Tf4R2f3R4f2R7P6P1CL'0p=Cf5R:P2P4P7P6C=/01'0p=WP6P1P5P5CLp=@g03hUR;f7R<f6R=#334%2494:2g00STR>%16747!sb$'0p=U1061,07,04,02p=8P!t0+DQ/01p=zg03]ER?00O1p=5g01jXS02P!sP$A^476P1J03p=>Q01P3P6P1H05p=O!tx0p=YP4P7%96P1C=p=bA4:24A4>76!u>&IA4;!s3$!tY'vP<P=!t]%DQ!tu&'0p=XP2P4%9!t$,iA4;61p=DA4>61p=d!s}'p=VA44!s{&2,0:p=o!sy'C=!sy-aA4>47!vg,'0p=qP6g00S5R@P>P>g00T4RAP1g00U;K0Qp>!xD$NnRBg00ONRC741p=`1R!tI&J!t8'P!x1%rCrp=M!vB%!s8$D|p=xA48!sV&?P8!s@'I0Tp=wA4;<=!vE2'0p=KP<P=!sn%!v;%|!wt-6Q!wa$!tC&!w^$k%_1,Z6p=:!uh&p=j%F!s9%AP2P41Z7!yz$p=[!wz0,0:,0=p=Bg03U6RD?461p=G%3194;6p=\!yp&%1694>!yj%p=fA4D!t5&t!s@,p>0=%3294;:%2694!zA&!t-$;A7<=:P2%F7,Z4!t|%CLp=H%219476p=s%1194>6p=u%3694;7!y>%p>0<%1794>4!x'1<!t:6p>0:A4;:2!y&'!s9$EP=P:!vl%!ur$D|!wb$Qp>0F%}1!{:&%}6p-0RE\4RF\?RGPE\D\8S03&0X2S04f:RHP2f8RIP<C]f;RJf9RK!vj$<DS%P2RLf>RM1T6KRNp,2HCROPH%96S05P1PJP6P1O2PHP1PIP<DCEWRPX2DX18S06POPMf<RQfBRRPQf@RSP1P4f?RTP1P4O2PMP4O1POP1%97RUP6C=RVf=RWP7P6O2%37RXPJ20;33RY%27RZPJ%17R[PJ1@16R\GUD8S07EzX0?#5!tF%X4ME>\L[[[[^=3^<3^>8^9?]8^:F];WHQ03Q04PHP21OH!ul$PJ1OJ!uj+!zF%MPQQ06PRPQ1O!u,%Q!t65S08P91T7HPOPJPUP6PQ!u0%!v6$KPIDCDYfCR]PWfAR^,O]P1P^PSP1P^O2PTP^!ut%!~5$bS09PMP2P4O2%32S0:%3QS0;PY%22S0<%2QS0=%12S0>%1QS0?1@14S0@EIDvGX!th$P11T2QP8PWPOPTP1P:!t;$:!t;$:PWPQCLR_'0DifGR`P^fERa,O`P1PaDQRbfDRcP1PaO2RdP]PaO1Re!tn$UP<C=PRP7P<O2%3SS0A,DXRf%2SS0B94YZRg%1SS0C,d[Rh1@1<S0DD8D8!te$[X18POPM%9WS0EP2PTPWP2!xn$2PQPJDCDYP9POPT%9MS0FP:C=PSPMP:O2/0_PbPdP!tW$%9SS0G!t[&SP<O2Q0AQ0A'DPYQ0B!s%$C!s%$D3VEo!tM&P1POP^Q!s_&]P^PIO2PRPIPSPTDCP9PcPRPKO2P]PKP^PSCLfKRePafIRd,OeP1PdfHRbP1PdO2P`Pd!zs'cS0HPJfFR_PcPJO2Ri%3cS0IQ0I'DPY%2cS0JQ0J%1cS0KQ0K1@1JS0LEIFa!wy+P_PQPcP]CLP?fNRjPbfLRk,OjP1PkPeP1PkO2fJRlPk!yE&`PMPdP`PMO2%3`Rm/DmPY%2`RnPn%1`RoPoP1PMCqEoDi!t6$P`fMRpP`1OpeP`PeDQPlP`PeO2S0MPdPeO1RqPOP`P_PWCbRrPbP_PWO2Rs%3_S0NQ0N'DRt%2_S0OQ0O54YRu%1_Rv/dvRw1@`WRx'0Ry'0Rz'0R{'0R|'0R}'0R~'0B07p`eQ0MP~PRPqP}P^PrP|P:PsP{P6PtPzQ0N,e;PuPyQ0O,eYPwPx1e>vP`PWPaPcP5P5P1g00RIRx$04&0Wx20V36&0U3&0S3RxP@P>P>PAP320R35Rwg00TTRyg00PN-0P3H02-01xRu&0M>P!sV-PwPyPw!sE&PuK0IL0H20GxAP1P71eBC20D17#`dB0C356H0BbdbebfXG3RC%P1%P69J55[^G3R!xB%^O2bFPCP5P1PaPSO2bFN90AFM!s$%H00WKXPi!#6?$n20010!s#$12!s/&W3W@!sD?P:P1EyW3!sJ=X3!#72%K0@PMQ!#77$1OMQQ08E>eXBLXALWEWCW?X=3X<3X>8X9?W8X:FX;GX46Q01%}4\3PE\:S08\?S0MQ08!#6B%QP2PKPIO1P<C]PWPHPKO1!#6F&PS!t?%SPWPQO1PcPQP^PSO1!#6K8SE>\L\L!#7\3]:];\3Q!tE2AxQHK!tD%AxWJH!tC+91~IMAcKT1#`PRA7HS6PTP6O1PWC][^53P^POPJQ05P1PQ!vY%PJP1!#7T&9?6H!ta%1lOTPTP1O19^ORX535w^Pa!zJ$]PRP1P4PS!#:e%TP4O1PVPM!#8L%XQ0;PYPZQ0=P[Q0?P\GKD8G6!ug0^CkP41~HSAcQR1#`PaA7W]6PR!t|$S!t|&9%FR/RH%_R1N]1P_P]P6O1%FcRE,ZQ1:JcPSDS[^537JKPaPOPT!uR%S!uR&TP1PWPQ!uR&M!uR+]P]!uR&_!uR$aPdP^Pd!~`$1P4Pc!uR&]!uR&R!uR%10h\9jfg!uE4aCkP=1REQ%_a1N_1PdP_P6O11AT`1:M`P]!tu'QP9%__/RW1N`1PlP`!sM%Sb%_bRE,ZTPc!sQ%PdPOP]!uE%c!uE&!#<0%!uE&R!uE+`P`!uE&l!uE$dPpPaPpPePl!uE$b!uE&`!uE&_!wq,I!wq%JP[Q0K!wq8dCkP11RET1Nl1PpPl!u$%]e1:ReP`!t|%!#>v$3Pk1lOlPl!t\&pS0PX531T6aREPOP_!uE%`!uE&_!uQ$]DCEW!t;%POPcPl!yz&^K0?fPRgPbPgPjPp!u@$e!u@&l!u@&d!u@%Rf1DXmRmA4YZnRn1d[oRo/0\3j!uE4k!t1/PSPKP:P6PWPQN<0>!u=%pAc`p7#`1Np7POA7`p7Rh!u1%b!u1%%36Q0N!#;+$6Q0O%16PhP1Pa%Fp1:cpD[7VvEoFBS0Q!tG%Q0PfQRhPdPhfORGPj!uE$k!uE&e!uE&l!w_'%3bS0RPYPZ%2bS0SP[%1bS0T!wh8pS0UQ0QP9Acbj4#`1Nj4POA7bj4RFPUP6PfPmPnPoPFP6P_%Fj1:ajD[D8EWPh1G129?6:X6DX78POPhPjP2O1fURFPpPFfSRofRRn!u#$g!u#&G!u#&j!u#,kS0V!u#%kS0WP[%1kS0X!u#8hE>P1Aclg:#`1Nh=POA7eh=Rm%9:S0YP2PkP:P2O2%3:S0Z%3lS0[!w4%:S0\%2lS0]%1:S0^%1lS0_PmP2Pd%Fh1:bhD[3VEoEWP91Nn<POA7kn<Rm%9=S0`P:PpP=P:O2%3=S0a/\ePY%2=S0bPe%1=S0cPePmP:Pl%Fn1:dnD[EfFaPFAtN1I!vC+FPnPIO1fYRNPhPNfWRmfVRfP1P4fTRU!vE&o!vE&n!vE,gS0d!vE%gS0eP[%1gS0f!vE8FE>P11NUKPOA7GFHRP%9KS0gPIPgPKPIO2%3KS0h/\jPY%2KS0i%2jS0j%1KS0k%1jS0lPPPIPp%FF1:kFD[EIFaP9POA7gfJRP%9HS0mPKC=PhPHPKO2%3HS0nPGPY%2HS0oPG%1HS0pPPPKPj%Ff1:pfD[80=GF;PN1G1Q9?6W!v7+NPfPQO1f]RPPFPPf[RifZR5!v7$XRC!v7&m!v7&f!v7,US0q!v7%US0rP[%1US0s!v78NE>P1POA7nCW%9QS0tPJC=PUPWPQO2%3WS0uPnPY%2WS0vPn%1WS0w%1nS0xPoPNPMPQPhPNPgPNGH3VF;P9PFPMPWO2%3MS0yPoPY%2MS0zPo%1MS0{PoPUP5PTPWPnP5PhP5GHGUPP1G1S9?6^!uw+PP5PSO1faRBPNPBf_Rxf^RA!uw$\Ru!uw&i!uw&5!uw'PCPYPZPCP[PCP\GU!uk4P!uk$mPSPTO2%3^S0|%3fS0}PY%2^S0~%2fS10%1^S11%1fS12PmPPPRPSPFPPPUPPGHGKP9%3RS13%3mS14!|c%RS15%2mS16%1RS17%1mS18PCPAP]P^PfPAPFPAGHEIPBAtE1c!uc+BPAPcO1feREPPPEfcS19fbRw!ud$`S1:!ue&x!ue&A!x^,uS1;!x^%uS1<P[%1uS1=!x^8BE>P1Q0I/\NPY%2aS1>P5%1aS1?P5PiPBP_PcPNPBPCPBGHEfP9Q0O%2iS1@54Y%1iS1APuPwP`PaP5PwPNPwGH5VvPE1G1b9?6d!uI+EPwPbO1fiRyPBPyfgS1BffR@!uI$dRz!uH%Q19!uI&w!uI'Q1:PYPZQ1:P[Q1:!x38E!u@%S=sYP%1dS1C%1AS1DPxPEPlPbPPPEPuPEGH3VP9Q0_%1xS1E'dQ1:P@PePdPAP@PPP@GHPy1G1k9?6p!u2+yP@PkO1fmRlPEPlfkRtfjR{!u1$hS1F!u2'B!u2&@!z<+z!z<$zP[Pz!u/8y!u/%X/uBQ19PyPjPkPBPyQ1:PyGHP1PzP{PGPpPwP{PBP{GHP9Q19/AtRz#P1:wtRs#PA7EtgR|#h/Ezg03W1Rz'R%pj#g%n|/Esg03YnS1G'Eg03[5Rs'm5Jz3jfnR|1G1h9?6n!ud+|PtPhO1frRrP{PrfpS1HfoR}P1P4!#A0$O2flS1I!ud&t!ud+y!ud$yP[Py!ud8|E>P11AEl#P1:E|RE#PQ1F?7|oRq#h1A@|'E/Rz%ph#g%nq/EEQ1G'E/ms!t|$P91:@}RE#PA7y}URq#hQ1B/A}'E%pn!sY67JzPr1G1F9?6f!uV+rP}PFO1fvREP|PEftS1JfsRq!x=$qR~!x<'H!uV&}!uV+l!uV$lP[Pl!uV8r!x<$1F/:~#PQ1I?7rmS1F#h1A{r'E%pF#gQ1F#n1:yr'!tx2Q02P8fuRzPrPCO19^Oz1T6NRsPOA7}z5S02Q05P1Q1H!#Ad$Q02P11AlzQ1I/:z!#Cv+Ats1CS!#<D&fyS02fwRs=7~uS1GPEPu!#MG%1J!ub%S1FPqP4O1S1KPVPr!ug%S1LPX%3i!}4%@P[Q1AP\!#[`,!um'!u1$~Q02PsPE!t#%FQ1KPVQ1LPXQ1H!sh%HP[Q1H!vW8zP~PCQ1HP}P|A7lqCPm1Atq1:{qPyPBPCPnO2PNPCPjO2P:P6O=Q1IP91T751G6NPOQ1G%94RNP7PrP4P7O2Q1GP71A}s1:|s!#IR$4iP11T2uP8PP1G:PPOf{RiQ1:57zR5Q05P=PEP6P=O2P5P=1AqiRj1:riRn!sg%6x[X181G2uPDPPPOP5PxP1PEPxP1!sZ$1PjPnDCDi9?xxX2D1TAAPOQ1JfzRn;7xRjPAPPCbRuPzPAPPO2RBPjPPPr%Fn1:~nD[R~!#XA$1e8APuPyPhPBP~PpPSCrFM!#TO'!#TW<!s-%0W3!v|%fxR~f|RBPjQ02PxO1Ry!~$$s!xj%PE!{M&z!#9:+ARX!#99$ARAP[Q1D!xe6W!#jt%O3Q00P?PnA7r~PPsPP!ys$2PzP1P2O2Q1JP2!#\R%NP7Pq!wd%%34Q1;!#;n$4Q1<%14Q1=1@17!#]^'PiPqPi!yr$P1P:!yq$:O2PzP:O1Q09!t$$!}a$0:%3rR7PYQ0<%2rRNQ0>%1rRrQ0@!#;>,P1PBPjPyP1P=!uu$=!uu$=!tl%Q0Y!u+$:!u+$0Z/DXPYQ0\PAQ0^Q1D1@12!tj%P9f}RAP5PnQ1:O1P6P<DQP~P6P<O2PsP<!sw$6Q0`!u+$=P:O2Q0aPxPYQ0bPxQ0cQ1EP6P:CqF;FBp+01@RxPsPxPAPBP1PKPnP1PK!~B%K!#aP&IP<P~PI!#d^$IPEPY%2I%2ER~%1I%1EREQ0DEIH0<FB!ui,xA7sAwPBPwO1P4PKDQPiP2PHO2PnPH!t&$2Q0gPI!t:$PIO2Q0hPwPYQ0iPwQ0kPwP2PIC<F;FBP9PBP:PJO2PiPJ!sc$:Q0m!u#$H!u#%nQ19PYQ0oQ19Q0pQ19P:PKC<F;EWp+01DRHPiPHp+01BR2p+01AR=P1PWf~R5P1PWO2PAPW!w['tPJPBPQPJO2Q0;PnPYQ0=PnQ0?%1nRJQ0L3VF;!ug/5P<!sk$5PM!sk$IQ0EPQPA!#FE$Q0uP@PYQ0vP@Q0wP@PIPQ!tl%P9PxPT!sZ$KQ0FPWP5!#F;$Q0yQ1B'\PYQ0zQ1BQ0{Q1B1@KWEfFap+01HRIPxPIp+01FR<p+01ERBP1P^p+01CRX!#kd%2P^!}6$!uP$GPTP=!#EN$Q0AP5PYQ0BP5Q0!#`n$T!w8%!uN,O!#^'$P2P^PSO2Q0|P{PYQ0~P{Q11P{PQPSC<F;DiP9POPWPRP^CbPXPRP^O2Q13PtPYQ15PtQ17PtPWP^C<F;p+01LRtPHPtp+01JR!wa$IR2P1P!uR$G!w]$aO2P<Pa!w]'HP]PBPcP]O2Q0IP!|9$JPXQ0KPXP1P]!u35T!s[$C=P<PaPcO2%3aP|PYQ1>P|Q1?P|PSPcC<F;P9P5P_PaO2Q0NP}PYQ0OP}PvP}P^PaC<J0:p+01PR}PIP}p+01NR!w@$MRvP1Pdp+01KR|!#jx%H!#jx+bP`P2PbP`O2R2Q0R!w9%SP5Q0T!w9$`!u+2%3dP7PY%2dPNQ1CPrPcPbCqJ0EP9Q0[/\qPYQ0]PqQ0_Pq1@adEfp+01TRqPtPqp+01RR!vt$QRrP1Ppp+01ORNP1PpO2PIPp!ti'kPePvPkPeO2Q0V!v6$0WP|Q0XP|P1Pe!tg2Q0V/\zPY%2pP~%1pPE1@bkEIP9Q0j=sYsQ0lPsPdPpC!zK$XRsP}Psp+01VR!vQ$URbP1Php+01SREP1PhO2!#C~$!t_%gPGPrPgPGO2Q0dPNPYQ0ePNQ0fPNP1PG!t_4eQ025sY%1hPJPkPgCqP9Q0x/ui1@p!t6$\RiPqPip+01ZR!v;$YR9P1PFp+01WRkP1PFO2!#B{$!tS%UPoPbPUPoO2Q0qPEPYQ0rPEQ0!#?N$o!tS4s/uA1@gUP?p+01_RUPkPUp+01]PiP1PCPqP1PCO2P9PC!t3'mPfPsPmPfO2Q14!z-$16P}Q18P}P1Pf!t3-!vN%^RCP}PC!u@%[RqPhPmK0FP9PhPmO2R9PsPmO1RsPOPhPfPFCb!tW$fPFO2RfQ0}%3bRk'DRgQ10%2bRA54YRoQ12%1bRb'dRE1@hFRF'0RJ'0RG'0RN'0Rr'0Rt!#ob$PCP}PiPqP=PhPmPnPpN909P9P~PdPsPtPaPUPrP^PfPNPWPgPGP;!tG$xPkPKP{E{PoPJPY!tO$xPAP:P@E{PEPFP>!tV$xPbP6PwE{P1!#mt-LW^!#ms?W!sD@Z!sD?XN2!#nv\XSy!sc@R!sD@[!t%@0?!sE71!#BC/X4zN;0JWcWJ!t8@I!sD=b3WMW]!sd@V!sD@Y!sD@O!sD@Q!sD@U!sD@T!v\@iDXj8K08PpPOPaPeP_Pc!#oS$L0KQ0PQ0UCkeX53N;0LWbWa!t:@`!sD>XW\!sD=!#s@'AxSMWPcPQPcPRP^!#s?%!#KV1S!#tx?W:W;W_WhWgP1K06WHXD0P1O1XD0o"). Qed.
End HC.
