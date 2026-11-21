(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require AW_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset AllocWalkKit AW_DepotFrame AW_Leaves AW_Efs AW_Populate AW_Gfa AW_MaybeRelease.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AllocTacX.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AW_Rta2 () := KReplay.lz_vm "#%hrK47Corelib7Numbers7BinNums8positive02!sK=1Z02C56Stdlib6ZArith6BinInt1Z3mulC89OSSVerify6Proofs:boost_json:fuzz_parse3lib2As8AllocRep5akobjC13~~~!t0=add!t0UsShadow5aceil!t0B2le!sB<6moduloI!v<+4Init5Logic3and00C!sA75proj1!vr>N02I45stdpp9bitvector;definitions2bv!t&49Datatypes6length!u,=to_nat!u,82eq00!s`=of!s`#!x_>ax!sC34Znat5Nat2Z7inj_iff!v487iff_symK!te;1C4!t$&9micromega;ZifyClasses5mkrel!sKB7rew!tQ$!tt=9is_nonneg!u^<8max_spec!yM>!v~:or!x$#!tr49SatDivModCZ_mod!tP&!s,&K!sW5=RingM!s4'5Psatz!}_/!y&23nat!sE#!snI6!sO6:ZM!vo,!uc$!|z$!s{8!sR;3!tn<4list01!sFB2I!sFA0!tZ66VarMap1!t+$!sD>2!sD@3I!sD?0I!vwC7Formula!tq87Env!sT#5PExpr!tv8!sI2!x8E!t?+!st75Tauto8G!sJ'6!w><6option!#8Q>!#8v+!u/F5C!t\<B!t\&C!yf@=Z!sT$CheckerC!w\<4find!sqAC!sq0_sound!#:M[9!#:M#_env!#9G%!tI5!#4[1app!waF4!sJF3!sJF5!sJF8I!#=~>0!#>D?1I!#4%?!#5J68!v-#Inst@!#9M$_!#:6$_eq!y;<5eKind!~d=uni!~d9!se%4kind!#3l>!sf$1!|kD3Op2!#4{-!{y=!#3>6!#5t:0!#7d@1!#6gM!u9J5!vh=bool!t`>!sF%1!#BZ[;!#BZ#_facts!|?&7!sqN8HeapCeil5h!#CJE3sub!txP3Lib3Mem7mem_i!~1'!vK=prod!vK?!sF$1!tQT5Frame5munch!uY&!siZwmono!#4G&!tt'5Lists7!s+#Def6firstn!t0T4TacX2wz!t+%c!y#R7AW_Rta2:rcopy_post!u``3mkR!u^'!#Gh>7Z_to_bv!t5T8PropExec7seg_rom!t<%!#5r?3!#;^=3P!|V$!yQ1!#DZ$9False_!#:f-!wy%4!s+#9nth_errorI!#=SB0!#=uC1!#J'9x!sb4!s@,!sZ4Peano2le!#8;,!t~->!t~+_None!}FX2wa!y4Z4Step=wa_of_!xi'!{u2!uU-6eq_sym!trUArr;u32arr_read!t{Z!ua#3le4!{/G9bv_signed!{1]6v_addi!t='ELinuxProcessSemantics?!s<26BvBase@le_bytes!vs#word!t}A:bv_extract!t7;5Riscv7Prelude4sext!v`X4sx32!wH^@!tH#!t{'_!wU-!yG68eq!}^#_r!#9z;7add_0_r!v=A;bv_un!x>Z!{J$D!se'!{M'!xI#!y_G6!sQ&!y\\9b!sf#!wu$!w;Y8!u6#Fast<sf_load_goal!#6^&!yC?5Instr5i!s+#06K!yoItree!#='U6MState2MS!|>A!t<19bvmap_set!tlA3Sem4cor!#Mc#!}?I>!s_$!sE+>machine_result!uXV!wN+7sf_refl!x>c?sf_!wb#all!xF$!xAT8C!vSD5alu64!z|]8alu!#5\/!~D:trans!v%]8sf_congT!vrZ!#@t$9stk_spli!|yW2As<!#Ql#WalkKit!ss$cell!#HW%K!tbTC!sc#4!si#05!v]'!#A#3!#R\-;!#_l%_rev!#>j6@!#Eb$_!#cO$_le!xnFlow32!#:[Q=!#5z#!#:`&C!}#Y<write!so#memC3!#6b$7tac!sC$f_equal_help!#?R;in!#6vT!w<%7!w<#_a!#G[[!sk$5csize!siZ!#9l$rw!yY%_store_ok!tb]!sw$>!sn%!#?@$4'!#40b=sf!th&!#9IW7!tH]@!#5R,!tP$!v4`!w,+b!#]C#!xc_:!wv&!xh,!#SE;pow!~s`2!uj_A!yq4!zg`!#U$%!ss&c!~W%!vf_6!sj`!xE2!#3Q#!t]`8!~o$upd!#8hX9!#8h#TacX9region_lb!spc;!sp&rank!tdku!tdZ!#f-2!#<1[!ta,A!ta&side_intro!vOk!sx#!src:!sr&fam!tekpsep!sr&!#A\7!#=o$f!#w1B!#;?#ff!sLB9and_morp!#zn<>pow_po!#w\C:!sN#!#vO;!#ng1!#8AT3Mem:!#@@'!#P<%!#e^C!#vp%7!#Y]8or!#h|3!s@,2!tqUArr<!#WF%fram!#3q[!#E\#6in!z`Z!sj,;!#cc#!#5N`!so%!#ci#!sof!#G5#!sm-!#>eM5!#OrH6bv_eqb!$'F;4neg!#h~T!#SD/bra!vu#pc!v%Z!#Kv31!#3CX6AW_Gfa@!#;#'C4_!#Z5,!ux;3app!t9Z:!{E&!sh#!u%X;AW_Populate!#`Z&cons!ste!ti'ni!#EX'!~86!$2W#!#TcP4Spec6StrFun<!#MQ%S_nt!#mK&!#C_;!zD#!y1S7ZBridge6zr!#<+Y!sl/Binr64!#^2'!sx-!#67&4Bool!s'$=!{~#_true!$2c;3no!$3d<7eqb_neq!#{PE7!tM6>!tM$f!#kZ$!$2`4!$5;+!t5#!#zb,!#R6,:!wc&all!vPT2Nd:ex!#?G$F!#Gx[!#X9#evt_done!}<B7nat!#QQX!#qA$st!#HyZ3Arr6!|<%!u__3evt!|x'!#<uH4!#>WD!sIF3!#VHY=ov!#mM#!#W5&!#f,>D!#f]&obliga!s:#_1K!$>4C1!#dKN!#?GT!#L=#8!#8<&!yv'!v'X8!#OU'!#DO@3inj!#E@B!$0;#!$:\K5!#4|TCodeTab;!|h#step_c!#JuY5ASegs5asegs!zyJ!$'P#1!$?w=6inj_l!#vpT!#i`%5Wrd6!#FM%I!#ACL0I!#3=S!#V1,0!#:Y8!uL-8!uL#succ!$2x>7Inj_Z_Z!$-FA2!wmY7ct!#Zz#!xYY!$/2'3mem!v}'!#:r55!#~E#!#|C86nth_ok!$#d=N!~QC!w{&msize03!{a\8ct_entry!y?G!#oL+0I!#6%Y!#oL&s!za#00!uZHaluop!#Mg94True!$4?T!#R|+=!#R|%tabled!x>>!t8%!u$H;!#I>%cond!zcU!#X:'?REGIONINFO_SIZE!tk&!suR!#mK/6hidden!}^'!$1mZ=rta_tail!$1p-!{N63!#m?9!#Sv&!sE#!v<[5wli!}z[!#K;%<!si$!#nm%!u<'!#=T?!#}~,_i!#^Y#ge!$%pD!$V-#us!#F`<di!sK$!#Ih<div!sC<=mod!#Y>#!#h'$!sM@neg!sM25!#6x$PreO!s/#1Z;!t[#0_r_ext!sL>!st#!sL'!#9$S!#E?#:!#VB$!#zH]!sn&!#VA$!sn^!#;x%<!#L=5!sqS!$0k-slli!#;V8!#K;+shiftl!$/zIz!w3W!t`+5!$,&-!slS!#DP#F!$,{6_r!vIc7!#}Z%!}8'!#;['!#b&&Morphisms:respectful!sM?J!xz#exive_eq_dom_!s7+!s]?I!s],!s0,proxy!s\?@!sR0per!sS??eq!sL&!t#ENR!t#,artial_app!#e'$ism!sa5?Rel!#Jp#!s6&<eq_Symmetric!sUE8s!sR%y!#4V<sub!~S#!$Ctaloo!#hW>!$dV#2!#=h\!#if&hul!#ZO&!#3_S!#FQ,1!#4K_=disjoint_f!$Dc'!sqZ7out!#f7c6!x1#fp!sj`<!#f{%eaken!sp`!#gm%!$0k$!#=`W!#CO-x_not_in_s!#smW3!#hc2!te[!#6-'!#dn+!#Uu#!$&9[!$DG%8!#6gZ!#g<&6sf_ad2!smc=!sm$dr_zto!$Gv'!st\@!$'j&8_direc!vC_!#q~+8!w~_!$-D/8!$-Dc;sf_pair_eq1!srn!x6[!#@|%=!#=Z&plus0!sra;lit!#>J#!#Ao'!#q5M3!v+]7sf_btg!$EPc:sf!~L%MR!v#[!#9$#X<!~P+!#o/X!#42+?stk_of_!#_{1!ssY!#us#merg!$#~Y?AW_MaybeRelease9mrto!$ZTZ!sv<!$vX#!zF`6ret!#v<\!{3'!sk%_ev!#:|[!#6p14!smc?!$M0%!#5ya!#J%-lu!$Fq'!$VfBconca!#K?^b!t<,!~vN1!t@]7v_aui!#|5\!sn+b!sn/!u2N!#kIT5Image:ro!#9m%!#@P[!sn$>ro!#46%i!s5#!srZ!#m,%o!#40_2FP!y[#li!$r@#!tW^@!uJ+!#B+0!z~@5!$';#!|8`a!$BP[!#R@1n!#R@3!$%v2fst!sC=s!#Z{=4lan!$a@`sltu!u]c!$SS#!sog!t^#r!#Y3Ir!t~c!t7+!~>N9!#ivY!$ZD2!%62<3ltb!sC=b2z!umT!$'B&:!x[%_!sj#!wnY!sp'7zr!$fz$!sma9zr_!x9&!soaA!#`O-_l!}o]!th/!sm#_l!sob6zr!w6f;!t]+!$17c?zb_shl_shr!vG/!{<[s_svc_pending!slZ4step!}:ND!$[dD4exec!vBT!#D6&interp_eff!#M5dft!~Q&!#3q@!#3EQ3!snj2!$hlD3!u}#6!sNJ1!sNJ7!#ioH5!$jd#!wDT3Mem8!$mg#u64!{GA!tf,;amo_al!$qA$!sTD9!sT#!$1m$!tlO!#]O#sAtom!wr#!t@-!$;O-!xHX:fetch!$w8%!shX8is_ecal!#nSBDecodeC:d!s-$_any!|,[8!$0I#g!#N+&!~aNE!y~J8!#<8;8eqb!#sA$!sH;9add_asso!#3OT!#F5$!#Y^&lit_self!xN'!$w<Bnot!$waE!#C}U!#RF1fol!$qQT!$q%T!#e1%stk_r!#UL$!#6SY2Nd;!$AH'15!slZ!$AI+!z<#!sk_7!sk#cu!}n'!y^;?!#x9$_mul_pow!#P0T!#H52!#F5U:!w|ZB!#]m'!#^d#por!#e|[Arr@!$M#%!src!tj%F!yh#!sq+_!#p~&!x@[S!$eo/!$X|-!#tZ67!$rF%!x;U!#[h01!x9N!$4}$3!sRH!$8,$4!#:gD2w0!#3NZ6w0!#fvP!$55/!%:b,7Program6Basics4impl!#M~J<Mem!#XH#Type7Segment!%^'-!#{<:>!t4#_!#|Y'!#=]R!$3U+AINS!$}u%!%L~=N!$:RO:!sRN5!sRN7!sRG6awidth02I!#<SH0!um=!%LG+0!zIG1!zI]1!zI,".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv01Z37Corelib4Init9Datatypesk44list3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsm3dmachine_state3h5LinuxProcessSemantics5Riscv7Preludeqa5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~t83mem37Corelib4Init5Logichhc3and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~hj75asegs46Stdlib6ZArith6BinInt1Zhnb3addhnb3mulk46optionk44prodhhc2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~hr76u32arr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hvb2wzk44Nonek44consk43nilk44pairhhc2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~ild3mkRild5munchild5wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ir22MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~iv57mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~jja7seg_romhf7Z_to_bvk43nathnb6to_nat37Corelib5Lists7ListDefjpe6firstn89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AW_Rta24HCW2~~~~~~jrfarcopy_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~kgf3evtild3stkhnb2lehnb2lthnb3sub79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~kmb4cellkmb2C8hfbbv_unsignedkmb2C4k43app79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~ksf5wlistir26ret_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~li08rw_cells36Stdlib5Lists4Listlm73revksf5akobjt85aceilhnb6modulohhc2ork46length69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~lqbbkNumClasseslqbekFreeArraySizet86AHI_LOksf5AINSTjpe3mapksf7AGOT_LOksf9AGOT_VALSksf7APAGESZ" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Definition rcopy_post : ltac2:(zQ "70!h9!jc!k1!lc!pa!t0!hh6>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$6>2CH$2>1D$2>1n$2>2ws@1$3@1$1@1$0#k0>0$4P") := ltac2:(zQ "hc1!h9!jc!k1!hj0!hn2!hp3!hpa!hq1!hqa!hr1!pa!hv1!ij6!ijc!ik3!lc!ika!il0!il7!t0!hh6!ip9!iq0!iq9!iuf!jif!jn9!jo4&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2t0@1$1@1$0#k0\2t1@1$1@1$0#k0\2t2@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2a0@1$1@1$0#k0\2a2@1$1@1$0#k0\2a3@1$1@1$0#k0\2a4@1$1@1$0#k0\2a5@1$1@1$0#k0\2a6@1$1@1$0#k0\2a7@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\2t3@1$1@1$0#k0\2t4@1$1@1$0#k0\2t5@1$1@1$0#k0\2t6@1$1@1$0#k0\1F@2$h3@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1m$h4\2CH$2\1D$2\1n$2\2ws@1$f@1$1@1$0#k0\3ms'$a@2$9@1$1@1$0#k0\2a1@1$1@1$0#k0@2$9~0\2m'~0@2$3@3$h2$a^3@7$h8@hf$h5^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^2^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3@1$c@2$5^7@2$6+4^5^h2^h1@1$c@2$5^6@2$6+4^5^h0^f^e^d^c^b^a@2$hb@1$0#k0+mrum8^9@1$d@1$1@1$0#k0^1@1$ha$4@2$3@3$h6@3$e@2$8$2$2@4$h1$2$2^6@2$5^6@2$6+4^5@1$h0@2$8$2$2^8^1@2$3@3$h7$4^8^1@2$3@2$h9$4^1@2$3@4$b$4^1^6^4@4$b$4^1^7^4").

Section CopyLoop.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (CH D n : Z) (ws : list word).
  Hypothesis CHR : ltac2:(zQ "90!hj0!hpa!il7!k1!lo1!loa!hp3!kl8!lp2@2$0@3$4?5HCEIL?2CH@2$1+4?1n@2$0@2$7@2$6?2CH@2$1+4?1n@1$5?5HCEIL@3$2$3@2$8?2CH+4Z").
  Hypothesis DR : ltac2:(zQ "80!hj0!kl8!il7!k1!loa!hp3!lp2!hpa@2$0@2$1+hgg0?1D@2$0@2$1@2$5?1D@2$7+4?1n@1$4?5HCEIL@3$2$3@2$6?1D+4Z").
  Hypothesis DISJ : ltac2:(zQ "40!hp3!kl8!hpa!lpc@2$3@2$1@2$0?2CH@2$2+4?1n?1D@2$1@2$0?1D@2$2+4?1n?2CH").
  Hypothesis NR : ltac2:(zQ "10!kle@2$0Z?1n"). Hypothesis WSL : ltac2:(zQ "60!lq2!joe!il7!h9!jp4!jc@3$2$1@2$0@1$5@1$3#k0?2ws@1$4?1n").

  Let CHE : 4096 <= CH /\ CH + 4 * n <= aceil. Proof. exact (akobj_env _ _ (proj1 CHR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Lemma rcopy_loop : ltac2:(zQ "i00!k1!hn2!hp3!hpa!h9!ij6!jc!joe!hqa!hv1!jp4!ijc!ik3!ika!il0!hj0!il7!jr5!kg1!hh6!kka!ip9!iq0!kl1!iq9!iuf!jif!jn9!kl8!kle!km4!jo4>1k$7>1i$0>2a1@1$6@1$4#k0>2m1$h3>0@3$h0$7@1$a@2$he?1n^3^4>0@2$f@2$hcZ^4@2$hd^4?1n>0@2$ha$1^3>0@3$h6@3$c@2$8$0$0@4$e$0$0?1D@2$2?1D@2$3+4?1n@1$d@2$8$0$0?1m^4>0@3$h8$1?1m^5>0@4$h7$1^6@2$2?1D@2$3+4^8@2$2?1D@2$3+4?1n>0@4$9$1^7?1D@3$h1@1$6@1$4#k0@1$a^9?2ws>0@4$9$1^8?2CH?2ws@3$h4$1@i3$h2?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1@1$5@2$2?2CH@2$3+4?1n?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5?2s7?2s8?3s10?3s11?2t3?2t4?2t5?2t6?1F?2fc?1m?2CH?1D?1n?2ws@7$h9@hf$h5?2ra?2sp?2gp?2tp?2t0?2t1?2t2?2s0?2s1@1$5@2$2?2CH@2$3+4?1n^a?2a2?2a3?2a4?2a5?2a6?2a7?2s2?2s3?2s4?2s5@1$5@2$2?2CH@2$3+4^b?2s7?2s8@1$5@2$2?1D@2$3+4^b?3s10?3s11?2t3?2t4?2t5?2t6?1F@2$hf@1$4#k0+mrul4?2fc@1$b@1$6@1$4#k0^9@1$hb$1").
  Proof.
    unfold AHI_LO in *. acb.
    induction k as [|k IH]; intros i a1 m1 HK HI MI1 MU1 WM1 JK ARR SRC. { exfalso. clear - HK HI; try acb. lia. }
    unfold wz.
    (* [comment removed for export] *)
    assert (NTH : exists w, nth_error ws (Z.to_nat i) = Some w).
    { destruct (nth_error ws (Z.to_nat i)) as [w|] eqn:E; [exists w; reflexivity|]. exfalso. apply nth_error_None in E. clear - E HI WSL; try acb. lia. }
    destruct NTH as [w NTH].
    pose proof (u32arr_read asegs _ _ _ i w (Z_to_bv 64 (CH + 4 * i)) SRC NTH ltac:(hci; clear - HI; try acb; lia) ltac:(hci; symmetry; apply wa_of_Z_to_bv; clear - CHR HI; try acb; aunf; lia)) as RD.
    (* [comment removed for export] *)
    step. clear RD. step.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (D + 4 * i + 4) _ JK ltac:(hci; clear - HI; try acb; lia)) as [SK1 SK2]. clear JK.
    destruct (stk_cells _ _ _ SK1 ltac:(hci; clear; lia)) as [jw JW]. clear SK1.
    replace (D + 4 * i + 4 - (D + 4 * i)) with 4 in JW by lia. change (Z.to_nat 4) with 4%nat in JW.
    assert (LF : length (firstn (Z.to_nat i) ws) = Z.to_nat i) by (rewrite firstn_length_le; [reflexivity| clear - WSL HI; try acb; lia]).
    remember (D + 4 * i) as DD eqn:ED in JW |- *.
    (* [comment removed for export] *)
    step. subst DD.
    (* [comment removed for export] *)
    step. step.
    apply rw_cells_C4_sx32 in JW.
    assert (ARR' : u32arr asegs m0 D (firstn (Z.to_nat (i + 1)) ws)).
    { replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by (clear - HI; try acb; lia).
      rewrite (firstn_S_nth _ _ w NTH). apply u32arr_app. split; [exact ARR|]. rewrite LF.
      replace (D + 4 * Z.of_nat (Z.to_nat i)) with (D + 4 * i) by (clear - HI; try acb; lia).
      apply u32arr_cons. split; [exact JW|]. apply u32arr_nil. clear - DR HI; try acb. aunf; lia. }
    clear ARR JW LF.
    if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      replace (CH + 4 * i + 4) with (CH + 4 * (i + 1)) in * by (clear; lia).
      replace (D + 4 * i + 4) with (D + 4 * (i + 1)) in * by (clear; lia).
      eapply (IH (i + 1)); try eassumption. { clear - HK HI K; try acb; lia. }
      { revert K. rewrite ?unsigned_lit by (clear - HI NR CHR DR; try acb; aunf; lia). clear - HI; try acb. intros K. lia. }
    - (* [comment removed for export] *)
      assert (i + 1 = n) as EQ by (revert K; rewrite ?unsigned_lit by (clear - HI NR CHR DR; try acb; aunf; lia); clear - HI; try acb; intros K; lia).
      replace (CH + 4 * i + 4) with (CH + 4 * (i + 1)) in * by (clear; lia).
      replace (D + 4 * i + 4) with (D + 4 * (i + 1)) in * by (clear; lia).
      rewrite EQ in ARR' |- *. rewrite <- WSL, firstn_all in ARR'.
      apply evt_done. unfold rcopy_post. do 2 eexists.
      split; [reflexivity|]. split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ARR'| exact SRC].
  Qed.
End CopyLoop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rta_tail_post : ltac2:(zQ "70!h9!jc!k1!lc!pa!t0!hh6>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$6>2lo$2>1R$2>2CH$2>3FAB$2>2nf$2>1n$2>3mfa$2>2au$2>2mu$2>2ws@1$3@1$1@1$0#k0>2fl@1$3$2>0$4P") := ltac2:(zQ "i61!h9!jc!k1!hr1!ik3!hp3!kq7!hj0!hn2!ij6!kqf!hqa!il0!kl1!hpa!kr5!lc!ika!hq1!pa!hv1!ks3!ijc!ks9!il7!t0!lgd!hh6!ip9!iq0!iq9!iuf!lh6!jif!jn9!llb!lna!km4&>0@1$1@1$0#k0@1$h2@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h9@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\1m$hb\2lo$2\1R$2\2CH$2\3FAB$2\2nf$2\1n$2\3mfa$2\2au$2\2mu$2\2ws@1$h0@1$1@1$0#k0\2fl@1$h0$2\3ms'$h3@2$3@1$1@1$0#k0\2t0@1$1@1$0#k0@2$3@1$1@1$0#k0\2t1@1$1@1$0#k0@2$3@1$1@1$0#k0\2t2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a0@1$1@1$0#k0@2$3@1$1@1$0#k0\2a1@1$1@1$0#k0@2$3@1$1@1$0#k0\2a2@1$1@1$0#k0@2$3@1$1@1$0#k0\2a3@1$1@1$0#k0@2$3@1$1@1$0#k0\2a4@1$1@1$0#k0@2$3@1$1@1$0#k0\2a5@1$1@1$0#k0@2$3@1$1@1$0#k0\2a6@1$1@1$0#k0@2$3@1$1@1$0#k0\2a7@1$1@1$0#k0@2$3@1$1@1$0#k0\2t3@1$1@1$0#k0@2$3@1$1@1$0#k0\2t4@1$1@1$0#k0@2$3@1$1@1$0#k0\2t5@1$1@1$0#k0@2$3@1$1@1$0#k0\2t6@1$1@1$0#k0@2$3~0\2m'~0@2$7@3$h8$h3^h1@7$hf@hf$hc^if^ie^id^ic^h0^f^e^ib^ia^d^c^b^a^9^8^7^6^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^5^4^3^2^hf@1$i0^if^he@1$h6@1$1@1$0#k0^1@1$i2$8@2$7@3$hd@3$4@2$b$2$2@4$c$2$2@2$i5@2$f@1$0#k0^ie+t0@2$f@1$0#k0^ie@3$4@2$b$2$2@4$c$2$2^hb@2$5^hb+8@3$4@2$b$2$2@4$c$2$2@2$5^hb+h0@2$5^hb+h8@3$4@2$b$2$2@4$c$2$2@2$5^hb+l0@2$5^hb+l8@3$4@2$b$2$2@4$c$2$2@2$5^h9@2$e+4^h8@2$5^h9@2$e+4@2$5^h8^h7@1$h1@2$b$2$2^hd^1@2$7@3$he$8^hd^1@2$7@2$i1$8^1@2$7@4$d$8^1^hc@2$f@1$0#k0^ie@2$7@4$i3$8^1^hb@3$4$6@1$a@1$9Z@3$4$6@1$h5@1$9Z@3$4$6@1$h5@1$9Z@3$4$6@1$a@1$9@2$5^h8^h7@3$4$6@1$a@1$9^h6@3$4$6@1$a@1$9^h5@3$4$6@1$a@1$9Z@3$4$6@1$a@1$9^h4@3$4$6@1$a@1$9Z@1$h1$6@2$7@4$d$8^1@2$5^hb+k5@2$5^hb+o0@2$7@4$h4$8^1^h9@3$h7@1$1@1$0#k0@1$ha@2$i4$2^h2^h3@2$7@4$d$8^1@2$5^h9@2$e+4@2$5^h8^h7@2$5^h9^h6@4$h4$8^1^ha^h3").

Section Tail.
  Variables (ra sp gp tp : word) (rax t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo sb ARI c CH FAB nf n mfa au mu : Z) (ws : list word) (fl : list Z) (j16 : list byte).
  Let R := ARI + REGIONINFO_SIZE * c.
  Hypothesis MI : ltac2:(zQ "20!hn2!jif@2$1$0?1m").
  Hypothesis ST : ltac2:(zQ "50!h9!hn2!kl1!hp3!kr5@4$2$1?1m?2lo@2$3@2$4@1$0#k0?2sp-o0").
  Hypothesis LO : ltac2:(zQ "20!loa!kl8@2$1@1$0?5HCEIL?2lo").  Hypothesis HI : ltac2:(zQ "40!h9!hp3!kl8!kr5@2$2@2$1?2lo+t0@2$3@1$0#k0?2sp").
  Hypothesis CR : ltac2:(zQ "40!hj0!luc!kl8!kle@2$0@2$2+1?1c@2$3?1c$1"). Hypothesis NR : ltac2:(zQ "10!kl8@2$0+1?1n"). Hypothesis NFR : ltac2:(zQ "50!kl8!hj0!lvb!hp3!hpa@2$1@2$0Z?2nf@2$1@2$0@2$4+4@2$3?2nf?1n?3mfa@2$0?3mfa$2").
  Hypothesis ARIR : ltac2:(zQ "80!hj0!kl8!il7!k1!mgd!loa!hp3!lp2@2$0@2$1$4?3ARI@2$0@2$1@2$6?3ARI+hgg0@1$5?5HCEIL@3$2$3@2$7?3ARI+hgg0Z").
  Hypothesis CHR : ltac2:(zQ "90!hj0!hpa!il7!k1!lo1!loa!hp3!kl8!lp2@2$0@3$4?5HCEIL?2CH@2$1+4?1n@2$0@2$7@2$6?2CH@2$1+4?1n@1$5?5HCEIL@3$2$3@2$8?2CH+4Z").
  Hypothesis FABR : ltac2:(zQ "80!hj0!kl8!il7!k1!mgd!loa!hp3!lp2@2$0@2$1$4?3FAB@2$0@2$1@2$6?3FAB?3mfa@1$5?5HCEIL@3$2$3@2$7?3FAB+hgg0Z").
  Hypothesis SEP : hidden ((CH + 4 * n <= FAB + 4 * nf \/ FAB + 4 * (nf + n) <= CH) /\ (CH + 4 * n <= R \/ R + 128 <= CH) /\ (R + 128 <= FAB \/ FAB + mfa <= R)).
  Hypothesis IRI : ltac2:(zQ "90!kq7!ik3!ika!hn2!mh6!kqf!llb!ij6!hp3@4$6$3?1m@2$8$4+j0@3$1$0@1$5@1$7?3ARI@1$2$0").
  Hypothesis ISB : ltac2:(zQ "a0!kq7!ik3!ij6!ks3!ika!hn2!mh6!kqf!llb!hp3@4$8$5?1m@2$9$6+i0@3$1$0@1$7@1$2?2sb@3$1$0@1$3@1$2+vvvvvvvf@3$1$0@1$3@1$2Z@1$4$0").   (* [comment removed for export] *)
  Hypothesis GOT : ltac2:(zQ "90!k1!mhf!hn2!mi6!mj1!kqf!kq7!llb!ij6@4$7$2?1m$3@4$1$0$6\1v$0@1$5@1$8^1$4").
  Hypothesis PSC : ltac2:(zQ "80!kq7!ik3!ika!hn2!mje!kqf!llb!ij6@4$6$3?1m$4@3$1$0@1$5@1$7+hgg0@1$2$0").
  Hypothesis FR : rw_cells asegs m (bv_unsigned sp + -128)
                    [CB 16 j16; C8 (wz (R + 8)); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis RI : rw_cells asegs m R (rinfo_cells nf mfa au mu).
  Hypothesis RST : stk asegs m (R + 69) (R + 128).
  Hypothesis SRC : ltac2:(zQ "20!hn2!hv1@4$1$0?1m?2CH?2ws"). Hypothesis WSL : ltac2:(zQ "60!lq2!joe!il7!h9!jp4!jc@3$2$1@2$0@1$5@1$3#k0?2ws@1$4?1n").
  Hypothesis FARR : ltac2:(zQ "50!k1!hn2!lgd!hv1!lna@4$3$1?1m?3FAB@1$2@2$4$0?2fl"). Hypothesis FLL : ltac2:(zQ "50!lq2!joe!il7!k1!jp4@3$2$1@2$0$3?2fl@1$4?2nf").
  Hypothesis FAJ : ltac2:(zQ "40!hp3!hn2!kl1!hpa@4$2$1?1m@2$0?3FAB@2$3+4?2nf@2$0?3FAB?3mfa").

  Let CHE : 4096 <= CH /\ CH + 4 * n <= aceil. Proof. exact (akobj_env _ _ (proj1 CHR) ltac:(lia)). Qed.   (* [comment removed for export] *)
  Theorem rta_tail :
    evt asegs (rta_tail_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo R CH FAB nf n mfa au mu ws fl)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 (wz R) (wz nf) (wz 1) a1 a2 a3 a4 a5 a6 a7
               (wz c) mm (wz AINST) (wz n) (wz CH) (wz (nf + n)) (wz (2^61)) (wz FAB) (wz (2^60 + 2^20 - 1)) (wz (2^60)) t3 t4 t5 t6)
          F (Z_to_bv 64 0x6be3c) fc None m (seg_rom asegs)).
  Proof.
    unfold AHI_LO, kNumClasses, kFreeArraySize, REGIONINFO_SIZE, AINST, AGOT_LO, APAGESZ in *. unfold AGOT_VALS in GOT. cbn [map] in GOT.
    acb.
    change (1821656 + 48) with 1821704 in IRI. change (1821656 + 32) with 1821688 in ISB. unfold rinfo_cells, kWriterLock in RI.
    pose proof SEP as SEPx. destruct SEPx as [SEPx].
    assert (LFL : length (wlist (rev fl)) = Z.to_nat nf) by (rewrite wlist_length, length_rev; exact FLL).
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    assert (RR : 17594333495296 <= R /\ R + 128 <= aceil /\ R mod 128 = 0) by (subst R; clear - ARIR CR; try acb; Z.div_mod_to_equations; lia).
    pose proof (munch_refl [(bv_unsigned sp - 208, bv_unsigned sp); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88); (FAB + 4 * nf, FAB + 4 * (nf + n))]%Z m) as MU.
    pose proof (wmono_refl asegs m) as WM.
    assert (E128 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -128)) = bv_unsigned sp + -128) by (apply unsigned_lit; clear - SPR HI LO; try acb; lia).
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (FAB + 4 * (nf + n)) _ FAJ ltac:(hci; clear - NR NFR; try acb; lia)) as [CJ1 CJ2]. clear FAJ.
    assert (ARR0 : u32arr asegs m (FAB + 4 * nf) (firstn (Z.to_nat 0) ws)).
    { change (Z.to_nat 0) with 0%nat. cbn [firstn]. apply u32arr_nil. clear - FABR NFR NR; try acb; lia. }
    pose proof (munch_refl [(FAB + 4 * nf, FAB + 4 * nf + 4 * n)]%Z m) as MU0.
    unfold wz in *.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by (clear - NR NFR; try acb; lia). clear - NR; try acb. intros K. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. step.
    rewrite ?(unsigned_lit nf), ?(unsigned_lit n) by (clear - NR NFR FABR; try acb; lia).
    rewrite (Z.shiftl_mul_pow2 nf 2), (Z.shiftl_mul_pow2 n 2) by (clear; lia). change (2^2) with 4.
    replace (FAB + nf * 4) with (FAB + 4 * nf + 4 * 0) by (clear; lia). replace (CH + n * 4) with (CH + 4 * n) by (clear; lia).
    (* [comment removed for export] *)
    assert (DR' : 4096 <= FAB + 4 * nf /\ FAB + 4 * nf + 4 * n <= aceil /\ (FAB + 4 * nf) mod 4 = 0) by (clear - FABR NR NFR; try acb; Z.div_mod_to_equations; lia).
    assert (DISJ' : CH + 4 * n <= FAB + 4 * nf \/ FAB + 4 * nf + 4 * n <= CH) by (clear - SEPx NR NFR; try acb; lia).
    assert (NR' : 0 < n) by (clear - NR; try acb; lia).
    replace (Z_to_bv 64 CH) with (Z_to_bv 64 (CH + 4 * 0)) by (f_equal; clear; lia).
    replace (FAB + 4 * (nf + n)) with (FAB + 4 * nf + 4 * n) in CJ1 by (clear; lia).
    replace (FAB + 4 * nf) with (FAB + 4 * nf + 4 * 0) in CJ1 at 1 by (clear; lia).
    callD (rcopy_loop _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m CH (FAB + 4 * nf) n ws
             CHR DR' DISJ' NR' WSL (Z.to_nat n) 0 _ m ltac:(hci; rewrite Z.sub_0_r; reflexivity) ltac:(hci; clear - NR; try acb; lia) MI MU0 WM CJ1 ARR0 SRC).
    clear MU0.
    lazymatch goal with H : u32arr _ _ (FAB + 4 * nf) ws |- _ => rename H into DARR end.
    lazymatch goal with H : u32arr _ _ CH ws |- _ => rename H into SRC' end.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ _ (R + 80) _ RST ltac:(hci; clear; lia)) as [RS1 RS2]. clear RST.
    destruct (stk_split asegs _ _ (R + 88) _ RS2 ltac:(hci; clear; lia)) as [RS3 RS4]. clear RS2.
    destruct (stk_split asegs _ _ (R + 96) _ RS4 ltac:(hci; clear; lia)) as [RS5 RS6]. clear RS4.
    destruct (stk_cells _ _ _ RS3 ltac:(hci; clear; lia)) as [jst JST]. clear RS3.
    replace (R + 88 - (R + 80)) with 8 in JST by (clear; lia). change (Z.to_nat 8) with 8%nat in JST.
    (* [comment removed for export] *)
    step. step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      lazymatch goal with H : rw_cells _ mq R _ |- _ => rename H into RIq end;
      lazymatch goal with H : rw_cells _ mq (R + 80) _ |- _ => rename H into J80 end;
      lazymatch goal with H : stk _ mq lo _ |- _ => rename H into STq end;
      lazymatch goal with H : mem_inv _ mq |- _ => rename H into MIq end
    end.
    change ([C8 (Z_to_bv 64 1152921504606846976); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (nf + n)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au);
             C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)])
      with ([C8 (Z_to_bv 64 1152921504606846976); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 (nf + n))] ++
            [C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)]) in RIq.
    apply rw_cells_app in RIq. destruct RIq as [RIa RIbc]. apply rw_cells_app in RIbc. destruct RIbc as [RIb RIc].
    cbn [cells_size csize Nat.add] in RIb, RIc. change (Z.of_nat 16) with 16 in RIb, RIc. change (Z.of_nat 8) with 8 in RIc.
    replace (R + 16 + 8) with (R + 24) in RIc by (clear; lia).
    pose proof (stk_of_rw_cells asegs _ _ _ J80) as RS3. cbn [cells_size csize Nat.add] in RS3. change (Z.of_nat 8) with 8 in RS3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      assert (RS8 : stk asegs mq (R + 80) (R + 96)) by
        (eapply stk_merge; [exact RS3| replace (R + 80 + 8) with (R + 88) by (clear; lia); exact RS5| clear; lia])
    end.
    clear RS3 J80.
    assert (NFR' : 0 <= nf + n < 2^64) by (clear - NFR NR; try acb; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      callD (mrto_spec _ (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mq lo sb ARI c (nf + n)
               MIq ltac:(hci; rewrite E128; exact STq) LO ltac:(hci; rewrite E128; clear - HI; try acb; lia) eq_refl eq_refl eq_refl CR NFR' ARIR IRI ISB GOT PSC RIb RS8)
    end.
    (* [comment removed for export] *)
    do 15 step.
    zb_fold_lits.
    (* [comment removed for export] *)
    step. step. zb_fold_lits. step. if_cases K; zify_cond K. { deadK K. } clear K.
    (* [comment removed for export] *)
    step. zb_fold_lits. step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. zb_fold_lits. step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    match goal with |- context [v_sltu ?a ?b] => let v := eval vm_compute in (v_sltu a b) in change (v_sltu a b) with v end.
    rewrite ?unsigned_lit by (clear; lia). zb_fold_lits. rewrite ?unsigned_lit by (clear; lia). zb_fold_lits.
    (* [comment removed for export] *)
    assert (AL8 : R mod 8 = 0) by (clear - RR; try acb; Z.div_mod_to_equations; lia). assert (ALR : 0 <= R < 2^64) by (clear - RR; try acb; lia).
    astep. step. if_cases K; zify_cond K. { deadK K. } clear K.
    astep. fix_lit_store. step. if_cases K; zify_cond K. { deadK K. } clear K.
    step. if_cases K; zify_cond K. 2:{ deadK K. } clear K.
    step. if_cases K; zify_cond K. { deadK K. } clear K.
    (* [comment removed for export] *)
    do 13 step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      lazymatch goal with H : stk _ mq lo _ |- _ => release_frame FR H (bv_unsigned sp) end;
      assert (RIn : rw_cells asegs mq R [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (nf + n)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au);
                                       C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)]);
      [ change ([C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 (nf + n)); C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au);
                 C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)])
          with ([C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 (nf + n))] ++
                [C8 (Z_to_bv 64 mfa); C8 (Z_to_bv 64 au); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 mu); C8 (Z_to_bv 64 0)]);
        apply rw_cells_app; split; [assumption|]; apply rw_cells_app; split; cbn [cells_size csize Nat.add];
        [ change (Z.of_nat 16) with 16; assumption | change (Z.of_nat 16) with 16; change (Z.of_nat 8) with 8; replace (R + 16 + 8) with (R + 24) by (clear; lia); assumption ]
      | ];
      assert (RSTn : stk asegs mq (R + 69) (R + 128));
      [ eapply stk_merge; [eassumption| eapply stk_merge; [eassumption | eassumption | clear; lia] | clear; lia] | ];
      assert (FARRn : u32arr asegs mq FAB (wlist (rev fl) ++ ws));
      [ apply u32arr_app; split; [assumption|]; rewrite LFL; replace (FAB + 4 * Z.of_nat (Z.to_nat nf)) with (FAB + 4 * nf) by (clear - NFR; try acb; lia); assumption | ]
    end.
    apply evt_done. unfold rta_tail_post. do 15 eexists. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
    split; [exact RIn|]. split; [exact RSTn|]. split; [exact FARRn|]. split; [exact CJ2| assumption].
  Qed.
End Tail.

End HCW2.

