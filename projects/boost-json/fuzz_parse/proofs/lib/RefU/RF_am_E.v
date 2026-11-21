(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, lemmas added for the revision, the revision's auxiliary vector (auxv_keys). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import F_memcpy.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_E.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_am_A.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RF_am_E () := KReplay.lz_vm "#&+ZC46Stdlib5Lists4!s+#8nil_consC47Corelib4Init5Logic6eq_ind!sB88!sB%_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmap!tQ7:firstn_nilC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8HeapCeil;hceil_rangeC13~~~K!u#+7Numbers7BinNums8positive01!sKG2!sK=1Z02!t~Y5!t~$!tx%C5!v/&6ZArith6BinInt1Z2leI!w=73and00!tGP:!tG#Secret=hs!s-$!vK/!sr[7!sr&!u?B3pow!u\>t!uA]canary!uAi!sr%!yTC1N02I45stdpp9bitvector;definitions2bv00!x#29Datatypes6op!sL#!sH>4list00C!sh<length!vo<6to_natK!t-A1!yq82or00C8!vaN3Lib3Mem7mem_inv!xyB6of!tk#!tK9eq00!s`34Znat5Nat2Z7inj_iff!#4:77iff_sym!#3e'9micromega;ZifyClasses7rew!sj$!t5=9is_nonneg!u<<8max_spec!sH<>pow_po!spD:!sN#!sJ%!ww<3nat02K!uO5=RingM!s4'5Psatz!sO8:ZM!v',!tO$!xE$!#52-!y;8!sr76VarMap1t01!sD@2I!sD?0I!uEC7Formula00!t567Env!sT#5PExpr!tX8!sI2!ua=!}H'2!skE3!sIE7!z?65Tauto8B!uH&K!{c;1C!x%@=Z!sn$CheckerC!v}<4f!#=G#!sq?C!sq0_sound!~UT6MState<unsigned_li!#8X&!#5w?7Z_to_bv!sLA;bv_!t$'!{bK7!sOK5!ucP4RefU8F_memcpy;!s,%!~<#!ue'!vXS5Frame3mkR!sgZ8PropExec7seg_rom!sn%!#9J<prod!#9j3!z8'x!#8BU!xk&2MS!#;x%!uzTCells4cell05!#?#Badd!wxf!#7X#!w7Y!ue&6ret_pc!#>c2!#B{21!t-T2Nd;ex_introF15!ttZ2Nd:and_elimF6!sk^ex!sj%!tX\4!z[#8evt_mono!skZ3Mem8bytes_a!|y[4Step8rw_!z##s!y~Cmax!#?#A5mkapp!sKErel!#4;J6!#<6?3K!#;pK!#;M6!#9r%G!sJ'4!sJF3!sJF5!sJF6!sJF8K!#4b@1!#6[Y5w!z7^!si&munch!~J3!#Ok51!#4JT5RSegs5rsegs!#7bA!#D,#0I!#6^^0!t13!u;60!{:68!{:#Inst@!#I,$_!#Jy$_eq!zSD3Op205!#AC;5eKind!#:N<unit!#D$7!se%4kind!#Tn-!sf81!ttI3I!#We9?!s<2>!#Wu#!sE+=machine_state!t|#!v};!#VL+3!#<q74True!#G:7!#I0:0!#JL@!up7!sq;1!wL=bool!t9>!sF%!}XU3Arr4u64!#75&!tz'!#[X,9nth_error!#I-C1!#7u=ul!#9kW3le8!#:RZArr:!uR#_sp!#G6,!ws;!#9B#!sC03Nat!u/$!y?78iff_refl!xNN3!#4j?!#LA>3P!xM#!#:eJ4!sp>!#M3%5!#;~A;!#TL%_rev!uv,!y,%7!s+#Def5skipn!sD;6!#b$$!vr7sub!z$8app_nil_r!#dK7!#bx%!#W>+5!vy$8Peano!s}#!t%'!sF>8sub_diag!zKX:!#[6$_!zR+!#3I2!t9$2le!#7i,!u8-;!u8&all2!#eR>!#@d-!v=7l!sD77!wS$_!tG8:!sB%!tF;9!sE&!{g9add!sz8!v&&!s\#!vjW@!#D|&_ov_read!#Ep]2wa!~<'!#95X!tQ&_!tb$!|$B6!#EM#2!zD@mul!#^|Bmul!#;ZH1!sp>6!sp#le!tZ@!x-#!tZB!#O:R!#@c+:!#IB#_size!x-V5Agent=F_malloc_free?!#J?&_prefix!#DfZ!tm$8!sp%!#Ky[!sl0wf!sl`;!sl%!yy%!so_<!t]'!}2$!sp_?!ta-!ss^!}9#<!~,+!tccB!tc/!#k#%!sv_>!za,!tj-!~BA3inj!{0d9wr!v-#sub!vv^5!sk$!#9d&!#54H<MemImageType7Segment!#Jt@7Inj_Z_Z!#@y73not!#C`;;lt_ge_cas!#68Deq!#mK$!sL@9and_morph!#@TD4!#EG<!w=#!w7S!#ZS/3!#9I_5wview!tPP!#QD#:RM!yX$Rep5rmre!|ZW!so$;!so&Tree8rauxv_ok!ssWSpec6!sr%8s_!#y\/!sn[3ctx!tYcc!tY1!#i7?D!#i7,_in!#zC%!sY@:bv_modulus!x3`;rreg!sw#!#95X!su39!y&$_!v^Z!ss2=!ss%globa!#_w&c!swT7RF_am_E>ram_entr!#kV[!#6C$9!tn+>ctx_head!#ah/!sx_7active!sqg6usag!sph:unmap_seq!stg8bouncess!wGktail!wGl2wz!slgb!#N>%!#oQ_4!sjf1!uDV3!#c]':!#c]#!#VD#!sna!#e8#!sn[!#8}3:!#8}$li!}|'K!$8cG4tree01!$98H4sext!ueT!#vk'8alu_addi!vV`9stk_carv!#L'&!#>&I6BvBase=!#|+#le!#PE&!#9F>6bv!#M}W!uh+9b!sf#!vT$!tz%!#A0:9add_assoc!t;UStepFast6sf_ad!{C[!sm+=!sm$dr_ztobv!stc7sf!|9`!#ND%b!#aE$!#ADX3!#O{,b!#b6/!slY5c!#SAY!si,6c!#Pa^7StoreDj:chunk_disj!{r'!#Ht?8or!#Hs$!t@T3Arr;!#em#!#OC`!}x$6inside!usb8!us%in!uq'!~$?9bv_!#Dy$!}9<6shiftl!~K]7v_auip!$%YZ!#|X#F!#Fp'!$1[%!}A#_r!uYKconca!#7H]7b!u9/!#98@5Instr5i!s+#02!#3$\8sf!u-#gT!#7uW@!#7p&!vM#word!#6>b4!#5HZ!vb'6v!#;&-!#Q?X<write!uI#mem!$Ob;trans!y~Y=wa_of!y{'!tz'!t666eq!$C]#3!z9%7tac!to$f_equal_help!tQYD!#aj's!~/#_ok!$,|a>!sn%!x|%8'!sq_D!}=7!y/[!#<G-!tq%goa!#;WZ3Mem4sx32!}Y&!#7$S!#G-,2!tR^3le4!se^@sext_extract_!srY!#VX->c_mmap_counter!xj_@!zV+!#mt#at!#5cS6!sRN5!yf]<sf_branch_!#9k[!#7+31!#5Ub5v_lui!sldb!sl,!vlN1!t@]7!#7]$w!#5b&!#<Y>8bv_swrap!#MM@3Sem5low32!sNFalu32!u5^w!u5/!vQN;!xY`mu!#4w&!uXD7mul_div!t>^m!t>,!uXNB!{|]@!#7Y&8_direc!#:>_A!#;73!stZ!#G$&<stk_!#>h$!#G+&!v5N3!v5]7sf_btgt!#32e!#<F+!#Hf:7add_0_r!uQN:!#d?\:r!#LT#!$$j,!#XhG6bv_eqb!tF]Cr!y4+app!#Q[_3Tac>!st+merg!#N%Z!$N4%;lit!#KN#!tb]!yQ+:sf!#F6$M!$T&%!#i2^!$Pf%callZ3!vL^5dfa!~:'K!sgW4ib!$Q,#!tQ]6ibs!~p]!xa$!u}#_ct!$Q|%!sp^8!sp'!#3Z&!#VS3!$Jd2!$JDZ=disjoint_f!$Y;'!sqZB!$$Z'!yu$port!sva!|P+!svc!vq#F!st5!|\^!tp%Fstk!su-!vi'!sz`7out!#Z:]!#Z~%sub_fp!sj`<!#k+$weaken!sp`;!sp%!#S3$!so`!#kw$!so/!#DT?5!#8b#!$p<8and_!$gL-!$<R,2InC!#5jS!#xo,7RW_hig!#`1V!sq3D!#yb$!yz,!s~Z3!#c:4noin!|^^A!#Ay$lb_of_b!$j]#!ssdu!ss4!x%8!#XH%!#@><le!#ih$!tYW5ib!#8T`?!uB%!#8Uf9!sq+!sk%!#;`W5wdesc!#;a`wd!#;ab!#3S%!#GQ#w!yA_;!#HA+!{o[!#]B44!#]B%!#F`M7!~6Q!#Xx,:set!$2/h=!sp#init_done!ssb7upd!z%,I!#bM%4gma!s'%!$p1Q!t%/9s_!$1E%!tr&!t'&9decidable;prod_eq_dec!sD+!#\9#!sD#>!sD$!s5+!uY]s_metas!vHcs_are!smd8s_group!snfshadow!snb:!wl#served!spb5s!#F:-!#7i52or!$cB3!s@,!#Y{P!#;y#<!#;y%Kit_B@!$7T'_frameW!uE&!#PVKltu!#M'\B!#PV0j!#<UX!sy/A9ram!uA%!spV!$1|$6!#Sc%am!#37$s!$%FB3eq!$CPW!$wk+20!#7FZ!$v9'!#5,Y!sk+7!sk#cut!vU\!$5S+;wz!$@['!suf7sx32_!$7=W!w/'!$GY'17!sl]!$HG+!#mcZ!%'Q%st!$Feb;c!#:j`!$D13!~d$!#7P[!su2<!$C<%!#7X[!sv9!#7`[!{J+3ev!#Rv[Arr6u64arr!sh^5u8!sg,!$J/@!#wr&obliga!s:#_1K!%D:C1!#BuM8!$;{N2K!#~[X>!$uN&result!$<kB!#mt&64K!sND4core!#ZlU!#iV1!$5|a!#kE/!vw#all!#jR$!zh[!#HA#!tm+!#P>^!#|-$7!so#!$$=aD!%H@%!#l|%!$7w_!uW2!#Kg#!uW`!$d+#_up!#kcB3le!#=>T!#Ua&!yG,!#?D#_dj!#7ja@c!#H0#!#6t#!$PR#!svV!$K=3pw!tdotail!svbBc_avail!s|,!#I:b<!sx/!tlp!#ML#!sxbG!uf4!s}hB!w]'!s3#_!$=S#!xWefree!s}%h!$u4\!|-+!#iI'!|-^!sw/!#XV/i!#e,a!#d<$!#3q-!$_BC!$1f%!#LyH9!%bM#_se!$?vU!#97&?sf_load!#}Ua!sv0!#:/&!s~#!uo'!#=^W8!#~E'!t^\<!uV&!$8`-!%-j:4neg!#7RT!$,7+!$T'%!vaZ!%D:#!ty$u6!$Yz&!#s^D7!{QUCodeTab;evt_st!#T7#!u%Z!%Go/!#P\V!#HC24RCTX!snf;RNEED_LOCKS!suf:RPAGE_SIZE!stf8RGOT_SSP!thhSSP_GUARD!yI'!#HYEaluop!#FCU!$$|%5Wrd!za'I!#IqL0!tjHmsize04I!#HXI0!#]<7!%?U$!%od=1N!#J3F2w!%V5[6w0!#z]Y!xQ$!%Gd$7ct!#6K#!w1&!slP!#<d,6m!%CF%!z/f6RM!|d#!zyhAUXV_CELL!#4,Y!#4x&8ct!$pp$!zQ'!y$65False!zBP3!sRG;!$DN%cond!#Qf<!t+1ul!}4#!t+T1!%M8S!$0G+!%M6DN!%N@U!#tm,0!zbb4mctx!z`+!#A^%7n!ts%1N6!#n9:;N!#n6+!|/]!#od$!|/Y!u;/aptr!u9:Z!u9=Z!u9f4meta!wLeare!slfghdr!sld6!#_a$!sn'!|=T5!%O<A2".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12ex01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~ld5rsegs46Stdlib6ZArith6BinInt1Zq22leq23addhf7Z_to_bvk13and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~t54cell37Corelib4Init9Datatypeshh84conshh83nilhh86optionq26to_nathh84Nonehh84listhh84prodk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshmfdmachine_statet52CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hrc3mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~hvf2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ik27mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~io77seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~it18rw_cellsq23powhh86lengthhh83nathh84pairk12or3h5LinuxProcessSemantics5Riscv7Preludejjc5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~jmb3evthrc5munchhrc5wmonohvf6ret_pcik28bytes_atq22lthh84Somehmfdov_read_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jv34u64sik23le8ik22wa36Stdlib5Lists4Listkk29nth_errorq23mulhh83appt5acells_sizeq26of_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~ko56mstatehfbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUaRMallocRep~~~~~~ktb4RCTX79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_E~~~~~~li5aam_init_sthrc3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU7RF_am_A~~~~~~ln99ram_framektb6RMLOCKktbaRSSP_GUARDktb5rmrepq23subko53ctxko5bc_init_doneko58c_secret69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~mge5hceil69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~ml27hsecret89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU7RF_am_E3HCW~~~~~~mpaeram_entry_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefUbRMallocTree~~~~~~muf8rauxv_okko58s_secret" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rmemcpy_callZ3 : ltac2:(zQ "i51!h9!jc!l5!la!pa!ra!rf!s5!sf!hh1!hj0!hj8!hjf!hk9!hl2!hla!hm2!hma!hq6!hr7!hv8!ijc!inc!is6!jgc!jh8!jhe!ji8!jif!jj7!jm2!jq6!jqd!jr6!jrf!js9!jt5&>0@1$1@1$0#k0@1$c@1$1@1$0#8>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$he@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m~0>1D$3>1S$3>1n$3>3src@1$f@1$1@1$0#8>4junk@1$f@1$1@1$0#8>0@4$i3$4^6^4^2>0@3$h1$hb@2$ha@1$1@1$0#8^3@1$d^4>0@4$h8$4^8^7@3$a$9@2$h3@1$d^5^3@1$b$9>0@2$5Z^8>0@2$5@2$6^9^7@2$h9+2+k0>0@2$5Z^9>0@2$5@2$6^a^9@2$h9+2+k0>0@2$i4Z^a>0@2$hd@2$5@2$6^c^b^d@2$5@2$6^d^b^c>0@2$h6$4^f@3$hf$4\3ms'$h2@2$2@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$2~0\2m'~0@2$8@3$h1$h2^h0@7$h5@hf$h4^je^jd^jc^jb^f^e^d^j7^j6@2$7@1$0#k0^hf^c^b^a^9^8^7^6^j0^if^ie^id^ic^ib^ia^i9^i8^i7^5^4^3^2^i2@1$i2^je^i1@1$e@1$1@1$0#k0^1@1$h7$4@2$8@3$i0@3$a@2$h0$3$3@4$hc$3$3^hf@2$6^hf^hd@1$b@2$h0$3$3^i0^1@2$8@3$i1$4^i0^1@2$8@2$h6$4^1@4$h8$4^1^hf@3$a$9@2$h3@1$d^hd^hc@1$b$9@7$h5@hf$h4^ie^id^ic^ib^ia^i9^i8^i7^i6@2$7@1$0#k0^f@2$7@1$0#k0^e@2$7@1$0#k0^d^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2@2$7@1$0#k0+uuil0^h1@1$e@1$1@1$0#k0^h0@1$h7$4").
Proof.
ltac2:(KReplay.run1z (kr_t_RF_am_E ()) ["HCW"] "##xBp'0h02m'h13a1'h23a2'h31zh42a3h52a4h62a5h72a6h82a7h92t0h:2t1h;2t2h<2t3h=2t4h>2t5h?2t6h@4__x1hA4__x2hB3a3'hC3a4'hD3a5'hE3a6'hF3a7'hG3t0'hH3t1'hI3t2'hJ3t3'hK3t4'hL3t5'hM3t6'hN3H12hO4LEN0hP1PhQ7__arithhR4__ffhS4__p1hT4__p2hU7__sat13hV!s0&4hW8__varmaphX5__withY4cstrhZ3ms'h[1xh\3z12h]2Hah^4__x3h_1Dh`2D0ha2D1hb3DSThc4DST'hd2EDhe2ENhf2EShg1Fhh1Hhi5HCANBhj6HCEILBhk5HSECBhl3LENhm2MIhn3MI'ho2MUhp2N0hq1Shr2S0hs2S1ht3SEPhu3SRChv2WMhw2_Hhx2fchy2gphz4junkh{1mh|1nh}2rah~2s0i002s1i013s10i023s11i032s2i042s3i052s4i062s5i072s6i082s7i092s8i0:2s9i0;2spi0<3srci0=2tpi0>2v0i0?2v1i0@3v10i0A3v11i0B3v12i0C3v13i0D2v2i0E2v3i0F2v4i0G2v5i0H2v6i0I2v7i0J2v8i0K2v9i0L1yp%0p&0p;1p;2p;3p;4p;Gp;Op;7p;Yp;Hp;6p;Pp;8p;Cp;<p10000p4p710R0g000MR1!s5%p8P!s7$iR!sF'2p8g001GR3p4p7210P2p8p1002!s7$!s6%g002Rk10_Tg003Zj14Tg004?j12!s/$dj1TTg005Bk10ETg006Dj2;!s/$`j21Tg007;k10:Tg008Gk107Tg009Mk20[!s0$jj2XTg00:Fk10!s0$;Rk10WTg00<Xj1!tI$=6j1jTP3k20N!s6$Yk10MTg00>;j1w!s/$[j2STg00?;R3j1R!s1$[j1dTg00@;j2>!s/$Uj2UTg00AXR2j1!si$B8j1xj3!t@$BRk206Tg00C5k305!s0$Rj4qTg00D9j1p!s/$^j2nTg00E@k20Z!s0$hk30YTg00FLj1O!s/$kj2QTg00GTj2kTg00H@j3K!s/$`k10VTg00I>k20!vF$I\k10!tj$J:k10!vv$Jej2|Tg00KHj2i!s/$kj1yTg00LMj3\Tg00M0k30I!s0$Sk20HTg00N5j2f!s/$Ok20GTg00O;k30F!s0$Zk40DTg00PLj2eTg00QWj23Tg00R=j28!s/$gk20CTg00SPk30BTg00T9mG0AmH0!xO$UFlO!xE$VGk10@Tg00WOk20?!s0$oj20Tg00XIj7bTg00YJj2tTg00ZNj2!vQ$ZkmY0<TP1j6uTg00\8j1vTg00]=j4!y3$]XmP09TP0j6{Tg00^^k80JTg00_cmC0!tw$`hk60!vs$amk40LTg00c1k40!tM$d6k20!wT$dSm<0PTg00e8m<0!w_$e]k30!y@$fFk40!yU$fdj4}Tg00gOj7~Tg00h3k60!{_$hWk70^Tg00i;k70]!s0$_j8mTg00jCk40!vc$jck30!wb$kfk302Tf0R0#4!s$%p=G%20#2p=P!s-$#2#2p=l!s2+!s$'p=ag00liR1/;0p=5g00mGR4f2R5f1R6P0H0Lp=Jg00nKR7?W60p=NP4f4R8f3R9g00njR:%R5/t6;K0H00p=61Z56!su$71X10p=@20O10p=Fg00onR;!sm%=1f;0p=LP;P7P;P;P3P8P2P9g010LP5P6P0N<0Pp=r!sF$0P2P6P5P9P8f5R2f6R3f7R<f8R=N<0Qp=oAW;01p=cB0R;60p=DP;!sm%H0Sp=IP;P6g0119P0C}p=^!s4%`R>g012?R?P?g012_R@P0g013?RAF~p=]P6P>P?P?P@P0J04p=zP5!s8+6P0K0^p=Y!s:-!t5%3_P0C}P!sj$9!sX3]p=hP9!s:+!ts$Gmp=gP3!s;+2P8!sI5Gmp=VP3P2%v8P9!s<%Fbp=Bg014FR>!vx%?!vm$51Z60H03p=CB0\460p=<1160,15p=EAK289@0256/10,13p=A%40#4p>0>P;P!t++E{p=HP4P9P5AK:6!xP$>0=!t0$21Z89H03=K35@0260p=`!t0&,19,18p=sp,5HCEILRA$0_g015MRB#4RC#4RD#G#G#GRE#2!s0$2#P#l#a#a#T&0EARA';%4E!sA3,;A'1RAePAp,4HSECRA$0:&07ARE#5%2BRF#TRG%PFRH#PRI#2RJ#TRK+0[RL,XE'1REePE&0XA&0WARA#51XAL!sz&%_JRJ#jRA%4FRF#_00NA%_I#j%_H#jRH$0M\ARI%wHS00Q00AJ2961SH5%R9'NP<!{'$5%d:R:D6%5<A7=3L%5=f9RE?7=L%@Ef;RMf:RNf<RO37A7ONM'>f>RP,U41SHMRQ%RORR'N%MQRS%FO'=RT%x7RU%x;RV%M6%M0'=1N6020660405Z0L7X[7R7PQPS%LSPR%F0X[;RRPOO1P!s1$SPRPOPO%LODrM9oP=CqPT1SHORT#p%MTRQ#51n1P%@P%FPRW/=P'11;P1%cW'1'>f?RX#FRYP;20ZGKRZ%@G%5K%@L[[R[%5GR\g0162R]B0YGK6UW]RK%5L\]^]\R\p-0R]g016NR^g017:R_#OR`#ORa#ORb,Q;Rc1Q;aRa1Q;_R_'D'Dg017YRd'k%d^Re3KRf%w^Rg&0V;Rh201;5Ri?I5h7I6&0U;Rj&0T;Rk1|;1Rl1i;FRF'^,]kRm1zk8Rn5YkA9kFl1zk2Ro5Yk5hk%y?R?PkPmP?Pk1i;BRB=\;F1|;G>0I;JRm59kP?PkA9klBRpP?1^Bm,]k9YkpRpCgRqCgFV20Hk@R@P0P5g018ERrg018eRs'f20G05=WrsdB0F;16H0DRsbRbWbXX@;XA;XS]WT%@6Rr/151;61/19'>%@5A759L%59%581X8L'1[[[[^@;^A;^S]^T]RtP0%c9RufCRv,=9PvfERwP8PEPOf=RxO8bQbUbVb\bNbYbO,eP13JP,8J/=PRy%RxRz,NT%Fx,=QR{PUPVP7PTPQ%LQPzPRPxO1PSPRPxPx%Lx!yO%ECqP{1SHxR{#p%M{Rz!yO$X%@X1=YX'11;X1%cY!yK$@RY#FRQP;PZP[PKP\PfPgAIh5i?I6hPjPk%2C,i;RC,^l,]kRf=YknA9kCl=Yko5h!wB$Pf!wH$\;BC=9kmP?P!w;$P@P!vg3XT]PtP0PufDRu,=9PuPwP8PNPMPO!v+6Py%RPRt,N{1=zWRW!ux&{Pz%LzPtPRPP!ux&PPP%LP!ux%NCqPW1SHPRW#p%MW!uv$Y%@Y1=QY'11;Y1%cQ!uv$ARQ#F!ut,%ObRb#O#O,Q;R\1Q;b1Q;`20C;G>0B!{^''D/kd1Da_,Dc,D\/kd=K^e5K^Pg201;99Ih9AIi9h7I6Pj!v7$CBRj=9kFA\;FBRi=9kC!vZ&1^lB,]!{%'jm!{2'C!s/&i!s8+FP?PpFVFV!vx6^;A7506A7605'>A785L%52A728L%53Rs1X3L,1s[[[[\r!zb'^;P0fFS01fGRrPw!wL%PxPPPXO9!wR6P4f`Ryf_Rsf^RLf]R@fYRpfXR?fRRFfQRlfPRkfORifNRmfMRCfLRjfKRBfJRhfIRgPuPv13JQR^13JYRe13JXRdPPfBR\NG0AfpRcfoR_fnS02fmRaPPPxPOfiRGfhR`13JlRbPMPNPEP=P<P3P2fbRKfaR[PyPsPLP@f\RZf[R1fZRWPp!#;o&MO:fTRRPcfSRS%yARtP0&0@4RzFB,?X20?;;R{AClli%d{R7PFP01<F01U40RVP0PlPiPmP:D63EFAX0I,0IXMA,0AXL!s+$K!s+$J!s+$F!s+$E!s+$D!s+$C!s+$B!s+$2!s+$1!s+$I!s+$H!s+$G!s+$Z>!u?'PZP1PWPpP?P^PePdfWRUfVR]fURqPRPSPFPlPk!te$CPjPBPhPgfHS03PrQ01PwMO:Pu%2D#4$0>#2#P#4!s&$2#4#l#T,3JPvPtP\PzFb!tB;PUP]P!t<<Q!t:+PuPvP\!ws$YAJv0XX3;PO18JeRDP6DHPX1SHX%R0RH'NX3;PM18JdRdP0DHPQPvP0PDPPP:D6X3;PXPvP\1tHPP:H0=X3;PNP!sQ$18J^RHP5DHPQA7HD01Z0DRf/;H'>X3;PY1;f\A7\D0!s6%XA7Q0\A7\0Q!s7%8!sn%P!tc%!sp%9NY0<P!yV'WPp!uc8wPu13J\RH!v7$XPvP0NH0;P;13Jv,8JfrRefqR^PcP_!zs&kRDfjRd13JSRf!zs2dRofcRnPK!tG+!wB%!zm,P]PePqPtP0P!zb$QS04P{18JbRb9CXXP7PRP01<R0S05P0PXPbPkP:D613JFRT,8J=J0kR|'17EV!zq+?!y{$>!s+$=!s+$<!s+$8!s+$7!s+$6!s+$5!s+$4!zq4;!s+$:!s+$9!s+$3;P0PvP8EuP!uu$Q02!ux%PdPGPT!up1P!uj5W!ul/qP^PR!ul,YP{13Jk,8JRT9CFFP7PSP01<S0P0PFPTPiP:D6AJ0bi!u_~!u_%P;18JHfsRHPe!u`$!xU%lRbPD13JR!xQ2eRTPo!ue4!ua-UPHP]!ua,\R}P{ACRRXP7PqP01<q0R~P0PRPXPl!xH$8Jf=J0lRf!ub~!xC/\P9EuQ04P{ACSSl!z1%Q!z,$S!|0$:D6/1|!tZ~!w>$!s$?IP}P{PRPRPF!vU%F`S05P~PV!vX$F!vX%R|/1fDsX!to$X>AX=AX<AX8AX7AX6AX5AX4AX2AX1AX;AX:AX9AP}Q!so&|!s`$!#8@y!t5-Pfp+01CS05p+01BR!s5$AS04p+01@!z,&{S06fzR|13Jn!z02tR~P!zZ'!}<$aPbPD!z1-ffR_Q05PT!z4,lP{ACnn[P7PoP01<o0P0Pn!zq$:D6!xH/!urw>P!u$'X!uU$aPb13JqPO!uP0_P!|X5!#T,$5MO:P?P~PUPtP6PzFBP{P]P]PRP7PUP5F`1<?91U48P2PpPUP]!#5x%p,8J=J3Up+01JS02p+01IRpp+01HS07p+01GRR!w9%Q05Pf13Jd!w51Q06P|fyRLfxRsfwRyfvR[fuRc!uJ&!~H-aQ02Pb!w;,uP{ACdd`P7PDP01<D0P0PdP`fgRa!w=~!w='[[[[[XZ>P{PqPqPSP7P]P6F`1<U51U49P8P?P]Pq!vJ&?!vJ$2]!}>BpQ07PRp+01FR]!#<2%fQ0413JGR!#<=2|PLPsPyP[P!vM'^!#?6+MO:Pb%vpRrPDPtPwPzFb!t,&P]!wZ%!t$$Pl!wX1!s|8!wM-bP!sw%0PzFb'?P{ACGGaP7PdP01<d0P0PGPaP_!wI/XMAXLAXKAXJAXFAXEAXDAXCAXB!#36&IAXHAXGA!#A:%QPY!{3&!{'1!th'!sL%eP^13JW!sT2DPdPGP`!tR$!{Y'!sh&MO:P@PLPZPtP3PzFBRz/?zP{PWPWP?P7P1P3F`R71<13R11U43R4P3!sB$UP:D6R:'1RU'1R?'11f>zP7P?P8P1PUP9P4P:P5P6C[!s$%NP09WwWcWnWvWoPvP0E{Xh}L0JX0IZ0CAZ0BAZ0AAZ0@AZ0KAZ0JAZ0IAZ0HAZ0GAZ0FAZ0EAZ0DAZ0?AZ0>AP0NC08bPbPWPXZ>J0KbebfbdWmWtWpWsWrWaW`WbWlWuWzY0<X|;Xq;X_;W{WxWg!#7_-Z02AZ01AZ0:AZ09AZ08AZ07AZ06AZ05AZ04AZ03!#8/2Z00AX~!#80+Z0=AXyAZ0;AW}bibkbjo"). Qed.

(* [comment removed for export] *)
Lemma rrw_cells_app_split : ltac2:(zQ "d0!hh1!jgc!pa!hla!h9!jc!km8!hjf!sf!la!kmf!rf!knc>1m>0@1$5@1$4#k0@1$7@1$5@1$4#8>1A$9>3cs1@1$3$0>3cs2@1$3$0>0@4$1$2^4^3@3$6$0^2^1@2$8@4$1$2^5^4^3@4$1$2^5@2$b^4@1$c@1$a^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RF_am_E ()) ["HCW"] "##H+h01Hh14__x1h24__x2h31ah41mh51Bh61nh71xh82B2h92Hah:1Wh;2WFh<7__arithh=4__ffh>6__sat3h?!s/%4h@8__varmaphA5__withB4__x3hC1bhD3bs1hE3bs2hF4cstrhG4segshH1AhI5HCANBhJ6HCEILBhK5HSECBhL3WF1hM3WF2hN2_HhO3cs1hP3cs2hQ5cstr0hR1lhS1yp&0p;1p;2p;6p;4p;3p;5p;8p;<p;9p;7p;Bg002Rk103Tg003Zj1?Tg004?j10!s/$dj1FTg005Bj1bTg006DR0j2<!s1$`R1j27Tg007;j1]Tg008Gj1[Tg009Mk201!s0$jj2ETg00:Fj1vTg00;Rj1qTg00<Xj1TTg00=6j1S!s/$Yj1hTg00>;j1DTg01R?j16Tg01SGj6`Tg01T^j4KTg01Udj13Tg01Vjj14Tg01X3j2^Tg01=gj3ITg01Y=j2\Tg000Mj6MTg00amj49!t1$[j2=Tg01ZJj5ZTg00AXR2j1:Tg00ZNR3j21Tg01[Rk202Tg00]=j4QTg01JEj2YTg01\bk20!vI$D9j1PTg00E@j2~!s/$hj3}Tg00?[j1uTg00I>j2VTg00H`j1tTg00fFj4U!sA$\j1pTg00J:j1o!s/$ej2lTg00KHj2L!s/$kj1iTg00LMj3HTg00i_j8jTg00MSj2kTg00N5j2R!s/$Oj2gTg00B8j3mTg00O;j3n!s/$Zj4fTg01>[j1eTg01]nj4dTg00e8l<wTg01B0j4xTg01^Ql9aTg00c1j4yTg01_bj4z!u3$dj4{Tg00gOj7|Tg01NJlBXTg00dSl<_Tf0R4#?!s$%p=>%04#0p=J!s-$#0#0p=W!s2+!s$'p=Gg00liR5/<4p=;g00njR6f1R7;I4p=8g00mGR8f2R9P7P4Cyp=@%:4,17p=5%64#:p=CP8P!sD%zp=A!s3+9p=2g00onR:P7g013_P4C{p=O!s4$1`R;g012?R<P<g012_R=P4g013?F|p=N1R:4p=Bg00nKR>P>P>P:P:P:g01Q<P2!s$$3g01Q\f5R?f4R@f3RA!tI%MBXp=r!sX'!sQ$?P@P!sD'<_p=s!sB&!s$%3P4P7P9P3PAP@P?f6R3f7R2f8RBf9RC!sv$cp,5!~~$RD$03g015MRE#?RF#?#>#>#>RG#0!s0$0#J#W#G#G#F%bDRD'<%?G!s@3,<D'7RDePDp,4HSECRD#]%[DRG#;%0ERH#FRI%JHRJ#0#JRK#FRL+01RM,EG'7RGePG%vD%qDRD#;1EDM!st&%TK#S%TJ#SRJ#h[RK%D6R61874RD9@A9A@@A9%69,5A=@@7P8!v7,E`P1!s6%1897RGCK%CG9A@A%6A,5@=@?9P4P8P3P?18@ACKP118?@RN#3%4N9223183?#C9AB2%62,5B=@C3[P41823#3f:RN18B2#472Cf;RO18CB#C7ANP1%3D%39RD%37RC'7[RP%34,7C%3GRG[%3A/7D\G1^74P7n20010!s#$12!s-%0XC6X36PP^C6^36P4POPNPAO3%3ORO%3N'7P1f<RN#3POf?ROf>RPf=#6'5;@NP4%3PRN%DJRGf@RD/8O#4fCRCfBRQ;24XRGP2%4D%4O5IJR21\DOEMfARD=2Q2g01`c#DR2P1!vi%AIJ74C9!z1'!s0%1=J9,5AP7C9'7[RO!w<'C9!w6$=J7,59P4C9'7!s_%AIJ97C9RR[P3!s8%C9!w@$=JA,5@P9C9'7\R!x+,DZ!v9:EGXDGX3:X4KWGPO^EG^DG^3:^4K^G2P4P8fDR2PC%4QRQ%4DRDP7O6A22CQ1=JQ,5C=22D!v`$ER1%4CRD7221=JD,52=21QfFRQ!x^$1;@CP4fGRC%41R172QfHR2!s~$,=J,5C;21P>%4CR1,=JfJRJfIRD%:4RK'1;21X6>P4%6CRG202CBEM%:GRO,12=2DQP8PJ%62RQ#:R@,1DRRPCCKAAJRO%3CA2JR1PBP4CQP>182C#6fKRB?AJKX6>PP1YQGRG2002C!s}$9AJDP8PBPJ%6DRD/YQRB#:R8%:DRG,1JR2P@P4%PD%;G1~ILRC1E5I%;L1E5M[[RP%;IRRg0162R1A}IL7UW9RL%;M\1^9R!sA%NR1#uRM%D1R1P:1V:9RIP7%t:CU%p:RO%o:R?P;P<P<P=1l:51L:HRH'O,N?%i<1L:EREAH:EHR<!s;$Gj1k?=R=P4P9g018ER;g018eR3'R1g49=m;3dAn:57CfR5b=b@bAX1:X2:%;71179R3,<7[^1:^2:P4fM#CR;fNRSPAO3b<b>b?bF112@R211J8RT'<11G@RU,1JRV,<2P:P:P0P4X7:RWP01<74#eXS:X7:P2P2%B2PTPVPW!s$$!#7T$ab1174Cd#BX4:X6:PJPJ%BJP8PUPWPW%BKX7>PBPUPDPG%BGPQP@%B@ErEsM:cM<w%PQ%;@%6JRJ#P%:J#;PCPPPLPRPMP1P:PIP71V:ACUPO1L:FRF9H:<AH:HF9H:E!vW$P=P!v,0XB:1147/191143'<!v0%^B:P4P;%CSfO!v-+QbFCxM9ab:CQb8W8WNP7P4O2!|z0!s/&b5b0b5XMNWL!sK>;b0W:W5W;!sJ=W0!sB=CQW0XP6WOXH:W4bIbKbJo"). Qed.

Lemma rrw_cells_app_join : ltac2:(zQ "c0!hh1!jgc!pa!hla!h9!jc!km8!hjf!la!kmf!rf!knc>1m>0@1$5@1$4#k0@1$7@1$5@1$4#8>1A$8>3cs1@1$3$0>3cs2@1$3$0>0@4$1$2^4^3^2>0@4$1$2^5@2$a^4@1$b@1$9^3^2@4$1$2^6^5@3$6$0^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_RF_am_E ()) ["HCW"] "##Xuh04__x1h11Hh24__x2h34__x3h41ih57__arithh64__ffh76__sat4h8!s/%5h98__varmaph:5__with;4cstrh<5cstr0h=4__p1h>1ah?1mh@1xhA3Hi0hB1nhC2HahD1bhE3bs1hF3bs2hG4segshH1yhI1AhJ2B1hK2B2hL2H0hM2H1hN2H2hO2H3hP2H4hQ5HCANBhR6HCEILBhS5HSECBhT2HihU2W1hV2W2hW3WF1hX3WF2hY2X1hZ2X2h[3cs1h\3cs2h]1lh^1oh_1zp&0p;1p;2p;4p;3p;5p;6p;<p;7p;8p;Bg002Rk10HTg003Zj1ITg004?j14!s/$dj1TTg005Bk102Tg006DR0j25!s1$`R1j2>Tg007;j1tTg008Gj1rTg009Mk20ETg00:Fk10ATg00;Rk10!sV$<Xj1mTg00=6j1j!s/$Yk109Tg00>;j1WTg01T^j4PTg01R?j11Tg01Udj17Tg01Vjj1BTg00ZNR2j20Tg00AXR3j13Tg01X3j2sTg00]=j4KTg01=gj3OTg00amj4!t[$>[j2YTg01ZJj5qTg01[Rk20GTg000ij6`Tg01Y=k20FTg01JEj2NTg01LGj1!uN$Kkj1pTg00B8j39Tg01bFj1!sf$D9j1MTg00E@k20@!v-$jR4j26!s;$hk30=Tg00?[k10<Tg00I>j2^!s/$\k10;Tg00J:k10:!s0$ej2k!tA$Hj2]Tg00MSk208Tg00N5j2S!s/$Ok207Tg00O;k30!t8$OZk405Tg01>[j1iTg01]nk40!xK$e8l<hTg00fFj4g!s|$0k30!w/$B0k400!uJ$_j2~Tg00@;R5j2}Tg01cDj3d!s/$jj6aTg00CRj4fTg00H`j1|Tg01dSj3b!t+$dj4\Tg01e6j2R!v|$Mj6{!s8$Sj6lTg01\bj2zTg00c1j4yTg01_bj4xTg01fXj3wTg00gOj7vTg00i_k80?Tg01NJlBoTg00dSl<uTg00LMk30!y/$h3k60C!s0$Wk70DTf0R6#I!s$%p=H%46#4p=X!s-$#4#4p=n!s2+!s$'p=Ug00liR7/56p=2f2R8f1R9/66'>p=:g00mGR:P8P9P6Cyp=C%16#3p==P!s;'xp=<%36,09p=8g00njR;?O96p=D!sJ+Ap=?Aw:96p=Fg00onR<P9g013_P6C\p=Q!s4$1`R=g012?R>P>g012_R?P6g013?Fvp=@f3R@P=P>P>P?!t#%L0?p=L1S<6p=;g00nKRAPAPAP<P<P<g01Q<P3!s$$2g01Q\f5RBf4RCP@!sf%MBop=[!sV'!sO$BP!sD,<up=Z!sB&!s$%2P6P9P8P2P@PCPBf6R2f7R3f8RDf9REMBop>03B0B<96p=J!sZ$4P3P4P2!t$1hp=eP9!uD+6J0Cp=cP8!s8+9P6K0Dp=VP!vI%19!vI%_p,5HCEILR=$0Hg015MR4#IRF#I#H#H#HRG#4!s0$4#X#n#U#U#T&02=R='5%IG!sA3,5='>R=eP=p,4HSECR=#t%r=RG#2%44RH#TRI%XHRJ#4#XRK#TRL+0ERM7:GRGePG&0A=&0>=R=#2?:=M!sr$%mKRK#j%mJ#jRJ$09R=[RG%W;R;AC@89P1P:!v,%CP%=89<C@%1@,8C=CB81DC@9C2B[P6P:!vW%CPP1%7B%BB9?32%=29<D3%13,8D=CE2f:RN1DD37CE[[P6%73%BD9?NEf;RO%=E7<Nf<RP%=NRQ,0O;CEP1P:f=RR%1O,8PRSPNCPA<RSQf>RS1DPO7CRP6P:f?RQ%1R,8SPP!tS%Rf@RT%=SRS,0Q%BR3?fARR%1Q,8T;<SfBRS1DTQ7CR!tX$QfCRQ%=RRR,0S%BT3?fDRT%1SRU,8Q;<RP:fERRPT1DQSRVCP%1VRW#39<RT%7V%BVRV9?RTP11D96#7%78%79RX'>RY[%76,>X1D89#7[RX1D@8#7\Y1s96P6n20010!s#$12!s-%0XD;X>;PX^D;^>;P6PTPQ%7T%7QPPP@CKO3b1%WJRX%BQRY%BS5OJfFRZ??R6X]Xg01`c#WR[P1!x+%AOJ96CA!{B'!s0%1YJ8,8@P9CA'>R1[!{^'CAPCP@1YJ9,88P6CA'>!s_%AOJ89CA[R\!x\%AOJ@8CA\1!|@,Dq!uG:FXXEXX><X?GWGP\^FX^EX^><^?G^G!yX%ZPR%BTR:PYA?ZR:1YJ:R[,8R=?ZYPOPA%1TRYfGRG%36RX,0Z;?:XBAP8P[20GTPE`CKO6b1PV20FQSE`CKPA%1QRV/NURUA<ZRXXBA%2TRP18TV/5M%26RV%3YRY7:610Z9#E,FG%pJRJ59=#G[^4<%3U9<RT10RY/5M%1ZRZ#3RY9:V6RTfIRUfHR[/09#E'F=9=J!s\%10GYR:#2R\%1RRR,8:/5MfJR:%1[R1#3R],0U!s\0\T^4<1NZR#39<[G%1G,8[/0Y/5MA:V6]fLRYfKR[%1:RG#3RR'0!tD4%2:%1URU/N1!tt$T,0:R^/5MR_1NGU#3!u+$`fMRa10Y!sc2Rb'>%M1Rc%2]Rd%MGRG%2RRR20@ILRe167I%2L167M[[Rf%2IRgg0162RhB0=IL9UWCRL%2M\h^Cg!sB%NRh$0<Ri%WhRh1^<9&0;<Rj&0:<Rk1k<7Rl1]<4R4'Q,@kRm%p>R>PmCL208k?R?P6P8g018ERng018eRo'S20768=9nodB06<79H05R7b6b9b:X0<%29\V^0<P6fORoPNO2b5b7b8b<b;P_PbP_%3UR_/0]Rb,0:Rn/5MP<P<P0P6X@<RpP01596#iXH<X@<P^PnPp!s$$!#:H$ab1096H04#;X?<XB<P:P:%;:PTPbPpPp%;XX@ARAPZPbPUP_%;_P1P]%;]E[EZN:03PMPM%;MM<hPcPdPGPRPePfPLPgPiPhP<1^<8RRP91^<@CgRGPjPk1]<HRH,J4Rd1]<FRF'J1k<I>01<KRK!v[$P>1JHFRI,J4/QK,@kCLP?P!v7,X2<X3<1069RK/08/5M108@,09/5M[^0<^2<^3<P6%1aRa#3RMfNRc#1R]#3R1PoP2O4!vh,H00%=[R[,~9169[15[9'}P5%=YRY,6815Y810c@#E,Fo!yw%P616@MPDPC%2CRD1N]aRc#3RY,6CR5'>101MR[9:DCR_PDP5PDPpP[O1R5,6Cp-0RU/SDA9UDDe9dDDPp16!wl,RDPCPC%;CPYP5!ws$APcP[P]P1%;1R[Pa!w9$E[EZGeEaP@CfRaP_%M]Rc%21R5fPRY#1Rb#MRZ%3b#2Rb!w[1PRP9%|<Cg!wT$ckC9VkmP>Pk1_4H,@kRRP>AVkmRCL!w>6=U1>V81698%28?:8@[!w8'=UP6fT#=RVfS#1'8,6NPVPNPBP2O5!w6,bAO2W1P6O115M@PaP_PcP5!yz$!tu/GPjP<Ab<FH,Jdg01P31J4FC\,@k!xz7R89,0K106859<!xq-PNPVfURNO3!tP/10o11RC1'010oC59<P<%1oRo#3RK,0Y1RBKRd'0fR%E6!#3]&X_<P2Pd%2BRd1No]R2#3RJ,6BR='>10K1Rb9:dBRZPdP=PdPpPbO1R=,6B1SUdA9Udde9dddPpPDPBPB%;BPJP=!xQ&2PbPoPK%;KP]P1P[!xN+CCfPZ%Mo%2KfQ#1RK#M%3K#2!vK4k1ckB1_4I,@k5Vk!x?$QH4!|]$Ab<4HRH,Ql,@k1_HF!sJ%!xO83!xR$0989:@615891R8@R8#2?:8C!x[+3!x^%%2OPV%=NPOPBP3O6!xU110YBP6E{bP!x_%!#<<,211000!s'$b^XT`X4<CKCKWZWOXN\P@ElWYWMXLPPEElPW1z!#;K$WVWKWXP9P6O2!#=2/!s/&W1!sB?WUWJWW!sd[X\;W[XI<W?bQbSbRo"). Qed.

Definition ram_entry_post : ltac2:(zQ "70!h9!jc!hjf!la!hq6!jm2!ks3>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2lo$3>2st$6>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>0$4P") := ltac2:(zQ "i31!h9!jc!l5!la!sf!pa!s5!ksd!rf!hjf!hm2!hj0!hla!jif!hq6!lhd!hl2!hj8!hma!jm2!lm4!hv8!jqd!ln2!jr6!ijc!inc!is6!jgc!lr8!ls5!lsf!ltd!ks3!lu6&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h3@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2lo$3\2st$i1\1m~0\3ms'$e@2$2@1$1@1$0#k0\2x1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\3s1x@1$1@1$0#k0@2$2@1$1@1$0#k0\3s4x@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$c@1$1@1$0#8\4junk@1$c@1$1@1$0#8@2$4@3$h2$e^h5@7$h9@hf$h5^h4@2$6@1$0#k0@2$8@2$7@1$0#k0^i9-k0^i8^i7^h3^h2^h1@2$6@1$0#k0+hgg0^h0^e^d^c^b^a^9^8^7@2$6@1$0#k0$hf@2$6@1$0#k0$he^f^i1^i0^hf^he^hd^hc^hb^6^5^4^3^ha@2$6@1$0#k0+ugml0^h9@1$h0@1$1@1$0#k0^2@1$hb$5@2$4@3$h6@3$b@2$a$3$3@4$d$3$3@2$i2@2$7@1$0#k0^i9+k0@2$7@1$0#k0^i9@3$b@2$a$3$3@4$d$3$3$f@2$8$f+h0@1$h1@2$a$3$3^h6^2@2$4@3$h8$5^h6^2@2$4@2$ha$5^2@2$4@4$hc$5^2@2$8@2$7@1$0#k0^i9-k0@8$hd?4HSEC^1^i2^i3^i4^i5^i6^ia@2$4@4$h7$5^2^h8@2$8@2$7@1$0#k0^i9-k0@4$i0?5HCEIL?4HSEC@1$h4^h7^2").

(* LPS 727298f3: [auxv_read8] reads one key word of [auxv_keys] (Ref/RMallocTree.v); it replaces
   [ru64s_read], which read a word of the old [u64s] auxv block.  boost-beast/http_request's
   Ref/RF_am_E.v (OSSV-509 tree). *)
Lemma auxv_read8 : forall m A w a, bytes_at rsegs m A (le8 w) -> a = wa A -> ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof. try hcb. try hsb.
  intros m A w a H ->. rewrite <- (Z.add_0_r A). change 0 with (Z.of_nat 0).
  rewrite (bytes_at_ov_read rsegs m A (le8 w) 0 8 H) by (rewrite length_le8; lia). reflexivity.
Qed.

Lemma ram_entry : ltac2:(zQ "i00!h9!jc!la!pa!luc!hma!ra!ksd!lv3!mg2!hl2!hjf!sf!jj7!jm2!mk9!mof!jq6!hv8!ln2!ijc!inc!is6!mtd!ltd!nj2!ks3!nje!jt5!jh8!lu6!s5>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$e@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>2lo$2>2st$ha>0@4$h8?5HCEIL?4HSEC^1^3>0@2$h5$3^4>0@4$h9?5HCEIL?4HSEC^5@2$7@1$0#k0^i5>0@4$h3$3^6^5@2$7@1$0#k0^i6>0@2$6@1$f?5HCEIL^6>0@2$6^7@2$he@2$7@1$0#k0^i8+k0>0@2$d@3$5$2@1$8@1$4^7Z@3$5$2@1$8@1$4^7+1>0@3$5$2@1$hb^8@1$h0?4HSEC>0@2$c@2$6Z@1$9@1$4^9@2$hc@1$9@1$4^9@2$hd+2+k0@3$h1$3@h5$h7^id^ic^ib^ia^i6^i5^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^e^d^b^a^c@7$h4@hf$h2^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e@2$hf@1$0#k0+uglpc^d@1$a@1$1@1$0#k0^c@1$h6$3").
Proof. try hcb. try hsb.
  (* LPS 727298f3: written out.  The recorded proof walked the auxv through [ru64s_read] over the
     old ten-pair [rauxv_list] block; [rauxv_ok] now claims [auxv_keys], the revision's key words
     (Ref/RMallocTree.v), so the walk reads one key per turn with [auxv_read8] and the
     CONFIG_RSEQ tail is split.  The text is boost-beast/http_request's Ref/RF_am_E.v
     [ram_entry] (OSSV-509 tree), the same allocator; only the [rauxv_ok] destructure differs
     (this tree keeps [x16] and the three phdr equalities). *)
  intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5 & _) & _). unfold ctx_head_cells in C1.
  try hcb; try hsb; unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *. unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM. unfold RCTX in MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
  destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AVC & AVL & RND & AB & BAV & AVH & BR & RH & X3 & X4 & X5 & X16 & X6 & X11 & X12 & X23 & XR & E3 & E4 & E5).
  unfold RAUXV_CELL in AVC.
  (* the 27 keys of [auxv_keys] (Ref/RMallocTree.v:340-353); the tail after
     AT_EXECFN is the per-CONFIG_RSEQ disjunction *)
  destruct AVL as (AV0 & AV2 & AV4 & AV6 & AV8 & AV10 & AV12 & AV14 & AV16 & AV18 & AV20 & AV22 & AV24 & AV26 & AV28 & AV30 & AV32 & AV34 & AV36 & AV38 & AV40 & AV42 & AV44 & AV46 & AV48 & AV49 & AV50 & TAIL & _ & _). rewrite <- (Z.add_0_r av) in AV0.
  st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.
  st1. st1. st1. st1. st1. st1.
  st1. rewrite sx32_wz by lia. st1. st1.
  st1.
  lazymatch goal with H : rw_cells rsegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
  destruct INIT as [I0|I1].
  2:{ (* already initialised: the walk is skipped *)
      rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
      st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
      apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
      unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
      eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; try hcb; try hsb; lia. }
  rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  (* one loop turn per auxv key that is neither AT_RANDOM (25) nor AT_NULL (0) *)
  Ltac skip_iter i key HB :=
    let RD := fresh "RD" in
    st1;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (auxv_read8 mX _ (wz key) (wa (_ + 8 * i)) HB ltac:(f_equal; lia)) as RD end;
    st1; try clear RD;
    st1; change (bv_eqb (wz key) (Z_to_bv 64 25)) with false; cbv iota;
    st1; change (negb (bv_eqb (wz key) (Z_to_bv 64 0))) with true; cbv iota;
    st1.
  skip_iter 0 33 AV0. skip_iter 2 40 AV2. skip_iter 4 41 AV4. skip_iter 6 42 AV6.
  skip_iter 8 43 AV8. skip_iter 10 44 AV10. skip_iter 12 45 AV12. skip_iter 14 46 AV14.
  skip_iter 16 47 AV16. skip_iter 18 51 AV18. skip_iter 20 16 AV20. skip_iter 22 6 AV22.
  skip_iter 24 17 AV24. skip_iter 26 3 AV26. skip_iter 28 4 AV28. skip_iter 30 5 AV30.
  skip_iter 32 7 AV32. skip_iter 34 8 AV34. skip_iter 36 9 AV36. skip_iter 38 11 AV38.
  skip_iter 40 12 AV40. skip_iter 42 13 AV42. skip_iter 44 14 AV44. skip_iter 46 23 AV46.
  (* AT_RANDOM (25) at index 48: the loop takes its value from index 49 *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (auxv_read8 mX _ (wz 25) (wa (_ + 8 * 48)) AV48 ltac:(f_equal; lia)) as RD end.
  st1. try clear RD.
  st1. change (bv_eqb (wz 25) (Z_to_bv 64 25)) with true. cbv iota.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (auxv_read8 mX _ (wz rnd) (wa (_ + 8 * 49)) AV49 ltac:(f_equal; lia)) as RD end.
  st1. try clear RD. st1. st1. st1.
  (* split the frame so memcpy writes only the secret word *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
      destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
      cbn [cells_size csize Nat.add] in FRc;
      replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
      apply (rw_cells_merge rsegs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
      rewrite app_nil_r in FRm; clear FR
    end end.
  st1.
  call rmemcpy_callZ3.
  1:{ exact RND. } 1:{ apply length_le8. } 1:{ exact FRm. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  1:{ lazymatch goal with H : mem_inv rsegs ?mX |- mem_inv rsegs ?mX => exact H end. }
  lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -64) [CB _ (le8 (wz hsecret))] |- _ => rename H into DST end.
  st1. st1.
  (* AT_EXECFN (31), then AT_RSEQ_* under CONFIG_RSEQ, then AT_NULL *)
  skip_iter 50 31 AV50.
  destruct TAIL as [(AV52 & AV54 & AV56) | AV52].
  (* the per-CONFIG_RSEQ tail is opened only here, so its facts still read the
     entry memory [m]: carry them across MU (they lie above sp, outside the
     frame and the context words) *)
  { pose proof (bytes_at_transport _ _ _ _ _ _ AV52 MU ltac:(cbn [disjoint_from]; rewrite length_le8; lia)) as T52.
    pose proof (bytes_at_transport _ _ _ _ _ _ AV54 MU ltac:(cbn [disjoint_from]; rewrite length_le8; lia)) as T54.
    pose proof (bytes_at_transport _ _ _ _ _ _ AV56 MU ltac:(cbn [disjoint_from]; rewrite length_le8; lia)) as T56.
    clear AV52 AV54 AV56. rename T52 into AV52. rename T54 into AV54. rename T56 into AV56.
    skip_iter 52 27 AV52. skip_iter 54 28 AV54.

    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (auxv_read8 mX _ (wz 0) (wa (_ + 8 * 56)) AV56 ltac:(f_equal; lia)) as RD end.
    st1. try clear RD.
    st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
    st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
    (* the memcpy destination narrowed to the single secret word *)
    lazymatch type of DST with rw_cells _ ?mX _ _ =>
      assert (DST8 : rw_cells rsegs mX (bv_unsigned sp + -64) [C8 (wz hsecret)])
        by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
            split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
      clear DST end.
    st1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; try hcb; try hsb; lia);
      pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    clear MUh. unfold RCTX in MUc.
    st1. st1.
    set (stI := upd_ctx (fun c => set_init_done 1 (set_secret hsecret c)) st).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
    { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold ctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        change (pw stI ?q) with (pw st q). unfold wz at 2.
        (* the donor hard-codes its own RCTX here as the decimal 371176; this
           mirror pins ITS OWN value by computing RCTX from its own
           RMallocRep.v, so the two mirrors can never share one tree's address *)
        let ctxa := eval cbv in RCTX in
        lazymatch goal with H : rw_cells rsegs ?mX ctxa _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
    clear MUc WMc MRX.
    st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      lazymatch goal with Hm : rw_cells rsegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells rsegs mX (bv_unsigned sp + -56) ?csc |- _ =>
        pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
        cbn [app] in J2; clear Hm Hc;
        lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
          apply (rw_cells_merge rsegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
      end end.
    apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
    unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
  }
  { pose proof (bytes_at_transport _ _ _ _ _ _ AV52 MU ltac:(cbn [disjoint_from]; rewrite length_le8; lia)) as T52.
    clear AV52. rename T52 into AV52.

    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (auxv_read8 mX _ (wz 0) (wa (_ + 8 * 52)) AV52 ltac:(f_equal; lia)) as RD end.
    st1. try clear RD.
    st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
    st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
    (* the memcpy destination narrowed to the single secret word *)
    lazymatch type of DST with rw_cells _ ?mX _ _ =>
      assert (DST8 : rw_cells rsegs mX (bv_unsigned sp + -64) [C8 (wz hsecret)])
        by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
            split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
      clear DST end.
    st1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; try hcb; try hsb; lia);
      pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
    clear MUh. unfold RCTX in MUc.
    st1. st1.
    set (stI := upd_ctx (fun c => set_init_done 1 (set_secret hsecret c)) st).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
    { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
      - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - left. unfold ctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
              c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
        change (pw stI ?q) with (pw st q). unfold wz at 2.
        (* the donor hard-codes its own RCTX here as the decimal 371176; this
           mirror pins ITS OWN value by computing RCTX from its own
           RMallocRep.v, so the two mirrors can never share one tree's address *)
        let ctxa := eval cbv in RCTX in
        lazymatch goal with H : rw_cells rsegs ?mX ctxa _ |- _ => exact H end.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
      - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
    clear MUc WMc MRX.
    st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      lazymatch goal with Hm : rw_cells rsegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells rsegs mX (bv_unsigned sp + -56) ?csc |- _ =>
        pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
        cbn [app] in J2; clear Hm Hc;
        lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
          apply (rw_cells_merge rsegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
      end end.
    apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
    unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
  }
Qed.

End HCW.

