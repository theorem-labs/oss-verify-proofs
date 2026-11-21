(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, lemmas added for the revision, the revision's auxiliary vector (auxv_keys). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import F_memcpy.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_malloc_free MallocTree MallocModel_B F_ntf_A F_ntf_B MallocKit_B MallocKit_B3 F_am_A F_am_K F_am_E.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_B RMallocKit_B3 RF_ntf_A RF_am_A.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RF_am_E () := KReplay.lz_vm "#&+=C46Stdlib5Lists4!s+#8nil_consC47Corelib4Init5Logic6eq_ind!sB88!sB%_rC4ELinuxProcessSemantics5Riscv7Prelude5bvmap!tQ7:firstn_nilC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8HeapCeil;hceil_rangeC13~~~K!u#+7Numbers7BinNums8positive01!sKG2!sK=1Z02!t~Y5!t~$!tx%C5!v/&6ZArith6BinInt1Z2leI!w=73and00!tGP:!tG#Secret=hs!s-$!vK/!sr[7!sr&!u?B3pow!u\>t!uA]canary!uAi!sr%!yTC1N02I45stdpp9bitvector;definitions2bv00!x#29Datatypes6op!sL#!sH>4list00C!sh<length!vo<6to_natK!t-A1!yq82or00C8!vaN3Lib3Mem7mem_inv!xyB6of!tk#!tK9eq00!s`34Znat5Nat2Z7inj_iff!#4:77iff_sym!#3e'9micromega;ZifyClasses7rew!sj$!t5=9is_nonneg!u<<8max_spec!sH<>pow_po!spD:!sN#!sJ%!ww<3nat02K!uO5=RingM!s4'5Psatz!sO8:ZM!v',!tO$!xE$!#52-!y;8!sr76VarMap1t01!sD@2I!sD?0I!uEC7Formula00!t567Env!sT#5PExpr!tX8!sI2!ua=!}H'2!skE3!sIE7!z?65Tauto8B!uH&K!{c;1C!x%@=Z!sn$CheckerC!v}<4f!#=G#!sq?C!sq0_sound!~UT6MState<unsigned_li!#8X&!#5w?7Z_to_bv!sLA;bv_!t$'!{bK7!sOK5!ucQRef8F_memcpy;!s,%!~;#!ud'!vWS5Frame3mkR!sgZ8PropExec7seg_rom!sn%!#9I<prod!#9i3!z7'x!#8AU!xj&2MS!#;w%!uzTCells4cell05!#>~Badd!wwe!#7V#!w6Y!ud&6ret_pc!#>a2!#By21!t-T2Nd;ex_introF15!ttZ2Nd:and_elimF6!sk^ex!sj%!tX\4!zZ#8evt_mono!skZ3Mem8bytes_a!|x[4Step8rw_!y~#s!y}Cmax!#>}A5mkapp!sKErel!#49J6!#<4?3K!#;nK!#;K6!#9p%G!sJ'4!sJF3!sJF5!sJF6!sJF8K!#4a@1!#6ZY5w!z7^!si&munch!~J3!#Oi51!#4IS5RSegs5rsegs!#7`A!#D&#0I!#6\^0!t13!u:60!{968!{9#Inst@!#I&$_!#Jv$_eq!zRD3Op205!#A@;5eKind!#:L<unit!#C}7!se%4kind!#Tk-!sf81!ttI3I!#Wb9?!s<2>!#Wr#!sE+=machine_state!t|#!v};!#VI+3!#<o74True!#G77!#I,:0!#JI@!up7!sq;1!wL=bool!t9>!sF%!}WU3Arr4u64!#74&!tz'!#[U,9nth_error!#I'C1!#7t=ul!#9jW3le8!#:QZArr:!uR#_sp!#G3,!ws;!#9A#!sC03Nat!u/$!y?78iff_refl!xNN3!#4i?!#L>>3P!xM#!#:dJ4!sp>!#M0%5!#;}A;!#TI%_rev!uv,!y,%7!s+#Def5skipn!sD;6!#a}$!vr7sub!z$8app_nil_r!#dH7!#bu%!#W;+5!vy$8Peano!s}#!t%'!sF>8sub_diag!zKX:!#[3$_!zR+!#3I2!t9$2le!#7i,!u8-;!u8&all2!#eO>!#@c-!v=7l!sD77!wS$_!tG8:!sB%!tF;9!sE&!{g9add!sz8!v&&!s\#!vjW@!#D{&_ov_read!#Eo]2wa!~<'!#95X!tQ&_!tb$!|$B6!#EL#2!zD@mul!#^yBmul!#;ZH1!sp>6!sp#le!tZ@!x-#!tZB!#O8S!#@c':!#IA#_size!x-V5Agent=F_malloc_free?!#J>&_prefix!#DeZ!tm$8!sp%!#Kx[!sl0wf!sl`;!sl%!yy%!so_<!t]'!}2$!sp_?!ta-!ss^!}9#<!~,+!tccB!tc/!#j|%!sv_>!za,!tj-!~BA3inj!{0d9wr!v-#sub!vv^5!sk$!#9d&!#54H<MemImageType7Segment!#Jt@7Inj_Z_Z!#@y73not!#C`;;lt_ge_cas!#68Deq!#mH$!sL@9and_morph!#@TD4!#EG<!w=#!w7S!#ZR/3!#9I_5wview!tPQRef:RM!yW$Rep5rmre!|YXRef;!sn&Tree8rauxv_ok!srV4Spec6!sr%8s_!#yW/!sn[3ctx!tYcc!tY1!#i2?D!#i2,_in!#z>%!sY@:bv_modulus!x1_;rreg!sv#!#92Y!st19!y#$_!v\Y!sr2=!sr%globa!#_q&c!svS7RF_am_E>ram_entr!#kN[!#6=$9!tm+>ctx_head!#aa/!sx_7active!sqg6usag!sph:unmap_seq!stg8bouncess!wGktail!wGl2wz!slgb!#N8%!#oI_4!sjf1!};W!#cV':!#cV#!#V>#!sna!#e1#!sn\!#8x1:!#8x$li!}{'K!$8YG4tree01!$9-H4sext!udT!#vb'8alu_addi!vU`9stk_carv!#K|&!#={I6BvBase=!#{z#le!#P>&!#9A>6bv!#MvW!uh+9b!sf#!vT$!tz%!#A%:9add_assoc!t;UStepFast6sf_ad!{B[!sm+=!sm$dr_ztobv!stc7sf!|8`!#N=%b!#a>$!#A?X3!#Ot,b!#b//!slY5c!#S:Y!si,6c!#PZ^7StoreDj:chunk_disj!{r'!#Hm?8or!#Hl$!t@T3Arr;!#ef#!#O<`!}x$6inside!usb8!us%in!uq'!~$?9bv_!#Dt$!}9<6shiftl!~K]7v_auip!$%QZ!#|P#F!#Fk'!$1Q%!}A#_r!uYKconca!#7H]7b!u9/!#98@5Instr5i!s+#02!#3$\8sf!u-#gT!#7uW@!#7p&!vM#word!#6>b4!#5HZ!vb'6v!#;&-!#Q8X<write!uI#mem!$OX;trans!y~Y=wa_of!y{'!tz'!t666eq!$CS#3!z9%7tac!to$f_equal_help!tQYD!#ac's!~/#_ok!$,ta>!sn%!x|%8'!sq_D!}=7!y/[!#<G-!tq%goa!#;WZ3Mem4sx32!}Y&!#7$S!#G,,2!tR^3le4!se^@sext_extract_!srY!#VS->c_mmap_counter!xj_@!zV+!#mm#at!#5cS6!sRN5!yf]<sf_branch_!#9k[!#7+31!#5Ub5v_lui!sldb!sl,!vlN1!t@]7!#7]$w!#5b&!#<Y>8bv_swrap!#MM@3Sem5low32!sNFalu32!u5^w!u5/!vQN;!xY`mu!#4w&!uXD7mul_div!t>^m!t>,!uXNB!{|]@!#7Y&8_direc!#:>_A!#;73!stZ!#G$&<stk_!#>h$!#G+&!v5N3!v5]7sf_btgt!#32e!#<F+!#Hf:7add_0_r!uQN:!#d=[:r!#LS#!$$b,!#XgG6bv_eqb!tE\Cr!y2+app!#QY_3Tac>!st+merg!#N#Z!$N&%;lit!#KL#!tb]!yO+:sf!#F4$M!$Sw%!#i-]!$P[%callZ3!vK^5dfa!~7'K!sgW4ib!$Pz#!tQ]6ibs!~m]!x`$!u}#_ct!$Qq%!sp^8!sp'!#3W&!#VP3!$JY2!$J9Z=disjoint_f!$Y/'!sqZB!$$P'!yt$port!sva!|O+!svc!vq#F!st5!|[^!tp%Fstk!su-!vi'!sz`7out!#Z7]!#Z{%sub_fp!sj`<!#k$$weaken!sp`;!sp%!#S0$!so`!#ks$!so/!#DQ?5!#8`#!$p/8and_!$g?-!$<H,2InC!#5iR!#xi,7RW_hig!#`,W!sp1D!#y[$!yx,!s}[!#c54noin!|\^A!#At$lb_of_b!$jN#!ssdu!ss4!x#8!#XC%!#@9<le!#ic$!tYW5ib!#8R`?!uB%!#8Sf9!sq+!sk%!#;^W5wdesc!#;_`wd!#;_b!#3Q%!#GL#w!yA_;!#H<+!{o[!#]=44!#]=%!#F[M7!tEP!#Xs-:set!$1}h=!sp#init_done!ssb7upd!z%,I!#bH%4gma!s'%!$o{Q!t%/9s_!$1<%!tr&!t'&9decidable;prod_eq_dec!sD+!#\4#!sD#>!sD$!s5+!uY]s_metas!vHcs_are!smd8s_group!snfshadow!snb:!wl#served!spb5s!#F8-!#7i52or!$c63!s@,!#YvQRef<!#;x%Kit_B@!$7K'_frameW!uD&!#PQKltu!#M#[B!#PQ0j!#<SY!sx,A9ram!u?%!soV!$1s$6!#S\%am!#34$s!$%>B3eq!$CAW!$w[+20!#7CZ!$v%'!#5&Y!sk+7!sk#cut!vU\!$5J+;wz!$@N'!suf7sx32_!$74W!w/'!$GJ'17!sl]!$H8+!#m[Z!%'@%st!$FXb;c!#:g_!$C|3!~a$!#7LZ!st2<!$C0%!#7SZ!su9!#7Z[!{G+3ev!#Rn[Arr6u64arr!sh^5u8!sg,!$Iw@!#wg&obliga!s:#_1K!%C}C1!#BoM8!$;pN2K!#~PX>!$u<&result!$<`B!#mi&64K!sND4core!#ZdU!#iK1!$5qa!#k:/!vw#all!#jG$!zh[!#H;#!tm+!#P8^!#{{$7!so#!$$2aD!%H'%!#lq%!$7l_!uW2!#Ka#!uW`!$cr#_up!#kXB3le!#=;T!#U[&!yG,!#?A#_dj!#7ga@c!#H&#!#6r#!$PF#!svV!$K13pw!tdotail!svbBc_avail!s|,!#I4b<!sx/!tlp!#MF#!sxbG!uf4!s}hB!w]'!s3#_!$=H#!xWefree!s}%h!$tz\!|-+!#iA'!|-^!sw/!#XP/i!#d}a!#d4$!#3q-!$_2C!$1[%!#LtH9!%b8#_se!$?kU!#97&?sf_load!#}Ja!sv0!#:/&!s~#!uo'!#=^W8!#~:'!t^\<!uV&!$8U-!%-X:4neg!#7RT!$,++!$Sx%!vaZ!%D##!ty$u6!$Yn&!#sVD7!{QUCodeTab;evt_st!#T2#!u%Z!%G\/!#PYW!#HB04RCTX!sme;RNEED_LOCKS!ste:RPAGE_SIZE!sse8RGOT_SSP!tfgSSP_GUARD!yD'!#HTEaluop!#F>U!$$n%5Wrd!z\'I!#IlL0!tjHmsize04I!#HSI0!#]17!%?>$!%oJ=1N!#J-F2w!%Ut[6w0!#zPZ!%GL'7ct!#6E#!w0&!skO!#<^-6m!%C-%!z,e6RM!|_#!zvgAUXV_CELL!#3}Y!#4p&8ct!$p\$!zN'!x}65False!z?P3!sRG;!$D;%cond!#Q^<!t+1ul!}1#!t+T1!%LvS!$07+!%LtDN!%M~U!#t_,0!z`b4mctx!z^+!#AV%7n!ts%1N6!#n':;N!#n$+!|,]!#oV$!|,X!u;0aptr!u9:Z!u9=Z!u9f4meta!wLeare!slfghdr!sld6!#_Y$!sn'!|=T5!%NzA2".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init5Logick12ex01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~ld5rsegs46Stdlib6ZArith6BinInt1Zq12leq13addhf7Z_to_bvk13and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~t44cell37Corelib4Init9Datatypeshh74conshh73nilhh76optionq16to_nathh74Nonehh74listhh74prodk12eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshmedmachine_statet42CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hrb3mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~hve2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ik17mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~io67seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~it08rw_cellsq13powhh76lengthhh73nathh74pairk12or3h5LinuxProcessSemantics5Riscv7Preludejjb5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~jma3evthrb5munchhrb5wmonohve6ret_pcik18bytes_atq12lthh74Somehmedov_read_bytes79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~jv24u64sik13le8ik12wa36Stdlib5Lists4Listkk19nth_errorq13mulhh73appt4acells_sizeq16of_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~ko46mstatehfbbv_unsigned79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefaRMallocRep~~~~~~kta4RCTX79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent6F_am_E~~~~~~li3aam_init_sthrb3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref7RF_am_A~~~~~~ln79ram_framekta6RMLOCKktaaRSSP_GUARDkta5rmrepq13subko43ctxko4bc_init_doneko48c_secret69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~mgb5hceil69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~mkf7hsecret89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref7RF_am_E3HCW~~~~~~mp7eram_entry_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3RefbRMallocTree~~~~~~mub8rauxv_okko48s_secret" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Lemma rmemcpy_callZ3 : ltac2:(zQ "i51!h9!jc!l5!la!p9!r9!re!s4!se!hh0!hif!hj7!hje!hk8!hl1!hl9!hm1!hm9!hq5!hr6!hv7!ijb!inb!is5!jgb!jh7!jhd!ji7!jie!jj6!jm1!jq5!jqc!jr5!jre!js8!jt4&>0@1$1@1$0#k0@1$c@1$1@1$0#8>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$he@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m~0>1D$3>1S$3>1n$3>3src@1$f@1$1@1$0#8>4junk@1$f@1$1@1$0#8>0@4$i3$4^6^4^2>0@3$h1$hb@2$ha@1$1@1$0#8^3@1$d^4>0@4$h8$4^8^7@3$a$9@2$h3@1$d^5^3@1$b$9>0@2$5Z^8>0@2$5@2$6^9^7@2$h9+2+k0>0@2$5Z^9>0@2$5@2$6^a^9@2$h9+2+k0>0@2$i4Z^a>0@2$hd@2$5@2$6^c^b^d@2$5@2$6^d^b^c>0@2$h6$4^f@3$hf$4\3ms'$h2@2$2@1$1@1$0#k0\3t0'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a1'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a2'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a6'@1$1@1$0#k0@2$2@1$1@1$0#k0\3a7'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t3'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t4'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t5'@1$1@1$0#k0@2$2@1$1@1$0#k0\3t6'@1$1@1$0#k0@2$2~0\2m'~0@2$8@3$h1$h2^h0@7$h5@hf$h4^je^jd^jc^jb^f^e^d^j7^j6@2$7@1$0#k0^hf^c^b^a^9^8^7^6^j0^if^ie^id^ic^ib^ia^i9^i8^i7^5^4^3^2^i2@1$i2^je^i1@1$e@1$1@1$0#k0^1@1$h7$4@2$8@3$i0@3$a@2$h0$3$3@4$hc$3$3^hf@2$6^hf^hd@1$b@2$h0$3$3^i0^1@2$8@3$i1$4^i0^1@2$8@2$h6$4^1@4$h8$4^1^hf@3$a$9@2$h3@1$d^hd^hc@1$b$9@7$h5@hf$h4^ie^id^ic^ib^ia^i9^i8^i7^i6@2$7@1$0#k0^f@2$7@1$0#k0^e@2$7@1$0#k0^d^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2@2$7@1$0#k0+uqtq8^h1@1$e@1$1@1$0#k0^h0@1$h7$4").
Proof.
ltac2:(KReplay.run1z (kr_t_RF_am_E ()) ["HCW"] "##xKp'0h02m'h13a1'h23a2'h31zh42a3h52a4h62a5h72a6h82a7h92t0h:2t1h;2t2h<2t3h=2t4h>2t5h?2t6h@4__x1hA4__x2hB3a3'hC3a4'hD3a5'hE3a6'hF3a7'hG3t0'hH3t1'hI3t2'hJ3t3'hK3t4'hL3t5'hM3t6'hN3H12hO4LEN0hP1PhQ7__arithhR4__ffhS4__p1hT4__p2hU7__sat13hV!s0&4hW8__varmaphX5__withY4cstrhZ3ms'h[1xh\3z12h]2Hah^4__x3h_1Dh`2D0ha2D1hb3DSThc4DST'hd2EDhe2ENhf2EShg1Fhh1Hhi5HCANBhj6HCEILBhk5HSECBhl3LENhm2MIhn3MI'ho2MUhp2N0hq1Shr2S0hs2S1ht3SEPhu3SRChv2WMhw2_Hhx2fchy2gphz4junkh{1mh|1nh}2rah~2s0i002s1i013s10i023s11i032s2i042s3i052s4i062s5i072s6i082s7i092s8i0:2s9i0;2spi0<3srci0=2tpi0>2v0i0?2v1i0@3v10i0A3v11i0B3v12i0C3v13i0D2v2i0E2v3i0F2v4i0G2v5i0H2v6i0I2v7i0J2v8i0K2v9i0L1yp%0p&0p;1p;2p;3p;4p;Gp;Op;7p;Yp;Hp;6p;Pp;8p;Cp;<p10000p4p710R0g000MR1!s5%p8P!s7$iR!sF'2p8g001GR3p4p7210P2p8p1002!s7$!s6%g002Rk10`Tg003Zj16Tg004?j12!s/$dj1UTg005Bk10=Tg006Dj2;!s/$`j21Tg007;k10^Tg008Gk10XTg009Mk20V!s0$jj2!s9$:Fk10TTg00;Rk10OTg00<Xj1aTg00=6j1jTP3k20J!s6$Yk10ITg00>;j1x!s/$[j2RTg00?;R3j1!sf$?[j1eTg00@;j2>!s/$Uj2!t3$AXR2j1STg00B8j1~j3Z!s2$Rk205Tg00C5k30]!s0$Rj4oTg00D9j1n!s/$^j2mTg00E@k20W!s0$hk30!v&$FLj1P!s/$kj2NTg00GTj2lTg00H@j3H!s/$`k10!tK$I>j2}!s/$\k10!sU$J:k10M!s0$ej2|Tg00KHj2k!s/$kj1yTg00LMj3[Tg00M0k30!s{$MSk20GTg00N5j2g!s/$Ok20FTg00O;k30E!s0$Zk40DTg00PLj2fTg00QWj23Tg00R=j28!s/$gk20CTg00SPk30BTg00T9mG0@mH0ATg00UElO9Tg00VFk10?Tg00WNk20!w,$Wnj20Tg00XHj7\Tg00YIj2uTg00ZMj2!vu$ZjmY0;TP1j6vTg00\6j1wTg00];j4_!s/$VmP0:TP0j6sTg00^\k80!tB$_amC0KTg00`fk60LTg00akk40!u3$bok40!tM$d4k207!s0$Qm<0!z|$e6m<0!wg$e[k30QTg00fDk40!yT$fbk40!zv$gMk70!{M$h1k60!u<$hUk70!w=$i9k70!yI$i]j8qTg00jAk404!s0$ak30YTg00kdk303Tf0R0#6!s$%p=M%60#6p>0_%60#2p=D%2!s-$W!s-$#2#2p=z!s2+!s$'p=^g00lgR1/;0p=5g00mER4f2R5f1R6P0H08p=Ig00nHR7?Z60p=LP4f4R8f3R9g00ngR:%O5/u6;H0H00p=41]56!su$71X10p=F20710p=Jg00okR;!sm%<1g;0p=QP;P7P;P;P3P8P2P9g010IP5P6P0N<06p=r!sF$0P2P6P5P9P8f5R2f6R3f7R<f8R=N<0Pp=pAZ;01p=dB0Q;60p=EP;!sm%H0Rp=KP;P6g011!s7$1p=b!s5%]R>g012<R?P?g012\R@P0g013<RAK02p=cP6P>P?P?P@P0J0\p={P5!s8+6P0K0[p=Y!s:-!t7%3\!t7$P!sl%:!sZ3Zp=iP9!s:+!tw$Gqp=hP3!s;+2P8!sI5Gqp=VP3P2%w8P9!s<%F\p=Ag014CR>!v|%C!vq$51]60H04p=@B0Y460p==1160,15p=?AH289@0356/10,13p=BP;P!s{+Esp=GP4P9P5AH:6!xK$>0<!t#$21]89H04=H35@0360p=`!t#&,19,18p=tp,5HCEILRA$0`g015JRB#6RC#6RD#M#M#MRE#2#6$0_#M#D#W#z#^#^#U&0=ARA';%ME!s?1,;A'1RAePAp,4HSECRA$0^&0XARE#5%2BRF#URG%WFRH#WRI#2RJ#URK+0VRL,XE'1REePE&0TA&0OARA#51XAL!sz&%aJRJ#jRA%6FRF#a00JA%aI#j%aH#jRH$0I\ARI%xHS00Q00AI2961RH5%O9'LP<!{#$5%e:R:D4%5<A7=3L%5=f9RE?7=L%FEf;RMf:RNf<RO37A7ONM'>f>RP,T41RHMRQ%OORR'L%SQRS%JO'<RT%~7RU%~;RV%S6%S0'<1L602056040]Z0L7X[7R7PQPS%QSPR%J0X[;RRPOO1P!s1$SPRPOPO%QODrM9pP=CoPT1RHORT#n%STRQ#51m1P%FP%JPRW/<P'11;P1%dW'1'>f?RX#JRYP;20WGKRZ%FG%5K%FL[[R[%5GR\g015oR]B0UGK6UW]RK%5L\]^]\R\p-0R]g016KR^g0177R_#PR`#PRa#PRb,N;Rc1N;aRa1N;_R_'E'Eg017VRd'l%e^Re3HRf%x^Rg&0S;Rh1};5Ri?K5h7K6&0N;Rj&0M;Rk1|;1Rl1k;FRF'b,ckRm1{k8Rn5YkA:kFl1{k2Ro5Yk5ik%y?R?PkPmP?Pk1k;BRB=[;F1|;G>0H;JRm5:kP?PkA:klBRpP?1bBm,ck9YkpRpChRqChFV20Gk@R@P0P5g018BRrg018bRs'g20F05=ZrsdB0E;16H0DRsbRbWbXX@;XA;XS]WT%F6Rr/151;61/19'>%F5A759L%59%581X8L'1[[[[^@;^A;^S]^T]RtP0%d9RufCRv,<9PvfERwP8PEPOf=RxO8bQbUbVb\bNbYbO,fP13JP,8J/<PRy%OxRz,LT%Jx,<QR{PUPVP7PTPQ%QQPzPRPxO1PSPRPxPx%Qx!yN%ECoP{1RHxR{#n%S{Rz!yN$X%FX1<YX'11;X1%dY!yJ$@RY#JRQP;PZP[PKP\PfPgAKh5i?K6hPjPk%2C,k;RC,bl,ckRf=YknA:kCl=Yko5i!wB$Pf!wH$[;BC=:kmP?P!w;$P@P!vg3XT]PtP0PufDRu,<9PuPwP8PNPMPO!v+6Py%OPRt,L{1<zWRW!ux&{Pz%QzPtPRPP!ux&PPP%QP!ux%NCoPW1RHPRW#n%SW!uv$Y%FY1<QY'11;Y1%dQ!uv$ARQ#J!ut,%PbRb#P#P,N;R\1N;b1N;`20C;G>0B!{]''E/ld1Ea_,Ec,E\/ld=H^e5H^Pg1};99Kh9AKi9h7K6Pj!v6$CBRj=:kFA[;FBRi=:kC!vY&1blB,c!{$'jm!{1'C!s/&i!s8+FP?PpFVFV!vw6^;A7506A7605'>A785L%52A728L%53Rs1X3L,1s[[[[\r!za'^;P0fFS01fGRrPw!wK%PxPPPXO9!wQ6P4f`Ryf_Rsf^RLf]R@fYRpfXR?fRRFfQRlfPRkfORifNRmfMRCfLRjfKRBfJRhfIRgPuPv13JQR^13JYRe13JXRdPPfBR\NG0@fpRcfoR_fnS02fmRaPPPxPOfiRGfhR`13JlRbPMPNPEP=P<P3P2fbRKfaR[PyPsPLP@f\RZf[R1fZRWPp!#;n&MO9fTRRPcfSRS%yARtP0&0?4RzFA,CX20>;;R{A@lli%e{R7PFP01=F01T40RVP0PlPiPmP:D43?FBX0I,0IXMA,0AXL!s+$K!s+$J!s+$F!s+$E!s+$D!s+$C!s+$B!s+$2!s+$1!s+$I!s+$H!s+$G!s+$Z>!u?'PZP1PWPpP?P^PePdfWRUfVR]fURqPRPSPFPlPk!te$CPjPBPhPgfHS03PrQ01PwMO9Pu%2D#D#D#6!s&&D#D#W#U,3JPvPtP\PzF\!t?;PUP]P!t9<Q!t7+PuPvP\!wp$YAIv0XX3;PO18JeRDP6DGPX1RHX%O0RH'LX3;PM18JdRdP0DGPQPvP0PDPPP:D4X3;PXPvP\1uHPP:H0<X3;PNP!sQ$18J^RHP5DGPQA7HD01]0DRf/;H'>X3;PY1;f\A7\D0!s6%XA7Q0\A7\0Q!s7%8!sn%P!tc%!sp%9NY0;P!yS'WPp!uc8wPu13J\RH!v7$XPvP0NH0AP;13Jv,8JfrRefqR^PcP_!zp&kRDfjRd13JSRf!zp2dRofcRnPK!tG+!wB%!zj,P]PePqPtP0P!z_$QS04P{18JbRb9@XXP7PRP01=R0S05P0PXPbPkP:D413JFRT,8J=I0kR|'17?V!zn+?!yx$>!s+$=!s+$<!s+$8!s+$7!s+$6!s+$5!s+$4!zn4;!s+$:!s+$9!s+$3;P0PvP8EvP!uu$Q02!ux%PdPGPT!up1P!uj5W!ul/qP^PR!ul,YP{13Jk,8JRT9@FFP7PSP01=S0P0PFPTPiP:D4AI0bi!u_~!u_%P;18JHfsRHPe!u`$!xU%lRbPD13JR!xQ2eRTPo!ue4!ua-UPHP]!ua,\R}P{A@RRXP7PqP01=q0R~P0PRPXPl!xH$8Jf=I0lRf!ub~!xC/\P9EvQ04P{A@SSl!z1%Q!z,$S!|0$:D4/1|!tZ~!w>$!s$?IP}P{PRPRPF!vU%F`S05P~PV!vX$F!vX%R|/1fDtX!to$X>AX=AX<AX8AX7AX6AX5AX4AX2AX1AX;AX:AX9AP}Q!so&|!s`$!#8=y!t5-Pfp+01CS05p+01BR!s5$AS04p+01@!z,&{S06fzR|13Jn!z02tR~P!zZ'!}<$aPbPD!z1-ffR_Q05PT!z4,lP{A@nn[P7PoP01=o0P0Pn!zq$:D4!xH/!urw>P!u$'X!uU$aPb13JqPO!uP0_P!|X5!#Sx$5MO9P?P~PUPtP6PzFAP{P]P]PRP7PUP5F`1=?91T48P2PpPUP]!#5x%p,8J=I3Up+01JS02p+01IRpp+01HS07p+01GRR!w9%Q05Pf13Jd!w51Q06P|fyRLfxRsfwRyfvR[fuRc!uJ&!~H-aQ02Pb!w;,uP{A@dd`P7PDP01=D0P0PdP`fgRa!w=~!w='[[[[[XZ>P{PqPqPSP7P]P6F`1=U51T49P8P?P]Pq!vJ&?!vJ$2]!}>BpQ07PRp+01FR]!#<2%fQ0413JGR!#<=2|PLPsPyP[P!vM'^!#?6+MO9Pb%wpRrPDPtPwPzF\!t,&P]!wZ%!t$$Pl!wX1!s|8!wM-bP!sw%0PzF\'CP{A@GGaP7PdP01=d0P0PGPaP_!wI/XMAXLAXKAXJAXFAXEAXDAXCAXB!#36&IAXHAXGA!#A:%QPY!{3&!{'1!th'!sL%eP^13JW!sT2DPdPGP`!tR$!{Y'!sh&MO9P@PLPZPtP3PzFARz/CzP{PWPWP?P7P1P3F`R71=13R11T43R4P3!sB$UP:D4R:'1RU'1R?'11g>zP7P?P8P1PUP9P4P:P5P6C_!s$%NP0:WwWcWnWvWoPvP0EsXh}L09X0IZ0CAZ0BAZ0AAZ0@AZ0KAZ0JAZ0IAZ0HAZ0GAZ0FAZ0EAZ0DAZ0?AZ0>AP0NC0KbPbPWPXZ>J0LbebfbdWmWtWpWsWrWaW`WbWlWuWzY0<X|;Xq;X_;W{WxWg!#7_-Z02AZ01AZ0:AZ09AZ08AZ07AZ06AZ05AZ04AZ03!#8/2Z00AX~!#80+Z0=AXyAZ0;AW}bibkbjo"). Qed.

(* [comment removed for export] *)
Lemma rrw_cells_app_split : ltac2:(zQ "d0!hh0!jgb!p9!hl9!h9!jc!km7!hje!se!la!kme!re!knb>1m>0@1$5@1$4#k0@1$7@1$5@1$4#8>1A$9>3cs1@1$3$0>3cs2@1$3$0>0@4$1$2^4^3@3$6$0^2^1@2$8@4$1$2^5^4^3@4$1$2^5@2$b^4@1$c@1$a^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RF_am_E ()) ["HCW"] "##H+h01Hh14__x1h24__x2h31ah41mh51Bh61nh71xh82B2h92Hah:1Wh;2WFh<7__arithh=4__ffh>6__sat3h?!s/%4h@8__varmaphA5__withB4__x3hC1bhD3bs1hE3bs2hF4cstrhG4segshH1AhI5HCANBhJ6HCEILBhK5HSECBhL3WF1hM3WF2hN2_HhO3cs1hP3cs2hQ5cstr0hR1lhS1yp&0p;1p;2p;6p;4p;3p;5p;8p;<p;9p;7p;Bg002Rk103Tg003Zj1?Tg004?j10!s/$dj1FTg005Bj1bTg006DR0j2<!s1$`R1j27Tg007;j1]Tg008Gj1[Tg009Mk201!s0$jj2ETg00:Fj1vTg00;Rj1qTg00<Xj1TTg00=6j1S!s/$Yj1hTg00>;j1DTg01R<j16Tg01SDj6`Tg01T[j4KTg01Uaj13Tg01Vgj14Tg01X0j2^Tg01=dj3ITg01Y:j2\Tg000Mj6MTg00akj49!t1$[j2=Tg01ZGj5ZTg00AXR2j1:Tg00ZMR3j21Tg01[Ok202Tg00];j4QTg01JBj2YTg01\_k20!vI$D9j1PTg00E@j2~!s/$hj3}Tg00?[j1uTg00I>j2VTg00H`j1tTg00fDj4U!sA$\j1pTg00J:j1o!s/$ej2lTg00KHj2L!s/$kj1iTg00LMj3HTg00i]j8jTg00MSj2kTg00N5j2R!s/$Oj2gTg00B8j3mTg00O;j3n!s/$Zj4fTg01>Xj1eTg01]kj4dTg00e6l<wTg01Amj4xTg01^Nl9aTg00boj4yTg01__j4z!u3$bj4{Tg00gMj7|Tg01NGlBXTg00dQl<_Tf0R4#?!s$%p=>%04#0p=J!s-$#0#0p=W!s2+!s$'p=Gg00lgR5/<4p=;g00ngR6f1R7;I4p=8g00mER8f2R9P7P4Cyp=@%:4,17p=5%64#:p=CP8P!sD%zp=A!s3+9p=2g00okR:P7g013\P4C{p=O!s4$1]R;g012<R<P<g012\R=P4g013<F|p=N1R:4p=Bg00nHR>P>P>P:P:P:g01Q9P2!s$$3g01QYf5R?f4R@f3RA!tI%MBXp=r!sX'!sQ$?P@P!sD'<_p=s!sB&!s$%3P4P7P9P3PAP@P?f6R3f7R2f8RBf9RC!sv$cp,5!~~$RD$03g015JRE#?RF#?#>#>#>RG#0!s0$0#J#W#G#G#F%bDRD'<%?G!s@3,<D'7RDePDp,4HSECRD#]%[DRG#;%0ERH#FRI%JHRJ#0#JRK#FRL+01RM,EG'7RGePG%vD%qDRD#;1EDM!st&%TK#S%TJ#SRJ#h[RK%D6R61874RD9@A9A@@A9%69,5A=@@7P8!v7,E`P1!s6%1897RGCK%CG9A@A%6A,5@=@?9P4P8P3P?18@ACKP118?@RN#3%4N9223183?#C9AB2%62,5B=@C3[P41823#3f:RN18B2#472Cf;RO18CB#C7ANP1%3D%39RD%37RC'7[RP%34,7C%3GRG[%3A/7D\G1^74P7n20010!s#$12!s-%0XC6X36PP^C6^36P4POPNPAO3%3ORO%3N'7P1f<RN#3POf?ROf>RPf=#6'5;@NP4%3PRN%DJRGf@RD/8O#4fCRCfBRQ;24XRGP2%4D%4O5IJR21\DOEMfARD=2Q2g01``#DR2P1!vi%AIJ74C9!z1'!s0%1=J9,5AP7C9'7[RO!w<'C9!w6$=J7,59P4C9'7!s_%AIJ97C9RR[P3!s8%C9!w@$=JA,5@P9C9'7\R!x+,DZ!v9:EGXDGX3:X4KWGPO^EG^DG^3:^4K^G2P4P8fDR2PC%4QRQ%4DRDP7O6A22CQ1=JQ,5C=22D!v`$ER1%4CRD7221=JD,52=21QfFRQ!x^$1;@CP4fGRC%41R172QfHR2!s~$,=J,5C;21P>%4CR1,=JfJRJfIRD%:4RK'1;21X6>P4%6CRG202CBEM%:GRO,12=2DQP8PJ%62RQ#:R@,1DRRPCCKAAJRO%3CA2JR1PBP4CQP>182C#6fKRB?AJKX6>PP1YQGRG2002C!s}$9AJDP8PBPJ%6DRD/YQRB#:R8%:DRG,1JR2P@P4%PD%;G1~ILRC1E5I%;L1E5M[[RP%;IRRg015oR1A}IL7UW9RL%;M\1^9R!sA$6KR1#uRM%D1R1P:1V:9RIP7%t:CU%p:RO%o:R?P;P<P<P=1l:51L:HRH'O,N?%i<1L:EREAH:EHR<!s;$Gj1k?=R=P4P9g018BR;g018bR3'R1g49=m;3dAn:57CfR5b=b@bAX1:X2:%;71179R3,<7[^1:^2:P4fM#CR;fNRSPAO3b<b>b?bF112@R211J8RT'<11G@RU,1JRV,<2P:P:P0P4X7:RWP01<74#eXS:X7:P2P2%B2PTPVPW!s$$!#7T$a_1174Cd#BX4:X6:PJPJ%BJP8PUPWPW%BKX7>PBPUPDPG%BGPQP@%B@ErEsM:cM<w%PQ%;@%6JRJ#P%:J#;PCPPPLPRPMP1P:PIP71V:ACUPO1L:FRF9H:<AH:HF9H:E!vW$P=P!v,0XB:1147/191143'<!v0%^B:P4P;%CSfO!v-+QbFCxM9ab:CQb8W8WNP7P4O2!|z0!s/&b5b0b5XMNWL!sK>;b0W:W5W;!sJ=W0!sB=CQW0XP6WOXH:W4bIbKbJo"). Qed.

Lemma rrw_cells_app_join : ltac2:(zQ "c0!hh0!jgb!p9!hl9!h9!jc!km7!hje!la!kme!re!knb>1m>0@1$5@1$4#k0@1$7@1$5@1$4#8>1A$8>3cs1@1$3$0>3cs2@1$3$0>0@4$1$2^4^3^2>0@4$1$2^5@2$a^4@1$b@1$9^3^2@4$1$2^6^5@3$6$0^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_RF_am_E ()) ["HCW"] "##Xuh04__x1h11Hh24__x2h34__x3h41ih57__arithh64__ffh76__sat4h8!s/%5h98__varmaph:5__with;4cstrh<5cstr0h=4__p1h>1ah?1mh@1xhA3Hi0hB1nhC2HahD1bhE3bs1hF3bs2hG4segshH1yhI1AhJ2B1hK2B2hL2H0hM2H1hN2H2hO2H3hP2H4hQ5HCANBhR6HCEILBhS5HSECBhT2HihU2W1hV2W2hW3WF1hX3WF2hY2X1hZ2X2h[3cs1h\3cs2h]1lh^1oh_1zp&0p;1p;2p;4p;3p;5p;6p;<p;7p;8p;Bg002Rk10HTg003Zj1ITg004?j14!s/$dj1TTg005Bk102Tg006DR0j25!s1$`R1j2>Tg007;j1tTg008Gj1rTg009Mk20ETg00:Fk10ATg00;Rk10!sV$<Xj1mTg00=6j1j!s/$Yk109Tg00>;j1WTg01T[j4PTg01R<j11Tg01Uaj17Tg01Vgj1BTg00ZMR2j20Tg00AXR3j13Tg01X0j2sTg00];j4KTg01=dj3OTg00akj4!t[$>[j2YTg01ZGj5qTg01[Ok20GTg000ij6`Tg01Y:k20FTg01JBj2NTg01LDj1!uN$Kkj1pTg00B8j39Tg01bCj1!sf$D9j1MTg00E@k20@!v-$jR4j26!s;$hk30=Tg00?[k10<Tg00I>j2^!s/$\k10;Tg00J:k10:!s0$ej2k!tA$Hj2]Tg00MSk208Tg00N5j2S!s/$Ok207Tg00O;k30!t8$OZk405Tg01>Xj1iTg01]kk40!xK$e6l<hTg00fDj4g!s|$0k30!w/$Amk400!uJ$\j2~Tg00@;R5j2}Tg01cAj3d!s/$gj6aTg00CRj4fTg00H`j1|Tg01dPj3b!t+$bj4\Tg01e3j2R!v|$Mj6{!s8$Pj6lTg01\_j2zTg00boj4yTg01__j4xTg01fUj3wTg00gMj7vTg00i]k80?Tg01NGlBoTg00dQl<uTg00LMk30!y/$h1k60C!s0$Uk70DTf0R6#I!s$%p=H%46#4p=X!s-$#4#4p=n!s2+!s$'p=Ug00lgR7/56p=2f2R8f1R9/66'>p=:g00mER:P8P9P6Cyp=C%16#3p==P!s;'xp=<%36,09p=8g00ngR;?O96p=D!sJ+Ap=?Aw:96p=Fg00okR<P9g013\P6C\p=Q!s4$1]R=g012<R>P>g012\R?P6g013<Fvp=@f3R@P=P>P>P?!t#%L0?p=L1S<6p=;g00nHRAPAPAP<P<P<g01Q9P3!s$$2g01QYf5RBf4RCP@!sf%MBop=[!sV'!sO$BP!sD,<up=Z!sB&!s$%2P6P9P8P2P@PCPBf6R2f7R3f8RDf9REMBop>03B0B<96p=J!sZ$4P3P4P2!t$1hp=eP9!uD+6J0Cp=cP8!s8+9P6K0Dp=VP!vI%16!vI%_p,5HCEILR=$0Hg015JR4#IRF#I#H#H#HRG#4!s0$4#X#n#U#U#T&02=R='5%IG!sA3,5='>R=eP=p,4HSECR=#t%r=RG#2%44RH#TRI%XHRJ#4#XRK#TRL+0ERM7:GRGePG&0A=&0>=R=#2?:=M!sr$%mKRK#j%mJ#jRJ$09R=[RG%W;R;AC@89P1P:!v,%CP%=89<C@%1@,8C=CB81DC@9C2B[P6P:!vW%CPP1%7B%BB9?32%=29<D3%13,8D=CE2f:RN1DD37CE[[P6%73%BD9?NEf;RO%=E7<Nf<RP%=NRQ,0O;CEP1P:f=RR%1O,8PRSPNCPA<RSQf>RS1DPO7CRP6P:f?RQ%1R,8SPP!tS%Rf@RT%=SRS,0Q%BR3?fARR%1Q,8T;<SfBRS1DTQ7CR!tX$QfCRQ%=RRR,0S%BT3?fDRT%1SRU,8Q;<RP:fERRPT1DQSRVCP%1VRW#39<RT%7V%BVRV9?RTP11D96#7%78%79RX'>RY[%76,>X1D89#7[RX1D@8#7\Y1s96P6n20010!s#$12!s-%0XD;X>;PX^D;^>;P6PTPQ%7T%7QPPP@CKO3b1%WJRX%BQRY%BS5OJfFRZ??R6X]Xg01``#WR[P1!x+%AOJ96CA!{B'!s0%1YJ8,8@P9CA'>R1[!{^'CAPCP@1YJ9,88P6CA'>!s_%AOJ89CA[R\!x\%AOJ@8CA\1!|@,Dq!uG:FXXEXX><X?GWGP\^FX^EX^><^?G^G!yX%ZPR%BTR:PYA?ZR:1YJ:R[,8R=?ZYPOPA%1TRYfGRG%36RX,0Z;?:XBAP8P[20GTPE`CKO6b1PV20FQSE`CKPA%1QRV/NURUA<ZRXXBA%2TRP18TV/5M%26RV%3YRY7:610Z9#E,FG%pJRJ59=#G[^4<%3U9<RT10RY/5M%1ZRZ#3RY9:V6RTfIRUfHR[/09#E'F=9=J!s\%10GYR:#2R\%1RRR,8:/5MfJR:%1[R1#3R],0U!s\0\T^4<1NZR#39<[G%1G,8[/0Y/5MA:V6]fLRYfKR[%1:RG#3RR'0!tD4%2:%1URU/N1!tt$T,0:R^/5MR_1NGU#3!u+$`fMRa10Y!sc2Rb'>%M1Rc%2]Rd%MGRG%2RRR20@ILRe167I%2L167M[[Rf%2IRgg015oRhB0=IL9UWCRL%2M\h^Cg!sB$6KRh$0<Ri%WhRh1^<9&0;<Rj&0:<Rk1k<7Rl1]<4R4'Q,@kRm%p>R>PmCL208k?R?P6P8g018BRng018bRo'S20768=9nodB06<79H05R7b6b9b:X0<%29\V^0<P6fORoPNO2b5b7b8b<b;P_PbP_%3UR_/0]Rb,0:Rn/5MP<P<P0P6X@<RpP01596#iXH<X@<P^PnPp!s$$!#:H$a_1096H04#;X?<XB<P:P:%;:PTPbPpPp%;XX@ARAPZPbPUP_%;_P1P]%;]E[EZN:03PMPM%;MM<hPcPdPGPRPePfPLPgPiPhP<1^<8RRP91^<@CgRGPjPk1]<HRH,J4Rd1]<FRF'J1k<I>01<KRK!v[$P>1JHFRI,J4/QK,@kCLP?P!v7,X2<X3<1069RK/08/5M108@,09/5M[^0<^2<^3<P6%1aRa#3RMfNRc#1R]#3R1PoP2O4!vh,H00%=[R[,~9169[15[9'}P5%=YRY,6815Y810c@#E,Fo!yw%P616@MPDPC%2CRD1N]aRc#3RY,6CR5'>101MR[9:DCR_PDP5PDPpP[O1R5,6Cp-0RU/SDA9UDDe9dDDPp16!wl,RDPCPC%;CPYP5!ws$APcP[P]P1%;1R[Pa!w9$E[EZGeEaP@CfRaP_%M]Rc%21R5fPRY#1Rb#MRZ%3b#2Rb!w[1PRP9%|<Cg!wT$ckC9VkmP>Pk1_4H,@kRRP>AVkmRCL!w>6=U1>V81698%28?:8@[!w8'=UP6fT#=RVfS#1'8,6NPVPNPBP2O5!w6,bAO2W1P6O115M@PaP_PcP5!yz$!tu/GPjP<Ab<FH,Jdg01P01J4FC\,@k!xz7R89,0K106859<!xq-PNPVfURNO3!tP/10o11RC1'010oC59<P<%1oRo#3RK,0Y1RBKRd'0fR%E6!#3]&X_<P2Pd%2BRd1No]R2#3RJ,6BR='>10K1Rb9:dBRZPdP=PdPpPbO1R=,6B1SUdA9Udde9dddPpPDPBPB%;BPJP=!xQ&2PbPoPK%;KP]P1P[!xN+CCfPZ%Mo%2KfQ#1RK#M%3K#2!vK4k1ckB1_4I,@k5Vk!x?$QH4!|]$Ab<4HRH,Ql,@k1_HF!sJ%!xO83!xR$0989:@615891R8@R8#2?:8C!x[+3!x^%%2OPV%=NPOPBP3O6!xU110YBP6E{bP!x_%!#<<,211000!s'$b^XT`X4<CKCKWZWOXN\P@ElWYWMXLPPEElPW1z!#;K$WVWKWXP9P6O2!#=2/!s/&W1!sB?WUWJWW!sd[X\;W[XI<W?bQbSbRo"). Qed.

Definition ram_entry_post : ltac2:(zQ "70!h9!jc!hje!la!hq5!jm1!ks2>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2lo$3>2st$6>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>0$4P") := ltac2:(zQ "i31!h9!jc!l5!la!se!p9!s4!ksc!re!hje!hm1!hif!hl9!jie!hq5!lhb!hl1!hj7!hm9!jm1!lm2!hv7!jqc!ln0!jr5!ijb!inb!is5!jgb!lr5!ls2!lsc!lta!ks2!lu3&>0@1$1@1$0#k0@1$9@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h3@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2lo$3\2st$i1\1m~0\3ms'$e@2$2@1$1@1$0#k0\2x1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\3s1x@1$1@1$0#k0@2$2@1$1@1$0#k0\3s4x@1$1@1$0#k0@2$2@1$1@1$0#k0\2a0@1$1@1$0#k0@2$2@1$1@1$0#k0\2a1@1$1@1$0#k0@2$2@1$1@1$0#k0\2a2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@2$2~0\2m'~0@2$2@1$c@1$1@1$0#8\4junk@1$c@1$1@1$0#8@2$4@3$h2$e^h5@7$h9@hf$h5^h4@2$6@1$0#k0@2$8@2$7@1$0#k0^i9-k0^i8^i7^h3^h2^h1@2$6@1$0#k0+hgg0^h0^e^d^c^b^a^9^8^7@2$6@1$0#k0$hf@2$6@1$0#k0$he^f^i1^i0^hf^he^hd^hc^hb^6^5^4^3^ha@2$6@1$0#k0+tthq8^h9@1$h0@1$1@1$0#k0^2@1$hb$5@2$4@3$h6@3$b@2$a$3$3@4$d$3$3@2$i2@2$7@1$0#k0^i9+k0@2$7@1$0#k0^i9@3$b@2$a$3$3@4$d$3$3$f@2$8$f+h0@1$h1@2$a$3$3^h6^2@2$4@3$h8$5^h6^2@2$4@2$ha$5^2@2$4@4$hc$5^2@2$8@2$7@1$0#k0^i9-k0@8$hd?4HSEC^1^i2^i3^i4^i5^i6^ia@2$4@4$h7$5^2^h8@2$8@2$7@1$0#k0^i9-k0@4$i0?5HCEIL?4HSEC@1$h4^h7^2").

(* LPS 727298f3: [auxv_read8] reads one key word of [auxv_keys] (Ref/RMallocTree.v); it replaces
   [ru64s_read], which read a word of the old [u64s] auxv block.  boost-beast/http_request's
   Ref/RF_am_E.v (OSSV-509 tree). *)
Lemma auxv_read8 : forall m A w a, bytes_at rsegs m A (le8 w) -> a = wa A -> ov_read_bytes rsegs m a 8 = Some (le8 w).
Proof. try hcb. try hsb.
  intros m A w a H ->. rewrite <- (Z.add_0_r A). change 0 with (Z.of_nat 0).
  rewrite (bytes_at_ov_read rsegs m A (le8 w) 0 8 H) by (rewrite length_le8; lia). reflexivity.
Qed.

Lemma ram_entry : ltac2:(zQ "i00!h9!jc!la!p9!lu9!hm9!r9!ksc!lv0!lvf!hl1!hje!se!jj6!jm1!mk6!moc!jq5!hv7!ln0!ijb!inb!is5!mt9!lta!nid!ks2!nj9!jt4!jh7!lu3!s4>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$e@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m>0@1$1@1$0#k0@1$b@1$1@1$0#8>2lo$2>2st$ha>0@4$h8?5HCEIL?4HSEC^1^3>0@2$h5$3^4>0@4$h9?5HCEIL?4HSEC^5@2$7@1$0#k0^i5>0@4$h3$3^6^5@2$7@1$0#k0^i6>0@2$6@1$f?5HCEIL^6>0@2$6^7@2$he@2$7@1$0#k0^i8+k0>0@2$d@3$5$2@1$8@1$4^7Z@3$5$2@1$8@1$4^7+1>0@3$5$2@1$hb^8@1$h0?4HSEC>0@2$c@2$6Z@1$9@1$4^9@2$hc@1$9@1$4^9@2$hd+2+k0@3$h1$3@h5$h7^id^ic^ib^ia^i6^i5^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^e^d^b^a^c@7$h4@hf$h2^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e@2$hf@1$0#k0+ttgv4^d@1$a@1$1@1$0#k0^c@1$h6$3").
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

