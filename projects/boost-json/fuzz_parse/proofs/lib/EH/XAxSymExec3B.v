(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec XAxSymExec3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_XAxSymExec3B () := KReplay.lz_vm "#,}SC47Corelib5Lists7!s+#Def3map!sB,4Init9Datatypes3fstC46Std!s^+4!s+#:fold_rightC99OSSVerify6Proofs:boost_json:fuzz_parse3lib2EH;XAxSymExec33AX25sfactC13~~~!t9-ogicHFunctionalExtens!s1$ityIf!s?+_e!s@0!u@2!sn%8eq_ind_r!u^=app!u^7;filter_true!u_c6pt_gss!u`&!ssho!ssi;!ss#et_leaf!sx%I!ve72eq00K!s@;1!wA86!wA%!sB89False!sE$!u7b9aluop_eqb!u58!xV,4bool!u;4!sF31I4ELinuxProcessSemantics5Riscv5Instr5!tB$!sr#!sRL1!tFB2!w=85!vE$00!sC84True!w\:!sB%1!toN2!sRN3!sRN4!sRN5!sRN6!sRN7!sRN8!sRN9!sRN:!{Odmul!{O1!tJF!sZ$!zgJ!sR%1!sRN2!sRN3!sRN4!sRN5!sRN6!sRN7!sRN8K!xJb4expr01!#7y%5!#:'%6ZArith6BinInt1Z3!xj#!sC;6eqb_eq!tXi2!tX%!ssi3!sso4!sso5!sso6!sso7!sso8!yn25!yP$8PeanoNat3Nat!yT&!#4Rb8!t>#!#4Q+!#BR;4andb!sD<9!sD#_propc!t^R<!t^-B4AX2B>p_!#>_'!uW#!tf$!s}h!#75'!s}+!#Dt'4Bool!s'$!}i0!w>6!sF$!s]58!s}#!uw#!wWiind!#Cb=3and00I!z%h0!#BcA3nat!#@]-7Numbers7BinNums1Z00!wde4lget!zA3!#Li1nth!t7gs!t7'!#EN<list!#EN>!sF$1!sFB2K!vq@2!|[<7nat!xo#!sfA1!u5<6option!w]g8okey!#HxE7reflect00!|I?!|2$specK!u1C!#Ke87f_equal!#PE;transK!tsD!t+93not!sbE2!u2D2!#8Qb6kentry!#:=&!x4e7v!x4#of!svlri_vars!svk8ri_other!sw%k!swd6rindex!#B}&!tpe9ri_buck!#3A&!sxfl!#Tr#!#4;+!yKj!#7u%i!vbl!#8nB4prod!#3rf5mk_ri!#8R%!v+b:f!#\0#ange!sw%!}Jk1!suq2!suq3!suq4!suq5!xJi9lit_strip!tm&!zX+!#@%28positive!#7\-!#@N52!#N~<pow!sC=su!#OC<3add!sC=ltb!|?e=!#=3&!#<B#!#4Gj=p_!#J1&!#HLm9first_var!sxk>!#79'_cons!ziq7!suq8!suq9!suq:!}N&!#80:8lis!#Eg#!w{e;!#7>+I!}t3!#9N71!|R>eb!~4@1!#<Ab5sadd!#M7'!#3mF3!#Occfacts!#C1m5mkbc0!stlbc!#=9'!}xf!x{-!#3qne!sy$_fB!#9fh8!sv'!sui6clamp!#@vi6lin!yD+!#s_c!ss#trivial!~qB3s!#ree!t=#!#C%,!v&dzdiv6!#@B%!#3=<mul!t8emod!t8+!u}et_shamt!#3nL!#5l=max!#Gccmask_cov!#NO&!t<=div!#iU<modulo!sF<4log!#BX=min!vydzsigne!wq,!{5<or!#km=of_nat!#aJ?le!#CVeA!#5f-!#7^,!u}c5two!zlk7!sr$m!#S_k!#6[%0!#7Ri7!su&!tmk>!#9B'_eqf!wVj;!s{'uel!twk!uo&!vej6e!#7>m5dea!#iD&!srdunlin!vSk=!z;'!xK-!#Fbebase_!wUo:!sx,!tsk<!yF&!upp7ealign!zCl!st$!~wk!ss$!}xj<pageup_!to-!v\e6bc_ffk!xPl!su%_!#Iwo!#DQ#nowrap!{Bk!sx,!tslsrl_expand!tsk!sx,!{Bjlins_!#6_&!#A:;op!#yEc7!u1#rem!v#jhigh!#DM#!#lkk@!yi-!#4<o<!#4<%!s{qfact!{hq;!sy-!{imum_!s~$x!{il!sx+!xhl!}^-!wkp!tz+s!usj9!sw+!urm!wg,!urpA!z_/!t$p?!vt,!s~p5bc_f!vwl4mkb!#j&k@!#CQ,!ujp=!#Ya#est_rel!zcj<!sz/!#3Ok!#DV,!}Ul!x_$_!wo,!}Uhsubs!#}4m!vj&!#azj!sv'!~El!yW0!wdo!#Ci#s!#L,o!sx,!swi>srl_scale_nee!#Bqi7has_srl!sti5zcdiv!wZk?!#;p1!s~k<!#BZ+R!#@\j!sy-!uul!zQ-!uuo!#7+'!|Ouapart0!|Oo!sx%!swi6lsub_!#VKk@!y]/!#8xo!uo+!#COj!sw+!w`jshares!$$fn?!yU-!zUtb!#7~sb!#],o4xlo!tlj3xl!$jOi6zlit!#j_&!xOjb!#4|t4xhi!vZlh!#}|k:x!#S6q9x!#S40!xMdxterms!xMpge0!#@/$!#\pj>!s|1!t{k8!s}&!ttj7!su&!sti8x!$7A$t!xVl_!#mSmC!xV2!~%o>x!#Tq/!s}k9xinsid!x]l8!sv'!tok<!zM'!#Fco!tt&_num!#Fcj!sy-!}Alxhi!unp8xlo!swp?!#X\1!twm!vl%!#43j!su&!#3<ino!$WQn@!zK/!#L:o!~:+!wapsub_itv!wak!su&!waja_!zP#!ssi5a_of!#3zs!#4wpkdisj!#L~o;!sy-!tul!yJ'!{Ep!#3}#s!usp<!sz/!~?l!wk/!#>Ro!#Rj+!s}o!#kD#!$#[k!#fY#k_!#kJn:!ye&!#txk9!sw+!wal!xb-!tul=!s{0!tyl!vl,!y\o7end_!#Q5k6!st%!}Il!$AN2!tti5mkAlu!tsk?!#4;-!y[l>!s|1!s{&!$Y%;neg!$E^e;!x{&!ywoB!|q1!t%oA!#9Q/!t$o;!u&$side!$#oj:!sx,!tsk=!sy,!z5l<!sz/!twk9in!vjp8!sv'!x]l!sw'!$0Cl!sx,!vdlmk_spre!#_tj8!sv'!su%!$gzb5!sr$!$|glA!{D0!#Rlo!~;-!s~,I!uvi!$1'l!#8O/p!#9Mw!#e^jsp_rng!ssi4sp_D!sqi5sp_h1!srmD!~&l?!#3w,!#N'o!#6h'!s|,!$]u<shiftrK!%?y&9micromega6VarMap1!%8z#!sD>0!sD6=RingM!s4'7Formula00!t567Env!sT#5PE!%M%#K!stL!sQ75Tauto8G!sJ'4C!sJ<B!sJ&!sH6:Z!t<+=Z!sT$CheckerC!v#<4f!%^8#!sq?C!sq0_soun!$~b<2le!sB<?!wz%_div_pow2!yIe4gra!#jy%I!u:@;!tY%!t3$00!v{<5eKind!%2S<unit!x|8!se%4kind!xyF3Op203K!t5A1!w&>t!{^@2!sD@3!{3E2!z`F8!tm<;!xN#le_mono!xQe8!xQ#_!$4D'!vzI5!tFfext_fi!$Gb&!#47<leb_le!#AYe!u_$!vS#!u`<!wm24!tc<!%EI,!vMB5Psatz!x`8!sO86K!|vM!y]G3!vWe7!wp#has!vU<!tB37!u:N!~'J1!wQArefl!$q@>!sK+!#EQekx!%VG,!tG$!#=6i!t$#!%VJ+!t$,!%Um59!sH'x!#Hhb8!#Cz#rel!#Hkl@kx!%8:+!u=-!txb7rel_li!%FWi!un,!#Hc%!vgm2!sws3!sws!$4ck7is!wY#!va'!%66>3I!%$PE!%VZfkx_cand!$iSnt0!&#H$t!#:JBto_nat!tBe>know_lookupA!$'^&!%g&clres0!#Lai4ele!$q;i9img_byte!&%Mi<lit_of!sy/!#Wfd!%=J#!#5yk<!|F&!&,&$!ul%!#F+0!%\l%iff!#6A$!#;l4;ZifyClasses3inj!sIB7rew_iff!z{34Znat5Nat2Z9is_nonneg!#ARD!#?>e<!#Bo#betwee!$6~k<!#8t%_sam!$EVk=!s{'!%\=,!{\d!%8<$!%mJ+!#3[:>pow_po!wa'!sN<:!sN#!sJ&!x,59SatDivModCZ_mod!sP&!s{C7div!sU#!sG<=!sr#!tl#b!#Qm?!sM$!t>#!sM15!tj$8PreO!s/#!#LJ%0_r_ext!sL>!st#!sL3!#DG3le!#Hr$!#P};8BoolSpec!#Qh7!|K/5mkre!#Dke?!#AN'!~\$!$\DjmkEx!$AEi8fil!#BE,!v6E!&;;-!sK96!sK$2I!#:]g0!|<9!#4t,8inj_succ!%c3d4bct!%c1,!&+58?!s<2<MemImageType7Segment!%vUd8sidecond!#F/j!vn%3!xV<8!x1#Inst7Inj_Z_Z!#Bzl!#w1l!#<6&!&#P,!#3;&!&B_+6!&B_$!t=eD!#Bu0_skip!#E>k!t'7!#e|3P!#5:'Pos3Pos2l!#EEe6tagg!$PMl6all_g!%K?3!%|f06Forall!#U0-!uS44!}}#!#8/95!us#Z:pos_is_pos!#44A;!#A6%_rev!tbC2!tB@!#3g'!{wimer!$oh'!z{6:!tb%_inv!vH>8lt!%f-%!yA?e!sD>!%gch@!&LZ&!yg$!xs+!#<$e!vH'!$UR#_l!s~zr!wO2!#Yi+;orb_f!&K3#!#3Pe9narrow_!$Vwl!ya#w!$S|n7kx_gkey!v0'!#Ke56eq_sym!#{dcptree!#{dl9kx!%|E/!#zacpt_s!ssog!%~/l6kx_ad!#7ak;!xc&_inj!#7f%!xKi1!{Nobuil!uil>!yD+!&Wb,K!{U7!&:~#1!t@eB!t@,add!#Q`,C5!#^a'!#^Y%6IntDef!%xd$!tHeC!tH1!#R,-8!t&N3Lib2Nd:and_elimF!#Dt%!&01d3ki!&0-m!#4q#!#z`'!sve5kx_w0!stpf!{,o!#c~#_sp!#N}4!&eM/!#=9$ex!#Dhe?!#:f%not!#9t#!uDk@!#=,'!t|%!$@fl!#3E&!&$lo6mk_ki!$<|lkx_select!z&ok!{nlF!#Kq1!wj%0!#$,~er!$^om!v|'!&O-n!u&0I!s}xBI!{lm!s}/!#32%!s|R!#>#2!ty%!#k;#!#\-+!#WKh2!unkA!wl1!#eS+!tub6s_!t$#!tuk:sym_read!x`m9!sy+!uhi5s_lo!$Bti8sc_hin!%Rel;log!xT&B!#6@kextK!stl8flat_sc!wTj7sc_dirs!wVm!yA#!#v;i7script!#yqk6s_nex!#3gi!#e,+6!#3kwB!#3k+I!vfk0!svi!~q$state!&9CD1N02C45stdpp9bitvector;definitions9bv_!&%N$!#qH;!$J2$!&/Nc4s_pc!yalregs!sskr!#U0n:conc!$5_#!#3'&!wF@7bv_!%:\#!wD;4la!&Abf>decide!%?Q#ch!#5gk<enum!s{1!~9m!#P_k:to_!$+9#K!#7_i;msize!$-%/!xT@2bv01C!&yG?7Prelude6bv!#o}#!||cridx!|/mupd!}qns!%+bi:!sq#_inv!&?I&!&L3cs!&Z7/!#@aestoreok!#>r+!sze7!$tY#K!#3eG;bv_un!#8/$!#A5e!tH$w!|Tk6!su%!v6k6mkMd!tjk5!ss#!til=amo!&+N$edb!v\k!sz#sz!sso!#37i9!#6j#!#}s,!svc!v\%uo!%{Xl!sx#newval!}Ml>!#Od+!$f=n:!#Cu$ep!#Pcq!sy$!#3IF7Z_to_bv!#D-d!#qC'!#Kadtep!$FTm5sjum!$uJi!#Hm,!tl&!&qCcs!&qC/!'=NGi!s+#!$4+d!w/+0!x#r2!uBN!#BJ#!$P2f<coeffs_divk!#D7j!sy-!#4Kk!&3q,!szk!%\v#lowbits_k!&B3j>!s|1!s{i:!&AE%l!#`#l@!xg/!$vZo!%oR+_!&'@o!sz'!twk6mkSrl!#ARlS!%{aj:!wa,!swjldiv_!%fC,!~Adl!#w@#!tp#!#t#kA!yN0!~Gt!%adu8!~E&!#d$j!su&!tmkC!#561!%$yE4lxor!sD<3lo!$8>e!yR-B!{Ek!sx+!yIla!%C$#gh!$#i$!#8jj!s|1!t{k!s}$low!tzp=!s{0!tyk<!$&C%mas!#?Uk!sy-!sxi5ctz!%zll7mkAnd0!#Uvm!$l@mB!yQ1!#5tnC!|Q2!#7xp!#3J+!s~o<!#7x&!#Qdo!#?N$!#6},!xrb4mkM!$QXl!yg$!#A<lAn!$B`l!|H&!wSo@!#4/-!t#o!~E%K!~EpK!zAnA!&@hror_disjoin!%k2k!sy-!tuk5mkOrB!}-lO!$oYi6i!$2x,!tfdza!%_M&!#C`=no!$@se@!xd/!yeo;!|M&!szo9!#ym#try!xnj8!sv'!sui7closed!#g7jevalS_de!#9[i6wrap!'$cj5!tk$!tgjprobe!ssj<all_!tk#_to!syj!$${$lim!#G\l;!sy#retiz!&E0k!sx,!swi;!vc$!{8%!||jsubexp!$7pj4nubE!wWk=!#3`'!#4^n6fol!#wSl!ss$!tik?!z@-!#8Eo!&Hy&!$/Q'!{@d!sx,!sw&!%%&::!'g5$_map!#k:F;!s{%_!$yo%!tub=!$3B/!uqlt!swq!ub#_on!$J;k;diff!tqp!&,y$!sy0!{Tf!zT-!~?pmkSlt!#h@ml!#9YkB!$:j0!#dUo!$0j$!&Lqk!su&!sti8!'IO#!'T~m:!xR%!#FFo!#L2#!sx,K!#4\R3!sXT5!vvc!$46$!#9vk<!yZ'!#Z7o!#<^$!#Z7l!$57#K!zWjpow2!$VW+!#Mxhlu!#Mxp8zband32!~9k!su&!|Gn!$<J#!&T=k!sv'!yEjzsx!uc'!#<Hc!sq#_stabl!'EYl!xL'!|0m7!v`&!tqk=!xP+!#=>oext!yKl!$^l#!yHj4!sr#!#5Uk!u\%!xKn!$`X%!st%!$Qjl!~nl;wr!'^t$!&g\k:!sx,!swj!$LK+!ves5!vek?!ve-!yTm9!$[''!#5hi!$Y=,!wbj!#L}#!#\m#!uij!$Y:'!svj!#ul$!#h#k8!tn'!sui<!$Np-!sy%!#T#F6awidth!#Szd:!$Kh+!{qk<!$Tl&!{nm:!$qh+!swi=!sw#!$z'1!%/462tl!#3sl3!u2j!$zD/!#5hr!#iTi<!ts/!ypkB!%+$1!yvl8!$SZ&!txk!$rC0!#Bfn?!$z[,!s~o<!$yi&!#TTo!${\#!tup!vw-!#|Qj!sy-!tuk=!$ZC'!xjp!$\=,!s~oA!$am/!t$o>!$ox+!s}o@!$rm-!t~p!$vT+!x#p!$ke,!s~o:!$hY$!#5_qst!&S_&I!$stC0!$`c@4BvWf!%K>5PosDef!%[_#eqb!+zjHmoop00!sRHcsr!sRK4ffmt!s}Jfma!s}K6fari!sSMsgn!sSK9fminmax!t'Mcmp!sSK7fcvt_ty!t%Kmvdir!$^rf:zf!#MV$!'d+k!sw+!}{l!+Dh$_!s{#la!$/gj>!s|1!#4wk!vn,!#3wn=kwr_offima!'H`k<!sz/!syi:segs_avoi!#CXk@!wn&readabl!usk?!s}2!t}kA!wo0!xqoC!{m2!#Cdq!w#s;!sy-!sx&!#ON57ex!s2#b!~+e!%Kl+co!$Y1kD!z;3!w;o!v@#!#5&p:!sx,!sw&!&0:'!$Ax#!+?,1t!w=d8evars_!#~9l@x_discharge!~Lo!s}2!s|i=!'#Q$ead!'9P+!~Ff!uy3!+Qdnx!%Yl%!#t3j!sv'!sui5rd!+Pnk8e!%<q#!xZk6cap_r!#:tk<!wO+!xLn<!%'~'!s{n!%,v'X!#DOj!sw+!tqk=!sx'!%ZLo;!x`%!szp=!vk,!win=!%2a+!s|n;!tz,!%3`k?!sz#execTXBI_g!'eIi=!s|,!szl7s_clea!%%&i;itab!#^%q>!wf+!zap>!xe-!$Abk7scr_ni!%#:i4!vl#!#63o!zQ'!tni:!sy,!swi3cl!'s8kB!}92!#38m5kcu!$D@j4!sr#!tgk:kzero_!tlm9!sw+!tqk9!vZ$!#c&ok!&Nr#!uko!sw'!ukmunk!tpn8!sv'!tolprune_z!+r<k!sv'!sui5ktri!'gzl!tk$1!#r=j7!su&!z;kword!xJo=!xJ+!#ZDo!'<11!#q4o!t&1!%slj!'>41c!|Kq1!tvl!z^'!tolD!vn3!#_9o!|\'!#g,p!#6/&!#v{o!#8x+!s}q!#<d'!s}o!xu%!yll7!su&!sti5k!'m{l9br!$%Tr!}H+!wW,".
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemantics5Riscv5Instr05aluop37Corelib4Init5Logicib2eq37Corelib4Init9Datatypesk44boolk44true89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~ma9aluop_eqb05mulopma9mulop_eqbma4exprma8expr_eqbk43natk46optionk43fst37Corelib7Numbers7BinNumsv51Zma9lit_strip99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B5FPX_1~~~~~~hhe9first_vark44listhhe4lgetk44conshhe4lset46Stdlib5Arith8PeanoNat3Nathp63eqbma6kentryhhe6rindexhhe8ri_otherhhe7ri_varsk44prodmaafind_rangehhe9ri_buckethhe7vkey_ofk45falsek47reflecthhe8okey_eqbhhe2RIma6KRangehhebfind_rangeIhhe5mk_rima5sfacthhe4bctxma8facts_ofhhe2BC89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B~~~~~~in44bctxmaberange_fuel99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B5FPX_2~~~~~~it19erange_fBit17erangeBk44Somek44pairma5two6446Stdlib6ZArith6BinInt1Zjkc6moduloma7ealign0macpageup_alignin46bc_ffkjkc3maxk44andbk43sndma3linma6lin_ofma9lin_rangejkc3lebjkc3ltbjkc3addin45bc_fkin45mkbc0in45bc_riin4bfind_rangeIma8erange_fin49erange_fBma7erange0in48erange0Bma6erangein47erangeBmaabase_rangein4bbase_rangeBma6ealignin47ealignBmaalin_nowrapin4blin_nowrapBmaasrl_expandin4bsrl_expandBmabfact_nowrapin4cfact_nowrapBmaasum_fact_xin4bsum_fact_xBma9sum_factsin4asum_factsBk43nil99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B6FPX_13~~~~~~lg34mkbcin45bc_fsin44mkbcma9sum_subst99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B6FPX_24~~~~~~ln6dlin_test_relBln6clin_nowrapRBjkc3subk43orbma6lsub_eln69lin_testBjkc3oppmaashares_varln6blin_apart0Bk44Noneln6blin_brangeBln6blin_srangeBma6zlit64ln68lin_ge0Bln64xhiBln64xloBjkc3eqbma6novarsln69xinside0Bln6cxinside_numBma5saddrma5a_offma6a_basema4ELitln68xinsideBln6ckdisj_apartBln6alin_apartB07ALU_ADDma5mkAluln67end_hiBk44negbln6ekdisj_apart_xBln6dranges_apartBma5sprepma5SPrepln6bdisj_sidesBln6ddisj_sides_xBma6sp_rngma5sp_Dxma5sp_h1ln6bin_sides_xBma4sp_Dln69in_sidesBmaclin_test_relma8lin_testin49lin_testBmaalin_srangein4blin_srangeBmablin_nowrapRin4clin_nowrapRBmaalin_apart0in4blin_apart0Bma9lin_apartin4alin_apartBmaalin_brangein4blin_brangeBma3xloin44xloBma3xhiin44xhiBma9xt_nowrapma6xtermsin4axt_nowrapBmaelin_ge0_scaledin4flin_ge0_scaledBma7lin_ge0in48lin_ge0Bma8xinside0in49xinside0Bmabxinside_numin4cxinside_numBma7xinsidein48xinsideBma7sub_itvin48sub_itvBmabkdisj_apartin4ckdisj_apartBmacranges_apartin4dranges_apartBma9sub_itv_xin4asub_itv_xBmadkdisj_apart_xin4ekdisj_apart_xBma6end_hiin47end_hiBmaeranges_apart_xin4franges_apart_xBmaadisj_sidesin4bdisj_sidesBmacdisj_sides_xin4ddisj_sides_xBma8in_sidesin49in_sidesBmaain_sides_xin4bin_sides_xBma8mk_sprepin49mk_sprepBmaeranges_apart_pin4franges_apart_pBjkc3powmaapageup_low99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B6FPX_52~~~~~~qpeccoeffs_divkB07ALU_SRLjkc3divma5unlinmaaldiv_termsmablin_trivialmaacoeffs_divmablsplit_divcqpedlin_nowrap_lB07ALU_ANDjkc3mulma5ctz64jkc4log205M_MULma4mkMdqpeflin_lowbits_knBqpeblsplit_divBqpe6mkSrlBqpefand_high_splitBqpeeand_low_splitBqpe8lowbitsBjkc4landqpe7mkAnd0Bqpecnarrow_maskBqpe6mkAndB06ALU_ORma4EAluqpe7mkAndKBjkc4lnotqpecor_disjointBma6is_litma4zaluma7closedbmabeval_closedma4nubEma8subexprsqpe9conc_tryBqpebconcretizeB0bbranch_condk4aoption_mapmaacond_on_eqmabdiff_branchmacrange_branchqpeblin_branchBmaalit_branchqpeedecide_branchBqpe6mkSltB07ALU_SLT08ALU_SLTU07ALU_SUB05BC_LT06BC_LTUma8shamt_ofqpe5mkOrBqpe6foldKBqpe8mkAluK0Bma8pow2_logqpe7mkAluKBma6mkAluwqpe8zband32Bmabsx32_stablema5zsx32qpe9mkAluwK0Bjkc6of_nathp63lebqpe6extK0Bma8sidecondma6SCFlatma4elenma9SCStoreOkqpebwr_coveredBma8to_saddrma2SAma9split_lit06awidthqpe8mkAluwKB3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeujb7Segmentma4lresma4LHitma5LMissma6LStuckmaeknow_bytes_litmaclit_of_bytesqpeeknow_lookupA0Bma7scriptsma9sym_statema8sc_readsk43appma3SCRma6s_nextma7sc_dirsqpe8flat_scBqpe5extKBk41Sma4EVarmaaSCReadBasema6s_knowma5s_logma8sc_hintsqpedknow_lookupABqpeblog_lookupB05instrma7stepresv54Npos35stdpp9bitvectorbdefinitionsvod2bvma5SStopma3SOkma4sset04ffmtma6s_regsvod9bv_signedvodbbv_unsignedma3SSRmabmsize_bytesqpeato_saddrKBib1I05msize3h5LinuxProcessSemantics5Riscv7Preludehghd6bv_eqbma4ridxma6s_resvma5sjumpma6sr_updvod2BVvod4BvWfvod7Z_to_bvma2SEma6amo_szma6sentryqpedamo_alignedbBqpeaconc_exprBqpebstoreok_scBqpe9sym_readB05csrop07fcvt_tyma6amo_sxmaaresv_invaljkc6shiftl05amoop06fariop06fcmpop05fmaop09fminmaxop06fmvdir06fsgnopma4SCBrma9amo_aluopma5mkMdwma4s_pcma9saddr_eqbma6sr_getqpebamo_newvalBqpecenum_branchBqpe6mkMdKBvod7bv_wrapjkc6shiftrv58positivema6zmod6499OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B6FPX_53~~~~~~hhsc4granhhsc8ext_fitshhsc7is_lit0hhscblit0_extenthhsc7ext_hashhsc8kx_wide0v52xIv52xOma5ptreema6pt_gethhsc7kx_gkeyma6pt_sethhsc9kx_buckethhsc3kixhhsc2KXhhsc8kx_buildin4eknow_lookupA0Bhhsc5kx_knhhsc9kx_selectjkc2lejkc2ltma8rangerelma9RDisjointma7RInsidema8RPartialma7rel_litma8RUnknownhhsc8kx_cand0hhsc8kx_candf36Stdlib5Lists4Listhjl06filter37Corelib5Lists7ListDefhjme6Forall46Stdlib6PArith6BinPos3Poshjp02lthhsc6all_gthhsc6taggedhhsc8kx_mergehhsc9narrow_inhhsc6kx_addib3notma6PTLeafib3andhhsc6mk_kixhhsceknow_lookupA0Ihhsceknow_lookupABIin4dknow_lookupABin43kixin48flat_scBin45extKBin4eknow_lookupABIin4blog_lookupBin4ato_saddrKB99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B6FPX_54~~~~~~hkofasym_readBIin4damo_alignedbBin4aconc_exprBin47mkAluKBin4bstoreok_scBin4edecide_branchBin48mkAluwKBin4bamo_newvalBin4cenum_branchBin46mkMdKBin46mk_kixin49sym_readBhkofasym_stepBIin49sym_stepBmabcoeffs_divkin4ccoeffs_divkBmaelin_lowbits_knin4flin_lowbits_knBmaclin_nowrap_lin4dlin_nowrap_lBma5mkSrlin46mkSrlBma7lowbitsin48lowbitsBmaalsplit_divin4blsplit_divBmaeand_high_splitin4fand_high_splitBmadand_low_splitin4eand_low_splitBmabnarrow_maskin4cnarrow_maskBma6mkAnd0in47mkAnd0Bma5mkAndin46mkAndBma6mkAndKin47mkAndKBmabor_disjointin4cor_disjointBma4mkOrin45mkOrBma8conc_tryin49conc_tryBmaaconcretizein4bconcretizeBma5foldKin46foldKBmaalin_branchin4blin_branchBmaddecide_branchma5mkSltin46mkSltBma7mkAluK0in48mkAluK0Bma6mkAluKma5mkMdKma7zband32in48zband32Bma8mkAluwK0in49mkAluwK0Bma7mkAluwKma5extK0in46extK0Bma4extKma7flat_scmaawr_coveredin4bwr_coveredBmaastoreok_scma9conc_exprmabenum_branchma9to_saddrKmacamo_alignedbmaaamo_newvalmaalog_lookupmadknow_lookupA0macknow_lookupAma8sym_readmabknow_lookupin4cknow_lookupBma8sym_stepa9OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B6FPX_958WithSegs~~~~~~hou2azf_coversBmaasegs_avoidhou2fkentry_overlayBhou2dkwr_offimageBmaeknow_bytes_covhou2h0kentry_readableBhjl07existsbmabkn_readablema8evars_ltmaakn_overlayhp63ltb36Stdlib4Bool4Boolhptb3eqbjkc6to_natmadfind_readbasehou2h0x_dischargeableBma6cap_rdhou29x_filterBma9zf_coversmaekentry_overlaymackwr_offimagemafkentry_readablehou2ckn_readableBhou2bkn_overlayBmafx_dischargeablema8x_filterma9sym_stepXhou2asym_stepXBin4asym_stepBIhou2bsym_stepXBIma4itabma3clrhou2fsym_execTXBI_gomadsym_execTX_gomaasym_execTXhou2csym_execTXBIma5KZero99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B6FPX_95~~~~~~hrk85kcutBma5KFillma4KUnkk44unitk42ttma5ktrimhrk89prune_zfBma4KImgjkc3minma6SCDisjma9kword_cuthrk88prune1pBhrk8h0ranges_apart_pcBhrk8akfill_cutBhrk89kunk_cutBhrk8akzero_cutBma4kcutma9kzero_cutin4akzero_cutBma9kfill_cutin4akfill_cutBma8kunk_cutin49kunk_cutBma8prune_zfin49prune_zfBma7prune1pin48prune1pBmafranges_apart_pcin4h0ranges_apart_pcBma8prune1pcin49prune1pcBma7prunepcin48prunepcB99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHcXAxSymExec3B4AX2B7FPX_106~~~~~~hth94gval" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Module AX2B.
Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Create HintDb bceq discriminated.
Section FPX_1. Context {fx : XPropExec.FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma p_aluop_eqb_eq : ltac2:(zQ "50!i4!jf!lc!m3!qf>1a$0>1b$0>0@3$1$2@2$4^2^1$3@3$1$0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_1"] "##N_p'0h02H0h11bi001bh21ai011ah31ep;3p;2p;6p-1R0p10000R1p4p710p8P0P!s2$2!s3%!sE$L!sEAi!s7+p1001Hp4p70!t$%2T!sS23V!sp%R1!s8'44!t&'!s4$Q!s4%P1!s6%51!s616>!s617K!s6,g008]j30Tg0097j23!s/$Qj64!s/$mj22Tg00:Lj25Tg00;\R1f1R0f0R2'5g00<<R330p=1g00<\R4P41102f2=040[^14P2P4g00=HR5/12A0450[P2A0133R61345U1155A0455[eg00>4R7=013R8P1P7P1p-0P2g00>TR7g00?1n01!wE$020000X31g00?MP3P2E4R3P!sK$iR19045R9/22b0U1151P9[eP!sE%@UR9!sE$:!sE$V81159P:!sF+AAR:!sF$;!sF,:P;!sF,mR;!sF$<!sF,;P<!sF+BYR<!sF$=!sF,<P=!sF+CER=!sF$>!sF,=P>!sF+D1R>!sF$?!sF,>P?!sF,]R?!sF$@!sF,?P@!sF+EIR@!sF$A!sF,@PA[e!vY$1000:0!s#6X1!x'$!wk$10[P2P3P7A041!so/15PA[e1341V61111A0411!tH%A0419!sQ/9PA!s@,:!s@/:!s@/;!s@/;!s@/<!s@/<!s@/=!s@/=!s@/>!s@/>!s@/?!s@/?!s@/@!s@/!vHM92A049!vH-9!vH/95!t1-91!s@/1!vb&9V61199A0499!sQ,!vH/9!vH/9!vH/9!vH/9!vH/9!vH/9!vH/9!vH/9!vH/9!vH/9!vH/9!vH/9!vH/9!vHM:2A04:!vH-:!vH/:!vH/:!vH/:1!s@/!ys/:9!vb&:V611::A04::!sQ,!vH/:!vH/:!vH/:!vH/:!vH/:!vH/:!vH/:!vH/:!vH/:!vH/:!vH/:!vHM;2A04;!vH-;!vH/;!vH/;!vH/;!vH/;!vH/;!}=/;!ys/;:!vb&;V611;;A04;;!sQ,!vH/;!vH/;!vH/;!vH/;!vH/;!vH/;!vH/;!vH/;!vH/;!vHM<2A04<!vH-<!vH/<!vH/<!vH/<!vH/<!vH/<!vH/<!vH/<!}=/<!ys/<;!vb&<V611<<A04<<!sQ,!vH/<!vH/<!vH/<!vH/<!vH/<!vH/<!vH/<!vHM=2A04=!vH-=!vH/=!vH/=!vH/=!vH/=!vH/=!vH/=!vH/=!vH/=!vH/=!}=/=!ys/=<!vb&=V611==A04==!sQ,!vH/=!vH/=!vH/=!vH/=!vH/=!vHM>2A04>!vH->!vH/>!vH/>!vH/>!vH/>!vH/>!vH/>!vH/>!vH/>!vH/>!vH/>!vH/>!}=/>!ys/>=!vb&>V611>>A04>>!sQ,!vH/>!vH/>!vH/>!vHM?2A04?!vH-?!vH/?!vH/?!vH/?!vH/?!vH/?!vH/?!vH/?!vH/?!vH/?!vH/?!vH/?!vH/?!vH/?!}=/?!ys/?>!vb&?V611??A04??!sQ,!vH/?!vHM@2A04@!vH-@5R0!so+@5P0!t1+@1!s@/1!s@/9!s@/9!s@/:!s@/:!s@/;!s@/;!s@/<!s@/<!s@/=!s@/=!s@/>!s@/>!s@/?R7!s@,?P7!vb$@V611@@A04@@!vHF!sG-1!s$5W2o"). Qed.
Lemma p_mulop_eqb_eq : ltac2:(zQ "50!rb!jf!lc!m3!s2>1a$0>1b$0>0@3$1$2@2$4^2^1$3@3$1$0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_1"] "##@;p'0h02H0h11bi001bh21ah31ei011mp;3p;2p;6g008]j30Tg0097j23!s/$Qj64!s/$mj22Tg00F5j25Tg00;\R0f1R1f0R2'5g00<<R330p=1g00GER4P41112f2=041[^14P2P4g00H1R5/12A0451[P2A0033R61345U1155A0455[eg00>4R7=003R8P0P7P0p-0P2g00>TR7g00?1n0110000020000X30g00?MP3P2E4R3P7g00H]R09045R9/22b0U1150P9[eP!sE%IIR9!sE$:!sE$V81159P:!sF+J5R:!sF$;!sF,:P;!sF,aR;!sF$<!sF,;P<!sF+KMR<!sF$=!sF,<P=!sF+L9R=!sF$>!sF,=P>!sF,eR>!sF$?!sF,>P?[e!uq$100080!s#2X1!w?$02A0401[P2P3P7A040!sk/05P?[e1340V61100A0400!tD%A0409!sQ/9P?!s@,:!s@/:!s@/;!s@/;!s@/<!s@/<!s@/=!s@/=!s@/>!s@/!uhI92A049!uh-9!uh/95!t,-90!s@/0!v&&9V61199A0499!sQ,!uh/9!uh/9!uh/9!uh/9!uh/9!uh/9!uh/9!uh/9!uh/9!uhI:2A04:!uh-:!uh/:!uh/:!uh/:0!s@/!x[/:9!v&&:V611::A04::!sQ,!uh/:!uh/:!uh/:!uh/:!uh/:!uh/:!uh/:!uhI;2A04;!uh-;!uh/;!uh/;!uh/;!uh/;!uh/;!{E/;!x[/;:!v&&;V611;;A04;;!sQ,!uh/;!uh/;!uh/;!uh/;!uh/;!uhI<2A04<!uh-<!uh/<!uh/<!uh/<!uh/<!uh/<!uh/<!uh/<!{E/<!x[/<;!v&&<V611<<A04<<!sQ,!uh/<!uh/<!uh/<!uhI=2A04=!uh-=!uh/=!uh/=!uh/=!uh/=!uh/=!uh/=!uh/=!uh/=!uh/=!{E/=!x[/=<!v&&=V611==A04==!sQ,!uh/=!uhI>2A04>!uh->5R1!sk+>5P1!t,+>0!s@/0!s@/9!s@/9!s@/:!s@/:!s@/;!s@/;!s@/<!s@/<!s@/=R7!s@,=P7!v&$>V611>>A04>>!uhB!sC-1!s$1W2o"). Qed.
Lemma p_expr_eqb_eq : ltac2:(zQ "50!se!jf!lc!m3!t5>1x$0>1y$0>0@3$1$2@2$4^2^1$3@3$1$0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_1"] "##z|p'0h01Hh12H0h22y1h32y2h41ni001nh52opi012oph61yh73op0h82sxi022sxh92H1h:4IHx1h;4IHx2h<1ii031ih=1ki041kh>2loi052loh?2n0h@1zi061zhA2x1hB2x2hC2H3hD2H2hE1mhF3sx0hG1xhH3IHxhI1ei071ehJ2i0hK2k0hL3lo0hM2z0i081ai091bp%0p;1p;2p;3p;6p;4p;:p;7g00MQj1@Tg00N^j2DTg008]j3:Tg00O;j2WTg003Vj6>j7XTg009Qj6S!sD$[j1?Tg00Phj35Tg00R5j38Tg00SBj37Tg00TOj36Tg00U\j49Tg00Vij4=Tg00X6j2VTg00:Lj2L!s8$Yj2BTg00Yhj2FTg00ZFj3A!s/$ij3TTg00F5j2KTg00\@j3RTg00]Wj2<!s/$nj24Tg00^Nj3O!s/$jl:Q!u&$7j2P!s/$mj2UTg00`9R0j2YTg00;\R1f1R2f0R3'Bg00<<R43:p=1g00`TR5?:23p=0A:134p=31P53p=Gf2R6=:52/U3p=21423=:14p=Ig00aaR7!s\%H1F!s?';A:124/Y3p=CP5f5R8f4R9f3R:P6P2P3FXp=E1F62/F3p=N1<!s0&MP9P!sI$C==:53p=J11231062[^65R;XG5g00b@R<P5%@6R=/13%@:R>/02[P31D:3#3P01D23#3A:<62[R?A:<231D62#3R@[A:<:6\@1W23P2n20010!s#$12!s-%0XE<X4<S00P?^E<^4<S01P3P8P6P2O3!su$86P<P:%@3R@%@9RA'0X@<%G>f6RBP3E>b0b1W011>@%@2RC,0A[eXM<P3O1g00>4RD=:14REP1PDP1p-0P3g00>TRDg00?1n01109000!ta$XI1g00?MP4P3ESR4PD%@8%?6RF;23b1W0%?3RG,1>%?2R>!t:%47!t:&<\RAP4PDf9RH#@RIA59:6RJ!s`$X0Ef7RK#@RLA5623RM'1f8RN#@ROA5:62RP'0[eX35X25W5!x$%O3P4PDA89:6RQ=2I!sn%A8623RR,1LA8:62RS,0O!s`'X5A!sa'g00GERT!sh$79:6RU!sh,7623RV,1LA7:62RW!sh-!tJ269:6RX!s`,6623RY,1LA6:62RL!tJ0T!sa/f;RO#@RZP8!y~%C9R[!v%'!z6%P3C9R\,1If:R]#@R^!zO+9R_!v+$65X47X>7X81!sY'O4P4PD!s{+=R`=2Z!s|2=RZ,1I!{E,RI,0^!wp$X<<X=!su1!xo$70008101061010030101108109!s1D40102105100107!s4&4103100X65W@P511F3%?:R^!|H%P4PD%?8?2=!u-%11^@%?9Ra/0C[eX@!zz$1I:3P01I231H62[Rb1H231I62Rc[1H:6\c1V!|d=7X47RcPb^E7^47RbP?1H86P7P:10GaX47%G^P!|M0^G10a>[eX?!{5$!tr%HRa?2J!tt%%?KR^/1M%?NR?/0P!z16!yH$2aQ!uM+R10?S!sO=U!sO+V10?W!y_:A2aX!sO+Y10?L!sO:%?OR??2[!sS'a\%?]R^/0_!ya%?!ya8A2?`!sX+Z10^I!u{$!y@~!y@:X47P5A5B8:/13A5KB9!yG/A5HNBRa!yK0A5NK8R?!yM/!vO&F!sK+G10?>!#4T'1LO61B]2S02'F1BN3S03';S04f<R?/L:1BO6S05'FR^1BH2Ra;A3S06%3aS07,C^S08P0f=R^/L91B?:S09';S0:11]6Rdf>Re?5^ORfA589:'0P3f?Rg/LB1Be8S0;';S0<11^8RhfARi/LNRjf@Rk/BKRl;A2S0=%3lS0>,CjS0?P0fBRj/LH#3S0@11iNRmfCRn?5jkA5]HN!t0$DRo/LO#3Rp11oORqfFRr?T^2S0AA:Ar^RsPnP?PBO2Rt10o?RuPrPeP6O2RvfGRw/0eRxPAPkfIRy=53wA5ikg'0X5APgfHRz95j2A5jikR{'0^:;XA511k310i!#;p$|PgA5nj2A5nji'0^;;XB5%G{X;|PwP6PrEEW:PzP3PwEEPyP6E>b9b1b0W9W0!yq$!}|8b0W1!sFB0A5O]NR{/1MA5?OHR}!}O/7!|~15^?]R~?2!}U+{R10}S!sU;2~!}U+{V10}!}U,7!}U2~!}U+{Y10}L!sO;5ge?R}!}W-~\10f_!#86>A2}!}S+~Z10fI!#7mO1!}Sm!xC$X!xk$X5AP5A8!}_&8KB9Rf!}_-8HNBR~!}_-f@A8NK8R}!}_5~!}_+fG10}!}_,!sp%^?]R}!#7$'A8O]NRf/1MA8?OHR~!x[9Q04Q06Q08P0Q0:PdA8e^OR{A8!}I&Q0<Q0=Q0?P0Q0@PmA8njkA8!|]&Q0APsPtPuPvP!{|$A83ywA8!{y,A8j2zA8jikRs!{v'PgA8nj2A8!{h0s!{h-X:|!{i7X9qX0p!{K?X1h!{lC11fR10~!{1=}!{1+fV10~!{1=}!{1+fY10~!{1<8ge?R~!{1-}\10{!{1B~!{1+}Z10{I!#?xZ1!{1s7!{1&7KB9R{!{1-7HNBR}!{1-{@A7NK8R~!{15}!{1+{G10~!{127!#4'%!{1'7!#4f'7!#4fB2~!#4`D1KO6Q02'FQ03';Rf1K?:Q05'FRp?Aa3S05Q07,CpS07P01K^9Q!#:W$9PdA7e^ORpA7!|,&1KgBQ0;';Ra1KiNRs?Al2S0;Q0>,CsS0>P01KjH#3S03PmA7njkA7!|K&1KoO#3RsARr^2S02A:Tr^S04!|^+TPkA73ywA7!|^&TPgA7j2zA7jikRl!|^-7nj2A7!|^0l!|^H!|<A!|]H!#8?i7!#8?6p!#8?OpI!#I-e1!|4dTP5A6!|4&6KB9Rp!|4-6!#8?2p@A6!#8?Cp!#8?56!#8?16O]NRp/1MA6!#8?=!vV&!|4+p!#5cJp!#5c:Q!|>$P0Q!|/$6e^ORdA6!#96';Q0>P0Q!{f$6njkA6!#93'2Q!{T263ywA6!{T-6j2zA6jikRx!{T-6nj2A6!{T0x!#94Is!{UBX0a!sH@0f11p!#8<?6!#8<6d!#8<OdI!#Q6p1!{-\PB!#SC$C9Rd/13PK!s7%C9R}!{:,PHPNPKPBC9!{?0}@!s=%P8C!{i$!{D=}G10p!#P]0P^P?POP]C9Rp!{I+POP]PHPN!tM$1M!sH%PHC9!{S1!#PI2p!{S+}!{S1!sO4!{S+}!{S1!#Pr2p!#5&'}!xz1!sO,1<^:14?6R~14O23N1B]3';1<e914^:Rf;N~R~1BO!#MM$%3a,C~P014e99Mg8/;f11?6PkPgPeP^C9Rf/0dP314kB9MiK14g8';11g814jNRd9MnHR~14iKRa;A2!su+<o]14nH';%3dfERdPoPnPjC9/0}P31<r?14dOR}';%3}1<zeR}14w^R~!sj$~,C}P01<yg#31IzefJR}PyPzPw!w8%fP3fKRf/<i#31IfiPcPbP3fLRaPjPBO31Haj!s:&ORhPdP:O31HhdfQRs?Ow8A:1swfNPdPgO210hdP1PyP3fSRqfRR|PsC9/0~X81P7PzP}P3P!s:+>7P7PwP}PyP3!s:'47PrPf!s:$2C9!s0&zC9'0^H;XG511w310z2[^65%G~WHfPR~P3PhEEPsP9E>P|P6E>PqP2E>b1b0bDbCb9bCWD!#;K7!s/&!#NX;1!#NXA!sF,011p\Pe!{Z%C9Rh!#W+-L7XF!#]g2!y'$P?C9?2!#3?'pZ10h!#W5/F!#W5n1!#3?@!w$$!#55+511`3!#3C'=R`!#34,!~s'=R;!#34,`@!#3c'=R@!#344;!#34'`G10@!#341!~h'=R@!#34+]!#4G$C=RJ/1M!#3C'=RM!#34>@!#34'JR10M!#34<@!#34'JV10M!#34<@!#34'JY10M!#]$:!xo+=!#93,@\!#5`'=R\!#]41!xO/1<?:14O6R_1D]23N14H3';1<^914?:1DO63NRE14]2R[;A3%3[,CEP014^99Me81D?:';%3_!yr'P`DJP314gB9MkK1De8';1Ie814iN9MjHR`1DkKR_;A2%3_,C`P01<n]14jH';1DiN#3!#3s$PiPM!sq$<d?14oO';1DoO#31<weRo14r^RO!sk$O,CoP01<zg#31Iwe!#3q$Pr!#5['=!sm%}i#31I}iQ00Q01P3Pf!#3u$A:<f!#3v%PaPnP^O31Han!s8&~PwP8O31H~wAO|yKA:1|yP1P}P3PqP|Ps!#37'=RKDJ!#3|$yPf!#3|$PKDJX=7P<Pz!sN$3!s9&<<P7Pw!sa&3!s9$47!sn%PwC=#GP~P:E>PsP8E>P|P2E>Pq!#dx%DbCb1!#3h~!#3h0@Z10\!~~&J<XK!~~r!#??01!#c54!#@\+3M:QXG5o"). Qed.

(* [comment removed for export] *)
Fixpoint first_var (e : expr) : option nat :=
  match e with
  | ELit _ => None
  | EVar n => Some n
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b =>
      match first_var a with Some n => Some n | None => first_var b end
  | EExt _ _ _ a => first_var a
  | EBlob _ _ _ _ => None
  end.
Definition vkey_of : ltac2:(zQ "30!u0!u6!se>1e$2@1$1$0") := ltac2:(zQ "50!se!uf!hge!hh2!hmb\1e$0@1$4@3$1$0$2@1$3^1").   (* [comment removed for export] *)
Fixpoint lset {A : Type} (l : list (list A)) (n : nat) (x : A) {struct n} : list (list A) :=
  match n, l with
  | O, [] => [[x]]
  | O, b :: rest => (x :: b) :: rest
  | S m, [] => [] :: lset [] m x
  | S m, b :: rest => b :: lset rest m x
  end.
Definition lget {A : Type} (l : list (list A)) (n : nat) : list A := nth n l [].
Lemma lget_lset : ltac2:(zQ "80!hn8!hnf!lc!u0!ho7!jf!hoe!hr1>1AT>1l@1$0@1$0^1>1n$3>1x^3>1m$3@3$5@1$0^5@3$1^5@4$6^5^4^3^2^1M2\0$2@1$0^6@2$7^1^3@3$4^5^2@3$1^5^4^1@3$1^5^4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_1"] "##>Yp'0h01mi001mh11li011lh21xh31bi021bh41ni031nh54resth61Ah72IHp;1p;4p;2p;3p;6g00b^R0p6091000R1g00ckR2p4p710p8p200R3g00dGR4!sL'p8P3g003VR5!sN'P3P1p8g00eTR1j11TP4j47Tg00f4j13Tg00]nj24TP2j42!s>$Tj30Tg0097j28Tg008]j35Tg00g4j1:TP5j6=!s5$Sj4>TP0j3<Tf5R0f4R5f3R2f2R4f1R6C2f0R735p=6P4P6g00h4R8P7C7p=;P4P8P6P7C2p=9%17#1g00aaR9%12#1f6R:#1R;P;P7P:P4P2P6C7%3:R<g00;\R=f7R>#1R?1472R@!sN$4P<C2RA90:6PAn010!s#$20000E6^09^25]1RAX49%14#1RBP1%10RCP;P;P6A;:74P<P=P?1468P;P6P7!sx$D90:4PD!sx3P4P9!sa$7%3;RD=;:!se+78RE!ta$D!sg$<!sg$<!sg47%30R<9006,8C%3CRD=;06=9C<P=P;1488RFA9CD<RD9006!tQ355CeP9f8RD#1R<P9f9RG#1RHP7%3DRI%3GRJn01103!sX%10100;5IP7%3>RK,8?RL18HJX09P7O1!sQ33P?P?%:7RM%3?RN=;>2PKP=P<14M8ROP?PMPNPKC2RP90>2PP!uV3e!t#;%1<P9f:RP#1RQPQP7A0Q46RR=;P:%3PRSP=f;RT#1RUPEPQP7PRPSC2RR90P:PR!vf45A0G06,8HA0H67RR=;G0=9HJP=PQPFA9HRJRR90G0!sb355HePUP7P4%3TRRC2,8UPUPUPMA0U24RF=;T>PRP=f<RE#1RVPOPUPMPFPRC2RF90T>PF!umLW5X3?P6P7O2n101!wU$020020!s4%X09X22W1%15#1P1P?P<P<P6PDP7%:0R1P4C7PIP=PH1461!sA$7PI!tW%D4!tW5!z_$<P<P7PD%3<RFP!si071!sA$F!si$I!si$I!za5PLP>PN%:5RLP6C7=9?!xr&8LA9?NKRN90>6PN!vw3?ePHP=PQ147:R?P!zS$HRNPJC2RK90G2PK!sY1P=PU146>A0P5SRKPS!sE195Q7X1HP?P=!s$$VP7PUP4%3UR?!wT$L90T0PL!s{4VP7A0T0RRL!xl5UP7P9!xo$!sj%?90T0=5ULP618QK%3ERK90E:,8V!|3<9A5U?R!sW$S18VK!sO;!s7$2!tJ'b3PHP7PGPNP:P2C7PJC2P0PNP2P7O3E=PHPHPMPGPN%::RS!sI%!vn%MS!sA$!vi%J!vi$J!zBH1!}1$QP9PV!v]$EA0V46RQ%:GRJP:C7PKP=f=RN#1RS147J!sL$Q!~A$!u}$!wy3E6P518U6PTA0U67R5%:DRDP0C7=9URP=PV148DA9U5RR5!we$5!wH4ePGP4P>P7O3PSPSPMPNA0S24RG%:PRPP>C7%3NRUP=f>#114MP!sK$GPUC2RU90N>PU!}8PH!}851!}800W1X7AX49P7C>P0!#9s&=<07P=P;P@A<047R79006P7!uG3C^09^22^1BeP6O1W4W1X63o"). Qed.
Record rindex := RI { ri_vars : list (list kentry); ri_other : list kentry }.
Definition ri_bucket : ltac2:(zQ "50!hn8!u0!u6!hr8!hs1>2ri$4>1k@1$2$1@1$0$3") := ltac2:(zQ "80!u0!u6!hr8!hn8!hnf!hsb!ht7!hs1\2ri$7\1k@1$1$0M1\1k@1$1$0@1$3$2^1\1n$0@3$4$2@1$6^3^1@1$5^2").
Fixpoint mk_ri (fk : list kentry) : rindex :=
  match fk with
  | [] => RI [] []
  | K :: rest =>
      let t := mk_ri rest in
      match K with
      | KRange e' _ _ =>
          match vkey_of e' with
          | Some n => RI (lset (ri_vars t) n K) (ri_other t)
          | None => RI (ri_vars t) (K :: ri_other t)
          end
      | _ => t
      end
  end.
Definition find_rangeI : ltac2:(zQ "50!hge!u6!hu2!se!hs1>2ri$4>1e$3@1$1@2$2$0$0") := ltac2:(zQ "50!se!hu9!hv6!hs1!ig3\2ri$3\1e$0@2$1@2$2^2@1$4^1^1").

Definition okey_eqb : ltac2:(zQ "30!u0!u6!lc>1a@1$1$0>1b@1$1$0$2") := ltac2:(zQ "60!u0!u6!lc!ige!m3!hr1\1a@1$1$0\1b@1$1$0M1\1a@1$1$0$2^2\1x$0M1\1b@1$1$0$2^2\1y$0@2$5^2^1$3M1\1b@1$1$0$2^1\1n$0$3$4").
Lemma okey_eqb_spec : ltac2:(zQ "50!u0!u6!ih6!jf!ii0>1a@1$1$0>1b@1$1$0@2$2@3$3@1$1$0^2^1@2$4^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_1"] "##19p'0h01bi001bh11Hh23Heqh31ei011eh42H0h51ah61yh71fh81ni021nh91ri031rh:1th;1xi041op;1p;3p;2p;6g00hSR0j1ATg008]j30Tg00i5j23Tg00jFR1j21!s1$ij2?Tg00]nj29Tg00kNj1=j2>Tg0097j28Tg00l0j65!s/$Mj6<!s/$kj27Tg00mNj14!sS$mj2;!s8$gj26Tg00nJj1@!sA$Qj6:Tg00aaR2f0R3'>p=2%A2R4P0P2f1R5=0431353'1^04P3!s=$2R6#2R7!sA%73'1P3f3R8/?3A02831983'1f4R9/95g00;\P1f5R1=026f7R:#2R;%29R<504R=/15P5f6=028R>P4P;P;P<P4^52R<P4P3f8R;O1X7<%=2R?P?18<?E5P2P4P?P:P9P3E5E<,7=W3P3O1%4>P4P2P0P2P2P3P3f9n101104000210!s#$X:4%2;%21P3E5A02;1g00>TR;P6P3O1';b2X1=%4=e,6=W8P3O1n1!sd$103!sn%!sz$102b0b9%28R8%23R=504138='1eX62!t]$25R5%@2R6504R1P3A0476P4P8P0P2p-0R8P3g00?1R>P;!tx634g00?MR9P6P3E:P;1;;3R:b4b2X11%41e'61356,11e!se010200X04X;!tW$P0P2A0463136!wx$A046=!t`&65P4P6!vR$8P3P;P>!tX8P9P7!tS%P!tO36=,1!uk+A0466R31846'71366,13!tk9!s;/1!s;$W5o"). Qed.
Lemma ri_bucket_cons : ltac2:(zQ "h20!hr8!u0!u6!hv6!lc!ho7!hn8!jf!hge!iic!hsb!ht7!hs1!ig3!ij2!se!hoe!ii0>1t$c>1K$0>2e'$f>2lo$8>2hi$8>1k@1$2$1>0@3$7$0^5@3$e^4^3^2@3$7@1$6$0@2$3M2\1x@1$2$1$c@1$d^5\1n$1@2$9@4$h0$0@1$b^8^1^7@1$a^8@2$9@1$b^7@3$5$0^6@1$a^7^2M4\0$4@1$6$0@2$h1^2@1$d^5@3$5$0^6@2$3^7^2@2$3^7^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_1"] "##3\p'0h02Evh11Kh21mh31Hh42e'h52hih61kh72loh81ni001nh91oi011oh:1ti021xp;1p;3p;4p;2p;5p;6g00hSR0j1CTg00nlj37Tg008]j38Tg00eTj1=Tg010;j19Tg011Kj16Tg00dGj4:Tg012[j15Tg013lj21Tg00i5j23Tg015=j22Tg0097j2<Tg00kNj2;Tg016Oj5B!tC$Jj1ATg00b^j3@Tg003Vj6?Tg00fTj3>Tg017aR1f1R2f0R33>p=0f3R4f2R5/22;83p=4g0190R6g00`!sr$@R7g00aaR8#CR9f4R:A7452581P1A7:45%=1R;P0P8P6f5R<#9R=P1f8R>#6P3P2C:%5>'1f7R?#6%5?,03'1n10110200021010000P5g00;\R@P;135=12?5RA,03PAn!sG%0!sU$0C4X11%9:P91<93A89=3P0P8%9?=893P!tW&P2P1f;R6#6R=P3f9RA?7>?RBC:%56RC'1f:RD#6f6RE97>?RF%5D'0'1RG!th6<P!tc$<212D<RH,0FPH!tc3]0P2%9>1;83RH589!tU$;P1f<RI#6P5A7DA>R>C:%5I'1P3!sy$;85,3312I3RI,0>PI!s|3PEP1f=RI#6R>P4A76DAR5P3DBP;P1P>P4P5!sx'H!sx&4,3H12IHRI,05!sx5eX28P3O11<;C!sk$=P2PBC:/1C%A8RI!sl&2,3I126IR2,0BP2!sl4!vD%1!vD-W0X8!t$$%9E=89I!uw&G!ua&33I12D3RD,0FPD!u^4:A@1=3,<;P;10BC,1=!uG&3HI126HRH,0B!w<5!uD'A7?E<RE%5A'0R?!sm$%6A/1?P!uG%3II12AIRI,0E!v26!uD7!s:5P3O1b0b9P<P3E?W3W6X57W7W4X11W:o"). Qed.
Lemma find_rangeI_eq : ltac2:(zQ "a0!hge!hn8!u6!hu2!jf!se!hu9!hr8!ijb!ika>2fk@1$1$7>1e$5@3$4@1$2@2$3$0$0@2$8@1$9^2^1@2$6^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_1"] "#$4dp'0h02Eeh12Lxh22IHh32NEh41oi001oh51ai011ah61ni021nh72Evh82e1h91lh:2e2h;2opi032oph<1pi041ph=3Le'h>1bi051bh?1ei061eh@1vi071vhA1ci081chB2fkhC2hii092hihD2loi0:2lohE2sxi0;2sxhF2EQhG1Ki0<1KhH2a1i0=2a1hI2a2i0>2a2hJ2bkhK2c'i0?2c'hL2e'i0@2e'hM1ii0A1ihN1ki0B1khO3lo0i0C3lo0hP1mi0D1mhQ2n1i0E2n1hR2n2i0F2n2hS1ri0G1rhT4resthU2v'i0H2v'hV1wi0I1whW1zi0J1zi0K2e0i0L1xp%0p&0p;1p;2p;4p;6p;3p;8p;7p;5g00eTk102Tg01:AR0j2kTg00hSR1j1e!s<$aj18Tg010;j13Tg01;oj20Tg00f4j1dTg013lj2HTg00nJj1cTg0097j2;Tg00kNj2aTg011Kj1UTg00dGj4\Tg012[j1TTg015=j2G!s\$Qj6YTg01=@j3{Tg01>Oj2qTg01?^j3pTg01@mj2oTg01B<j2n!tC$lj3XTg00XYj29Tg01CKj16Tg01D[j1ITg01E@j1b!s/$^j2mTg01F;j2?!s/$Xj2!uv$G5j25Tg00i5j2l!s8$Rk201Tg008]j3!s/$jFR2k20!uv$3Vj6Vj8}j7|Tg00mNj1^Tg01Hhj3j!uF$mj2iTg01J>j1DTg00MQj1STg00O[j1RTg00Phj3QTg00R5j3LTg00SBj3KTg00TOj3NTg00U\j4MTg00Vij4OTg01KPj7zTg01Lgj2yTg01N6j4xTg01OEj3wTg01PTj2tTg01Qcj5uTg01REj2v!x$$Tj3_Tg01SYj4gTg01T9j2[Tg00Yhj2ZTg000Lj3~Tf4R3f3R4f2R5'Gf1R6'0f0R731p=>1056=147p=<%86/G7p=W10451067513p=`g017aR8?_67p=JA_856/07p=f!s1'9134p=@1G!s?&B%35,G4/06=137p=sg00b@R9P9P6P7Cg,a5p=4g01TVR:f6R;'[f5R</[3'Z1545'Z1[:6'Z/Z7p=7A1567#^p=]g00;\R:g00>4R=717p=hg00`TR>!t%'p==%66=157p=:A~>97p=P1967=1:=p=A%34,G3/0!uU&<p=E%3!sV$#^p=F1067,;5p=C10679145p=r&028R=P81k99R?#eR@%87RA%36RBP61076D>XB=%37RCg00aaRD#eREP1PDP@%d=%d8RF'HRGP7P510F5D>P7PDP@PDP=P7PFPFn011020002001010DRHP3%c?RIC<P71;@IRJPJX6DP7O1!sS32P@PHP4PIC<eP@PG1aD7P410F4D>e!sZ&PJP@PG%cDP610F6D>en1011000002!sk$00b4P@1WFC!ta$7D`eP@PA%35RAP51075D>P8P@P8g0190RFP7%8<RG%83RJPGPJPJ!uh$FPAP8%8;RI#UP7P3C\%TI'H%UG%TG,J4'H!tH%L!tH-PJPIPGPJ!uP$<000:30!sK$I1072!s1%2!s9&210B2010:1092010610D3010@!s9,11024010=10E10>10F!sb,8!sG'%33RJP3Af753D>P5g01U4RHP@f7RK#8RLf9RM#3RN'GRO/0MRPP@f8RQ#8RRf:RS#3RTPSP7D>X4@1;@P10KMS00P;EYRUP@PPA{567PKPMD@eX@>XVDW5P5P6P7O3P@%3K=BGKRGP@PIPQPQP7Ds!sq%G10<KP3EYRI!x>$q67P<PKD@eX9>X5H!si$2P!t3%p!t3-JD!sG&!t4'!sf%o!sf,C9XD9!sf&!sC%n!sC,P9X8>!sC&@PPP@!x?%%34RVP8%8MRW#UP7AX345C\%TW'H%URS01AX456S02%TRRR'J!xQ8TPSP:P@19S4RXA4?56RYP>P@PSP6P0P>P9P@f;RZ#6R[!s6'%6;R\!s\%46R]P:P@PKPKP;P;g01VB#IR^#b%I^#I!s$&b'mR^1?57R_,2KR`12;_Ra/5^F7RbA4?`aRaP<n0!{`%!|T$0!s63n20!u4'12010H10?!s:37108!u++=R`#6Rc!u+,QRd!tz$!u$%MPM!xN$^12M_Re12Q_Rf!ta%gA4?efRfPK!ta2K!taYRhP!s$%!ti'>Rh#6Ri!ti,MRj!ti-SPS!tm$^12S_Rk15e^F7RlA4?keRePQ!td2Q!tdZmPm!~9$600081010J!y+$30103!y@$5!s1D4010;10C!}{$K!s4&B10A102!td01!}G$P=P:P=1lNARmAX567Rn/JOPO!uG2@P7!zU%PXP!zL&%3ZRY=BWZRW!vT'P!zO+P\!v[-bPa%8`f?Ra#3;BaRb!t'2b!ymaP!yg+P!yd/gPf%8aS03fARf#3;BfRg!tG2g!wmZgP!s$%!tE'!yM+P!yJ/lPef@Rg#8S04fBRd#3;Bd!uskRb!s`$!yA~!yA/C<X9=201NAA1ENA000m1lTVP:P2A1EYJP@P:P=P6AX;<3%3`RJ,WZR2'JS05P!sr10P`!#4W$`;RmA4?<3R\!yg$`f<RO#8%3h;BhPb!}@,gRb!yw-!v~,OPOPZPZP^12O_Ro12Z_Rp/5^F7S06A4?opRq%8dfDRr#3;BrRs!tW2s!wAZsP!s$%!tp+fR!s3-ORt!ts-`P`!tw$^12`_Ru15o^F7RvA4?uoRofCRw#8fERx#3;BxRy!tp2y!tpZy!s`$!y3~!y3/RyC<P6%3ORz%3<51ER{P@10Z`R|!xX%hKR}A4?;<!xV$h!#:e+%6aS07!s4,S!vW-ZPZPSPSP^Pp15k^F7A4?pk!#:1r!x4,P!w|/vPo!#9`kpP!s$%!u\+dR!s3+Pc!tC-hPh!yE$^12h_Rk15u^F7R~A4?kuRk!#9ZkuPu!y2~!y23u=1@uX4@!uX$mP!~I&10Oh!#6<D10gdRe!um2e!x_b!#3R7Q06Pq10drRq!t=2q!w+Z[P!s$%!y~D10wxRo!tD2o!tDZvPv!xJ~!xJ2,;@102`R2PSEVP@Q05P`PyC<eWFP7O1%^{P@P|A1@7!xo$mP:1;:7RmA1:}7P:19gM=1:7P@PaPf!v,$6A4?MQ!y9$fPe!vP+!|=9~PkfFRk,0rR~!v]2~!y:a%6r!s1'Q07!#?9/gPaPaP^12g_R~12a_Rc/5!#4K$~cfHRc,0k!zqkReP!s$%!te+x!{+-!td,fPf!th$^12f_Re15~!t_%e~fGRefIR~'0R}!tb2}!tbER}!#3F~!#?_J]0P619aQRug00<<R|51!#6'$gA4?QKC<P4AjgM7A1>gMP>PSP@Q04PCP710g7D>A]EBzA1EAJ]3]2X?>P@Q03PTPS10aS!sF$YY1;EzW3W2PfP7PhP3G}b0O1'iW0%huPb1k>9Ru1;u7RYA1us7!#>-&%6wRT=1u7RJ!zt$rPo!wi+5P}!y{?P3!{F-!x;,wPwPdPdP^12w_Rp12d_Rd!yy'pdfKRd,0~!x=W!x;8oP!s$%!tY'<!s0+T!tc-rPr!tg$^12r_R_15p!t^%_pfJR_fLRp'0Rw!ta2w!taZ]P]!yv~291@q]1P61=679:ukRqPbPuPY!#7H'>P@PdPw!x6-:P@19M6!v%$kPkPxPxP^1?Q7Rw,2kRs12xwRw!wk'swfNRw,0p!#EFV!y4-!tD$Z!tD%cPc!~h$^1?S7Rs,2cRY12esRs!tD'YsfPRs,0wRY!tD2Y!~HFYP!s$%!xu,!tL$O!tL%~P~!tP$^1?Z7R0,2~RY12c0R0!tL+0fOfQR0'0!tMXcPc!xa~291@}^=JP619M5P:PmA1:X7P:19O<=1:7fRRX,0sRm!xj$XfSRJ,00R}!us$!xm$!}I$_P_P^1?`;Rc,2dRb12_c!#8M+bcP!}KB!so$!xF$fMR}P}PpPpP^1?aQRc,2}Rb12p!sw0fURc,0J!#PA2R]!#PC2RbP!s$%:!x&'!}e$}P}P^1?gMRb,2wRT12}bRb!t-'TbfTRbfV'0RT!tw2!s62RT!s8$!wf|51@]7P619Z3RT=1:|!wN$0Pm!u@$_P_!z@$^1?O<R|,2_Ro12~|R|!u@'o|Pm!w16pPp!#6I%?hKRh,2pRm12dhRh!s_'mh10X!vj3!#[`&!#46~!zS%YPrPu1=OZRY%P7#DR]%6d#P#D51EX<uPu1=<3Rd1=`O#P#D=1E]X<uAjO<7A1>O<P>P;1=7`9:uJ%D6%DQ51E]1X@>1=;O9:uX%DK,;EW1P`P7PZF|b7%PY#D%Pd!t3$e%6_P4EV%60PSEV%30Rd%3_51EeO1'iW7%hTP>P@1WsCP7PsP7D`%3p9]EB1A5}1=ga9:u4P@PbP3!w{$310c<RaPafWRa/0KRBP!s$$fX/0QRBPB!vq~2C<]1]0]3]2P0P@%80RB%S7R!#N;$pEE%S6%3}R}5FE%S5/Aw%S41=fgRg5:u%S39C@cW1W0W3W2XW9P7O1P@PB%R7!u=$0PBEE%R6=FE}%R!sf$R4=:ug%R!sa1!#m`$g00<\RgP@%8cR}AQ56!sm%cPBEEAQ456=FEdAQ345/AXAQ<341=xrRx5:ufYRBAQ;<35C@!s}+:>X8>W;!#j8+P}AL567R0P0PcP0EEAL!s|'L!s|&L<34=:uxAL;<39C@B!st1X;g!su'g00GERg!s|$K!s|1K!s|'K!s|&K!s|'K!s|8!tr2N567R}P}PcP}EEAN!st'N!st&N!st'N!trCP@%8aRgP4!s7%CM!vo$aPBEEP3!s<%CM%3JRJ5FEP<!s:%CM/AbP;!s5%CM1=ekRe5:uf[RkPK!s?%CM!w//?>X6DXODXE:!t9'O4P@P!tG,OR!#J%$g!tG-O=FEJ!tC+O!tC/O=:ue!t:+O9C@k!yC-XM9XN!t;1!|4j:!|4$6!|41PwPrPfPSO4W7!t6$501020101P7O1b7b>X=qXK9XU!#oI%!#=I%401012110610J!sQ$=b<W1XA9X@!sPC1b<W0!t;-0!t;&0b>P2PSEVW3P7O1n!t~$510G01021!sh$1102b>bS!#v2+Q01P7Q02C\/HR%UL%TL,Jn!#pZ6/GNRRPLPn!vv%PN1;8nFzEVQ!#t,$P@PRPMAfnKMC<!#rR%XL>!#rt1y!#rW+6!#s\,@PWP@1WSzPOP7C<!#t@$W10MZPQ!t%$W!yE+xPMPZD@eXR>XIHXQ>XHH!yp-!#tN$w!#tN,A9!#tN7t!#u67!vv$B!#x[U!wh%!#x[OP@1J56R5/WV!u7$4D`eW2XT=XG8P6DuP@%86/v7!um$reX?>WBo"). Qed.

Record bctx : Type := BC {
  bc_fk : list kentry;      (* [comment removed for export] *)
  bc_ffk : list kentry;     (* [comment removed for export] *)
  bc_fs : list sfact;       (* [comment removed for export] *)
  bc_ri : rindex            (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition mkbc0 : ltac2:(zQ "40!hn8!hr8!il3!ilb>2fk@1$0$1>2fs@1$0$2$3") := ltac2:(zQ "60!hn8!im3!hr8!il3!ime!ika\2fk@1$0$2\2fs@1$0$3@4$4^2@1$1^2^1@1$5@1$1^2").

End FPX_1.


(* [comment removed for export] *)
Section FPX_2. Context {fx : XPropExec.FPState}.


Fixpoint erange_fB (fuel : nat) (bc : bctx) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_fB fuel' in
  match find_rangeI (bc_ri bc) e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange bc) (fst l) (snd l) with
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)   (* [comment removed for export] *)
  | EVar _ => None
  | EAlu op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          (* [comment removed for export] *)
          match (match b, erange bc a with
                 | ELit m, Some (al, ah) =>
                     let m' := (m mod two64)%Z in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (al / 2 ^ j) (ah / 2 ^ j) && Z.eqb (al / 2 ^ j) (ah / 2 ^ j))%bool
                     then Some ((al mod 2 ^ j)%Z, (ah mod 2 ^ j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%bool
                          then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
                          else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
          end
      | ALU_OR =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange bc a, erange bc b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s => Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb (ah * 2 ^ s) two64 then Some ((al * 2 ^ s)%Z, (ah * 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool then
                (if Z.ltb ah bl then Some (1%Z, 1%Z)
                 else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
              else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      end
  | EAluw op a b =>
      match op with
      | ALU_ADD =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
              then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange bc a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
              then Some ((al * bl)%Z, (ah * bh)%Z) else None
          | _, _ => None
          end
      | M_MULHU =>
          match erange bc a, erange bc b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some ((al * bl / two64)%Z, (ah * bh / two64)%Z) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange bc a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := (2 ^ (8 * Z.of_nat n))%Z in
      if sx then
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah (w / 2))%bool then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (w / 2) al && Z.ltb ah w)%bool
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange bc a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
        | _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  end
  end
  end
  end.

Definition erange0B : ltac2:(zQ "50!hge!u6!hu2!se!irb>2bc$4>1e$3@1$1@2$2$0$0") := ltac2:(zQ "40!is3!se!jhe!irb\2bc$3\1e$1@3$2$0^2^1").

Definition erangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let r := erange0B bc e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  match erange0B bc (unlin (lin_of e')) with     (* [comment removed for export] *)
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some ((lo' - s)%Z, hi')
        end
      else r
  | None => r
  end.

Definition base_rangeB : ltac2:(zQ "50!hge!u6!hu2!se!irb>2bc$4>1e$3@1$1@2$2$0$0") := ltac2:(zQ "e2!se!hge!jib!u0!lc!hu2!i4!rb!jj6!u6!jjd!jk4!irb!jm4&\2op$6\1a$0\1b$0@2$2^5^4&\2op$7\1a$0\1b$0@2$2^5^4\2bc$c\1e$0M0\1e$0@1$9@2$5$1$1^1\1z$1=1v$1@2$d^1$b@2$8@2$5$1$1@4$a$1$1^1^1\1n$3@2$2^3^2~0~0~1~1\2sx$4\2lo$3\1n$3\2e0$0@2$2^6^5\2sx$4\1k$3\1i$1\1n$3@2$2^6^5").

Definition ealignB : ltac2:(zQ "30!hge!se!irb>2bc$2>1e$1$0") := ltac2:(zQ "60!jme!se!jn8!jo7!irb!jp1\2bc$4\1e$1@2$5@2$0@1$3^2^1@1$2^1").

Definition lin_nowrapB : ltac2:(zQ "30!lc!se!irb>2bc$2>1e$1$0") := ltac2:(zQ "h20!hge!hu2!se!lc!hn8!u6!jp8!ige!uf!jpf!jq5!jqb!jr4!jk4!jib!irb!js0!js7\2bc$f\1e$2=1l$a@1$b^1M5\1x@1$5@2$1$0$0$3@3$c@1$e^3@3$8$0@1$4@2$1$0$2^1@3$9$0@1$4@2$1$0$2^1\1p@2$1$0$0M1\1p@2$1$0$0$3^1\2lo$0\2hi$0@2$6@2$h0Z^2@2$h1^1$d$7").

Fixpoint srl_expandB (bc : bctx) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expandB bc rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let m := (2 ^ ((s mod two64) mod 64))%Z in
          if (Z.eqb (k mod m)%Z 0%Z && lin_nowrapB bc e)%bool then
            let q := (k / m)%Z in
            let le := lin_of e in
            if Z.leb ((s mod two64) mod 64) (ealignB bc e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | EAlu ALU_AND e (ELit mk) =>
          (* [comment removed for export] *)
          match highmask_s mk with
          | Some s =>
              if lin_nowrapB bc e then
                let le := lin_of e in
                ((c + k * fst le)%Z,
                 lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
              else keep
          | None => keep
          end
      | _ => keep
      end
  end.

Definition fact_nowrapB : ltac2:(zQ "40!lc!hge!se!irb>2bc$3>1e$2>2hi$1$0") := ltac2:(zQ "h20!hge!hu2!se!lc!hn8!u6!jk4!js7!jp8!ige!uf!jpf!jq5!jqb!jr4!jib!irb!jse\2bc$h0\1e$2\2hi$0=1l$c@1$d^2M5\1x@1$5@2$1$0$0$3@3$e@1$f^4@3$a$0@1$4@2$1$0$2^1@3$b$0@1$4@2$1$0$2^1\1p@2$1$0$0M1\1p@2$1$0$0$3^1\1a$0\1b$0@2$8@2$7^1$6@2$7^5@2$h1^2$6$9").

Definition sum_fact_xB (bc : bctx) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expandB bc ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
  | [] => []
  end.

Fixpoint sum_factsB (bc : bctx) (kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_factsB bc rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrapB bc e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_xB bc ts (lo - c)%Z (hi - c)%Z ++ sum_factsB bc rest
            else sum_factsB bc rest
        | _ => sum_factsB bc rest
        end
      end
  | _ :: rest => sum_factsB bc rest
  end.


(* [comment removed for export] *)
Lemma bc_fk_mkbc0 : ltac2:(zQ "60!hn8!hr8!jf!il3!jt5!jte>2fk@1$0$1>2fs@1$0$3@3$2@1$0$1@1$4@2$5^2^1^2").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_2"] "h02fkh12fsp;1p;2g00eTj10Tg0097j21Tg017a#0R0g001H#0f1,10W1W0o"). Qed.
Lemma bc_ffk_mkbc0 : ltac2:(zQ "70!hn8!hr8!jf!im3!il3!jo7!jte>2fk@1$0$1>2fs@1$0$4@3$2@1$0$1@1$5@2$6^2^1@1$3^2").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_2"] "h02fkh12fsp;1p;2g00eTj10Tg01Vgj12Tg0097j21Tg017a#0R0g001H#0f1#2,10W1W0o"). Qed.
Lemma find_rangeI_mkbc0 : ltac2:(zQ "d0!hn8!hge!u6!hu2!jf!se!im3!hu9!hr8!il3!ju7!jv0!jte>2fk@1$0$8>2fs@1$0$9@3$4>1e$5@1$2@2$3$1$1@1$b@1$a@2$c^2^1@1$7@1$6^2").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_2"] "h01eh12fkh22fsp;1p;2p;5g00eTj11Tg01:Aj29Tg00hSj13Tg01X6j22Tg01YDj18Tg01REj17Tg01Vgj10Tg01;oj14Tg01ZRj25Tg002Tj56Tg017a#1g001H#1g00`TR0g00b@R1/91#3f1R1f0R2'2#8#7%01#4f2#0/52X00D6W2W1o"). Qed.
End FPX_2.

#[export] Hint Rewrite bc_fk_mkbc0 bc_ffk_mkbc0 find_rangeI_mkbc0 : bceq.
Ltac bcfe := repeat (apply functional_extensionality; intros ?).
Section FPX_3. Context {fx : XPropExec.FPState}.


Lemma erange_fB_eqf0 : ltac2:(zQ "d0!hn8!hge!u0!u6!hu2!jf!jvf!se!im3!hr8!il3!kga!jte>2fk@1$0$9>2fs@1$0$a>4fuel$2@3$5>1e$7@1$3@2$4$1$1@2$b^1@2$c^3^2@2$6^1@1$8^3").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_3"] "#$7Qp'0h04fuelh11oh21xi001xh32IHh41ei011eh51fh62fkh72fsi021ai032a0i042ahi052ali061bi072b0i082bhi092bli0:1di0;2e0i0<2hii0=1ii0>1ki0?2loi0@1mi0A1ni0B2n0i0C2opi0D3op0i0E1pi0F2p0i0G1ri0H1si0I2sxi0J1zi0K2z0p;1p;2p;3p;5p;4p;6g00eTj1KTg01:AR0j2ZTg00hSR1j1]Tg01X6j2CTg01[ij2Ij3bTg01Vgj18Tg01];j2Ej35Tg008]j3FTg0097j2NTg002Tj5MTg00g4j19Tg01YDj1LTg01REj2gj1`Tg01^Jj1eTg00kNj2@Tg01_Wj1TTg01`dj1YTg00nJj1^Tg000Lj3RTg01b6j3Q!s/$Sj3JTg01ccj1PTg00N^j2DTg01e0j24Tg01F;j22!s8$Mj1\!s8$Xj2:Tg01G5j21Tg01T9j2<Tg01fZj1[Tg01D[j1?Tg01E@j1=!s/$^j27Tg01gjj1BTg00Yhj23Tg01SYj4GTg01hOj2S!s/$lj1fTg01j=j26!s/$Zj2>Tg01k:j1X!s/$Xj2ATg01l5j1OTg01mEj2d!s/$bj1HTg01nBj2WTg01;oj2Vj1a!s;$bj2_Tg003Vj6U!w'$Sj4cTf2R2g00b@R3P3f1R4f0R5CG'@p=0P3P3g01TVR6P5CG,@4p=;g017a#Kg001H!s,$aaR7g00`TR81Z33R9#]R:]4R;f3R</C2,I5%8<R=,E53FR>X07P8P:g00h4R?1C24'I%82,E?A5?=5,N:X28DMP8P:%94R=f4R@/C<'I%8@,E=P;f5R=#8RA,E2RBP1P9P:f6RC/C=#L/g4%e5,@9RD!s@%g00;\REP:%T4RF#YRG%^9RH!sC%1Z38#KRI=R3FRJAQ3IFRF5J5P!up$P:P5PEP:%P4RK%P5'Dg020<RL,4KRK,24125K509PHn010!s#$20000n200110E00012010?10<RKPHn101!sN%210!sF$!s^11@95R!un$P4%\5RN=09NRNPHg00<\ROP:P2!u-%P<P4O1RP!tv-!s>%CP<O1RQ!u611:<5RR/1L1:@4RS=09R!s=$<LS12SL12RL!u<7!uJ7F!uJ'9108RR!uJ4F!ut55104!ur7!u$&!u:5!u43<5@RS12@5RT12<4RU509RV!sA$1<4RW1:TL1:U!u:ZT!u:t3P:%[<RXPEP:g01VBRY#?RZ#=R[/75R\,44R]/1L142\=09]!u'3!t74H!t_9R]!vu_%BY#B#B#BR^#B#=,7[R_,1<115_'3PEP:PW%=YRY=09Y!s5$S!sd$6P6CG,@91;9YRW!w4?R`PW!wFFaPW!wFJW!ucZ`!tF8`!tF~!s8$1S<5#fRb,;9!tO3K108Rc!z7GJ!z7RPX162\164\509R\!yaLd!t3Q!}3%4_P\!z{\\!z{[1S@4=09b!xD8b!~+f8!tF-@P2O1!|G11><LR_/:YRe%Xe,7[Re'D164eRf165eRg'<'31Dfg'31>4e1>5e509!s`$2L_R_%X_R_!s]&%?Z!~y$?#?Rg#?#=,1_!s]%,241>5e,25!#5,J!v}1e!uW1!sF%PH!s$/n0110600081110@1010A3010D103107!s1D4010I10?10A10;!s4&>10=10APM!x9HA<5!|,;_1;95Rf!|1J!#;\&5!wt0f!sR68Rh!xj7!s8DG!w=$10C000:0!s#51P!#=6-!#6}CPEP31D45Ri%O4P4!x@1,:@Rj,<6PEP3Pi%O5P5!sG3<Ri%=^,7[R^'1'3A09ji!#?n9!|01i!#=J~!|2+1U^,3SPV!taHV!#<qv!#4S$%=gRg,>5RS,7[RU,44Rj/1^142U=09j!#4l[j!tY8!|g%!t_@17[g,14116S114^R^'d'3162U164U509RU!tb\S!v=UP^P!t>]U!uz;!|6@0g00GER^!|;O1<6@1<64RX'3Rg14<5Rk/1L'314@4Rl=09k!z#Hm!z#`!xJ;!~<7g16lL16kL!#J=<!ti1k!tib!tg58P:P<!v\$>5LRl,16Rg162l164l!td6!#8j;010:!#8jo!yc8Q!uNUPg12lY,A4,;!uD~!uDXl!#OS9!{}%8!{y3PH!uF$<P7!{|-@P5O1Rg!yo1%=ZRZ%H@'4,7[RP/6[Rn,15,3XA0945Ro!sK$9?R?/W@%9?#9!s$,,W@'31<n4'3115PRn'312LPR?/:41:?!#?OY?!x#9!uc$?!s`%1010B!uR0!uL213XnPo12PY12LYRL'A,;9!tJFP%H4,4Z,7[/2Y/AL,;9Ro!t\5%H2!sL3n!tn4!s7$I!yV+!wV%3P3P6g021HCG,@9%H5!so2!s\1RL!s6$1!z$'J!z$%110C102106!s1:0!s1+41!z$-2!z$2!#?w21!s85!v~%%8CRY/V4P!#XR%!uD$G!|\'1E<Y?JJFP!#W9EP!#W5%PNPH!#@o-f9RF#8RJ=5C4RY!#5e2f<#8=5F<RFP!#Uyf!t-4PFPT!s~h]!tDR!#Qcf!s~7`!s~z!#PrfYPd!sD@\!vbR!#Naqf7RGf:#8R[;52P!#Le~!#LeN!uo7_P!#L<OA5CJ5RZP!#Ku~2!t}>i!}pzV!s~h!#HODYPS!sh@!#F=YP^!vVB!#E;j!t&7!#DThYPQ!sFB!#@NeA5G[5R[P!#>^W[PPP!#=_5P!#=MC!#<o~!#<o5R[!s:6G5F:X1;P;%aA!uF&5P4O1PDP!sU6=F:GX1;!sO%1VA5!#=K-%T5RD#Y!w`'AR3IDAQ3ID5JB!#=UM5!#=U38RN#8RK=5=4RB!z#3f;#8=5N<RN!#=Ug!t-4PN!#=UgB!#=U?!tD7!#=Uf!s~7`!s~z!#=UfB!#=U?B!#=U?!tb7!#=UqA5CJ!#=M~!#=MP!ug7!#=MS=K5!#=K~!}z'!t{8i!}fzV!s~h!#=KDB!#=K?B!#=Kg!uV7!#=Kj!t&7!#=KhB!#=KAB!#=KfPZ!#=FXZ!#=F~!#S7~1,N:1C=@RL#L#`1_=@EU1I2LP4EU%92R2?bL5A52A55F:eX28DMX3>X57P5CcW0W7W6o"). Qed.
End FPX_3.

#[export] Hint Rewrite erange_fB_eqf0 : bceq.
Section FPX_4. Context {fx : XPropExec.FPState}.


Lemma erange0B_eqf0 : ltac2:(zQ "b0!hn8!hge!u6!hu2!jf!kh7!se!hr8!il3!ki1!jte>2fk@1$0$7>2fs@1$0$8@3$4>1e$6@1$2@2$3$1$1@1$9@2$a^2^1@1$5^2").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_4"] "h01eh12fkh22fsh31oh41xp;1p;2p;3p;6p;5g00eTj14Tg01:Aj2@Tg00hSj17Tg01X6j22Tg022Vj1?j2=Tg023gj1:j2;Tg01Vgj11Tg01];j26j30Tg008]j33Tg0097j25Tg01[ij28Tg0255j39Tg003Vj6>Tg002Tj5<Tg017a#4g001H#4g00`TR0g00b@R1/@1#7R1f1R2f0R3'2#?%:2P1^00R4g026LR5f2R6#1R7'6P3P2O1f3#1=052531X34A0573,511262R7,85A9625E>1=731;63531eX40D<W2W1o"). Qed.
End FPX_4.

#[export] Hint Rewrite erange0B_eqf0 : bceq.
Section FPX_5. Context {fx : XPropExec.FPState}.

Lemma erangeB_eqf0 : ltac2:(zQ "b0!hn8!hge!u6!hu2!jf!kid!se!hr8!il3!kj6!jte>2fk@1$0$7>2fs@1$0$8@3$4>1e$6@1$2@2$3$1$1@1$9@2$a^2^1@1$5^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_5"] "##2xp'0h01eh12fkh22fsh31oh41xi001xi012e'i022hii033hi'i042loi053lo'i061pi071ri081sp;1p;2p;4p;3p;6p;5g00eTj17Tg01:AR0j2ITg00hSR1j1=Tg01X6j24Tg027^j1Hj2CTg028nj1?j2DTg023gj1>j20Tg02:;j12Tg00N^j2;Tg01_Wj1:Tg02;Gj18Tg01T9j29Tg01F;j21Tg01hOj2GTg01kXj2FTg01SYj45Tg00kNj23Tg008]j36Tg0097j2@Tg022Vj1ATg02<Sj2BTg003Vj6<Tg002Tj5ETg017a#7g001H!s,$`TR2g00b@R3/I3R4#=R5f1R6f0R7'4#H%?6P5^02R8f2R9#>P0P2P3P5%26R:g00;\R;P5g01TV,;7R<P9f3R=O1R>P1P4P5P9%:6#8R?O1P0P3P3P5P7P;P519=6R@!sK%f5RAf6RBO1RC!sL-3P3f4RD/1B,G61F7=C5,34n2001106000120104102REP3P3116=P7!sK$RFn101107000210!sU$PCn010!s#$20000!so35103P>!s^%0!s^-!s\80!s\'1108!v3'P:P;P5P<10A=R=!uR%10A?!up1P!ul'8/0BRBPEP!t{7B!t{F=!t{W565X3!u%+%27!u&'D9R<!u&'D!u&;7/0ARA!u&:A!u&F<!u&W,@51496R<#A1B96E<1C<71D97565eX42DEW2W1o"). Qed.
End FPX_5.

#[export] Hint Rewrite erangeB_eqf0 : bceq.
Section FPX_6. Context {fx : XPropExec.FPState}.

Lemma base_rangeB_eqf0 : ltac2:(zQ "b0!hn8!hge!u6!hu2!jf!kk1!se!hr8!il3!kke!jte>2fk@1$0$7>2fs@1$0$8@3$4>1e$6@1$2@2$3$1$1@1$9@2$a^2^1@1$5^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_6"] "##/gp'0h01ei001eh12fkh22fsh31oh41xi011ai021bi032e0i041ii051ki062loi071ni082opi092sxi0:1zp;1p;2p;4p;3p;6p;5g00eTj13Tg01:Aj2BTg00hSj18Tg01X6j21Tg02=ij1Aj2<Tg02?=j1:j2=Tg028nj19j20Tg01jZj27Tg01SYj45Tg00kNj26Tg008]j32Tg0097j24Tg027^j1@Tg02@Nj2?Tg003Vj6;Tg002Tj5>Tg017a#3g001H!s,$`TR0g00b@R1/B1R2#8R3f1R4f0R5'1#A%:4P3^00R6f2R7#9P0P3P4P1P1g020<,75R1P1C5,62R2P4P7O1f3R1f4R8O1R9P!s$%8f5R9O1R:P:n0110000081010:10107301!s5$102!s1D40109106107103!s4&5104107!tk&21087f6/08R8P!s$$f7/09!tL~!tL$523X36!tR$5P21014109!uz-P8!tL~7,431174R8#@1?74E;1<851=75523eX40D>W2W1o"). Qed.
End FPX_6.

#[export] Hint Rewrite base_rangeB_eqf0 : bceq.
Section FPX_7. Context {fx : XPropExec.FPState}.

Lemma ealignB_eqf0 : ltac2:(zQ "90!hn8!jf!hge!kld!se!hr8!il3!km6!jte>2fk@1$0$5>2fs@1$0$6@3$1>1e$4$2@1$7@2$8^2^1@1$3^2").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_7"] "h02fkh12fsh21lh31xp;1p;2p;3p;6p;5g00eTj15Tg01X6j22Tg02Acj1<j2?Tg02C3j17j2>Tg01Vgj16Tg02D@j20Tg02ENj14Tg01hOj21Tg008]j33Tg0097j2;Tg02Faj18Tg02H0j29Tg003Vj6:Tg002Tj5=Tg017a#5R0g001H#5g00`TR1g00b@R2f1R3f0R4'2#<%73P0f2R5#6R61043%43R7'1f3#6/03/17532X201064%44'1,;21253R6#81953E:1?641>54532eX31D=W1W0o"). Qed.
End FPX_7.

#[export] Hint Rewrite ealignB_eqf0 : bceq.
Section FPX_8. Context {fx : XPropExec.FPState}.

Lemma lin_nowrapB_eqf0 : ltac2:(zQ "90!hn8!lc!jf!se!hr8!kn1!il3!kne!jte>2fk@1$0$4>2fs@1$0$6@3$2>1e$3$1@1$7@2$8^2^1@1$5^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_8"] "##,Dp'0h01eh12fkh22fsh31oh41xi001xi012hii022loi031pp;1p;2p;3p;6p;5g00eTj11Tg01X6j23Tg02IEj1<j2=Tg02JYj1;j2@Tg01:AR0j28Tg00hSR1j1CTg028nj14Tg01_Wj12Tg000Lj35Tg01b6j36!s/$Sj30Tg01T9j2:Tg01G5j29Tg00Yhj2ETg008]j37Tg0097j2DTg027^j1BTg02@Nj2?Tg003Vj6>Tg002Tj5ATg017a#1g001H!s,$`TR2g00;\R3f1R4f0R5'3#<%;4g00b@R6/86R7#C^02R8f2R9#4R:P1P7P31862#1R;%24R<556R=A66;<R<505P0P6P6P3P5g01TV/:4g020<,95'En2001103000120102101R0g00>4R>n10110000!s=$0300!t;%f3#4?0=<P0P!sJ6573X38!sP%%25R7956;A66;750:!sY9,D31394R>#B1?94E>1=>51@95573eX42DAW2W1o"). Qed.
End FPX_8.

#[export] Hint Rewrite lin_nowrapB_eqf0 : bceq.
Section FPX_9. Context {fx : XPropExec.FPState}.

Lemma srl_expandB_eqf0 : ltac2:(zQ "a0!hn8!hu2!hge!se!jf!hr8!il3!kod!jte!kpa>2fk@1$0$5>2fs@1$0$6@3$4>2ts@1$0@2$1$2$3@2$1$2@1$0@2$1$2$3@1$9@2$8^2^1@1$7^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_9"] "##S0p'0h03acch11th21ei001eh32tsh42IHh51ai011ah62a0i022a0h71bi031bh82fkh92fsh:1kh;1lh<1pi041ph=4resth>1zi051zi062b0i071ci082e0i091ii0:2k0i0;2loi0<2mki0=1ni0>2opi0?3op0i0@1si0A2sxi0B3ts'i0C1xp;1p;2p;3p;5p;6p;4g00eTj1ETg01:AR0j2NTg01X6j21Tg02Kjj1Uj26Tg02M>j1\j23Tg008]j32Tg00f4j1VTg0097j2I!s8$Tj3GTg01D[j15Tg01E@j1OTg01jZj27!s8$^j2DTg00N^j2MTg02IEj2Lj1PTg00Yhj2<Tg02Acj2Wj1[Tg01T9j2;!sk$=j2=Tg01_Wj1JTg000Lj3BTg01e0j24Tg01FXj29Tg01b6j3@Tg02NOj38!sS$ij5>Tg02O\j1:Tg02P9j2HTg02QGj1TTg02JYj2?j1QTg02C3j2Fj1RTg02RXj2STg003Vj6ATg02T1j2ZTg01SYj4CTg01Qcj5YTg002Tj5XTg00b@R1f4R2f3R3f2R4f1R5f0R638CCp=0P1P4P5P6CCp=Kg017a#Eg001H!s,$`TR7,N1R8#ER91N19R:1156#U%\5P81134/66133652:X39%V8,34,I:P0P1P7f5R;/12!sI$;652:f6R</1;AG845R='613<=52:[^;9P6f8R=f7R>'1!sW$=652:P:f9R?/35R@!sy$9P:P6P7P:P;P9P4P>P<P5D0RAPAg00<\RBP:P4P9P2P?P=P3D0RCP!s$,7P:P6g00;\RDP:f:REg01VB#5RF#ORGg020<RH,76%5F#5!s$&ORF'7RI'DRJ'7g01TVRK'MRLf@RMf?RN'1RO/L4'<RPPDP:1WO4,;I1=EJRO%J4RQ9B19RR'4,9;RSP9P8f<RT174H/7F,DGRF'=AB175RH'4A@175RU;86X09X18P2A@19QRQD>RV5K9RWP9PS%:O1H4JROPVD0RVn010!s#$20000P9P;PEP?P2D0RS!sB-100PSP9P>PTf;RXP<D0RYP!s$%9P=f=RZPTP>D0R[P[n0110300081110@1010=3010?102106!s1D4010A10;10=108!s4&:10910=!wR0hSR\P1P:%T6R]PDP:fAR^/1M/L3P9%J3R_!v^$`,4X,9<%:X1DG6,H3RGP9P814ZH?8U!vL';A@19_R_D>D0RZP9P<PXPEP;D0Ra!vD2Sn10110C00021010@!v<$!v-'!ux1010<!uxpRb!t+$>000:0!s#/!tq&!zn&SPS!sN$1!tT'5!tT%110>10010330!s1$2!s1<!tT00!tT1n20!uy'12110710B!|u'13E4Rc!|y&APAP!|h%!|\4!{Y$?M4,<L!s1$FM4,;IPWP!zT2RdP!zJ5!w49!z-~P!z%$P!y~$1?^3PZP!y-~!txU!y+~!y+`R^52:X<:P1^27Re%R?!y>'P!y:JPP!s+$<P4O1RP!y98!y7~!y7G!}I~!wCa=2:^X>ePD!wB%Q!wBT1<LPP!}6~!}6YP>P3O1!}8~!}8~!xs~!xs?7e!xi+@!vo$2P9P4P<P;P5D0R@P@P!#A7+=P>P3D0RBP!s$,!y%,7?J/MK1?N4'<!s7$FN!#@E$?JRJ/4R,9;RRP9P81=XF/4!#<S-2PQD>RQ5K9P9PR%:JPOPQD0!#?l5?P=P2D0R2!z822P9P>PXPEP<D0RQP!s$%9P=PTPXP>D0R>P>!zP~=!v'-!#8`/M3P914E`,9<%:EP!#?I%T!ut/;P_D>D0P9P<PEP?P;!up42!z~62!uZ&QP!uP1!z~~!z~8!xu%2P2!z~~!z~8,I:11?=R2#P1S?=EA%[21Z?=EA1625P6EAP1P7P3P4CC=G85R4,6213?452:eW4X=9X57X:1P5P6O2!t0&4!t0'5100X68P6DYX39DXW9W8o"). Qed.
End FPX_9.

#[export] Hint Rewrite srl_expandB_eqf0 : bceq.
Section FPX_10. Context {fx : XPropExec.FPState}.

Lemma fact_nowrapB_eqf0 : ltac2:(zQ "a0!hn8!lc!jf!hge!se!kq9!hr8!il3!kr7!jte>2fk@1$0$6>2fs@1$0$7@3$2>1e$4>2hi$3$1@1$8@2$9^2^1@1$5^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_10"] "##-@p'0h01eh12fkh22fsh32hih41oh51xi001xh62x0i011ai021bi031pp;1p;2p;3p;6p;5g00eTj12Tg01X6j20Tg02UFj1>j2Gj3ATg02V[j1<j2Ej3BTg01:AR0j2:Tg00hSR1j1=Tg028nj15Tg01_Wj16Tg000Lj34Tg01b6j38!s/$Sj33Tg01G5j21Tg01FXj2FTg00Yhj2;Tg008]j39Tg0097j2DTg027^j1CTg02@Nj2?Tg003Vj6@Tg002Tj57Tg017a#2g001H!s,$`TR2g00b@R3g00;\R4]3f1R5f0R6'0#>%<5P3P4f2R7/05/G61E761:33R8#=^02R9f3R:#5R;P1P8P41:32#2R<%67R=543R>A83<=R=536P0P3P3P4P6g020<R?,16R@f4RA1F5?R?'1';n2001103000120101102RBg00>4RCn!s6$0000210!sK$!tC%%5A?3>=PBP!sI6594X49!sO&65R8943<A83<853;!ta,11:?,;@!tN7!s|7,D410:7RC#C1?:7E@AAC56AB:56594eX63D7X52D7W2W1o"). Qed.
End FPX_10.

#[export] Hint Rewrite fact_nowrapB_eqf0 : bceq.
Section FPX_11. Context {fx : XPropExec.FPState}.

Lemma sum_fact_xB_eqf0 : ltac2:(zQ "a0!hn8!hge!il3!hu2!jf!se!hr8!ks7!jte!kt4>2fk@1$0$6>2fs@1$0$2@3$4>2ts@1$0@2$3$1$5>2lo$1>2hi$1@1$0$2@1$9@2$8^2^1@1$7^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_11"] "##/Rp'0h02fkh12fsh22hih32loh41pi001ph52tsh61xi011xh72x0h82x1i022c2i031li043ts2p;1p;2p;3p;4p;6p;5g00eTR0j13Tg01:AR1j20Tg01X6j21Tg02Wmj1;j2Fj3?j4ATg02YAj1Gj2Cj3=j4>Tg02M>j1<j28Tg00f4j16Tg00N^j2:Tg01F;j25Tg01SYj42!sJ$Tj39Tg008]j37Tg0097j2ETg02Kjj1DTg02ZRj2BTg003Vj6@Tg002Tj54Tg017a#3g001HR2#3R3g00b@R4g00`T'0R5#3R6P3^24R7^34f1R8f0R9'1#;%G8P4P7f2R7/18/F91C79P4P3f3R:/17??89A=:891046^56R;f4R<#<P1P4P6P3P9P:O1P0P5P3P9%62R2g00;\R=P3g01TV,::R>P21044R?,06R@P6P?P7P4P4f6/5:f5RA/5:RBC2C2%6@RC39n010!s#$20000n101104!s5%20100103RDn20011!sP$120102104!te'18A:P!sH8573X4;!sN,<7!u3'P2P=P3P>P2!tp,PB15<:C2C2=9@C!teF!tA7,E311<:RC#D1B<:E@PCP7P8P9CAP<!s0&>573eX84D4X74D4X66D4W1W0o"). Qed.
End FPX_11.

#[export] Hint Rewrite sum_fact_xB_eqf0 : bceq.
Section FPX_12. Context {fx : XPropExec.FPState}.

Lemma sum_factsB_eqf0 : ltac2:(zQ "70!hn8!hr8!il3!jf!ku3!jte!kuf>2fk@1$0$1>2fs@1$0$2@3$3>2kn@1$0$1@1$0$2@1$6@2$5^2^1@1$4^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_12"] "##V'p'0h02hii002hih12knh21li011lh32IHh41Kh51bi021bh61ei031eh72fkh82fsh92loi042loh:4resth;2tsi05!s+$61ai072a1i082a2i091ci0:2e0i0;1ii0<1ki0=2k0i0>2l0i0?3lo0i0@1mi0A1ni0B2n1i0C2n2i0D2opi0E1pi0F2p0i0G2sxi0H1vi0I1wi0J1xi0K1zp;1p;2p;3p;4p;6p;5g00eTR0j1=Tg01X6j22Tg02[kj1Hj28Tg02]>j1Bj20Tg008]j33Tg00f4j1GTg0097j2@Tg01:AR1j2;Tg01_Wj1:Tg02UFj39j1ETg01F;j26Tg01SYj47Tg02Wmj4>j1KTg02V[j35j1MTg02YAj44j1LTg02^Nj2FTg003Vj6<Tg02_gj2D!tQ$Tj3ATg01Qcj5ITg002Tj5CTg0044j3JTg00b@R2P2f1R3f0R4C7p=?f3R5f2R6g001HR7?J343Ap=1g017aR8#=R9%=7R7P9P71234#H%B3P81256/841054537X19%G8,06,@7f4R:/25!sC$:4537P7f5R;/03P8P7P5P5P6!s&$6g00`TR<P7P6P1P21;2<R=#=R>P7%:5R?P0P=P7P4f6R@!s2+8RAg00;\RBP7f@RCf?RD'2REf9RFf7RG391;22RH,;>RIP>PHP:16A;RJ16G;RK'?C7RLPEP:PJPKC>REf:RMC1PMn010!s#$20000n1011!s8$2002010F10>!s;%5!s;,E101n200110J000120109105P:P1P2P!u?$;RN!u3'PA!s0+MPBP7fBROfARP'2RQf;RR;9FP!u&+M;RS16F;RT!u&$UPQP:PSPTC>RQf<RVC1PV!u&oRWP!s$%!u0+@RW!t~+F!s0+R!u0$CRX/2ORY?9VM!u&,R;RH/?SC7RZPYP:PHPSC>RYf=R[C1P[!t}p\P\n0110300081010K1010A3010D106102!s1D4010G10?10A10:!s4&<10;10AP6P:P5P6!t2$<000:30!s\$I10H2!s1%A!s9&A10=201041!u&%310@31!s-$!s9'610A4010710B10810C!sb,9!sG'!|/%10F;R\10A:R]P\P]P]P!|2+P>P7P!|#+10VAR!yj+f>R^/0MR_PBP7A5CFGR`PIPLPC!{S&410CVRCC1PC!wPo10M@R@!tl+!{T,_!s0+C!ta%ORFRaPIPUPO!{2&410O^R^C1P^!y3pbP!s$%!tc'!{/+10DRRb!s4,P[Rc!tk%XVMRdPIPZPX!zx&410XDRXC1PX!tkpePe!zx~AP]P@P\P]!zx~!zx4Re537X27PB^02^6<Rf%M;!{5%!{%$!{,@!#5m,!zz$PMPFPGO2!z{$EP!zotP!zkFPVPRPF!tR$UPQP!z`uQP!s$%!z`4P!z\+P!zX$P[PVPM!tX$ZPYP!zMuYPY!zM~!zM~!zM==37eX5fP7^02^92^;>Rf%L!zO]!#6F$M!#6F$O3!zQ~!zQ?!#69$V!#69$O3!zSvaP!s$%!zSE!#6$$[!#6$$O3!zUvX!sv$!zU~!zU~!zU?2f!zE$6P]10G5R5P]P5P5!#=y<RG!s2,[FR[!#:L$DFG!zR$D!#=r&PbC1Pb!zRp\!zR6[!y$-!tW$PRF!zU$P!#=h&PcC1Pc!xypcP!s$%!zU5!#?I4VM!zX$O!#=Z&!|4v^!sv$!zX}!#4P$5!zX~!zX4,@712;:R5#K1F;:E<%E51D;:E<1853P4E<AA863R6,8510;6537eW3X:9X48P4DIX19DCW8W7o"). Qed.
End FPX_12.

#[export] Hint Rewrite sum_factsB_eqf0 : bceq.
Section FPX_13. Context {fx : XPropExec.FPState}.



(* [comment removed for export] *)
Definition mkbc : ltac2:(zQ "30!hn8!hr8!irb>2fk@1$0$1$2") := ltac2:(zQ "60!jte!hn8!kvd!hr8!il3!kuf\2fk@1$1$3@2$0^1@2$5@2$0^1@1$2$4^1").
Lemma bc_fk_mkbc : ltac2:(zQ "50!hn8!hr8!jf!ll1!jt5>2fk@1$0$1@3$2@1$0$1@1$4@1$3^1^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_13"] "h02fkp;1p;2g00eTj11Tg0097j20Tg017a#1R0f0,00W0o"). Qed.
Lemma bc_ffk_mkbc : ltac2:(zQ "60!hn8!hr8!jf!im3!ll1!jo7>2fk@1$0$1@3$2@1$0$1@1$5@1$4^1@1$3^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_13"] "h02fkp;1p;2g00eTj12Tg01Vgj11Tg0097j20Tg017a#2R0f0#1,00W0o"). Qed.
Lemma bc_fs_mkbc : ltac2:(zQ "70!hn8!jf!hr8!il3!ku3!ll1!ll9>2fk@1$0$2@3$1@1$0$3@1$6@1$5^1@2$4^1^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_13"] "h02fkh12knh21lp;1p;2p;3p;6g00eTj14Tg02]>j1<j22Tg008]j30Tg0097j2;Tg00f4j1:Tg01X6j21Tg02[kj18j25Tg02aAj27Tg003Vj66Tg02bYj13Tg02cgj19Tg017a#4R0g001HR1#4R2^10R0f0R3#<P3f1R4O11244502X201233R0,;2%:1R1,13R4#81731E61543,13#3=020e%93#3=020eW0o"). Qed.
Lemma find_rangeI_mkbc : ltac2:(zQ "c0!hge!hn8!u6!hu2!jf!se!im3!hu9!hr8!ll1!ju7!jv0>2fk@1$1$8@3$4>1e$5@1$2@2$3$0$0@1$b@1$a@1$9^1@1$7@1$6^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_13"] "h01eh12fkp;1p;2p;3g00eTj1<Tg00f4j1;Tg01X6j20Tg02[kj21Tg01nbj2:Tg01:Aj22Tg00hSj13Tg02cgj14Tg01YDj15Tg01REj16Tg01Vgj17Tg01;oj18Tg008]j39Tg017a#<f0R0g001H#;,00/10':g00`Tg00b@R1/21#3]0%40#5#6%70#839eW1o"). Qed.
End FPX_13.

#[export] Hint Rewrite bc_fk_mkbc bc_ffk_mkbc bc_fs_mkbc find_rangeI_mkbc : bceq.
Section FPX_14. Context {fx : XPropExec.FPState}.

Lemma erange_fB_eqf : ltac2:(zQ "c0!hge!hn8!u0!u6!hu2!jf!jvf!se!im3!hr8!kga!lm2>2fk@1$1$9>4fuel$2@3$5>1e$7@1$3@2$4$0$0@2$a^1@1$b^2@2$6^1@1$8^2").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_14"] "h01eh12fkh24fuelp;1p;2p;3g00eTj1;Tg00f4j1:Tg01X6j20Tg02[kj21Tg0255j39Tg01:Aj22Tg00hSj13Tg02cgj14Tg01[ij25Tg01Vgj16Tg01];j27Tg008]j38Tg017a#;g00aaf1R0g001H#:,00/10f0R139g00`Tg00b@R2/22#3]0%40,51%60,7138eW2W1o"). Qed.
End FPX_14.

#[export] Hint Rewrite erange_fB_eqf : bceq.
Section FPX_15. Context {fx : XPropExec.FPState}.


Lemma erange0B_eqf : ltac2:(zQ "a0!hge!hn8!u6!hu2!jf!kh7!se!hr8!ki1!lm2>2fk@1$1$7@3$4>1e$6@1$2@2$3$0$0@1$8@1$9^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_15"] "h01eh12fkp;1p;2p;3g00eTj1:Tg00f4j19Tg01X6j20Tg02[kj21Tg02<Sj28Tg01:Aj22Tg00hSj13Tg02cgj14Tg022Vj15Tg023gj16Tg008]j37Tg017a#:f0R0g001H#9,00/10'8g00`Tg00b@R1/21#3]0%40#5%6037eW1o"). Qed.
End FPX_15.

#[export] Hint Rewrite erange0B_eqf : bceq.
Section FPX_16. Context {fx : XPropExec.FPState}.

Lemma erangeB_eqf : ltac2:(zQ "a0!hge!hn8!u6!hu2!jf!kid!se!hr8!kj6!lm2>2fk@1$1$7@3$4>1e$6@1$2@2$3$0$0@1$8@1$9^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_16"] "h01eh12fkp;1p;2p;3g00eTj1:Tg00f4j19Tg01X6j20Tg02[kj21Tg02@Nj28Tg01:Aj22Tg00hSj13Tg02cgj14Tg027^j15Tg028nj16Tg008]j37Tg017a#:f0R0g001H#9,00/10'8g00`Tg00b@R1/21#3]0%40#5%6037eW1o"). Qed.
End FPX_16.

#[export] Hint Rewrite erangeB_eqf : bceq.
Section FPX_17. Context {fx : XPropExec.FPState}.

Lemma base_rangeB_eqf : ltac2:(zQ "a0!hge!hn8!u6!hu2!jf!kk1!se!hr8!kke!lm2>2fk@1$1$7@3$4>1e$6@1$2@2$3$0$0@1$8@1$9^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_17"] "h01eh12fkp;1p;2p;3g00eTj1:Tg00f4j19Tg01X6j20Tg02[kj21Tg02e4j28Tg01:Aj22Tg00hSj13Tg02cgj14Tg02=ij15Tg02?=j16Tg008]j37Tg017a#:f0R0g001H#9,00/10'8g00`Tg00b@R1/21#3]0%40#5%6037eW1o"). Qed.
End FPX_17.

#[export] Hint Rewrite base_rangeB_eqf : bceq.
Section FPX_18. Context {fx : XPropExec.FPState}.

Lemma ealignB_eqf : ltac2:(zQ "80!hn8!jf!hge!kld!se!hr8!km6!lm2>2fk@1$0$5@3$1>1e$4$2@1$6@1$7^1@1$3^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_18"] "h01eh12fkp;1p;2p;3g00eTj18Tg00f4j17Tg01X6j20Tg02[kj21Tg02T1j26Tg02cgj12Tg02Acj13Tg02C3j14Tg008]j35Tg017a#8f0R0g001H#7,00/10'6g00`Tg00b@]0%20#3%4035eW1o"). Qed.
End FPX_18.

#[export] Hint Rewrite ealignB_eqf : bceq.
Section FPX_19. Context {fx : XPropExec.FPState}.

Lemma lin_nowrapB_eqf : ltac2:(zQ "80!lc!hn8!jf!se!hr8!kn1!kne!lm2>2fk@1$1$4@3$2>1e$3$0@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_19"] "h01eh12fkp;1p;2p;3g00eTj18Tg00f4j17Tg01X6j20Tg02[kj21Tg02RXj26Tg02cgj12Tg02IEj13Tg02JYj14Tg008]j35Tg017a#8f0R0g001H#7,00/10'6g00`Tg00;\]0%20#3%4035eW1o"). Qed.
End FPX_19.

#[export] Hint Rewrite lin_nowrapB_eqf : bceq.
Section FPX_20. Context {fx : XPropExec.FPState}.

Lemma srl_expandB_eqf : ltac2:(zQ "90!hn8!hu2!hge!se!jf!hr8!kod!lm2!kpa>2fk@1$0$5@3$4>2ts@1$0@2$1$2$3@2$1$2@1$0@2$1$2$3@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_20"] "h02fkh12tsp;1p;2p;3g00eTj11Tg00f4j19Tg01X6j23Tg02[kj22Tg02ZRj28Tg01:Aj20Tg02cgj17Tg02Kjj14Tg02M>j15Tg008]j36Tg017a#1f0R0g001H#9,30/20'8g00b@R1g00`T'0#1R21012]1%70#4%5036eW0o"). Qed.
End FPX_20.

#[export] Hint Rewrite srl_expandB_eqf : bceq.
Section FPX_21. Context {fx : XPropExec.FPState}.

Lemma fact_nowrapB_eqf : ltac2:(zQ "90!lc!hn8!jf!hge!se!kq9!hr8!kr7!lm2>2fk@1$1$6@3$2>1e$4>2hi$3$0@1$7@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_21"] "h01eh12fkh22hip;1p;2p;3g00eTj18Tg00f4j17Tg01X6j20Tg02[kj21Tg02_gj26Tg02cgj12Tg02UFj13Tg02V[j14Tg008]j35Tg017a#8f0R0g001H#7,00/10'6g00`Tg00b@g00;\]2]0%20#3%4035eW1o"). Qed.
End FPX_21.

#[export] Hint Rewrite fact_nowrapB_eqf : bceq.
Section FPX_22. Context {fx : XPropExec.FPState}.

Lemma sum_fact_xB_eqf : ltac2:(zQ "a0!hn8!hge!hu2!jf!se!hr8!il3!ks7!lm2!kt4>2fk@1$0$5@3$3>2ts@1$0@2$2$1$4>2lo$1>2hi$1@1$0$6@1$9@1$8^1@1$7^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_22"] "h02fkh12hih22loh32tsp;1p;2p;3g00eTj10Tg00f4j19Tg01X6j22Tg02[kj21Tg02^Nj28Tg01:Aj27Tg02cgj13Tg02Wmj14Tg02YAj15Tg008]j36Tg017a#0f0R0g001HR1#9,20/10'8g00b@R2g00`T'7#0%01^12^22]3%30#4%5036eW0o"). Qed.
End FPX_22.

#[export] Hint Rewrite sum_fact_xB_eqf : bceq.
Section FPX_23. Context {fx : XPropExec.FPState}.

Lemma sum_factsB_eqf : ltac2:(zQ "70!hn8!hr8!jf!il3!ku3!lm2!kuf>2fk@1$0$1@3$2>2kn@1$0$1@1$0$3@1$6@1$5^1@1$4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_23"] "h02fkh12knp;1p;2p;3g00eTj10Tg00f4j18Tg01X6j22Tg02[kj21j13Tg02aAj27Tg02cgj16Tg02]>j14Tg008]j35Tg017a#0R0f0R1g001HR2#8,21/11'7%02^10%61#3%4135eW0o"). Qed.
End FPX_23.

#[export] Hint Rewrite sum_factsB_eqf : bceq.
Section FPX_24. Context {fx : XPropExec.FPState}.


Definition lin_test_relB : ltac2:(zQ "60!hge!lc!hn8!hu2!se!irb>2bc$5>1c$0>2ts@1$2@2$3$0$4>4test>0$0>0$0$1$1") := ltac2:(zQ "f1!hge!hu2!lc!hn8!se!ige!il3!u6!jse!ho7!jr4!lma!ll9!irb!kj6&@2$1@1$3@2$1$0$4@2$1$0$0\2bc$d\1c$0\2ts@1$3@2$1$0$4\4test>0$0>0$0$2M3\1x@1$3$6$2@1$c^4$5\1s$6\1l@1$3$6M1\1x@2$1~0$2$2@5$b@3$9$6^2^1^4ZZ$5\1p~0\1b$2M1\1p~0$2^2\3ts'@1$3@2$1$0$4\2p0@2$1$0$0M1\2p0@2$1$0$0$2^1\3lo0$0\3hi0$0M2\1b$2$2^5M7\1x@1$7@2$1$0$0$2@3$a@1$e^c^b^4\1p@2$1$0$0M1\1p@2$1$0$0$2^1\2lo$0\2hi$0@2^c@2$8^2^5@2$8^1^4$5$5").

Definition lin_testB : ltac2:(zQ "60!hge!lc!hn8!hu2!se!irb>2bc$5>1c$0>2ts@1$2@2$3$0$4>4test>0$0>0$0$1$1") := ltac2:(zQ "b0!hge!lc!hu2!u6!ls4!hn8!m3!se!jr4!irb!kj6\2bc$9\1c$0\2ts@1$5@2$2$0$7\4test>0$0>0$0$1M3\1x@1$3@2$2$0$0$1@3$8@1$a^4^3^2\1p@2$2$0$0M2\1p@2$2$0$0$1^1\2lo$0\2hi$0M1\0$1$1@2^4^2^1$6@4$4^7^6^5^4@4$4^4^3^2^1").

Definition lin_srangeB (bc : bctx) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then   (* [comment removed for export] *)
    let sc := (2 ^ j)%Z in
    let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
    let '(c2, t2) := srl_expandB bc ts in
    let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
    match lin_range (erangeB bc) (sc * fst l + c2 + c3)%Z t3 with
    | Some (lo', hi') =>
        let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
        if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
    | None => None
    end
  else None.

Definition lin_nowrapRB (bc : bctx) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expandB bc (snd l) in            (* [comment removed for export] *)
  if lin_testB bc (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
  else (* [comment removed for export] *)
    match lin_srangeB bc e with Some _ => true | None => false end.

Definition lin_apart0B : ltac2:(zQ "40!hge!se!lc!irb>2bc$3>2b1$1>2k1$0>2n1$0>2b2$1>2k2$0>2n2$0$2") := ltac2:(zQ "h20!hge!se!hn8!hu2!jp8!uf!jpf!jq5!jqb!lt5!js0!lu5!luc!lv2!lvb!irb!jse!mg8\2bc$f\2b1$1\2k1$0\2n1$0\2b2$1\2k2$0\2n2$0@2$4@2$4@2$9^7^6@2$9^7^3=2l1$7@1$8^6=2l2$7@1$8^4@4$e^9@2$b@2$b@2$h0@3$5$0@1$2@2$3$0$1^1^4@3$5$0@1$2@2$3$0$1^2^7@2$d@3$6$0@1$2@2$3$0$1^1@3$6$0@1$2@2$3$0$1^2\2lo$0\2hi$0@2$c@2$a^8^2@2$a^1@1$h1^5").

Definition lin_apartB : ltac2:(zQ "40!hge!se!lc!irb>2bc$3>2b1$1>2k1$0>2n1$0>2b2$1>2k2$0>2n2$0$2") := ltac2:(zQ "70!hge!lc!se!ige!mgf!mhc!irb\2bc$6\2b1$2\2k1$0\2n1$0\2b2$2\2k2$0\2n2$0M1\0$1$1@2$4^6^3@7$5^7^6^5^4^3^2^1$3").

Definition lin_brangeB : ltac2:(zQ "50!hge!u6!hu2!se!irb>2bc$4>1e$3@1$1@2$2$0$0") := ltac2:(zQ "ha1!hge!hu2!u6!hn8!se!lc!mib!il3!jse!jj6!jp8!ho7!ige!uf!jjd!jpf!jq5!jqb!jr4!lma!jk4!ll9!irb!kj6!js0!js7&@2$1@1$3@2$1$0$4@2$1$0$0\2bc$h6\1e$4=1l$h0@1$h1^1M3\1x@1$3$7@1$2@2$1$0$0@1$h5^3@1$6@2$1$0$0\1s$7\2l0@1$3$7M1\1x@2$1~0$5@1$2@2$1$0$0@5$h3@3$b$7^2^1@3$f$0@1$3@2$1$0$4^3ZZ$c\1p~0\1b$5M1\1p~0@1$2@2$1$0$0^2\3ts'@1$3@2$1$0$4\2p0@2$1$0$0M1\2p0@2$1$0$0@1$2@2$1$0$0^1\3lo0$0\3hi0$0M5\1b$5@1$2@2$1$0$0^5M2\1x@1$2@2$1$0$0@1$2@2$1$0$0@3$h2@1$h7^b@3$d$0@1$3@2$1$0$4^9^4\1p@2$1$0$0M1\1p@2$1$0$0@1$2@2$1$0$0^1\2lo$0\2hi$0=3lo'$0@2$8^2^5=3hi'$0@2$8^2^5M5\0$5@1$2@2$1$0$0@2$a@2$h8Z^2@2$h9^1$h4@2$9@2$1$0$0@4$e$0$0^2^1@1$6@2$1$0$0@1$6@2$1$0$0@1$6@2$1$0$0").

Definition xloB : ltac2:(zQ "40!u6!hge!se!irb>2bc$3>1e$2@1$0$1") := ltac2:(zQ "fc!hge!u6!hu2!jj6!se!mib!mj2!mk1!kj6!u0!lc!i4!rb!ml0!irb&M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0@2$3$0^2&\1p@2$2$0$0~0&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~1@1$5$0&M1\1x@1$1@2$2$0$0@1$1$0@2$6^5^4~1~2&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~1~3&\1b$4~4&\1a$4~5&\2op$b~6&\2op$c~6&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~1@1$5$0&M1\1x@1$1@2$2$0$0@1$1$0@2$6^6^5~1~9&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~1~a\2bc$e\1e$4M4\1e$4@1$1$0^1\1z$0@2$3$0@1$d^1\1n$9M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~1M1\1x@1$1@2$2$0$0@1$1$0@2$6^3^2~1M1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2~1@1$5$0~7~7~8~8\2sx$a\2lo$9\1n$9\2e0$4~b\2sx$a\1k$9\1i$0\1n$9~b").

Definition xhiB : ltac2:(zQ "40!u6!hge!se!irb>2bc$3>1e$2@1$0$1") := ltac2:(zQ "fc!hge!u6!hu2!jj6!se!mib!mj2!mk1!kj6!u0!lc!i4!rb!ml0!irb&M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0@2$3$0^1&\1p@2$2$0$0~0&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~1@1$5$0&M1\1x@1$1@2$2$0$0@1$1$0@2$6^5^4~1~2&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~1~3&\1b$4~4&\1a$4~5&\2op$b~6&\2op$c~6&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~1@1$5$0&M1\1x@1$1@2$2$0$0@1$1$0@2$6^6^5~1~9&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~1~a\2bc$e\1e$4M4\1e$4@1$1$0^1\1z$0@2$3$0@1$d^1\1n$9M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~1M1\1x@1$1@2$2$0$0@1$1$0@2$6^3^2~1M1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2~1@1$5$0~7~7~8~8\2sx$a\2lo$9\1n$9\2e0$4~b\2sx$a\1k$9\1i$0\1n$9~b").

Fixpoint xt_nowrapB (bc : bctx) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => lin_nowrapRB bc e && xt_nowrapB bc r end.

Definition lin_ge0_scaledB (bc : bctx) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (2 ^ j)%Z in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expandB bc ts' in
    let '(c3, t3) := (if has_srl t2 then srl_expandB bc t2 else (0%Z, t2)) in
    lin_testB bc (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
  else false.

Definition lin_ge0B (bc : bctx) (pos neg : xterms) : bool :=
  (xt_nowrapB bc pos && xt_nowrapB bc neg &&
   (* [comment removed for export] *)
   (if lin_testB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
    else let '(c2, t2) := srl_expandB bc (lsub_e (xt_lin pos) (xt_lin neg)) in
         if lin_testB bc (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
         else (* [comment removed for export] *)
         if (if has_srl t2 then
               let '(c3, t3) := srl_expandB bc t2 in
               lin_testB bc (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
             else false) then true
         else (* [comment removed for export] *)
           lin_ge0_scaledB bc (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))))%bool.

Definition xinside0B : ltac2:(zQ "40!se!hge!lc!irb>2bc$3>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2") := ltac2:(zQ "a0!se!hge!hu2!ho7!jjd!kvd!lc!ml9!ige!irb\2bc$9\2b1$0\2k1$1\2n1$0\2b2$0\2k2$1\2n2$0M6\0$6$6@3$7^7@3$3@2$2$0$1@4$4$0$1^6^5@1$5@2$2$0$1@3$3@2$2$0$1@4$4$0$1^3^2@1$5@2$2$0$1@3$7^7@3$3@2$2$0$1@4$4$0$1^3^2@3$3@2$2$0$1@4$4$0$1^1Z@1$5@2$2$0$1@3$3@2$2$0$1@4$4$0$1^6^5@3$3@2$2$0$1@4$4$0$1^4Z@1$5@2$2$0$1$8").

Definition xinside_numB : ltac2:(zQ "40!se!hge!lc!irb>2bc$3>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2") := ltac2:(zQ "e0!hge!u6!lc!ige!jse!hu2!se!mm5!mmd!js0!jp8!kke!irb!mn5\2bc$c\2b1$6\2k1$0\2n1$6\2b2$6\2k2$0\2n2$6M1\1x@1$1$0$2@2$8^7^3\3lo2$0M1\1x@1$1$0$2@2$7^8^4\3hi2$0M2\0$2$2@2$d^2^1M1\1x@1$1@2$5$0$0$2@2$b^9^8\1p@2$5$0$0M5\1p@2$5$0$0$2^1\3lo1$0\3hi1$0M1\1x@1$1$0$2@2$7^c^9\2h1$0M1\1x@1$1$0$2@2$8^d^7\2l2$0@2$a@2$9@2$4^7^9@2$4^4^c@2$9@2$4@2$4^3^c^2@2$4@2$4^7^9^1$3$3$3$3$3$3").

Definition xinsideB : ltac2:(zQ "40!se!hge!lc!irb>2bc$3>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2") := ltac2:(zQ "90!lc!se!hge!ige!mnc!mgf!mo5!mp2!irb\2bc$8\2b1$1\2k1$2\2n1$1\2b2$1\2k2$2\2n2$1M0\0$0$0@2$5^6^3@7$6^7^6^5^4^3^2^1M0\0$0$0@1$4^3@7$7^7^6^5^4^3^2^1$3").

Definition sub_itvB : ltac2:(zQ "50!hge!se!lc!mq2!irb>2bc$4>1b$1>1k$0>1n$0>1c$3>1m$1$2") := ltac2:(zQ "h30!lc!hge!ige!mqa!js0!jp8!u6!mr2!se!jse!m3!mrb!t5!mq2!jk4!ms2!mmd!irb!js7\2bc$h1\1b$8\1k$1\1n$1\1c$d\1m$8M0\0$0$0M0\0$0$0@2$5@2$c^5@1$7^2@2$4@1$3^2^4M6\1x@1$6$1$0@2$h0^6^1\2ml$1@2$4@2$9^5^4@2$9@1$3^3^1$2$2$aM0\0$0$0@2$5@2$4Z^3@2$h2^3$e@7$f^6^5^4@1$b^3@1$7^2@1$3^2^1$2").

Fixpoint kdisj_apartB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itvB bc b1 k1 n1 c1 m1 then sub_itvB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itvB bc b1 k1 n1 c2 m2 then sub_itvB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apartB bc rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apartB : ltac2:(zQ "40!hge!se!lc!irb>2bc$3>2b1$1>2k1$0>2n1$0>2b2$1>2k2$0>2n2$0$2") := ltac2:(zQ "f0!hge!lc!hu2!jse!u6!ige!m3!se!kke!js0!luc!mse!mte!jt5!irb\2bc$e\2b1$7\2k1$0\2n1$0\2b2$7\2k2$0\2n2$0M1\0$1$1M4\1x@1$4@2$2$0$0$1@2$8^7^6\1p@2$2$0$0M2\1p@2$2$0$0$1^1\3lo1$0\3hi1$0M4\1x@1$4@2$2$0$0$1@2$8^a^6\2p0@2$2$0$0M2\2p0@2$2$0$0$1^1\3lo2$0\3hi2$0@2$a@2$9@2$3@2$3^4^b^a@2$3^2^8@2$9@2$3@2$3^1^8^7@2$3^5^b$5$5$6M1\0$1$1@8$b^7@1$d^7^6^5^4^3^2^1$6@7$c^7^6^5^4^3^2^1").

Definition sub_itv_xB : ltac2:(zQ "50!se!lc!hge!mq2!irb>2bc$4>1b$0>1k$2>1n$0>1c$3>1m$0$1") := ltac2:(zQ "70!se!hge!mr2!mqa!mq2!ms2!irb\2bc$6\1b$0\1k$1\1n$0\1c$4\1m$0@7$5^6^5^4^3@1$2^2@1$3^2^1").

Fixpoint kdisj_apart_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_xB bc b1 k1 n1 c1 m1 then sub_itv_xB bc b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_xB bc b1 k1 n1 c2 m2 then sub_itv_xB bc b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_xB bc rest b1 k1 n1 b2 k2 n2
  end.

Definition end_hiB : ltac2:(zQ "40!hge!se!u6!irb>2bc$3>1b$1>1k$0>1n$1>3lo1$0>3hi1$0>2h1$0@1$2$0") := ltac2:(zQ "h5e!hge!lc!u6!hu2!jse!mib!muc!mv5!se!jj6!ige!mrb!jk4!ju7!jv0!js0!js7!u0!i4!rb!irb&M3\1p@2$3$0$0@1$2$0^1\1z$0\3ehi$0@2$9$0^1&\1p@2$3$0$0~0&M1\0$1$1@2$fZ@2$4^6^8@2$h0@2$4@2$4^5^8^4$c$a&@2$e@1$d^a@3$7$6@3$7$6^9@1$b^8^7&M2\1x@1$2@2$3$0$0@1$2$0~3~1@1$5$0&M1\0$1@1$2$0~2~4@1$5$0&\2b0$8~5&\1a$8~6&\2op$h2~7&\2op$h3~7&M1\0$1$1@2$fZ@2$4^7^9@2$h0@2$4@2$4^6^9^5$c$a&@2$e@1$d^b@3$7$6@3$7$6^a@1$b^9^8&M2\1x@1$2@2$3$0$0@1$2$0~b~1@1$5$0&M1\0$1@1$2$0~a~c@1$5$0\2bc$h4\1b$8\1k$0\1n$8\3lo1$0\3hi1$0\2h1$0M8\1n$8@1$2$0^4\1z$0@1$5$0\2n0$h1M1\0$1@1$2$0M1\0$1$1@2$fZ@2$4^4^6@2$h0@2$4@2$4^3^6^2$c$aM2\1x@1$2@2$3$0$0@1$2$0@2$e@1$d^8@3$7$6@3$7$6^7@1$b^6^5~1@1$5$0@1$5$0~8~8~9~9\2sx$1\2lo$h1\2n0$h1\1e$8~d\2sx$1\2k0$h1\1i$0\2n0$h1~d").

Definition ranges_apart_xB (bc : bctx) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apartB bc b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_rangeB bc b1, base_rangeB bc b2, xhiB bc n1, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_xB bc (bc_fk bc) b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

Fixpoint disj_sidesB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sidesB bc rest b1 k1 n1 in
      let r1 := if sub_itvB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itvB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sidesB bc rest b1 k1 n1
  end.

Fixpoint disj_sides_xB (bc : bctx) (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_xB bc rest b1 k1 n1 in
      let r1 := if sub_itv_xB bc b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_xB bc b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_xB bc rest b1 k1 n1
  end.

Fixpoint in_sidesB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvB bc b2 k2 n2 c m then true else in_sidesB bc r b2 k2 n2
  end.

Fixpoint in_sides_xB (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_xB bc b2 k2 n2 c m then true else in_sides_xB bc r b2 k2 n2
  end.

Definition mk_sprepB : ltac2:(zQ "40!se!hge!nj2!irb>2bc$3>2b1$0>2k1$1>2n1$0$2") := ltac2:(zQ "h22!se!hu2!mq2!kvd!u0!hge!lc!i4!rb!jt5!hn8!nja!ml0!nk2!nl1!mm5!kke!irb&\2op$7\1a$0\1b$0@1$3@2$1$2$0&\2op$8\1a$0\1b$0@1$3@2$1$2$0\2bc$h1\2b1$0\2k1$5\2n1$0@4$b@2$h0^4^3@2$f^4^1M0\2n1$0@1$a@2$1$2$0^1\2z1$5@5$d^5@1$9^5^4^3@1$c^1\1n$4@1$3@2$1$2$0~0~0~1~1\2sx$6\2lo$4\1n$4\1e$0@1$3@2$1$2$0\2sx$6\1k$4\1i$5\1n$4@1$3@2$1$2$0@5$e^4@1$9^4^3^2^1").

Definition ranges_apart_pB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, base_rangeB bc b2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sidesB bc (sp_D sp) b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, base_rangeB bc b2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

Lemma lin_test_relB_eqf : ltac2:(zQ "a0!hge!lc!hn8!hu2!jf!se!hr8!npe!ls4!lm2>2fk@1$2$6@3$4>1c$0>2ts@1$2@2$3$0$5>4test>0$0>0$0$1$1@1$8@1$9^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_24"] "##6op'0h01eh12fkh21li001lh31oh44testh52tsh61xi011xh72x0h82x1i021bi032hii043hi0i052loi063lo0i071pi082p0i091si0:3ts'p;1p;2p;3p;6p;4p;5g00eTR0j12Tg01:AR1j26Tg02cgj10Tg02fMj1=j2Ij3@j4DTg02gcj1Jj2Cj3>j4ETg02]>j28Tg00fTj3<Tg027^j19Tg01bSj31Tg01FXj2;Tg028nj14Tg008]j33Tg00hSR2j1HTg0097j2GTg02i6j1BTg003Vj6:Tg02bYj1ATg02jJj1?Tg002Tj55Tg02k]j5FTf1R3f0R4g01TVR5P5g00>4R5DFp=7g017a#2g00b@R6g00`TR7,66#2R8g00;\R9\6\6R:P9]4R;]5%04#=%J4P8P;%03/I41C34P:P9f2R;#0?@34A>;34g001HR<#2R=f3R>/8>R?P0P<P9P4P5P11666R@,68RAP9P9A<<34RBf4RC'7RDP1P8P@P9P3P1P6P6!s\$9P9PCP2P@P9f<RE#0#9f;RF;1>!sK-E1;3CRG1;4>RHO2n2001107000120105103RIP5n101101000210!sF$P5n0110200!s&$0!s`&8!s`'6104!st3:108!s:&1!s:'7102!t+-0020109100!ut%18CCRJP5P1P!uo$P!ubD%4E?1F>P!u+~!u+>RE539X2=%H@^07R7%4>!x5&!u;Pf8!u:~!u:C=39EX37!u-&?!u-,17B>!wEEFf:!yz1FPGP!yr:!uV~!uV=,G9%0>R5#9%B>E:%A5%?>E:P5P;P3P4CDP>!s0&E539eX8:D5X78D5X66D5W1o"). Qed.
End FPX_24.

#[export] Hint Rewrite lin_test_relB_eqf : bceq.
Section FPX_25. Context {fx : XPropExec.FPState}.

Lemma lin_testB_eqf : ltac2:(zQ "a0!hge!lc!hn8!hu2!jf!se!hr8!nqd!nr8!lm2>2fk@1$2$6@3$4>1c$0>2ts@1$2@2$3$0$5>4test>0$0>0$0$1$1@1$8@1$9^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_25"] "##1Jp'0h01bh11ch21eh32fkh41oh54testh62tsh71xi001xh82x0h92x1i012hii022loi031pp;1p;2p;3p;4p;6p;5g00eTj19Tg01:AR0j28Tg02cgj10Tg02lmj1:j2Fj3>j4=Tg02n?j1Hj2?j3<j4CTg00hSR1j1;Tg028nj15Tg01bSj34Tg02fMj46j1DTg02gcj41j1GTg008]j33Tg0097j2ETg02oNj1BTg003Vj67Tg027^j1@Tg02i6j1ATg002Tj52Tg017a#9g00b@R2g00`TR3,82#9R4g00;\R5\2\2R6P5]5R7]6R8f0R9#0#:%H9P4P7f1R7#0/F91?79P6P5f2R:#0?>79A<:791822R;#;^23R3f3R<#5R=P1P;P5A49<:P0P2P2P5P9P5P5f4R>P7P9O2R?g00<<R@f7RA#0f6RBf5RCP>C6n010!s#$20000n2001103000120102101%0>P<P:P7C6n101!sU%210!sM$!tK%%5>?4<:RD!tO1P?P@PAPBPCP>C1!t8EP!t7'1!t75RA535X43P8^12R8%G<!tI%P!tB7<!tB%O3!tBF9!tB%O3!tB5=35AX08!w#'=:7!t:2<!v}%P@!t>%P<!u\H!t>$P9!u\7,E5%0<R>#D%B<E7%@>%A<E7P>!sY&=!sc+C535eX96D2X84D2X72D2W3o"). Qed.
End FPX_25.

#[export] Hint Rewrite lin_testB_eqf : bceq.
Section FPX_26. Context {fx : XPropExec.FPState}.

Lemma lin_srangeB_eqf : ltac2:(zQ "a0!hge!hn8!u6!hu2!jf!se!hr8!ns5!nt2!lm2>2fk@1$1$6@3$4>1e$5@1$2@2$3$0$0@1$8@1$9^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_26"] "##:'p'0h01th11eh22fkh31oh41pi001ph52tsh61xi011xi022c2i032c3i043hi'i053lo'i062t2i072t3p;1p;2p;3p;4p;6p;5g00eTj1ITg01:AR0j2>Tg00hSR1j1QTg02cgj16Tg030hj1Xj2STg032<j1Vj2TTg028nj1=Tg01_Wj12Tg033Mj11Tg01T9j20Tg01gjj1KTg01D[j17Tg01E@j1H!s/$^j24Tg000Lj3?Tg01e0j29Tg01b6j3ETg01SYj45!sJ$0j4DTg02Kjj2Cj1NTg034bj1UTg01FXj2:!s_$Sj3<Tg0360j2BTg01j=j2ATg01G5j2FTg00kNj2@Tg00nJj1PTg02M>j28j1MTg008]j3;Tg0097j2LTg037<j1OTg003Vj6GTg027^j1RTg02i6j1JTg002Tj5WTg00b@R2f1R3f0R43Ep=3g017a#Ig00`TR51>22R6#QR7%64#X%V4P7^15R8%=3g00;\R9P7P9P9g01TVR:1>25R;#IR<%23'3R=#1R>'0g01VBR?#K#7!s$$HR@,0>g00>4RAn010!s#$20000RBP0P2P<P7f2RC#6P;P;P2P5%7?#HR?%2C,3<#1'4A?254RD'9AE254REC5X0;P=CDR='C!sj'P91>2<RF%U4RGf4RH#6/C4!sB$:P4C5RI!tL1P1P6P7f5RJ#2RK!t8$,4?A?2<K'9f3RK':/:3RL=<H4!t2$2P7P4P!u{&f8#2!sZ'RM,B3RN,0:P9P91A4MRM,0Ng020<RO,FMP!uo2!s642P2PNPMC5,@6%P6RM!sF1n2001!s7%120105104RNPMn1011!sP$2!s,%!sP'1!sP'3107!s:32106P!t0/100!uM$!wU+18C=!vu,PFPG18H4P!v_96#=?<L4P!t^8RN!t`[RL5;7X38PF^5<R8%M3!tr1P4P=O1!tt1PCP4O1!tv4!tR\=;7LX48!xb'%24,3<R8#1RL,0:10L@!x84!t^'!{1&14?>/9DP!zq&8CD,83!vy3K!vy:%=J%2HRH!zZ/H'9/:K/:3;<!zT77!zT-?,B3R<!zT,?R?,0<1F?O!zNH<P?!zN$P!zKF!zIo,L7%63RM#N%O3EG%RM%J3EG1SM41T345;7eX65DWW2o"). Qed.
End FPX_26.

#[export] Hint Rewrite lin_srangeB_eqf : bceq.
Section FPX_27. Context {fx : XPropExec.FPState}.

Lemma lin_nowrapRB_eqf : ltac2:(zQ "80!lc!hn8!jf!se!hr8!nu1!nuf!lm2>2fk@1$1$4@3$2>1e$3$0@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_27"] "##2lp'0h02tsh11bh21ch31eh42fkh52hih62loh71oh81pi001ph94testh:1xi011xi022c2i032t2p;1p;2p;3p;4p;6p;5g00eTj1;Tg02cgj14Tg038Tj1Cj2KTg039ij1?j2LTg01:AR0j22Tg02M>j1Nj2:Tg01_Wj10Tg01b6j37Tg000Lj38Tg01FXj25Tg01T9j2>Tg01G5j2=Tg00Yhj2<Tg02lmj4Pj1ATg030hj2Oj1DTg02n?j49j1ITg032<j26j1FTg008]j31Tg00hSR1j1HTg0097j2BTg03;;j1ETg003Vj63Tg03<Sj1GTg02Kjj1@Tg037<j1JTg002Tj5MTg017a#;g00`TR2g00;\R3f0R4#4#C%?4g00b@R5/22#;R61256]0R7f1R8#NP0P5P6P3P4%089756R9O1P3P3f4R:#4R;f3R<#09856/58R=P4g01TV/>8g020<,=4'<X55X65R>CPg00<<R?P11255R@P31O;<P?g00>4R;n1011010002!s,%0RAn!s/%0020000n20!sI'120102103!tp'f2RB/:9R9P3P3P:P=P4P>C9RCP?P1P@P316:<P?P!t56!t3ER:513X87P3\5\5P3]9^06^25R7%I8!vB+!tI%B!tI%O3P?P!u6F=13:X17%H@^32R7%F!sv3!u7+PBP<O1!u9[!t6$77!t''%049756,:8!t3$<%0B!x3&!vV%!vT,<B!tA[,B3%48R;#D%E8E3%A;%G8E3%@;%J8E31K;41L84513eX:2DMW4o"). Qed.
End FPX_27.

#[export] Hint Rewrite lin_nowrapRB_eqf : bceq.
Section FPX_28. Context {fx : XPropExec.FPState}.

Lemma lin_apart0B_eqf : ltac2:(zQ "90!hge!se!lc!hn8!jf!hr8!nvf!ogc!lm2>2fk@1$3$5@3$4>2b1$1>2k1$0>2n1$0>2b2$1>2k2$0>2n2$0$2@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_28"] "##1Rh01bh12hih22loh32b2h41ch51eh62fkh72k1h82k2h92n1h:2n2h;4testh<2tsh=1xh>2x0h?2x1h@2x2hA2x3hB2x4p;1p;2p;3p;4p;5p;6p;7g00eTj1ATg02cgj11Tg03=ij1Ij2Wj3Jj4Gj5Dj6Bj7RTg03?=j1Ej2Oj3Hj4Fj5Cj6Vj7STg01:Aj2UTg02n?j1Tj4:Tg038Tj2?j1MTg00Yhj20Tg01_Wj14Tg000Lj35Tg01FXj2>!s/$;j27Tg01b6j33Tg03@Nj2=Tg01T9j26Tg02O\j1;Tg01mEj2<Tg039ij28j1KTg008]j39Tg0097j2LTg03A[j1NTg003Vj6@Tg02lmj1PTg03<Sj1QTg002Tj52Tg017a#Ag00`TR0g00b@R1g00;\R2^:1R3^81R4^30R5^91R6]7f0R7#1#I%E7P1P6f1R6#1/W71O67P1P5f2R5#1?J67AH567P0P4f3R4#1P5P6P7CGP4!s0&FP1P3f4R3#1!s:'DDP3!s2+CP1P2f5R8#1!s<,EBP8!s4-V1U10#AR9P2\1\1P2];]<^41R:f6R;#Tf7R<#1R=/?;1?=4'0P7%44R=9519/>5%4;R>9519'7/78R?A319=A319>'=R>16;6%;4,67'<X11X21R=O3'018<;18<4'0P<P?P>P=C:R='0R>592X0:P2^50R:%K;P7P;O1P7P4O1'0/0==92>X0:18;818;5'0P;%45R:!t^%6%48!t^,3A319:!t\&1686%;5!tZ-C:'0,L2%1;R>#M%N;E@%P>%Q;E@P>!vC/FRP;!s60S592eXB1D2XA1D2X@0D2X?1D2X>1D2X=0D2W6o"). Qed.
End FPX_28.

#[export] Hint Rewrite lin_apart0B_eqf : bceq.
Section FPX_29. Context {fx : XPropExec.FPState}.

Lemma lin_apartB_eqf : ltac2:(zQ "90!hge!se!lc!hn8!jf!hr8!ohb!oi7!lm2>2fk@1$3$5@3$4>2b1$1>2k1$0>2n1$0>2b2$1>2k2$0>2n2$0$2@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_29"] "##-Rh01bh12b1h22b2h32fkh42k1h52k2h62n1h72n2h81xh92x0h:2x1h;2x2h<2x3h=2x4p;1p;2p;3p;4p;5p;6p;7g00eTj1HTg02cgj10Tg03C4j1<j2Gj3=j4:j57j69j7CTg03DGj15j2>j3;j46j58j6Fj7DTg03?=j1Ej73Tg03EWj24Tg008]j32Tg0097j2?Tg03=ij1@Tg03Fhj1ATg003Vj6BTg002Tj51Tg017a#Hg00`TR0g00b@R1g00;\R2^71R3^51R4^20R5^61R6]4R7f0R8#0#<%58P1P6f1R6#0/G81>68P1P5f2R5#0?=68A;568P0P4f3R4#0P5P6P8C:P4!s0&6P1P3f4R3#0!s:'D7P3!s2+8P1P2f5R9#0!s<,E9P9!s4-FP7^10R7f6R:#EP2P214:4R;P8P:!sO,O6g00>4R<n010!s#$20000P2P2P;f7!sQ/F3P!sL2522X07!t%%95!sR/P8!sT5,?2%0:R<#@%A:EBP<!sU0C!se2D522eX=1D1X<1D1X;0D1X:1D1X91D1X80D1W3o"). Qed.
End FPX_29.

#[export] Hint Rewrite lin_apartB_eqf : bceq.
Section FPX_30. Context {fx : XPropExec.FPState}.

Lemma lin_brangeB_eqf : ltac2:(zQ "a0!hge!hn8!u6!hu2!jf!se!hr8!oj5!ok2!lm2>2fk@1$1$6@3$4>1e$5@1$2@2$3$0$0@1$8@1$9^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_30"] "##6~p'0h01eh12fkh21lh31oh41xi001xi011bi022hii033hi0i042l0i052loi063lo0i071pi082p0i091si0:3ts'p;1p;2p;3p;4p;6p;5g00eTR0j14Tg01:AR1j26Tg00hSR2j1BTg02cgj15Tg03H@j1Oj2?Tg03ITj1Nj2ITg02]>j2:Tg00nJj1ATg00fTj3@Tg01_Wj10Tg01b6j37Tg027^j19Tg000Lj3=!sA$Sj31Tg01FXj2<Tg01T9j2MTg01G5j2LTg00Yhj2KTg01SYj4FTg00kNj2ETg028nj12Tg008]j33Tg0097j2CTg02i6j1DTg003Vj6;Tg02bYj1GTg02jJj1HTg002Tj5JTg02k]j5>Tf1R3f0R4g01TVR5P5g00>4D>p=8g017a#4g00`TR6g00b@R7/67R8#BR9%54#O%N4g001HR:#4R;1:33R<P0P:P9P4%A8R=P11676#4R>/68R?g00;\R@P9A@:34RAf3RB#0977>'8RCP1P>P8P9P3P1P7P7P9P4P@P9f4RDP2P8P9f:RE#5#9f9RF#09=7>RG;1B!sU11<3DRH,M51<4BR5g020<'L'K!sJ$HP5CF,E8P=n010!s#$20000n2001107000120105102R5P=n101!sN%210!sF$!s`$1!sc$!s`/8!s`'6103!st3:108!s:&0!s:'7101!t+-0020109104!v_%f2RH/:HRIP=P1P?P@P9P!v@<P!v>&%2E?1GBP!u/~!u/>RE539X2;P9^06R;%23!xz&!u:Pf8RC!u;~!u;C=39EX3;!u0&<!u0,%0H977>,8A!wLEF%0C9=7>;1!u=~!u=@,C9%53R=#9%D3E;%G=%H3E;1?=41I34539eX46DJW1o"). Qed.
End FPX_30.

#[export] Hint Rewrite lin_brangeB_eqf : bceq.
Section FPX_31. Context {fx : XPropExec.FPState}.

Lemma xloB_eqf : ltac2:(zQ "90!hn8!u6!jf!hge!se!hr8!ol1!lm2!ol7>2fk@1$0$5@3$2>1e$4@1$1$3@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_31"] "##A&p'0h01oh11ei001eh22fkh31xi011xi021ai031bi042e0i051ii061ki072loi081ni092opi0:1pi0;2sxi0<1zp;1p;2p;3p;6p;5g00eTj1LTg00hSR0j19Tg02cgj11Tg03Jej1;j2FTg03L2j1Kj2GTg01:AR1j2JTg028nj1Bj22Tg03M<j1?Tg00kNj28Tg03H@j26j1ATg030hj25j1>Tg00nJj1:Tg03ITj20j1HTg032<j23j1ITg008]j34Tg0097j2ETg03NIj1@Tg003Vj67Tg03;;j1CTg027^j1DTg02i6j1=Tg002Tj5<Tg017a#Lg00`TR2g00b@R3#9R4f0R5#1#;%K51J33R6#9^12R7f1R8#BP2P4P8%?5,83R9P0P6P4P8f2R:O1R;P1P3P3P4P51838n200110:00012010710<R1!sZ%f3R<#1R=/6:R>P!s;&15=:P1%:3R3n101101000210!sj$!s8G!t^&<f4R=O1R?!t#'f5R@#1RA/6=RB!t<,A=P1P!t9ZRAP!s$%!tA%=P@O1RA!t?+6RC#1RD/6@RE!t?,D@!t?^DPDn0110000081010<1010830109102103!s1D4010;!wO$8104!s4&6105108!xH%P!xB&12<:RD!u0+0<:!s2+3!s2$!u<6RF!wjM12@=RG!t-,@=!t-,@!w]:RH!vFHIP!s$%!t6&C@RJ!t6,C@!t6,C!wT:RC!t6H@P@!wV~8R@544X07P7%I!wc2P!w_+P!|J+P;!yq]!sh&!wU+P!|2+P?!zo^BP!s$%!sp%!wK+P!{w+PA!t+^EPE!wE~8=44@!wD%H!wD=;P1PF!w$X?P1P!{5IHP!s$%!vd3AP1P!zgICPC!vH~!vH+2P4P5!#3F+:8!}+,!s2-3!s2$!zg`12=<!t&,!s2-3!s2$!yg[3P!s$%IPI!vM~8,E4%18RI#A%@8E7%>I%C8E7%DI%=8E71FI51G85544eX32D<W2o"). Qed.
End FPX_31.

#[export] Hint Rewrite xloB_eqf : bceq.
Section FPX_32. Context {fx : XPropExec.FPState}.

Lemma xhiB_eqf : ltac2:(zQ "90!hn8!u6!jf!hge!se!hr8!olf!lm2!om5>2fk@1$0$5@3$2>1e$4@1$1$3@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_32"] "##A0p'0h01oh11ei001eh22fkh31xi011xi021ai031bi042e0i052hii061ii071ki082loi091ni0:2opi0;1pi0<2sxi0=1zp;1p;2p;3p;6p;5g00eTj1LTg00hSR0j19Tg02cgj11Tg03Oaj1;j2FTg03Pnj1Kj2GTg01:AR1j2JTg028nj1Bj22Tg03M<j1?Tg00kNj28Tg03H@j26j1ATg030hj25j1>Tg00nJj1:Tg03ITj20j1HTg032<j23j1ITg008]j34Tg0097j2ETg03NIj1@Tg003Vj67Tg03;;j1CTg027^j1DTg02i6j1=Tg002Tj5<Tg017a#Lg00`TR2g00b@R3#9R4f0R5#1#;%K51J33R6#9^12R7f1R8#BP2P4P8%?5,83R9P0P6P4P8f2R:O1R;P1P3P3P4P51835n200110;00012010=105R1!sZ%f3R<#1R=/6:R>P!s;&15=:P1%:3R3n101101000210!sj$!s8G!t^&<f4R=O1R?!t#'f5R@#1RA/6=RB!t<,A=P1P!t9ZRAP!s$%!tA%=P@O1RA!t?+6RC#1RD/6@RE!t?,D@!t?^DPDn0110000081!vn%1093010:102103!s1D4010<108109104!s4&7106109!xH%P!xB&12<:RD!u0+0<:!s2+3!s2$!u<6RF!wjM12@=RG!t-,@=!t-,@!w]:RH!vFHIP!s$%!t6&C@RJ!t6,C@!t6,C!wT:RC!t6H@P@!wV~9R@544X07P7%I8!wc1P!w_+P!|J+P;!yq]!sh&!wU+P!|2+P?!zo^BP!s$%!sp%!wK+P!{w+PA!t+^EPE!wE~9=44@!wD%H!wD=;P1PF!w$X?P1P!{5IHP!s$%!vd3AP1P!zgICPC!vH~!vH+2P4P5!#3F+:8!}+,!s2-3!s2$!zg`12=<!t&,!s2-3!s2$!yg[3P!s$%IPI!vM~9,E4%18RI#A%@8E7%>I%C8E7%DI%=8E71FI51G85544eX32D<W2o"). Qed.
End FPX_32.

#[export] Hint Rewrite xhiB_eqf : bceq.
Section FPX_33. Context {fx : XPropExec.FPState}.

Lemma xt_nowrapB_eqf : ltac2:(zQ "80!lc!hn8!jf!hr8!omd!on9!lm2!oo2>2fk@1$1$3@3$2>2ts$5$0@1$7@1$6^1@1$4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_33"] "p'0h01bh11ei001eh22tsh32IHh41ah52fkh61kh71lh84resti011pi021zp;1p;2p;3p;6p;4p;5g00eTj18Tg02cgj12Tg03R8j1=j23Tg03SKj1;j20Tg01:AR0j2ETg00f4j1<Tg0097j26Tg00fTj35Tg038Tj2:j1CTg00Yhj24Tg039ij29j1DTg03A[j1@Tg003Vj67Tg01SYj4?Tg01Qcj5>Tg002Tj5ATg008]j3BTg00;\R1f1R2f0R33Bp=1g017a#8g03T[R4P1%23#=%;3g00`TR5g00b@R6'ER7%87R8f2R9#2/331093'1W2%<7,02,61P0P5P6f4R0#2/331003'1f5R:#2A5792R;'310:;'1[^78P3f7R;#2/3310;3'1P1f8R;/02R:f9R<#2/:0/4319<010<9R<'4R='1X01P1^15R>%D;P3P0O1/4</1=X0>f3R>,9;/4:,61%2;R1#C%@;E71312P3E7P5P6P>P9C?=572R9,3110;9'1eW3X88X66X15P2P3O2n2001101000120100102X47P3D>X24DAW5o"). Qed.
End FPX_33.

#[export] Hint Rewrite xt_nowrapB_eqf : bceq.
Section FPX_34. Context {fx : XPropExec.FPState}.

Lemma lin_ge0_scaledB_eqf : ltac2:(zQ "a0!hn8!hge!lc!hu2!jf!se!hr8!op0!oq1!lm2>2fk@1$0$6@3$4>1c$1>2ts@1$0@2$3$1$5$2@1$8@1$9^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_34"] "##4~p'0h02tsh11th21bh31ch42fkh52loh61ph74testh81xi001xh92x0i012c2i022c3i032t2i042t3p;1p;2p;3p;4p;6p;5g00eTj1ATg01:AR0j2@Tg02cgj12Tg03Uhj1Dj2Qj3MTg03W@j1Sj2Oj3BTg02M>j1Hj25Tg033Mj10Tg01G5j2;Tg01gjj1CTg01D[j13Tg01E@j1:Tg01T9j29!s8$^j24Tg000Lj3RTg01e0j26Tg01b6j3PTg01SYj48!sJ$0j4>Tg034bj1NTg01FXj21Tg02lmj4Gj1ETg02n?j4=j1FTg008]j37Tg0097j2ITg03<Sj1JTg003Vj6<Tg02Kjj1KTg037<j1LTg002Tj5?Tg017a#Ag00b@R1g00`TR2,@1R3#AR4g00;\R5]0f0R6#2#D%S6P4P5f1R7#2/Q61O761@14R8^04R9f2R:#HP5!s$%g01TVR;%07R<';g01VBR=#C#3!s$$:R>,9<g00>4R?n010!s#$20000R@P0P1P4P5P6P3P3P1P2%3=#:R=%0:'4AR126RA'6AP126RBC8X13P7C>RCO1!sa+5P8%N6RDP:P6O1!s;$;P6C8RE!t<1f7RF#2f5RG#0,4=f6RH'6f3RI'1/17RJP619;7V1X51RKCGn2001!sf%120102104!s:31103P!uK2!t`$!uO+15ICRC!tz/PD15G6P!tk2RLPFPJP6PKC=!tH[RF575X69P5\1\1P5]7^04^31R9%F:!te1P!ta,Lf4RL!tI%O3!tI[=75FX29!y$'%06R9,;;199>!v>4!tG'!x_&14=</6AP!xL&6C>,5:!vO3L!vO4PH%0L,4=/6G/1I/17!vZa,I5%2:R?#E%J:E<%K?%L:E<AM?76AB:76575eX94D?X81D?W4o"). Qed.
End FPX_34.

#[export] Hint Rewrite lin_ge0_scaledB_eqf : bceq.
Section FPX_35. Context {fx : XPropExec.FPState}.

Lemma lin_ge0B_eqf : ltac2:(zQ "80!on9!lc!hn8!jf!hr8!or4!ore!lm2>2fk@1$2$4@3$3>3pos$0>3neg$0$1@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_35"] "##;#p'0h02tsh11bh21ch32fkh42loh53negh61ph74testh81xi001xh92x0i012c2i022c3i032t2i042t3p;1p;2p;4p;3p;6p;5g00eTj1ATg02cgj12Tg03XUj1Mj2Wj3BTg03Yfj1Ej2Uj3RTg01:AR0j2?Tg02M>j1Lj28Tg03R8j2=j1DTg00Yhj20Tg03[4j11Tg01F;j23Tg03\Cj17Tg03@Nj2;Tg01T9j2VTg02lmj4<j1O!sV$Xj25Tg034bj1TTg03Uhj3Sj1FTg03SKj29j1ITg02n?j44j1KTg03W@j3>j1HTg008]j36Tg0097j2GTg03]Pj1JTg003Vj6:Tg03^lj1NTg03<Sj1CTg02Kjj1PTg037<j1QTg002Tj5@Tg017a#Ag03T[R1g00;\R2^51f0R3#2#M%E3P1P2f1R4#2/W31U43g00b@R5g00`T'?#AR61?56]0R7f2R8#Lf3R9#2R:/=81=:4'0R;P2P2P:%18R:%14R<'3R=%78R>%74R?';R@g01TV/V4V5X45RAC<g00<<RBP0P5P6P2P3P@O1P2P2f5RC#2RDf4RE#1RF%19RG'3RH/54RIP3PAC<PB!t@$2P2%T3RJ!sk+8P3O1f7RK#2f6RL#1%1CRM'3/59/54RN!sd%n2001100000120102104g00>4ROn0!s>%020000PB%7E%79RP';RQ9SDHRD!sH1!s42!t#21103!sH1'019981994'0RR!u9$9P=P@PAC4RSP!v,+189@RT!sF$CP!uk%4RU!um,P!uj+18C3RVPKP!uS%4!uS7P!uN2RKPBA>CHQ!uCcRC562X67P2\5\5P2]7^06^25R7%K8!tv$3!uT%O3!uR,P!uN%8!uN%!s@$!uL4PVPE!uH%O3!uHGPBP!w`b,0;=62CX17P2^01R7%I8P3P8O1P3P4O1'0!tp$S!u>4!w\'K!tRe'0!tQ-!vf&H8!tFF8PHPQO2!uxcR!tM&19841983!uj&8%13,3<%73,;?R?PAC4!zh/8?!sL$E13G:RG/54!zG%!zk9E3PL13MF!}H%!zqMPB1;P>9>EG!w%c,G2%28RG#F%J8E:%DG%N8E:%OG%C8E:%PG%Q8E:ABG43AR843562eX91D@X81D@W3o"). Qed.
End FPX_35.

#[export] Hint Rewrite lin_ge0B_eqf : bceq.
Section FPX_36. Context {fx : XPropExec.FPState}.

Lemma xinside0B_eqf : ltac2:(zQ "90!se!hge!lc!hn8!jf!hr8!osa!lm2!ot5>2fk@1$3$5@3$4>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_36"] "##0%h01bh12b2h22fkh32k1h42k2h52n1h62n2h73negh83posh91xh:2x0h;2x1h<2x2h=2x3h>2x4p;1p;2p;3p;4p;5p;6p;7g00eTj1MTg02cgj11Tg03`Cj1?j2Lj3@j4=j5:j69j7GTg03aUj1;j2Bj3>j4<j58j6Kj7HTg03Yfj1Jj33Tg01:Aj2ITg00f4j1A!s/$Tj30Tg008]j36Tg0097j2CTg03XUj1DTg03bdj1ETg003Vj6FTg002Tj52Tg01SYj47Tg00`TR0g00b@R1f1R2f0R3C7p=5P0P1P3g01TVC7p=4g017a#MP0g00;\R4^60R5^41R6^10R7^50R8^31%13#?%;3P1P8%12/L31B23P0P7f2R7#1?@23A>7!s9$6f3R6#1P7P2P3C=P6!s0&<P1P5f4R5#1!s:'D:P5!s2+8P0P4f5R8#1!s<,E9P8!s4-Kg03T[R9P4^79]8R9f6R:#JP4P4P31I01R;15:8R<%A;R=30R>1567R?=0;=R@O2P3%42=0;=90;?R?%45!s3&<R<O2g00>4RAn010!s#$20000P4P4f7RB?3>@A3B?<P!sG2564X09P4P41585R9=0;=1572RB=0;=53:%43!t4&B%46!s1&953:!sp3,C4%1:RA#D%E:EFPA!ur/FGP:!s60H564eX>0D2X=1D2X<0D2X;0D2X:1D2X90D2W2o"). Qed.
End FPX_36.

#[export] Hint Rewrite xinside0B_eqf : bceq.
Section FPX_37. Context {fx : XPropExec.FPState}.

Lemma xinside_numB_eqf : ltac2:(zQ "90!se!hge!lc!hn8!jf!hr8!ou2!lm2!ov0>2fk@1$3$5@3$4>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_37"] "##;wp'0h01oh11eh22b2h32fkh42k1h52k2h62n1h72n2h81xi001xh92x0h:2x1h;2x2h<2x3h=2x4i012h1i023hi1i033hi2i042l2i053lo1i063lo2i071pp;1p;2p;3p;4p;5p;6p;7g00eTj1WTg02cgj10Tg03d9j1Dj2Vj3Fj4Bj5?j6=j7RTg03eNj1@j2Mj3Cj4Aj5>j6Uj7STg01:AR0j2TTg00hSR1j1<Tg02?=j1Lj28Tg03Jej2:j1NTg03Oaj29j1JTg00N^j2ETg01FXj21Tg01T9j24Tg00Yhj2;Tg03L2j23j1GTg03Pnj25j1HTg008]j36Tg0097j2ITg03f`j1KTg003Vj67Tg03h1j1OTg02=ij1PTg03iBj1QTg002Tj52Tg017a#Wg00`TR2g00b@R3g00;\R4^72R5^53R6^22R7^62R8]4f0R9#0#D%@9P3P8f1R8#0/V91M89P2P7f2R7#0?F89AC7!s9$6f3R6#0P7P8P9CBP6!s0&AP3P5f4R5#0!s:'D?P5!s2+>P2P4f5R:#0!s<,E=P:!s4-U1T33R;#<^12R<f6R=#LP1P3P4f7R>#0/:6!s5&8R?#0/95R@P4P41E89RAP1P;P4P7P?O1P0P3P3P4P9!sW&<RB#0f9RC'9RD!s:&=RE#0/:>11=CRF116B'4117B/1811F9'4';RFg00>4RGn10110000021010400P!s:3100n2001107000120105102!sN47!sb$0!s8%0200!sr63!s:6600!u/%13>6RH!s2&5?5P4P4P!uu&18C?RI!uu315BC!sb'E>PFP!uF6RE!uH~!uH<RJ564X0<%<3!xc$%G=!tw%P9P6O1!s2&@!uY/P!uU4P!x@&P=P>O1!uU9!uS~!uS<=64JX0<P<%H!uL'!w}&P8P5O1!uLB:PCO1P!w]~!u0E!yJ&=7!y^'>6!z+1?>!|y4;R0/5?!sa'B=11=?R?1160!|m$0!|m$?!|m$!wo~!ueP,I4%0=RG#J%K=E7%NG%O=E7%PG%Q=E7PG!#4U-FRP!#4e/FS564eX=2D2X<3D2X;2D2X:2D2X93D2X82D2W3o"). Qed.
End FPX_37.

#[export] Hint Rewrite xinside_numB_eqf : bceq.
Section FPX_38. Context {fx : XPropExec.FPState}.

Lemma xinsideB_eqf : ltac2:(zQ "90!se!hge!lc!hn8!jf!hr8!pg0!lm2!pga>2fk@1$3$5@3$4>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_38"] "##10h01bh12b1h22b2h32fkh42k1h52k2h62n1h72n2h81xh92x0h:2x1h;2x2h<2x3h=2x4p;1p;2p;3p;4p;5p;6p;7g00eTj1NTg02cgj10Tg03jZj1?j2Mj3@j4=j5:j69j7ITg03kkj1;j2Fj3>j4<j58j6Lj7JTg03aUj1Kj74Tg03EWj27Tg03m9j15Tg03d9j7Ej1CTg03eNj73j1ATg008]j32Tg0097j2BTg03nFj1DTg003Vj66Tg03`Cj1GTg03o_j1HTg002Tj51Tg017a#Ng00`TR0g00b@R1g00;\R2^70R3^51R4^20R5^60R6]4R7f0R8#0#?%;8P1P6f1R6#0/M81F68P0P5f2R5#0?@68A>5!s9$4f3R4#0P5P6P8C=P4!s0&<P1P3f4R3#0!s:'D:P3!s2+8P0P2f5R9#0!s<,E9P9!s4-LP7^10R7f6R:#KP2P217:4R;P8P:!sO,O6R<P2P2%54R=f7R>#0!sE/FEg00>4R?n010!s#$20000!s41P2P2P;P>!s_04R@!s>$=!s>23P!sr@R>522X07P7%A:!t#&!so'<!saA=22>X07!u`%95!tD/P8F4!u\%!s=3!t]B,B2%0:R?#C%D:E6%G?%H:E6P?!sk0I!s{2J522eX=0D1X<1D1X;0D1X:0D1X91D1X80D1W3o"). Qed.
End FPX_38.

#[export] Hint Rewrite xinsideB_eqf : bceq.
Section FPX_39. Context {fx : XPropExec.FPState}.

Lemma sub_itvB_eqf : ltac2:(zQ "a0!hge!se!lc!hn8!jf!hr8!mq2!ph6!lm2!pi0>2fk@1$3$5@3$4>1b$1>1k$0>1n$0>1c$6>1m$1$2@1$9@1$8^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_39"] "##4>p'0h01bh12b1h22b2h31ch41eh52fkh61kh72k1h82k2h91mh:1nh;2n1h<2n2h=1oh>1xi001xh?2x0h@2x1hA2x2hB2x3i012mlp;1p;2p;3p;4p;5p;7p;6g00eTj1STg02cgj10Tg0415j1Fj2Rj3Kj4Cj5@j6NTg042Fj1Aj2Pj3Ej4Bj5?j6OTg00hSR0j1>Tg03L2j1Qj29Tg043Tj1=Tg00XYj2<Tg044aj16Tg01T9j21Tg00Yhj23Tg01FXj24Tg01G5j2:Tg00MQj18Tg03jZj7Dj1ITg03kkj77j1GTg008]j35Tg0097j2HTg045mj1JTg003Vj6;Tg03Jej1LTg03h1j1MTg002Tj52Tg017a#Sg00`TR1g00b@R2g01U4R3g00;\R4^91R5]3R6^:2R7]6f0R8#0#F%A8P2P7f1R7#0/R81P78P2P6f2R6#0?K78AE678P3P5f3R5#0P6P7P8CCP5!s0&BP1P4f4R9#0!s:'D@P9!s2+?%>2^41R:f5R;#QP4!s$%%=6R<,<;%66R=/19'3R>P0P2P4P8P7O114;9%65/48'1R?g00>4R@n10110000021010100P@n0!s8%020000g00<<RAP4P4g01TVRB/15g020<RC,:5'3RDf6RE#0P;P9%85RFP<P=P7FD!sp3!s41!u,'P!ts&19E7P?P!t`FR?P!t]$PDPEP;P9P!t@'7!t@ARE554X=:P4^<1^82^21^;1^72^11R:%G;!s{$!t',8!t'/O6!t'A=54EX0:!wS,7R:,<9%67RE/15'3!u\';8149514=8'1!udG!t]%11B61:6C'3!tc$5%86P:PEP8!ukC,H4%0;R@#I%J;E;%L@%M;E;P!yg-EN!sz%!s4&O554eXB1D2XA3D2X@2D2X?2D2X>1D2W5o"). Qed.
End FPX_39.

#[export] Hint Rewrite sub_itvB_eqf : bceq.
Section FPX_40. Context {fx : XPropExec.FPState}.

Lemma kdisj_apartB_eqf : ltac2:(zQ "90!hge!hn8!se!hr8!lc!jf!pic!pja!lm2>2fk@1$1$3@3$5>2kn@1$1$3>2b1$2>2k1$0>2n1$0>2b2$2>2k2$0>2n2$0$4@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_40"] "##?up'0h02b1h12b2h22k1h32k2h42n1h52n2h61bh72knh82IHh91Kh:1ci001ch;2fkh<1ki011kh=1mi021mh>1ni031nh?4resti041ai052c1i062c2i071ei082hii092k0i0:2loi0;2m1i0<2m2i0=1vi0>1wp;1p;2p;3p;4p;5p;6p;7p;8p;;g00eTj1MTg02cgj10Tg047Bj1@j2Lj3Bj4>j5;j69j7Jj86Tg048Wj1<j2Cj3?j4=j5:j6Kj7Ij81Tg008]j34Tg00f4j1ATg0097j27Tg0415j65j1ETg042Fj62j1DTg049ij1FTg003Vj68!sb$Tj3GTg01Qcl;HTg002Tj53Tg017aR0#MR1P1g00`TR2g00b@R3g00;\R4^53R5^33R6^12R7^43R8]2R9]0f0R:#0#@%<:P2P9f1R9#0/L:1C9:P3P8f2R8#0?B9:A?8!s9$7f3R7#0P8P9P:C>P7!s0&=P2P6f4R6#0!s:'D;P6!s2+:P3P5f5R5#0!s<,E9P5!s4-KP3P4f6R;#0!s>/FJP;!s60IP0f>R<#0!s>1G6P<!s821544^53^33^12^43^23^02X71f=%A!t30G1,74X53X33X12X43X23X02f?!t6^P4f@R<f7R=!sS1P0P4f9R!v[%7P8!s+&4!s$%fER?#0R@f:RAP>f8RBP7P8E5P@P=!tE$9P:E5g00>4RCn010!s#$20000g00<<RD!sp'P@PAP>PB!sX%!sf+!st%!sa2PDP6!s81!sF27P8n011!s;$:3010410>10=2!s1%3!s9&31092010:108201071023!s-%!s9'41034010510;10610<!sb,0!sG'P0P4P>fDR@f;!u:$!u2%6G1REfCPA!s8,P7G1RFPEPFP!s+%!ut'?!ut&7P8E2P?!v\-2!ut6!s\3!sN%?!vR-!s\7?f<!sV&!sN$G1R?!vd@EPF!vd~!vd4RG544X64g01U4P4^=2]:^>3^<3^62RH%D<!w-%!vV$!v`56!v`,O5P6!v`,O5!v`>6!v`,!s\-!sj%!v`6!vN~!vNT=44GX6H!v3$BPFfBP>!y},P8G1RHPFPHP!s+%!|u,!xo%!y;%@!sV&!z#C!s\'!sN%@!t4,!s\8E!vE@FPH!vE~!vE4,74%0<RH#E%F<E8PHP!#5806!#5u0O6E8PHAG0B=RB!#6H3B!#6H3e!#7-4W8X?1X9!#701M;HX53D3X33D3X12D3X43D3X23D3X02D3X71D3W;o"). Qed.
End FPX_40.

#[export] Hint Rewrite kdisj_apartB_eqf : bceq.
Section FPX_41. Context {fx : XPropExec.FPState}.

Lemma ranges_apartB_eqf : ltac2:(zQ "90!hge!se!lc!hn8!jf!hr8!pka!lm2!pl9>2fk@1$3$5@3$4>2b1$1>2k1$0>2n1$0>2b2$1>2k2$0>2n2$0$2@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_41"] "##:ep'0h01bh12b1h22b2h31eh42fkh52k1h62k2h72knh81lh92n1h:2n2h;1oh<1xi001xh=2x0h>2x1h?2x2h@2x3hA2x4i013hi1i023hi2i033lo1i043lo2i051pi062p0p;1p;2p;3p;4p;5p;6p;8p;7g00eTj1YTg02cgj11Tg04;>j1Cj2Xj3Ej4Aj5>j6<j7TTg04<Tj1?j2Mj3Bj4@j5=j6Wj7VTg01:AR0j2UTg02=ij2;j1PTg01FXj20Tg01T9j25Tg01mEj2:Tg047Bj89j1KTg03C4j7Dj1NTg02?=j24j1GTg048Wj87j1ITg03DGj78j1HTg008]j33Tg00hSR1j1FTg0097j2JTg04=gj1LTg003Vj66Tg04?@j1OTg03iBj1QTg04@Wj1RTg04Aej1STg002Tj52Tg017a#YR2g00`TR3g00b@R4g00;\R5^:4R6^64R7^23R8^94R9]5R:f0R;#1#C%?;P4P9f1R9#1/X;1M9;P4P8f2R8#1?E9;AB89;P3P7f3R7#1P8P9P;CAP7!s0&@P4P6f4R6#1!s:'D>P6!s2+=P4P5f5R<#1!s<,E<P<!s4-WP2f6R=P5P5P11U44R>P5f7R?#1R@/;=P0P4P4P5P;P1P>P5f:RA#1!s?0f;RB,07/0Af8RC,09'510;C/0?106B'5':n2001106000120104102RBg00>4RCn101100000210!sK$!sU&5!sU'3101P!sN3500g00<<RD!u2$@P;P=!uP,G9PDP@!s8/FDREn0!sg%020000!s41!ux%P>P514?!um414A=PBP!t{^RFP!tx%?P?!tx07PD!s81F8RG!tx?RH535X82%F>^33RI%G=!u3,P;P=O1!u53P7!s<$!u7`!u5&@!u529R@PDP!vy@=35HX;IP:^13R:%H!t}%!v-'@PD!x&1O6!ssD0:P:^72R2%I!ss1;!tl1O7PDPG!suE2!xl/=<!{[49R>/4!s=-107A/0>109?!{S$?/0=106A!{S;!w>f=!uN/P;!yM$!s80F8!u^?,J5%1=RD#K%L=E6%ND%O=E6%PD%Q=E6%RD%S=E6PD!sy0T!t12V535eXA4D2X@4D2X?3D2X>4D2X=4D2X<3D2W4o"). Qed.
End FPX_41.

#[export] Hint Rewrite ranges_apartB_eqf : bceq.
Section FPX_42. Context {fx : XPropExec.FPState}.

Lemma sub_itv_xB_eqf : ltac2:(zQ "a0!se!lc!hn8!jf!hge!hr8!mq2!pma!lm2!pn6>2fk@1$2$5@3$3>1b$0>1k$4>1n$0>1c$6>1m$0$1@1$9@1$8^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_42"] "##,Th01bh12b1h22b2h31ch42fkh51kh62k1h72k2h81mh91nh:2n1h;2n2h<1xh=2x0h>2x1h?2x2h@2x3p;1p;2p;3p;4p;5p;7p;6g00eTj1GTg02cgj10Tg04C8j1=j2Fj3>j4;j57j6ATg04DKj16j2Ej3<j4:j58j6BTg03kkj19j72Tg043Tj15Tg044aj14Tg008]j33Tg0097j2DTg03jZj1CTg045mj1?Tg003Vj6@Tg002Tj51Tg017a#Gg00`TR0g00b@R1g01U4R2g00;\R3^80R4]3R5^90R6]5f0R7#0#=%67P1P6f1R6#0/F71E67P0P5f2R5#0?>67A<567P2P4f3R4#0P5P6P7C;P4!s0&:P0P3f4R8#0!s:'D7P8!s2+8P3^;0^71^20^:0^61^10R9f5R:#9P7P:P8P4%55R;%45R<P6O6f6!s<%P;P<P6F2533X09!s:&5%56%46P7F2,D3%0:R9#C%?:E@P9!tE,EA!sU'!s4$B533eX@0D1X?2D1X>0D1X=1D1X<0D1W4o"). Qed.
End FPX_42.

#[export] Hint Rewrite sub_itv_xB_eqf : bceq.
Section FPX_43. Context {fx : XPropExec.FPState}.

Lemma kdisj_apart_xB_eqf : ltac2:(zQ "90!se!hn8!hge!hr8!lc!jf!po4!pp4!lm2>2fk@1$1$3@3$5>2kn@1$1$3>2b1$0>2k1$2>2n1$0>2b2$0>2k2$2>2n2$0$4@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_43"] "##?up'0h02b1h12b2h22k1h32k2h42n1h52n2h61bh72knh82IHh91Kh:1ci001ch;2fkh<1ki011kh=1mi021mh>1ni031nh?4resti041ai052c1i062c2i071ei082hii092k0i0:2loi0;2m1i0<2m2i0=1vi0>1wp;1p;2p;3p;4p;5p;6p;7p;8p;;g00eTj1MTg02cgj10Tg04E[j1@j2Lj3Bj4>j5;j69j7Jj86Tg04G2j1<j2Cj3?j4=j5:j6Kj7Ij81Tg008]j34Tg00f4j1ATg0097j27Tg04C8j65j1ETg04DKj62j1DTg04HFj1FTg003Vj68!sb$Tj3GTg01Qcl;HTg002Tj53Tg017aR0#MR1P1g00`TR2g00b@R3g00;\R4^52R5^33R6^12R7^42R8]2R9]0f0R:#0#@%<:P2P9f1R9#0/L:1C9:P3P8f2R8#0?B9:A?89:P2P7f3R7#0P8P9P:C>P7!s0&=P2P6f4R6#0!s:'D;P6!s2+:P3P5f5R5#0!s<,E9P5!s4-KP2P4f6R;#0!s>/FJP;!s60IP0f>R<#0!s>1G6P<!s821544^52^33^12^42^23^02X71f=%A!t30G1,74X52X33X12X42X23X02f?!t6^P4f@R<f7R=!sS1P0P4f9R!v[%7P8!s+&4!s$%fER?#0R@f:RAP>f8RBP7P8E5P@P=!tE$9P:E5g00>4RCn010!s#$20000g00<<RD!sp'P@PAP>PB!sX%!sf+!st%!sa2PDP6!s81!sF27P8n011!s;$:3010410>10=2!s1%3!s9&31092010:108201071023!s-%!s9'41034010510;10610<!sb,0!sG'P0P4P>fDR@f;!u:$!u2%6G1REfCPA!s8,P7G1RFPEPFP!s+%!ut'?!ut&7P8E2P?!v\-2!ut6!s\3!sN%?!vR-!s\7?f<!sV&!sN$G1R?!vd@EPF!vd~!vd4RG544X64g01U4P4^=2]:^>2^<3^62RH%D<!w-%!vV$!v`56!v`,O5P6!v`,O5!v`>6!v`,!s\-!sj%!v`6!vN~!vNT=44GX6H!v3$BPFfBP>!y},P8G1RHPFPHP!s+%!|u,!xo%!y;%@!sV&!z#C!s\'!sN%@!t4,!s\8E!vE@FPH!vE~!vE4,74%0<RH#E%F<E8PHP!#5806!#5u0O6E8PHAG0B=RB!#6H3B!#6H3e!#7-4W8X?1X9!#701M;HX52D3X33D3X12D3X42D3X23D3X02D3X71D3W;o"). Qed.
End FPX_43.

#[export] Hint Rewrite kdisj_apart_xB_eqf : bceq.
Section FPX_44. Context {fx : XPropExec.FPState}.

Lemma end_hiB_eqf : ltac2:(zQ "90!hge!se!hn8!u6!jf!pq6!hr8!pqf!lm2>2fk@1$2$6@3$4>1b$1>1k$0>1n$1>3lo1$0>3hi1$0>2h1$0@1$3$0@1$7@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_44"] "##;Up'0h01ei001eh12fkh22h1h33hi1h41kh53lo1h61ni011nh71oh81xi021xh92x0h:2x1h;2x2h<2x3h=2x4i031ai042b0i053ehii061ii072k0i082loi092n0i0:2opi0;1pi0<2sxi0=1zp;1p;2p;3p;4p;5p;6p;7g00eTj1STg00hSR0j1:Tg02cgj12Tg04I]j1>j2Fj3Bj4?j5<j6Qj7LTg04Jmj1Rj2Cj3@j4=j5;j6Pj7MTg01:AR1j2NTg01Vgj13Tg01;oj1Ej27Tg00nJj1DTg01FXj20Tg01T9j26Tg01G5j25Tg00MQj18Tg00kNj2ATg008]j39Tg0097j2GTg01YDj1HTg01REj1ITg04L:j1JTg003Vj6KTg002Tj54Tg04MSj3OTg00=Hf1R2f0R33Op=1g017a#Sg00`TR4g00b@R5%:5R6^25R7^35R8^55R9^64R:]4%23#>%R3P5P:%22/F31C23P4P9f2R9#2?B23A@923P5P8f3R8#2P9P2P3C?P8!s0&=P5P7f4R7#2!s:'D<P7!s2+;P5P6f5R:#2!s<,EQP:!s4-P1N55R;#:^04R<f6R=#3#EP4P6P7%D5R>g00;\R?P6P?P?g01TVR@107='6108=/09g020<RA'5g00>4RBn010!s#$20000RCP0P;P6P2f7RD%8='1/1:REO1P1P5P5P6P31A53n200110;00012010=105R1P>n1011!sq$210!sF$P>!t01P!tj&f8RF,0=,6@10:F/07/5AP!t\3G!t\&8f9RH%8F'1/1DRI!t\$!t:FRJP!s$%!tB&10DH!t?$=H/0:!t?7J!t?&7f:RK%8H'1/1FRL!t?LMPMn011!s;$81!v7%1093010:103104!s1D4010<108109100!s4&7106109!xW%P>!uG$!wq&%3F/7EP!wCM!vs&%3K/7I!uNJIP!s$%?P6P!vB&f;#3/7L!sgJLPL!v7~9596X7<!v=$8!v=&!x^$8:!x^$9:/02!x^6!v$'D%8:,1=/17'7P!{,P10:D!t1$7D/08!t1>H%8D,1F/1=!t1KR>P!s$%IPI!vZ~9,G6%2=RI#H#I%J=EKPI!#3z-FLP=!s60M596eX=5D4X<5D4X;5D4X:4D4X95D4X84D4W1o"). Qed.
End FPX_44.

#[export] Hint Rewrite end_hiB_eqf : bceq.
Section FPX_45. Context {fx : XPropExec.FPState}.

Lemma ranges_apart_xB_eqf : ltac2:(zQ "90!se!hge!lc!hn8!jf!hr8!pra!lm2!psb>2fk@1$3$5@3$4>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_45"] "#$oKp'0h01bi001bh11oh22b1h32b2h41ei011eh52k1h62k2h72n1i022n1h82n2i032n2h92fkh:2h1i042h1h;3hi1i053hi1h<1ki061kh=2knh>1lh?3lo1i073lo1h@1ni081nhA3neghB3poshC1xi091xhD2x0hE2x1hF2x2hG2x3hH2x4i0:1ai0;2e1i0<2e2i0=2h2i0>3hi2i0?1ii0@2loi0A3lo2i0B2opi0C1pi0D2p0i0E2sxi0F2z1i0G2z2p%0p;1p;2p;3p;4p;5p;6p;7p;8g00eTj1sTg02cgj10Tg04N_j1Wj2rj3Zj4Sj5Oj6Mj7XTg04P7j1Pj2^j3Vj4Qj5Nj6qj7jTg03M<j1JTg04;>j7ij1`Tg01:AR0j2KTg02=ij2;j1dTg03Oaj2:j1[Tg01mEj2DTg04I]j7<j1hTg04E[j89j1]Tg03EWj2CTg04QLj1BTg00f4j1R!s/$Tj37Tg03XUj38j1aTg04<Tj7Gj1nTg02?=j26j1TTg03Pnj23j1pTg04Jmj74j1lTg04G2j8Aj1mTg03Yfj31j1oTg00hSR1j1HTg0097j2k!tQ$jj1eTg003Vj6@Tg04S>j1_Tg04TYj1\Tg03bdj1bTg03f`j1cTg03iBj1YTg04@Wj1fTg04Aej1gTg002Tj5ETg01FXj2FTg01T9j2ITg01SYj4LTg008]j3UTf4R2f3R3'Ff2R4'Ff1R5f0R6'F'Ip=51F56,I4p=2g00`TR7g00b@R8P5P6CLp==P7P8P5g01TVCL=7469723p=>g00;\R9?U56p=?g017a#sR:P7P9^87R;^68R<^37R=^77R>^58S00%06#W%P6P8P>%05/r61^56P7P=%04?Z56AV4!s6$<%03P4!tS$SP!s0'QP8P;%02!s7'DOP!s2,NP7P9f5R;#0!s<,EMP;!s4-qP:f6R<P7P9P2!s+$4f9R=#0R>f8R?f7R@%J5RAP;P2%J6RBFiRCP9P9P11K88RDP91;>?P0P8P8P9P6P1PDP9f<RE#0RF/;!sA18P9f?RG#0RH/:E!s7&@RI#0RJf:RK':!t&$;PGP5P3PED5P4PEP6P<PGD5'DS01g00<<RL!tR%!sf$ARM#0RNPIPGf>ROP<P;P5F<f=RP9262S02g00>4RQn10110900021010;00PL!sj%PNPPPEf;RR!v8$6F<A26@IS03P!s\3<00n010!s#$200!s43S04!sY4=00!s:4400n200110D00012010A10>S05!sQ4D!sQ+C!sQ'71!sN6C!uF$9P9P>P4P?P@!v$$2P3G9!s>%1C?;#BS06PQ!s5$K78RS1=;2RT%RSRU37RVPS1=?@RWPSP<PUD>RX58>PLA7SWU!s<$TPSP3!s@$T58>!v%A7!sE?!x0&DP9%0RRY/;K!y\3%0ORZ!s>38P91:NO!xj&BR[#0R\/:E!yO&M!yO$O!yO$O!yO$M!yO%8P!yJ/CR]#0R^P[PMPI!yH'A262GS09P!y@?^PGPOPP!y>/[S0:!y>U;!y>a<!y>fYP2PKP=!yB'!y>,K@#BS0=!y>&=@<R_=7SUR`PS1=K=RaPSP?!xs$b58Y!y5$aU!s<$_PSP;!s@$_58Y!ux?Rc!sD@dP!s$%!y<+1;FR!y831;HR!y45\G!s0'^P!y,&[!y,$G!y,$G!y,$[!y,%>!y,0DR^#0ReP]!y/$!y,-IS0?!y,@ePI!y/$!y,-]S0@!y,UA!y,aB!y,fFP;PR!y/,!y,,R?#BS0C!y,%PS1=RKRePSP=!x_$f98FW!xz$eURe=8FX!xO@g!sD@hPhn0110300081010G101083010B10:100!s1D4010E10@1!sg$!s4&610?108!#4'-?Rh/;@!yq5Y@!yq5ZR!s0'H=!yq&O!yq$R!yq$R!yq$O!yq%D!yq/PJ!#3>%!yk-ES0E!yk@JPE!wO$!yk-GS0F!ykUG!ykaH!ykfhP5!#:0+P4!yk,@2#BS0I!#3r&23RH=7SURZ=8h_PLPSPHPSP4!yy$H98h`!uaAJ!#9jJKRi/;=!#9j4P!s<3!x]$JP!s0'NR!xg&I!xg$P!xg$P!xg$I!xg%K!xg0\PM!~z$!xg-OS0L!xg@\!yA$E!xg/MS0M!xgSR\!xfaN!xffiP3!#9X+P2!xf,=<#BRN!xe'<;RJ!xe$jPS1==?RkPSP@!xc$l58iPLA7SkU!s<$JPSP2!s@$J58i!x|AO!v=@mP!s$%dPdn011!s<$81110F!#3sp!#H+,!v&&A!{n$BFGS0P!zS,16=?Rd!zQ316E?Rm!zQ43GES0Q!s3'IKS0!zW$Q01!z=0!z;%!#G<&4Q02!z8@M!z6$!#G,&4Q!#G$T!z1_!z-f=!z+/P3GA!s>%Q!#Ft&A1=VXPLA1=WT!y3@n!yb3S!sG2o!x#/RKRp!x#5OKRq!x#5MOS0T!s3'[ES0U!tp%!#Ey/!#?j%I!x#,!#En@]!#En/4Q!#EiT!x#~!x#GR!#?Z-P;!x#,=!x#'R`bPLA1Ra_!x#@r!x#3V!sG2sP!s$%!x,-ERRt!x,5GRRu!x,5[GS0W!s3']PS0X!tv%!#Dy/P^!#Ds/4Q!#DnA^!#Dn/4Q!#DiT!x,~!x,GE!#@:%!x/&!x,,C!x,'EWfPLA1Ee!#DF@^!x,3!#Jd1RvPv!#DI~!y,/?@Rv!y,5R@Rw!y,5ORS0Z!s3'G=S0[!uv%!#D50I!#D5/4Q!#D0AI!#D0/4Q!#D'T!y,~!y,G?!#73-P4!y,,I!y,'?Z_PLA1?`H!y,@x!y,3\!s73]!x$/K=Ry!x$5P=Rz!x$5IPS0^!s3'MRS0_!tq%!#CN0[!#CN/4Q!#CIA[!#CI/4Q!#CDT!x$~!x$GK!#74-P2!x$'PN!x#'KjlPLA1Kk!#HA?R{!wn3!#I71R|P!s$%sPs!#Bd~R}'?X>:%HD^47R~%T!#c|/PC!yT,P4P?O1!yT3P;P?O1Q!#`/i!#@309R>PLQ!#^n2!#_#3!tq-2PK!tq6@PKO1Q!#[bi!#<}09RYPLPc!tp3<!x;2cP!s$%!tx,;PR!tx6?PRO1Q!#WUi!#9p09RFPLPg!tx3B!tx2g!sI$!#9=~!ux'5P@!ux62P@O1Q!#Sbi!#6c09RhPLQ!#Ri2!#Rz3!tq-3P=!tq6<P=O1Q!#Omi!#3T09RiPLQ!#N^2!#No3RgP!s$%c!z9$!~{|/?}X1~%H8S0N!~}%p!~}=!#N`3P!#N\3P?PEO1!s2&=!}L%4!#7w~!wIAQ!#3P=!#K}3P!#Ky3PKPO!uD+RPEO1Q!#i5`!uDc!#3|D!#ID3P!#I@3PRPG!uL+EPPO1Q!#eT`!uLc!#4P~!#4P@!#Fc3P!#F_3P@PR!vL+?!~w%G!vL~!vLD!#4{<!#D#3P!#C{3P=PP!uD+K!uP$\!uC~!uCD!#5M~!#5MCg03T[R~P9^A~]BR~%o!#5R_Q!#]+&Q0R!#5L~!vuBRC!#BK'!#[H0P4PVPXO2PLP4PWPTO2!#F>>!#guH!#6DFQ!#[;&Q0U!#6>~!v6CT!#Ch'!#YW0P2P`Pb!v6$2PaP_!v6]RaP!s$%!#76OQ!#YL&Q0X!#70~!v>Cb!#E-'!#Wh0P;PWPf!v>$;PePX!v>^XPX!#8$~!#8$PQ!#W]&Q0[!#7z~!w>CX!#FL'!#Uy0P5PZP_!w>$5P`PH!}fh!#8rEQ!#Uk&Q0_!#8l~!v5B\!#Gh'!#T-/P3PjPl!v4$3PkPJ!zL^kP!s$%aPa!#9c~/?}X0~P9^88^68^37^78^58^27R~%n!#9i04!#p4-O6!ug$!#7v-n!xUD!#5<-r!uu@YP!s$%9P9P!~Z/^!s\@FPF!}y~!}y%!{x/x!uhD!y?/{!u2@iP!s$%YPY!x_~!x_&Q00^27^=:R:%m!xT0Q!#uR%!xG'4!#Xd0O7!xWP2!#WW0!sd$!xgArP!s$%!xg/;!#VK0!sl$!xwA^!sF$!xw~!xw-5!#U?0!tl$!y/M3!#T20!sd$!y?A{P!s$%r!vh$!y?~}X0:Q0N^:8^;8^?8^@7^<8^07R:%l!yK8!#EeW!#{g6K!#{g-O6!#{gBK!#{g-O6!#{g~!#K-uS!#F?j!#zP6E!#zP-O6!#zPBE!#zP-O6!#zP~!vhv!#yK2qP!s$%!#Fq[!#y;6P!#y;-O6!#y;BP!#y;-O6!#y;~!vpv!#x62[P[!#6W~!#GK\!#w~6=!#w~-O6!#w~B=!#w~-O6!#w~~!wpv\!#G}k!#vf5R!#vf-O6!#vfBR!#vf-O6!#vf~!vhv!#ub2IP!s$%qPq!#<_~/?}X1:P7P9P3!s+$!#??&AP2P3PBFGQ0]P!#w?2!}?~!#}7&@<!#}K4K<!#}I4PK!s0'O?!#C>%PP5P3PKD5P4PKP6P<PPD5'!}\1!}Z%E!#}Z&A262R!yt@G!#D;%!#}\%A26@O!yv~0!#}^u@!#D`-P5!#}^&1C<3#B!$Au&34RQ=7SU=1@JPLPSPQPSP5PUD>91@j!#Sv[o!s$&|P|!{5~8,k9%0<R9#h%e<E@%]9%_<E@%`9%\<E@%a9%b<E@%[9%c<E@%d9%Y<E@%f9%g<E@!yU$!$cZ'FX!vM/P6Fj'?eXH7DEXG8DEXF7DEXE7DEXD8DEXC7DEW9o"). Qed.
End FPX_45.

#[export] Hint Rewrite ranges_apart_xB_eqf : bceq.
Section FPX_46. Context {fx : XPropExec.FPState}.

Lemma disj_sidesB_eqf : ltac2:(zQ "a0!hn8!hge!se!hr8!hu2!jf!pte!mq2!pub!lm2>2fk@1$0$3@3$5>2kn@1$0$3>2b1$2>2k1$1>2n1$1@1$0@2$4$7$2@1$8@1$9^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_46"] "##:=p'0h02b1h12k1h22n1h31bh42knh52IHh61Kh71ci001ch82fkh91ki011kh:1lh;1mi021mh<1ni031nh=4resti041ai052c1i062c2i071ei082hii092k0i0:2loi0;2m1i0<2m2i0=1vi0>1wp;1p;2p;3p;4p;5p;6p;8g00eTj1;Tg01:Aj2ITg02cgj11Tg04V3j1=j2Fj3Aj4>j56Tg04WGj1Hj2Dj3?j4<j50Tg008]j33Tg00f4j1GTg0097j2:Tg0415j69j1BTg01SYj48!sM$Tj32Tg042Fj65j1CTg049ij1@Tg003Vj67Tg01Qcj8ETg002Tj54Tg017aR0#;R1P1g00`TR2g00b@R3g01U4R4/I2R5#;R6^23R7]1R8]0f0R9#1#=%H9P2P8f1R8#1/F91D89P3P7f2R7#1?A89A?7!s9$6f3R:#1P7P8P9C>P:!s0&<P0f8R;#1!s8'D6P;!s2+0536^23^13^02X41f7R<%G0!sD',:6X23X13X02f9R=!sl0=!sl9P6f:R>f4R?!sD'P0P6f6R@!sV$:P7!s+%g00;\RAP6f?RB#1RCP<P@f5RDP:P7E9P4P2!u7$8REPAP6P!sF$PDP8P9!sD&:P7C8RC=25?P?n010!s#$20000RF525PF!s;1P:P7n011!s;$:3010410>10=2!s1%3!s9&31092010:108201071023!s-%!s9'41034010510;10610<!sb,0!sG'P0P6P@f>RFP;!u1$?D0R;f=P<PDP?P:D0RGP;PGP!s+%AP6PB!u[&:P7E5!s808P9E5PBP=!s6%D0R=925CRBP=!uq2H925EPH!ur2;PG!ur~!ur4RH536X:6PA^;2^74^<3^93^32R4%C>!v8%!ul$!uv1?!uv,O5!s808P9O!uv$!ud2=!ud$=!ud~!udF=36HX34!uM$DPGf<P@P?P:P7D0R4PGP4P!s+%AP6PF!xy%!xQ-!s8'!xQ$A25C;P;!u\2;!u\$!s<2PGP4!u\~!u\4,:6%1>R4#B%@>E7P4P!~A'6!~i'O3E7P4A20D?RD!sC+>PD!#30,e!#3Y'W5X=1X60!sd'GEX23D4X13D4X02D4X41D4W8o"). Qed.
End FPX_46.

#[export] Hint Rewrite disj_sidesB_eqf : bceq.
Section FPX_47. Context {fx : XPropExec.FPState}.

Lemma disj_sides_xB_eqf : ltac2:(zQ "a0!hn8!se!hr8!hu2!jf!hge!pva!mq2!qg9!lm2>2fk@1$0$2@3$4>2kn@1$0$2>2b1$1>2k1$5>2n1$1@1$0@2$3$7$1@1$8@1$9^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_47"] "##:=p'0h02b1h12k1h22n1h31bh42knh52IHh61Kh71ci001ch82fkh91ki011kh:1lh;1mi021mh<1ni031nh=4resti041ai052c1i062c2i071ei082hii092k0i0:2loi0;2m1i0<2m2i0=1vi0>1wp;1p;2p;3p;4p;5p;6p;8g00eTj1;Tg01:Aj2ITg02cgj11Tg04XXj1=j2Fj3Aj4>j56Tg04Ynj1Hj2Dj3?j4<j50Tg008]j33Tg00f4j1GTg0097j2:Tg04C8j69j1BTg01SYj48!sM$Tj32Tg04DKj65j1CTg04HFj1@Tg003Vj67Tg01Qcj8ETg002Tj54Tg017aR0#;R1P1g00`TR2g00b@R3g01U4R4/I2R5#;R6^22R7]1R8]0f0R9#1#=%H9P2P8f1R8#1/F91D89P3P7f2R7#1?A89A?789P2P6f3R:#1P7P8P9C>P:!s0&<P0f8R;#1!s8'D6P;!s2+0536^22^13^02X41f7R<%G0!sD',:6X22X13X02f9R=!sl0=!sl9P6f:R>f4R?!sD'P0P6f6R@!sV$:P7!s+%g00;\RAP6f?RB#1RCP<P@f5RDP:P7E9P4P2!u7$8REPAP6P!sF$PDP8P9!sD&:P7C8RC=25?P?n010!s#$20000RF525PF!s;1P:P7n011!s;$:3010410>10=2!s1%3!s9&31092010:108201071023!s-%!s9'41034010510;10610<!sb,0!sG'P0P6P@f>RFP;!u1$?D0R;f=P<PDP?P:D0RGP;PGP!s+%AP6PB!u[&:P7E5!s808P9E5PBP=!s6%D0R=925CRBP=!uq2H925EPH!ur2;PG!ur~!ur4RH536X:6PA^;2^74^<2^93^32R4%C>!v8%!ul$!uv1?!uv,O5!s808P9O!uv$!ud2=!ud$=!ud~!udF=36HX34!uM$DPGf<P@P?P:P7D0R4PGP4P!s+%AP6PF!xy%!xQ-!s8'!xQ$A25C;P;!u\2;!u\$!s<2PGP4!u\~!u\4,:6%1>R4#B%@>E7P4P!~A'6!~i'O3E7P4A20D?RD!sC+>PD!#30,e!#3Y'W5X=1X60!sd'GEX22D4X13D4X02D4X41D4W8o"). Qed.
End FPX_47.

#[export] Hint Rewrite disj_sides_xB_eqf : bceq.
Section FPX_48. Context {fx : XPropExec.FPState}.

Lemma in_sidesB_eqf : ltac2:(zQ "b0!hn8!hge!se!lc!hu2!jf!qha!hr8!mq2!qi5!lm2>2fk@1$0$7@3$5>1D@1$0@2$4$8$2>2b2$2>2k2$1>2n2$1$3@1$9@1$a^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_48"] "##2Rp'0h02b2h12k2h22n2h31bh41Dh51ch61mh72IHh81ah92fkh:1kh;1lh<1nh=4resti001ei011pi021sp;1p;2p;3p;4p;5p;6p;8g00eTj19Tg01:AR0j2JTg02cgj10Tg04[Aj1;j2Fj3?j4<j53Tg04\Sj1Ij2Cj3=j4:j51Tg00f4j1HTg0097j28!s8$Tj37Tg0415j6Ej1@Tg042Fj66j1BTg049ij1ATg003Vj65Tg01SYj4>Tg01Qcj8DTg002Tj54Tg008]j3GTg00;\R1f1R2f0R33Gp=2g017a#9g01U4R4g00`TR5'JR6#9R7g00b@R8P1^28R9]1R:^05%03#;%I3P5P:%02/F31C23P8P9f2R9#0??23A=9!s9$1f3R:#0P9P2P3C<P:!s0&:P6f8R;#0!s8'D3P;!s2+1'2^28^18^05X47f7R;%H6!sC',81X28X18X05P0P4P5f:R0!sq00!sq8f;R0#0f5R<f4R=576R>!sX->!sX6[^;7P3f=R>!t,0>!t,8P1f>R>P=!sA'R0P1P1f?R?!sc+;f6R@EEg00<<RAP3n010!s#$2000!sU$P?!sQ'P@E6PAP?P!vT&D1R?!sV1RB'2X31P1^65^54^<8^:8^35RC%B>!ss$3!ss,O5PAP!sg2/2BX3C!sP$!ut&P@P<!tE$0!sP1,81%0>R1#@%A>E5P1!u]+!t1'3O3!s>$4P5P@P<C>=76=R!sL,!v7-'2e!x/+W7X=7X65X54!sk$2n20011!tK$120102100X86!t4'GDX28D4X18D4X05D4X47D4W9o"). Qed.
End FPX_48.

#[export] Hint Rewrite in_sidesB_eqf : bceq.
Section FPX_49. Context {fx : XPropExec.FPState}.

Lemma in_sides_xB_eqf : ltac2:(zQ "b0!se!hn8!lc!hu2!jf!hge!qj2!hr8!mq2!qjf!lm2>2fk@1$1$7@3$4>1D@1$1@2$3$8$0>2b2$0>2k2$5>2n2$0$2@1$9@1$a^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_49"] "##2Rp'0h02b2h12k2h22n2h31bh41Dh51ch61mh72IHh81ah92fkh:1kh;1lh<1nh=4resti001ei011pi021sp;1p;2p;3p;4p;5p;6p;8g00eTj19Tg01:AR0j2JTg02cgj10Tg04]bj1;j2Fj3?j4<j53Tg04_6j1Ij2Cj3=j4:j51Tg00f4j1HTg0097j28!s8$Tj37Tg04C8j6Ej1@Tg04DKj66j1BTg04HFj1ATg003Vj65Tg01SYj4>Tg01Qcj8DTg002Tj54Tg008]j3GTg00;\R1f1R2f0R33Gp=2g017a#9g01U4R4g00`TR5'JR6#9R7g00b@R8P1^25R9]1R:^05%03#;%I3P5P:%02/F31C23P8P9f2R9#0??23A=923P5P1f3R:#0P9P2P3C<P:!s0&:P6f8R;#0!s8'D3P;!s2+1'2^25^18^05X47f7R;%H6!sC',81X25X18X05P0P4P5f:R0!sq00!sq8f;R0#0f5R<f4R=576R>!sX->!sX6[^;7P3f=R>!t,0>!t,8P1f>R>P=!sA'R0P1P1f?R?!sc+;f6R@EEg00<<RAP3n010!s#$2000!sU$P?!sQ'P@E6PAP?P!vT&D1R?!sV1RB'2X31P1^65^54^<5^:8^35RC%B>!ss$3!ss,O5PAP!sg2/2BX3C!sP$!ut&P@P<!tE$0!sP1,81%0>R1#@%A>E5P1!u]+!t1'3O3!s>$4P5P@P<C>=76=R!sL,!v7-'2e!x/+W7X=7X65X54!sk$2n20011!tK$120102100X86!t4'GDX25D4X18D4X05D4X47D4W9o"). Qed.
End FPX_49.

#[export] Hint Rewrite in_sides_xB_eqf : bceq.
Section FPX_50. Context {fx : XPropExec.FPState}.

Lemma mk_sprepB_eqf : ltac2:(zQ "90!se!hn8!jf!hge!hr8!qke!nj2!ql9!lm2>2fk@1$1$4@3$2>2b1$0>2k1$3>2n1$0$6@1$7@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_50"] "##7zp'0h02k1h11lh22n1i002n1h32b1h41ei011eh52knh61oh72fkh81xh92x0h:2x1i021ai031bi041ii051ki062loi071ni082opi092sxi0:2z1p;1p;2p;3p;5p;4p;6g00eTj1=Tg02cgj11Tg04`Gj1Mj2Yj3Uj4STg04aYj1Aj2Vj3Lj4TTg02=ij2Cj1PTg03Oaj2Bj1NTg01:Aj2;Tg03M<j1?Tg04V3j56j1JTg00f4j1XTg04XXj5<j1GTg04bhj40Tg02?=j2:j1KTg03Pnj28j1ITg04WGj55j1DTg04Ynj59j1ETg00hSj17Tg0097j2FTg04d6j1HTg003Vj63Tg04ePj1@Tg03f`j1OTg03iBj1QTg04@Wj1RTg04Aej1>Tg002Tj54Tg008]j3WTg04fhR0f1R1f0R23Wp=2g017a#=R3g00`TR4g00b@R5P0^24R6]0%12#M%A2P5P6%11/Y21V12P4P0f2R6#1?U12AL612P3f3R7f4R8#1R9/C71B91R:P4g01U4/;4R;#=R<P1f5R=#1R>P1P8P7%?2R?D6%X;R;P!s$-n0110000081010:1010730108102103!s1D40109106107101!s4&5104107P9P2P7P6P1D<C01:87R@1881RAP4P<P1P=P=P8P7P?D5P!td~!td1RBP8!tD$6P1D9C0RC'2X131;55#7^44RD%K7P2P7O1P:!tw&>!tw+6!tw~!tw3>P9!tw+<R9C0/2CX6D%75!tu%I7P@P2P1O1P>P!sE+P<^25^05^34^53RD%D7P@P!w9'1!u@'O4!u@~!xw4!tk%1!tk$4!tk,3%E!tk%BP2!ua'O4!sS&31:761872!u1$2!w|+!yD~!u167!td%P2D9C0,F0%17R0#G%H7E3%J0%@7E3%N0%O7E3%P0%Q7E3%R0%>7E3P0!sa%CS!sk'CT'2eX:4D4X95D4X84D4W7o"). Qed.
End FPX_50.

#[export] Hint Rewrite mk_sprepB_eqf : bceq.
Section FPX_51. Context {fx : XPropExec.FPState}.

Lemma ranges_apart_pB_eqf : ltac2:(zQ "a0!se!hge!lc!hn8!jf!hr8!qm6!nj2!lm2!qn7>2fk@1$3$5@3$4>2sp$7>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2@1$9@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_51"] "#$t^p'0h01bi001bh11oh21Dh32b1h42b2h51ei011eh62k1h72k2h82n1i022n1h92n2i032n2h:2fkh;2h1i042h1h<3hi1i053hi1h=1ki061kh>3lo1i073lo1h?1ni081nh@3neghA3poshB1xi091xhC2x0hD2x1hE2x2hF2x3hG2x4hH2x5i0:1ai0;2e1i0<2e2i0=2h2i0>3hi2i0?1ii0@2loi0A3lo2i0B2opi0C1pi0D2p0i0E2sxi0F2z1i0G2z2p%0p;1p;2p;3p;4p;5p;6p;7p;8g00eTj1PTg02cgj11Tg04h6j1^j2|j3bj4Yj5Uj6Sj7zj8rTg04iNj1Vj2vj3]j4Wj5Tj6{j7yj8sTg01:AR0j2KTg00hSR1j1LTg02?=j1fj2FTg04jcj1DTg01FXj20Tg03M<j1JTg04l0j1MTg04[Aj5Zj1aTg03C4j7Xj1\Tg04m;j1@Tg03Oaj2Ij1mTg04I]j77j1`Tg01T9j2HTg04nGj1?Tg04]bj5Gj1cTg03EWj2>Tg04QLj1ETg00f4j1R!s/$Tj34Tg03XUj35j1jTg04\Sj5Qj1kTg03DGj7Oj1uTg03Pnj2Aj1tTg04Jmj72j1lTg04_6j5Bj1hTg03Yfj33j1qTg0097j2eTg04oSj1dTg003Vj6<Tg050kj1g!ta$jj1iTg03bdj1_Tg03f`j1nTg04?@j1oTg02=ij1pTg03iBj1[Tg002Tj5=Tg01mEj2wTg01SYj4NTg008]j3xTf5R2f4R3'Hf3R4f2R5'0f1R6'0f0R7'H'wp=:1056/07p=C1067,H5p=6g00`TR8g00b@R9P6P7CNp=8P8P9P6g01TVCN=4579434p=9g00;\R:?x67p=;g017a#Pg04fhS00P:^98R;^79R<^48S01^88R=^69R>^38%17#^%V7Q00P8P>%16/|71v67P9P=%15?b67A]567P8Q01%14P5!t^$YP!s0'WP8P<%13!s7'DUP!s2,TP9P;%12!s9,ESP!s4/{P8P:f6R;#1!s>/FzP;!s60y1K99R<#L^58R=f7R>#fP8P:P3!s+$5P:P:P1P<P:f9R?#DR@P0P9P9P:P7!s>%P2f8RAO1RB!s@,f=RC,04RD%J>S02'0f:RE,06P7PE%J;S03103CRFE:n200110D00012010A10>RGg00>4RHn101109000210!sK$!sU&C!sU'7105P!sN3C00g00<<RIP:P:%1ERJ%M?S04P2P3%J7RKDZS05PIPJPAP>%J6RL!v3$KFXn010!s#$20000!s41!v&,P!u|5B!s809P:f?RB#@RM!s4&ARN#1RO/IEP:P:AC2B6f<RP,04S06P5PPP710;BE:S07PI!t9&9P:fBRQ#1RRf@RSPBf>RT!x0$6F71H7FS08!uu4;00PI!sc%PRPCPPf;RF!x_$7F7A67>SS09!s\4<!ud3!s41S0:!sY4=00!s:44!wj+!xA0S0;P!x=^!v/&J%??S0<!{#%DGS0=!s?%1>A2#ES0>PH!s5$K89RU1823RV%RURW34RXPU18A>RYPUP;PWD9RZ55JPIA4UYW!s<$VPUP4!s@$V55J!v&?!v83?!y=;%DFRJ!y@4>PEO1!yD3%@NR[!x`&CR\#1R]/IP!yA&N6104TP5PT!y;$NE:S0@!y;0DR^#1R_PQPNPS!y7'A673BS0A!y8@_PBPTPC!y6/QS0B!y6UC!y6_R`!y5e%1PRa%?FS0DP>P;P2DGS0E!y8'E>#ES0F!y8&8>;Rb=4UWRcPU18E?RdPUPA!xm$e55a!y/$dW!s<$bPUP2!s@$b55a!y/OG!s71RaP!s$%!y7-PRf!y74APF!y77QRg!s1%1I_C!y0&Q6104BP5PB!y0$QE:S0H!y00ER_#1RhP\!y2$!y0-SS0I!y0@hPS!y2$!y0-\S0J!y0UK!y0`h!y0gCRi%?PS0LPAP>P;DGS0M!y0'FA#ES0N!y0%PU18FERjPUP?!xb$k95iY!x}$jWRj=5iZ!xpMRi!s62lPln0110300081010G101083010B10:100!s1D4010E10@1!sg$!s4&610?108!yo/ARl!yo43P>!yo7TRm!s1&1S/I?!yq&T6104FP5PF!yq$TE:S0O!yq/PO!#3A%!yk&103PS0P,H7S0Q!yp@OPPPFPE!yp/BS0R!ypUS!#:2`T!yqg?RO%?AS0!#B}%DGS0V!yq'>3#ES0W!#3{&34Rn=4UWRo=5ObPIPUPnPUP5!z#$n95Oc!yrNO!#9l<ERp!xj4;P?!xj7SRq!#3[&RF!xh&S6PDP5PC!xf$SE:S0X!xf0]PN!~y$!#3S,TS0Y!xa@]!y@$P!xa/NS0Z!xaU[!xaa\!xagFR]%?ES0]!uy$3DGS0^!xa'?;#ES0_!xa';2RD!xa$RPU18?ARrPUP>!x_$s55]PIA4UrW!s<$DPUP3!s@$D55]!xxN!sR2RtP!s$%aPan011!s<$81110F!#3tp!#JE7!#GA41FCARaPG!w@_RG!z@&EQ!#I=$PKDQPIPEPAP>P!#I4&OS0`!yTAa!tw?Pa!|-3P!#I4%1ANERtP:P:Q!#Hl0PQ!#;k%!{r%2Q!#H^AQ!{k$!#H\&2Q!#HWT!{e_!wH_S0b!wI,!#HQ&B!s9%Q!#HH&A3EXZPIA3EYV!wOA!#5@?Ru!wm-J!yf5BERv!wq4[!wq'\PRw!td%!#GJ/P^!#GD/2Q!#G?A^!#G?/2Q!#G:T!wq~!wqBd!uo&PQ!#G2'!wq+F!wq'PcePIA3Pdb!wqAe!wq@xP!s$%!ww,f!ww5SFRy!ww4!#FL&A^CR^!tj%!#F9/P_!#F3/2Q!#F-A_!#F-/2Q!#F%T!ww~!wwBf!uo&CQ!#Ey'!ww+N!ww'CYkPIA3CjZ!wwAg!ww@_P_!#EZ~!xw-l!xw5P>R_!xw4m!xw'S?Rz!uj%!#E?0N!#E?/2Q!#E5AN!#E5/2Q!#E0T!xw~!xwBh!uo&?Q!#E#'!xw+W!xw'?obPIA3?cn!xwAi!sEAj!wr-p!wr5T?R{!wr4!#D\&AQFR|!te%!#DK0\!#DK/2Q!#DFA\!#DF/2Q!#DAT!wr~!wrBk!uo&FQ!#D8'!wr+_!wr'FRsPIA3FrD!wSAl!}k@}P!s$%xPx!#CY~R~';X1=P:^99^79^48S0m^89^69^38R=%u>!#C|3G!ui'5PIP5!#Bn-O6!#d|[aQ!#agbQ!#_}<!#?94PvP`!t=c!#[32`P!s$%!#;_=PyP!#X+b!~A2RhPh!#8+~!#8+>P_Q!#SXc!#R3;!#4O4P{Q!#O4c]!v\5!s$$`P`!|u~8/;~X0=%L9S0\^58R=%t!|fAQ!#LF@R`!#LEXP?PEO1Q!#lI`!}]~!}]6!#Il9PFPPO1Q!#hS`!~`s!yd'!~`A!#G=9PPPCO1Q!#dk`!#3cqi!s8$!#3c~!#3c=!#De:PAP?O1Q!#aB`!#4e~!u?2!#B2;PEPFO1Q!#]x`!#5gq]P!s$%!#9M&!#5g}1=g03T[R=P:^@=]AR=%q!#5l0!#5<Zt!#58~!#aiGQ!#zH&!#Xx'P5PXPZO2PIP5PYPVO2!#a#L!#6/gw!#6'~!v3JE!#W:1P3PcPe!v3$3PdPb!v3]RdP!s$%!#6zX^!#6v~!v;JM!#UV1P2PYPk!v;$2PjPZ!v;^ZPZ!#7n~!#7nYz!#7j~!w;JV!#Sr1P6PoPb!w;$6PcPn!}]h!#8bN|!#8^~!v3J^!#R31P4PRPs!v3$4PrPD!zH^rP!s$%dPd!#9V~!#H?$Q0\^;9^<9^>9^?8^=9^08R=%l!#9]i!#m66E!#m6-O6!#m6BE!#m6-O6!#m6~!#;/|Q!#lL2Rt!#:Qh!#lD6P!#lD-O6!#lDBP!#lD-O6!#lD~!#;{|Q!#kZ2Rw!s62[P!s$%!#;EY!#kT6C!#kT-O6!#kTBC!#kT-O6!#kT~!#<o|Q!#jj2RQ!s62\P\!#<9~!#<9Z!#jd6?!#jd-O6!#jdB?!#jd-O6!#jd~!#=c|Q!#iz2Rz!#=,h!#iq6F!#iq-O6!#iqBF!#iq-O6!#iq~!#>W|Q!#i/2RN!s62|P!s$%[P[!#=y~!#PQ&1U4/K8#PR=Q0m]2R[%k!#_B;P5!$+|'O4!#_LC!uj%bPIPt!s?7dPIP!#7,2wP!s$%!sG$fPIP!#3E2Q!s8$!#3E~:Q0hPIP!{]6Q0kPIP!wu3NP!s$%w!uC$!wu~~X0[Q01^2=R=%h!wj0Q!$0v$Q!$,I'5!$,I'!wn%c!wnE!$%9&3!$%9'!sa%!$$\@!#;~,Q!#}''2!#}''!si%!#|N@!vW'!xA~Q!#xu'6!#xu'!ti%i!v7E!#td&4!#td'!sa%l!uLC!s$$!}|~!y,+=!xt$4!s+$6!#;HJQ06Q02'0106?P7P?Q03Q0P!$[g8!#5RdP?%MA!w?$!$9>$?!yy$L!s8%FO!vi?Q0jP!#wu2!yB~!$CZ&>!#}w4F;!$CV4C!#}v&BAP!$CT$C6104EP5PEP710;CE:!#;;/S!#:d%!#~-%A673F!#;=?SPFPEP?!#~0&A67>T!#;?~!xkvA%?>!u6$6!#~/&1>;4#E!$C;&45RH=4UW=3ADPIPUPHPUP6PWD993AR!#V@[u!s$&}P}!}:~8,e:%1>R:#c%d>E<%a:%g>E<%`:%i>E<%j:%_>E<%m:%n>E<%\:%o>E<%p:%[>E!$JJ$!$gI,Gr!|&$!s8/s';eXH8D=XG9D=XF8D=XE8D=XD9D=XC8D=WBD=W:o"). Qed.
End FPX_51.

#[export] Hint Rewrite ranges_apart_pB_eqf : bceq.
Section FPX_52. Context {fx : XPropExec.FPState}.


(* [comment removed for export] *)
Fixpoint coeffs_divkB (bc : bctx) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0) && coeffs_divkB bc m rest)%bool
  end.

Definition lin_lowbits_knB : ltac2:(zQ "40!hge!u6!se!irb>2bc$3>1e$2>1k$0@1$1$0") := ltac2:(zQ "h00!hge!se!qoa!lc!hn8!hu2!jj6!uf!u6!jpf!jq5!jqb!qp1!quc!irb!jm4\2bc$e\1e$1\1k$0=1l$a@1$b^2M3\0$3@1$8$0@3$d^4@2$2+2^2@3$9$0@1$4@2$5$0$1^1@2$6$0@2$f@3$7$0@1$4@2$5$0$1^1@2$2+2^2@2$c^3@2$2+2^2").

Definition lin_nowrap_lB : ltac2:(zQ "60!hge!lc!hn8!hu2!se!irb>2bc$5>1c$0>2ts@1$2@2$3$0$4$1") := ltac2:(zQ "e0!hge!hu2!lc!u6!jp8!ige!hn8!se!jr4!jk4!irb!kj6!js0!js7\2bc$a\1c$0\2ts@1$6@2$1$0$7M3\1x@1$3@2$1$0$0$2@3$8@1$b^3^2^1\1p@2$1$0$0M1\1p@2$1$0$0$2^1\2lo$0\2hi$0@2$4@2$cZ^2@2$d^1$9$5").

Definition mkSrlB : ltac2:(zQ "30!se!hge!irb>2bc$2>1a$0>1s$1$0") := ltac2:(zQ "he1!hge!hu2!se!hn8!lc!jjd!qvc!mrb!mv5!rg5!jp8!uf!u6!jpf!rgc!ng8!kvd!rh4!ri1!kne!mib!rif!jq5!jqb!rjc!rka!irb!kj6!mn5!qoa&@2$1@1$3@2$1$0$2@1$3@2$1$0$2\2bc$ha\1a$2\1s$0=1l$h6@1$h7^2=1m$0@2$hd+2^2M4\0$4$2@2$a@2$a@1$f@1$h2^2@2$h5^1@3$d$0@1$3@2$1$0$2^2@2$h3^5^4@1$e@4$5$0@1$3@2$1$0$2@2$9@3$b$0@1$3@2$1$0$2^2^1@2$h1^1@3$d$0@1$3@2$1$0$2^2M1\1x~0$2M4\0$4~0@2$a@1$f@1$h2^2@2$h3^5^4@2$h8^1@3$d$0@1$3@2$1$0$2^2@4$5@1$3@2$1$0$2@1$3@2$1$0$2@1$h0@2$1$0$2@1$h0@2$1$0$2\3dts@1$3@2$1$0$2\3rts@1$3@2$1$0$2M3\3dts@1$3@2$1$0$2$2^2@3$8$6^6@1$7^5\1p@2$1$0$2\2l0@1$3@2$1$0$2M3\3rts@1$3@2$1$0$2$2^3@3$8$6^8@1$7^7\2p0@2$1$0$2\2l1@1$3@2$1$0$2Mc\1x@1$c@2$1$0$0$2M4\0$4@1$c@2$1$0$0@3$h9^b@3$b$0@1$3@2$1$0$2^8^5@2$hb^b@1$e@4$5$0@1$3@2$1$0$2@3$b$0@1$3@2$1$0$2^8^5@1$h4@2$1$0$0\1p@2$1$0$0M1\1p@2$1$0$0$2^1\2lo$0\2hi$0M4\0$4$2@2$hc@2$9^2^a@2$9^1^a@1$e@4$5$0@1$3@2$1$0$2@2$9^2^a@2$h1^a^9@3$8$6^d@1$7^c@3$8$6^a@1$7^9").

Fixpoint lowbitsB (bc : bctx) (e : expr) (j : Z) {struct e} : option Z :=
  let m := (2 ^ j)%Z in
  let dflt := if Z.leb j (ealignB bc e) then Some 0%Z else lin_lowbits_knB bc e j in
  match e with
  | ELit z => Some ((z mod two64) mod m)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some (Z.land v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbitsB bc a j with Some v => Some (Z.lxor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_ADD a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
  | EAlu ALU_SUB a b =>
      match lowbitsB bc a j, lowbitsB bc b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbitsB bc a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
  | _ => dflt
  end.

Fixpoint lsplit_divB (bc : bctx) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divB bc m rest in
      if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealignB bc a) mod m) 0)%bool then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

Definition and_high_splitB : ltac2:(zQ "50!hge!se!hn8!hu2!irb>2bc$4>2bk$1>1j$0>1c$0>3dts@1$2@2$3$0$1>3rts@1$2@2$3$0$1$1") := ltac2:(zQ "h40!hge!se!hu2!hn8!jjd!mv5!rgc!rg5!lc!u6!muc!rlb!jm4!irb!kj6!jse!mn5!rm4!qoa!lu5\2bc$d\2bk$1\1j$0\1c$0\3dts@1$3@2$2$0$1\3rts@1$3@2$2$0$1=1m$0@2$h2+2^4=2cA$0@2$h3^4@2$c^4^1=1r$1@1$6@4$4$0@1$3@2$2$0$1@2$c^5^2^3M9\1x@1$9@2$2$0$0$1@2$e^9^1\1p@2$2$0$0M2\1p@2$2$0$0$1^1\2lo$0\2hi$0M8\0$8$1@2$h0@2$7^2^6@2$7^1^6@1$6@4$4$0@1$3@2$2$0$1@2$f^5@2$h1@2$7^2^6^6^8@3$5$a@1$6@4$4$0@1$3@2$2$0$1^5^8@3$5$b^4^b@3$5$a@1$6@4$4$0@1$3@2$2$0$1^2^5@3$5$b^1^8").

Definition and_low_splitB : ltac2:(zQ "50!hge!se!hn8!hu2!irb>2bc$4>2bk$1>1j$0>1c$0>3rts@1$2@2$3$0$1$1") := ltac2:(zQ "h20!hge!se!hu2!hn8!rg5!lc!u6!jjd!rlb!mv5!rgc!jm4!irb!kj6!mn5!rm4!qoa!lu5\2bc$c\2bk$1\1j$0\1c$0\3rts@1$3@2$2$0$1=1m$0@2$h0+2^3=1r$1@1$a@4$7$0@1$3@2$2$0$1@2$b^3^1^2M6\1x@1$6@2$2$0$0$1@2$d^7^1\1p@2$2$0$0M2\1p@2$2$0$0$1^1\2lo$0\2hi$0M5\0$5$1@2$e@2$4^2^5@2$4^1^5@1$a@4$7$0@1$3@2$2$0$1@2$h1@2$b^7^5@2$f@2$4^2^5^5^6@3$9$8^4^9@3$9$8^1^6").

Definition narrow_maskB : ltac2:(zQ "40!hge!u6!se!irb>2bc$3>1a$2>2k'$0@1$1$0") := ltac2:(zQ "h10!hge!u6!lc!qoa!mib!js7!jp8!jj6!rmb!se!jk4!irb!om5!jse!mn5!rn3!lu5\2bc$b\1a$9\2k'$0=1i$0@1$8^1=1m$0@2$d^2@2$3+2^1=1j$0@1$f^1M2\0$2@1$1$0@2$6@2$6@2$5Z^4@2$e^2@2$3+2^1@2$5^1+k0M1\1x@1$1$0@1$1$0@2$c^6^5\1h$0M2\0$2@1$1$0@2$5^1@2$3+2^2@2$7$0@2$h0$a@2$3+2^4@1$4$0@1$4$0@1$4$0").

Definition mkAnd0B : ltac2:(zQ "20!se!irb>2bc$1>1a$0>1b$0$0") := ltac2:(zQ "ib4!se!hge!hu2!hn8!lc!rlb!mv5!qoa!u6!mrb!jp8!u0!jpf!jqb!uf!ri1!jk4!jse!js0!rn3!js7!lu5!ng8!jjd!rnb!i4!rb!ro2!ro9!rpc!rqb!km6!mn5!jm4!kvd!jq5!rgc!rr5!rs8!quc!rta!irb!ru6&@2$2@1$3@2$2$1$0@1$3@2$2$1$0&\1x~0$0&\2op$h9\2a0$0\2b0$0@3$6$5^5^4&\2op$ha\2a0$0\2b0$0@3$6$5^5^4\2bc$i9\1a$0\1b$0M0\1b$0$0^1\1k$1=2k'$1@2$i1^1$h0=1j$1@1$h3@2$h5$h0^1M4\0$4$0@2$a@2$i0@2$h5$h0^2@2$7+2^1@2$h4^1+k0M4\0$4$0@2$h2^1@2$hf^6^5^5=1l$i3@1$d^5M4\0$4$0@2$a@1$h6@1$f^1@3$i7^7@2$7+2^2@3$c$1@1$3@2$2$1$0^1@1$i4@4$h7$1@1$3@2$2$1$0@2$h5@3$e$1@1$3@2$2$1$0^1@2$i1@3$e$1@1$3@2$2$1$0^1@2$7+2^2@3$c$1@1$3@2$2$1$0^1M2~1M4\0$4~0@1$f^1@4$h7@1$3@2$2$1$0@1$3@2$2$1$0@1$i2@2$2$1$0@3$c$1@1$3@2$2$1$0^1@3$hd^7@2$7+2^2@3$c$1@1$3@2$2$1$0^1\3dts@1$3@2$2$1$0\3rts@1$3@2$2$1$0M3\3dts@1$3@2$2$1$0$0^2@3$hb$h8@1$9@2$7+2^4@3$he^9^8^4\1p@2$2$1$0\2l0@1$3@2$2$1$0M3\3rts@1$3@2$2$1$0$0^3@3$hb$h8@1$9@2$7+2^6@3$he^b^a^6\2p0@2$2$1$0\2l1@1$3@2$2$1$0@6$i5^d^b^8@3$e$1@1$3@2$2$1$0^7^6^5=2j2$1@1$h3@2$h1^2+1M4\0$4$0@2$a@2$i0@2$h1^3+1@2$7+2^1@2$h4^1+k0M4\0$4$0@2$h2^1@2$hf^7^6@1$9ZM8\1x@1$8$1$0@3$i8^7^6^1\1v$1@1$9^1M4\0$4$0@1$f@1$d^6@3$6$5^6^5M8\1x@1$8$1$0@3$hc^7^6^1\1v$1@1$9^1M2~1@3$hd^7@2$7+2^1@3$c$1@1$3@2$2$1$0@1$d^6\1l@1$3@2$2$1$0\3rts@1$3@2$2$1$0M3\1l@1$3@2$2$1$0$0^2@3$6$5^8^7\1p@2$2$1$0\2l0@1$3@2$2$1$0M3\3rts@1$3@2$2$1$0$0^3@3$6$5^a^9\2p0@2$2$1$0\2l1@1$3@2$2$1$0@5$i6^d^b^7@3$e$1@1$3@2$2$1$0@1$d^c^5=2j3$1@2$h1@1$h3^3+1M4\0$4$0@2$a@2$a@2$h4Z^4@2$h2^1+k0@1$h6@1$f@1$d^7M8\1x@1$8$1$0@3$hc^8^7^1\1v$1@1$9@2$ia^1^5@3$6$5^7^6@3$6$5^7^6\1n$b@3$6$5^3^2~2~2~3~3\2sx$4\2lo$b\1n$b\1e$0@3$6$5^6^5\2sx$4\1k$b\1i$1\1n$b@3$6$5^6^5").

Definition mkAndB : ltac2:(zQ "20!se!irb>2bc$1>1a$0>1b$0$0") := ltac2:(zQ "d2!se!rue!u0!hge!lc!u6!i4!rb!mrb!jk4!rv9!irb!jm4&\2op$6\2a0$0\2b0$0@3$1^6^5^4&\2op$7\2a0$0\2b0$0@3$1^6^5^4\2bc$b\1a$0\1b$0M0\1b$0$0^1\1k$3M5\1x@1$5$3$0@3$a^4^3@2$c^1$9\1m$3@3$1^5^4@1$8^1@3$1^4^3^2\1n$2@3$1^4^3^2~0~0~1~1\2sx$4\2lo$2\1n$2\1e$0@3$1^7^6^5\2sx$4\1k$2\1i$3\1n$2@3$1^7^6^5").

Definition mkAndKB : ltac2:(zQ "20!se!irb>2bc$1>1a$0>1b$0$0") := ltac2:(zQ "fh3!se!sg9!u0!i4!lc!rb!hge!jk4!jm4!mrb!ru6!qoa!irb!mn5!lu5&\3op0$3\2a0$0\2b1$0@3$1^a^9^8&\3op0$5\2a0$0\2b1$0@3$1^a^9^8&\2lo$2\1n$2\1e$0@3$1^b^a^9&\2sx$4~2&\1k$2\1i$6\1n$2@3$1^b^a^9&\2sx$4~4&\3op0$3\2a0$0\2b1$0@3$1^9^8^7&\3op0$5\2a0$0\2b1$0@3$1^9^8^7&\2lo$2\1n$2\1e$0@3$1^a^9^8&\2sx$4~8&\1k$2\1i$6\1n$2@3$1^a^9^8&\2sx$4~a&\3op1$3\2a1$0\2b2$0@3$1^e^d^c&\3op1$5\2a1$0\2b2$0@3$1^e^d^c&\3op1$3\2a1$0\2b2$0@3$1^d^c^b&\3op1$5\2a1$0\2b2$0@3$1^d^c^b&\3op0$5\2a1$0\2b1$0@3$1^a^9^8&\3op0$3\2a1$0\2b1$0@3$1^9^8^7&\3op0$5\2a1$0\2b1$0@3$1^9^8^7\2bc$c\1a$0\1b$0M0\1a$0$0^2\1z$6@3$1^4^3^2\1n$2@3$1^4^3^2\2op$3\1x$0\2b0$0M3\2op$3$0^3@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4M0\2b0$0$0^1\2m1$6M0\1b$0$0^5\1k$6@3$1^8^4@1$9@2$a@2$8^2$7@2$8^1$7\1n$2@3$1^8^7^6~0~0~1~1~3~5\1n$2@3$1^7^6^5~6~6~7~7~9~b\2op$3\2a0$0\2b0$0@3$1^6^5^4\2op$5\2a0$0\2b0$0M5\2op$5$0^3M0\2a0$0$0^2\1m$6M0\2b0$0$0^2\1z$6@3$1^8^7^6\1n$2@3$1^8^7^6\3op0$3\1x$0\2b1$0M3\3op0$3$0^3@3$1^a^9^8@3$1^a^9^8@3$1^a^9^8@3$1^a^9^8@3$1^a^9^8@3$1^a^9^8M0\2b1$0$0^1\1i$6M0\1b$0$0^9\1k$6=2i'$6@2$8@2$8^2$7+k0M4\0$4$0@2$d@2$8^7$7@2$b+2^1@3$1^d^5@1$9@2$a@2$e$7@2$b+2^1@2$8^2$7@3$1^d^c^b\1n$2@3$1^c^b^a~c~c~d~d\2sx$4\2lo$2\1n$2\1e$0@3$1^f^e^d\2sx$4\1k$2\2i0$6\1n$2@3$1^f^e^d\1n$2@3$1^b^a^9~e~e~f~f\2sx$4\2lo$2\1n$2\1e$0@3$1^e^d^c\2sx$4\1k$2\1i$6\1n$2@3$1^e^d^c@3$1^a^9^8@3$1^a^9^8@3$1^a^9^8\3op0$3\2a1$0\2b1$0@3$1^a^9^8~h0~h0~3~5\1n$2@3$1^7^6^5~h1~h1~h2~h2~9~b@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4\2op$5\2a0$0\2b0$0@3$1^6^5^4\2sx$4\2lo$2\1n$2\1e$0@3$1^7^6^5\2sx$4\1k$2\1i$6\1n$2@3$1^7^6^5").

Definition or_disjointB : ltac2:(zQ "30!se!lc!irb>2bc$2>1a$0>1b$0$1") := ltac2:(zQ "d0!hge!hu2!lc!u6!se!jp8!ige!irb!km6!kj6!js0!js7!qoa\2bc$7\1a$4\1b$4M3\1x@1$3@2$1$0$0$2@2$9^3^1\1p@2$1$0$0M1\1p@2$1$0$0$2^1\2lo$0\2hi$0@2$5@2$aZ^2@2$b^1@2$c+2@2$8^6^5$6").

Definition mkOrB : ltac2:(zQ "20!se!irb>2bc$1>1a$0>1b$0$0") := ltac2:(zQ "h4ia!se!sh3!shb!u0!lc!hge!mrb!i4!rb!muc!mv5!jk4!si2!sid!jm4!u6!sj5!sk5!ske!irb&\2op$7\2a0$0\2b0$0@3$2$1^7^6&\2op$8\2a0$0\2b0$0@3$2$1^7^6&@3$c^8^6@1$6@1$d@2$e^1$b&@3$a$9~2@1$6^1&\1c$5~3&\2op$7\2a0$0\2b0$0@3$2$1^9^8&\2op$8\2a0$0\2b0$0@3$2$1^9^8&\2lo$3\1n$3\1e$0@3$2$1^a^9&\2sx$4~7&\1k$3\1i$5\1n$3@3$2$1^a^9&\2sx$4~9&M0\1a$0$0^6~4\1n$3@3$2$1^7^6~5~5~6~6~8~a&\2b0$0~b&\2a0$0~c&\2op$7~d&\2op$8~d&@3$c^9^7@1$6@1$d@2$e^1$b&@3$a$9~h0@1$6^1&\1c$5~h1&\2op$7\2a0$0\2b0$0@3$2$1^a^9&\2op$8\2a0$0\2b0$0@3$2$1^a^9&\2lo$3\1n$3\1e$0@3$2$1^b^a&\2sx$4~h5&\1k$3\1i$5\1n$3@3$2$1^b^a&\2sx$4~h7&M0\1a$0$0^7~h2\1n$3@3$2$1^8^7~h3~h3~h4~h4~h6~h8&\2op$7\2a0$0\2b0$0@3$2$1^6^5&\2op$8\2a0$0\2b0$0@3$2$1^6^5&@3$c^7^5@1$6@1$d@2$e^1$b&@3$a$9~hc@1$6^1&\1c$5~hd&\2op$7\2a0$0\2b0$0@3$2$1^8^7&\2op$8\2a0$0\2b0$0@3$2$1^8^7&\2lo$3\1n$3\1e$0@3$2$1^9^8&\2sx$4~i1&\1k$3\1i$5\1n$3@3$2$1^9^8&\2sx$4~i3&M0\1a$0$0^5~he\1n$3@3$2$1^6^5~hf~hf~i0~i0~i2~i4&\2b0$0~i5&\2a0$0~i6&\2op$7~i7&\2op$8~i7\2bc$h3\1a$0\1b$0Mf\1x@1$f$5$0@1$h1^2\1x$5Mf\1x@1$f$5$0@1$h1^2\1y$5@1$6@3$h2$1^2^1M4\0$4$0@3$h0^4^3^2@3$a$9^3^2M4\0$4$0@3$h0^4^2^3@3$a$9^3^2M0\1b$0$0^2\1c$5@3$a$9@3$c^5^4@1$6@1$d@2$e^1$b@1$6^1\1n$3M0\1a$0$0^4\1c$5@3$a$9@3$c^6^4@1$6@1$d@2$e^1$b@1$6^1\1n$3@3$2$1^5^4~0~0~1~1\2sx$4\2lo$3\1n$3\1e$0@3$2$1^8^7\2sx$4\1k$3\1i$5\1n$3@3$2$1^8^7~e~e~f~f\2sx$4\2lo$3\1n$3\1e$0~h9\2sx$4\1k$3\1i$5\1n$3~h9M4\0$4$0@3$h0^3^2^1@3$a$9^2^1M4\0$4$0@3$h0^3^1^2@3$a$9^2^1M0\1b$0$0^1\1c$5@3$a$9@3$c^4^3@1$6@1$d@2$e^1$b@1$6^1\1n$3M0\1a$0$0^3\1c$5@3$a$9@3$c^5^3@1$6@1$d@2$e^1$b@1$6^1\1n$3@3$2$1^4^3~ha~ha~hb~hb\2sx$4\2lo$3\1n$3\1e$0@3$2$1^7^6\2sx$4\1k$3\1i$5\1n$3@3$2$1^7^6~i8~i8~i9~i9\2sx$4\2lo$3\1n$3\1e$0~b\2sx$4\1k$3\1i$5\1n$3~b").

Fixpoint conc_tryB (bc : bctx) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_tryB bc e rest else
      if negb (evalS_def s e) then conc_tryB bc e rest else
      match erangeB bc s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_tryB bc e rest
                else conc_tryB bc e rest
            | None => conc_tryB bc e rest
            end
          else conc_tryB bc e rest
      | None => conc_tryB bc e rest
      end
  end.

Definition concretizeB : ltac2:(zQ "40!u6!hge!se!irb>2bc$3>1e$2@1$0$1") := ltac2:(zQ "a0!lc!u6!hge!sl5!slf!se!smd!sn4!snf!irb\2bc$9\1e$5M0\0$0@1$1$2@1$3^1@1$4^1@3$8^2^1@1$6@1$7^1").

Definition foldKB : ltac2:(zQ "20!se!irb>2bc$1>1e$0$0") := ltac2:(zQ "dh4!hge!se!u6!hu2!mrb!lc!soc!kj6!mn5!u0!i4!rb!irb&M2\1x@1$2$0$1@2$6^6^5\1v$0@1$4^1^5&M2\1x@1$2$0$1@2$6^8^7\1v$0@1$4^1^7&M5\0$5$1@2$8^2^1@1$4^2~1&\2hi$0~2&\2lo$0~3&M3\1p@2$3$0$0$1^1~4&\1p@2$3$0$0~5&M2\1x@1$2$0$1@2$6^5^4\1v$0@1$4^1^4&M2\1x@1$2@2$3$0$0$1@2$7^5^4~6~7&\1b$1~8&\1a$1~9&\2op$a~a&\2op$b~a&M2\1x@1$2$0$1@2$6^9^8\1v$0@1$4^1^8&M5\0$5$1@2$8^2^1@1$4^2~d&\2hi$0~e&\2lo$0~f&M3\1p@2$3$0$0$1^1~h0&\1p@2$3$0$0~h1&M2\1x@1$2@2$3$0$0$1@2$7^6^5~h2~0\2bc$c\1e$1M1\1e$1$1^1\1z$0^2\1n$9M2\1x@1$2@2$3$0$0$1@2$7^3^2\1p@2$3$0$0M3\1p@2$3$0$0$1^1\2lo$0\2hi$0M5\0$5$1@2$8^2^1@1$4^2~0M2\1x@1$2$0$1@2$6^3^2\1v$0@1$4^1^2~b~b~c~c\2sx$5\2lo$9\1n$9\2e0$1~h3\2sx$5\1k$9\1i$0\1n$9~h3").

Definition lin_branchB : ltac2:(zQ "50!se!lc!u6!spb!irb>2bc$4>1c$3>1a$0>1b$0@1$2$1") := ltac2:(zQ "h6hb!hge!lc!se!hu2!u6!ho7!kvd!jjd!ige!spb!m3!ng8!sq8!ore!mib!jj6!kj6!js7!qoa!jp8!luc!irb&@3$5@2$3$2$0@4$7$2$0^2Z@1$6@2$3$2$0&@3$5@2$3$2$0@4$7$2$0^2-1@1$6@2$3$2$0&@3$5@2$3$2$0@4$7$2$0^3Z@1$6@2$3$2$0&@3$d^5~1~2&@3$5@2$3$2$0@4$7$2$0^3-1@1$6@2$3$2$0&@3$d^5~4~0&@2$h4~3~5&@2$f$1M9\1c$9$1^4$8$a$a$a$a$a&@3$d^5~2~0&@3$d^5~0~2&M1\0$1$1~8~9$8&@2$f$1M9\1c$9$1^4$a$8$8$8$8$8&M1\0$1@1$4$1~a~b@1$e$1&M1\0$1@1$4$1~6~7~c&@2$h3@2$h1^4@2$h2+2+jf@2$h1^1@2$h2+2+jf&M9\1c$9@1$4$1^a@4$c$1$1$b^7@4$c$1$1$b^7^7@4$c$1$1$b^7@4$c$1$1$b^7@4$c$1$1$b^7&M1\0$1@1$4$1~e~f@1$e$1&\2bh$0~h0&\2z0$0~h1&M3\2p0@2$3$0$0@1$4$1^1~h2&\2p0@2$3$0$0~h3&M4\1x@1$4@2$3$0$0@1$4$1@2$h0^8^5~h4@1$e$1&\2ah$0~h5&\1z$0~h6&M3\1p@2$3$0$0@1$4$1^1~h7&\1p@2$3$0$0~h8&M4\1x@1$4@2$3$0$0@1$4$1@2$h0^5^3~h9@1$e$1\2bc$h5\1c$9\1a$2\1b$2=3ltu@1$4$1M1\0$1@1$4$1@3$d^4@3$5@2$3$2$0@4$7$2$0^1-1@1$6@2$3$2$0~0@2$f$1$aM1\0$1@1$4$1@3$d^4~0@3$5@2$3$2$0@4$7$2$0^1Z@1$6@2$3$2$0@2$f$1$8@1$e$1M9\1c$9@1$4$1^4~d~d~ha~ha^1@4$c$1$1$b^1").

Definition decide_branchB : ltac2:(zQ "50!se!lc!u6!spb!irb>2bc$4>1c$3>1a$0>1b$0@1$2$1") := ltac2:(zQ "h3ic!lc!hge!u6!hu2!jj6!mib!kj6!se!sr5!ss2!t5!st0!stf!u0!i4!rb!spb!sue!irb&\2bl$1\2bh$1@5$b^d^5^4^2^1&M3\2p0@2$3$1$1@1$2$0^1~0&\2p0@2$3$1$1~1&M2\1x@1$2@2$3$1$1@1$2$0@2$6^b^8~2@1$5$0&\2ah$1~3&\2al$1~4&M3\1p@2$3$1$1@1$2$0^1~5&\1p@2$3$1$1~6&M2\1x@1$2@2$3$1$1@1$2$0@2$6^8^6~7@1$5$0&M2\1x@1$2$0@1$2$0~8\1t$0@2$4$0^1@4$c^8^7^6^5&M2\1x@1$2$0@1$2$0@3$9^7^6^5\1t$0@2$4$0^1~9&M0\0$0@1$2$0@2$a^6^5@2$4$0@1$8^7~a&\2b0$7~b&\2a0$7~c&\2op$e~d&\2op$f~d&\2bl$1\2bh$1@5$b^e^5^4^2^1&M3\2p0@2$3$1$1@1$2$0^1~h0&\2p0@2$3$1$1~h1&M2\1x@1$2@2$3$1$1@1$2$0@2$6^c^9~h2@1$5$0&\2ah$1~h3&\2al$1~h4&M3\1p@2$3$1$1@1$2$0^1~h5&\1p@2$3$1$1~h6&M2\1x@1$2@2$3$1$1@1$2$0@2$6^9^7~h7@1$5$0&M2\1x@1$2$0@1$2$0~h8\1t$0@2$4$0^1@4$c^9^8^7^6&M2\1x@1$2$0@1$2$0@3$9^8^7^6\1t$0@2$4$0^1~h9&M0\0$0@1$2$0@2$a^7^6@2$4$0@1$8^8~ha&\2bl$1\2bh$1@5$b^c^5^4^2^1&M3\2p0@2$3$1$1@1$2$0^1~hc&\2p0@2$3$1$1~hd&M2\1x@1$2@2$3$1$1@1$2$0@2$6^a^7~he@1$5$0&\2ah$1~hf&\2al$1~i0&M3\1p@2$3$1$1@1$2$0^1~i1&\1p@2$3$1$1~i2&M2\1x@1$2@2$3$1$1@1$2$0@2$6^7^5~i3@1$5$0&M2\1x@1$2$0@1$2$0~i4\1t$0@2$4$0^1@4$c^7^6^5^4&M2\1x@1$2$0@1$2$0@3$9^6^5^4\1t$0@2$4$0^1~i5&M0\0$0@1$2$0@2$a^5^4@2$4$0@1$8^6~i6&\2b0$7~i7&\2a0$7~i8&\2op$e~i9&\2op$f~i9\2bc$h2\1c$h0\1a$7\1b$7M7\1a$7@1$2$0^2\1x$1M7\1b$7@1$2$0^2\1y$1@2$4$0@3$h1^5^2^1\1n$dM0\0$0@1$2$0@2$a^4^3@2$4$0@1$8^5M2\1x@1$2$0@1$2$0@3$9^5^4^3\1t$0@2$4$0^1M2\1x@1$2$0@1$2$0M2\1x@1$2@2$3$1$1@1$2$0@2$6^6^4\1p@2$3$1$1M3\1p@2$3$1$1@1$2$0^1\2al$1\2ah$1M2\1x@1$2@2$3$1$1@1$2$0@2$6^9^6\2p0@2$3$1$1M3\2p0@2$3$1$1@1$2$0^1\2bl$1\2bh$1@5$b^b^5^4^2^1@1$5$0@1$5$0\1t$0@2$4$0^1@4$c^6^5^4^3~e~e~f~f\2sx$0\2lo$d\1n$d\1e$7~hb\2sx$0\1k$d\1i$1\1n$d~hb\1n$dM0\0$0@1$2$0@2$a^3^2@2$4$0@1$8^4M2\1x@1$2$0@1$2$0@3$9^4^3^2\1t$0@2$4$0^1M2\1x@1$2$0@1$2$0M2\1x@1$2@2$3$1$1@1$2$0@2$6^5^3\1p@2$3$1$1M3\1p@2$3$1$1@1$2$0^1\2al$1\2ah$1M2\1x@1$2@2$3$1$1@1$2$0@2$6^8^5\2p0@2$3$1$1M3\2p0@2$3$1$1@1$2$0^1\2bl$1\2bh$1@5$b^a^5^4^2^1@1$5$0@1$5$0\1t$0@2$4$0^1@4$c^5^4^3^2~ia~ia~ib~ib\2sx$0\2lo$d\1n$d\1e$7~b\2sx$0\1k$d\1i$1\1n$d~b").

Definition mkSltB : ltac2:(zQ "40!se!i4!spb!irb>2bc$3>1c$2>2op$1>1a$0>1b$0$0") := ltac2:(zQ "cc!lc!se!u6!mrb!mv5!svb!u0!i4!hge!rb!spb!irb&\2b0$0M0\2b0$0$1^1@1$3+1@1$3Z&M2\1x@1$2$0$1@4$5^9^8^6^5~0@3$4^7^6^5&\2b0$1~1&\2a0$1~2&\3op0$7~3&\3op0$9~3&M2\1x@1$2$0$1@4$5^a^9^7^6~0@3$4^8^7^6&M2\1x@1$2$0$1@4$5^8^7^5^4~0@3$4^6^5^4&\2b0$1~7&\2a0$1~8&\3op0$7~9&\3op0$9~9\2bc$b\1c$a\2op$7\1a$1\1b$1M1\1a$1$1^2\1z$8M1\1b$1$1^2\2z0$8@3$4^5^4^3\1n$6M2\1x@1$2$0$1@4$5^7^6^4^3~0@3$4^5^4^3~4~4~5~5\2sx$0\2lo$6\1n$6\1e$1~6\2sx$0\1k$6\1i$8\1n$6~6\1n$6M2\1x@1$2$0$1@4$5^6^5^3^2~0@3$4^4^3^2~a~a~b~b\2sx$0\2lo$6\1n$6\1e$1~1\2sx$0\1k$6\1i$8\1n$6~1").

Definition mkAluK0B : ltac2:(zQ "30!se!i4!irb>2bc$2>2op$1>1a$0>1b$0$0") := ltac2:(zQ "hb6!se!mv5!u0!si2!lc!hge!i4!u6!rb!jk4!mrb!t5!sk5!tgd!lu5!th7!ti0!tia!tj3!tja!tk2!sg9!tkd!rqb!irb!mn5!jm4&\3op0$6\2a0$0\2b0$0@3$1^6^5^4&\3op0$8\2a0$0\2b0$0@3$1^6^5^4&\3op0$6\2a0$0\2b0$0@3$3^8^5^6&\3op0$8\2a0$0\2b0$0@3$3^8^5^6&\3op0$6\2a0$0\2b0$0@3$3^7^5^4&\3op0$8\2a0$0\2b0$0@3$3^7^5^4\2bc$h8\2op$6\1a$0\1b$0M6\2op$6$0^3@3$1^3^2^1@3$1^3^2^1@3$1^3^2^1@5$d^4$h2$f^2^1@5$d^4$h3$h0^2^1M4\0$4$0@2$b^2^1@1$aZM7\1x@1$7$5$0@1$c^2\1z$5@3$1^4^3^2M0\1b$0$0^1\1k$5M4\0$4$0@2$h9@2$ha^1$9@2$e$9+1@3$1$h1@1$a@2$e$9+1^3@3$1^4^3^2\1n$2@3$1^4^3^2~0~0~1~1\2sx$4\2lo$2\1n$2\1e$0@3$1^7^6^5\2sx$4\1k$2\1i$5\1n$2@3$1^7^6^5M7\1x@1$7$5$0@1$c^2\1z$5@3$1^4^3^2M7\1x@1$7$5$0@2$h4^1+6\1s$5@3$h7^5^3^1@3$1^3^2^1@3$1^3^2^1M4\0$4$0@2$b^2^1^2@3$h6^4^2^1M0\1a$0$0^2\1z$5M0\1b$0$0^2\2z0$5@3$h5^6^4^3\1n$2@3$3^6^3^4~2~2~3~3\2sx$4\2lo$2\1n$2\1e$0@3$3^9^6^7\2sx$4\1k$2\1i$5\1n$2@3$3^9^6^7\1n$2@3$3^5^3^2~4~4~5~5\2sx$4\2lo$2\1n$2\1e$0@3$3^8^6^5\2sx$4\1k$2\1i$5\1n$2@3$3^8^6^5").

Definition mkAluKB : ltac2:(zQ "30!se!i4!irb>2bc$2>2op$1>1a$0>1b$0$0") := ltac2:(zQ "50!se!i4!tl6!tm0!irb\2bc$4\2op$1\1a$0\1b$0@2$2^4@4$3^4^3^2^1").

Definition mkMdKB : ltac2:(zQ "30!se!rb!irb>2bc$2>2op$1>1a$0>1b$0$0") := ltac2:(zQ "h16!se!ro2!u0!hge!rb!u6!lc!i4!mrb!tmc!tn7!rlb!qvc!sk5!irb!qoa!lu5&\3op0$7\2a0$0\2b0$0@3$1^6^5^4&\3op0$4\2a0$0\2b0$0@3$1^6^5^4&\2lo$2\1n$2\1e$0@3$1^7^6^5&\2sx$6~2&\1k$2\1i$3\1n$2@3$1^7^6^5&\2sx$6~4\2bc$e\2op$4\1a$0\1b$0M5\1x@1$5$3$0@1$d^2\1z$3@3$1^4^3^2M4\2op$4$0^3@3$1^3^2^1@3$1^3^2^1@3$1^3^2^1@3$1^3^2^1@3$1^3^2^1M0\1b$0$0^1\1m$3M5\1x@1$5$3$0@1$9^1\1k$3@4$a^6$c^4@1$8^1@3$1^4^3^2\1n$2@3$1^4^3^2~0~0~1~1~3~5@3$1^3^2^1M0\1b$0$0^1\1m$3M5\1x@1$5$3$0@1$9^1\1k$3@4$a^6$b^4@1$8@2$h0@2$f+2^1+1@3$1^4^3^2\1n$2@3$1^4^3^2~0~0~1~1~3~5").

Definition zband32B : ltac2:(zQ "30!lc!se!irb>2bc$2>1d$1$0") := ltac2:(zQ "h20!hge!hu2!se!lc!hn8!u6!js7!qoa!jp8!ige!uf!jpf!jq5!jqb!jr4!irb!kj6!mg8\2bc$f\1d$2=1l$c@1$d^1M5\1x@1$5@2$1$0$0$3@3$e@1$h0^3@3$a$0@1$4@2$1$0$2^1@3$b$0@1$4@2$1$0$2^1\1p@2$1$0$0M1\1p@2$1$0$0$3^1\2lo$0\2hi$0@2$8@2$6@1$h1@2$7+2+hf^2@2$6^1@2$7+2+hf$9").

Definition mkAluwK0B : ltac2:(zQ "30!se!i4!irb>2bc$2>2op$1>1a$0>1b$0$0") := ltac2:(zQ "fa!hge!se!lc!to2!u6!hu2!tob!i4!mrb!sk5!mv5!tp7!tq5!kj6!irb&M2\0$2$1@2$6^8^4^4@3$3^7^6^5&M2\0$2$1@2$b^2^1^4~0&\2hi$0~1&\2lo$0~2&M5\1p@2$5$0$0$1^1~3&\1p@2$5$0$0~4&M2\0$2$1@2$6^5^1^1@3$3^4^3^2&M4\1x@1$4@2$5$0$0$1@2$d^5^1~5~6&M4\1x@1$4$0$1@1$9^1\1v$0@1$8@1$c^1~7&=1d$1@3$a^3^2^1~8\2bc$e\2op$7\1a$1\1b$1M7\2op$7$1^3~9~9@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1").

Definition mkAluwKB : ltac2:(zQ "30!se!i4!irb>2bc$2>2op$1>1a$0>1b$0$0") := ltac2:(zQ "50!se!i4!tl6!tqd!irb\2bc$4\2op$1\1a$0\1b$0@2$2^4@4$3^4^3^2^1").

Definition extK0B : ltac2:(zQ "20!se!irb>2bc$1>1v$0$0") := ltac2:(zQ "h00!se!hge!lc!u0!hu2!u6!i4!rb!rm4!tra!qoa!irb!kj6!ts4!rg5!js7\2bc$b\1v$0M0\1v$0$0^1\1z$1^2\1n$3^2\2op$6\1a$0\1b$0^4\2op$6\1a$0\1b$0^4\2op$7\1a$0\1b$0^4\2op$7\1a$0\1b$0^4\2sx$2\2lo$3\1n$3\1e$0M3\2lo$3$0^3M2\0$2$0@2$d^2N7M5\1x@1$5@2$4$1$1$0@2$c^6^1\1p@2$4$1$1M4\1p@2$4$1$1$0^1\2lo$1\2hi$1M2\0$2$0@2$f^1M2\2sx$2$1^7@2$e@2$a+2@2$8+8@1$9^5+2@2$a+2@2$8+8@1$9^5^4^8^5^5\2n0$3^6\2sx$2\1k$3\1i$1\1n$3^5").

Definition extKB : ltac2:(zQ "20!se!irb>2bc$1>1v$0$0") := ltac2:(zQ "40!se!tsb!tl6!irb\2bc$3\1v$0@2$2^2@2$1^2^1").

Definition flat_scB : ltac2:(zQ "50!hn8!u0!mq2!tt5!irb>2bc$4>1a$2>1n$1@1$0$3") := ltac2:(zQ "h50!hge!tt5!hu2!hn8!kvd!jse!lc!ho7!u6!tu0!mqa!tu9!js0!jp8!u0!mr2!mq2!kke!irb!tra!qoa\2bc$h2\1a$h0\1n$eM8\1x@1$8@2$2$0$0@1$3$1@2$h1^3@1$f^2\1p@2$2$0$0M2\1p@2$2$0$0@1$3$1^1\2lo$0\2hi$0M6\0$6@1$3$1@2$d@2$cZ@2$5^2@1$a^5@2$c@2$5@2$5^1@1$a^5@1$h3^4@2$h4+2+k0@1$4$1@3$7$1@2$9^5@1$b^4@1$4$1@3$7$1@2$9^2@1$b^1@1$4$1").

Fixpoint wr_coveredB (bc : bctx) (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xloB bc len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else if xinsideB bc (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
      else wr_coveredB bc rest a n
  | _ :: rest => wr_coveredB bc rest a n
  end.

Definition storeok_scB : ltac2:(zQ "50!hn8!u0!mq2!tt5!irb>2bc$4>1a$2>1n$1@1$0$3") := ltac2:(zQ "b0!tt5!lc!kvd!ho7!hn8!u0!tv0!mq2!tvc!jt5!irb\2bc$a\1a$7\1n$5M1\0$1@1$4$0@4$8^3@1$9^3^2^1@1$2$0@3$3$0@2$6^2^1@1$2$0").

Definition conc_exprB : ltac2:(zQ "20!se!irb>2bc$1>1e$0$0") := ltac2:(zQ "a6!se!hge!u6!mrb!soc!u0!lc!i4!rb!irb&M2\1x@1$2$1$0@2$4^5^4\1v$1@1$3^1^4&\1b$0~0&\1a$0~1&\2op$7~2&\2op$8~2&M2\1x@1$2$1$0@2$4^6^5\1v$1@1$3^1^5\2bc$9\1e$0M0\1e$0$0^1\1z$1^2\1n$5M2\1x@1$2$1$0@2$4^3^2\1v$1@1$3^1^2~3~3~4~4\2sx$6\2lo$5\1n$5\2e0$0~5\2sx$6\1k$5\1i$1\1n$5~5").

Definition enum_branchB (bc : bctx) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match concretizeB bc e with
  | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
  | None => None
  end.

Definition to_saddrKB : ltac2:(zQ "40!hge!se!mq2!irb>2bc$3>1e$1>3imm$0$2") := ltac2:(zQ "h16!hge!u6!mrb!se!mq2!ugb!muc!uh6!mv5!soc!u0!lc!hu2!i4!rb!uhb!irb&M1\1x@1$1$0$4@2$9^8@3$8$6^7@1$2^6\1v$0@2$7@1$2Z^1@2$5^7^6&\1b$3~0&\1a$3~1&\2op$d~2&\2op$e~2&M1\1x@1$1$0$4@2$9^9@3$8$6^8@1$2^7\1v$0@2$7@1$2Z^1@2$5^8^7\2bc$h0\1e$3\3imm$0Mc\1x@2$c$3$0$4@1$f^2\2e0$3\1z$0M3\2e0$3$4^2\2z0$0@2$5^5^4\1n$aM1\1x@1$1$0$4@2$9^6@3$8$6^5@1$2^4\1v$0@2$7@1$2Z^1@2$5^5^4~3~3~4~4\2sx$b\2lo$a\1n$a\2e1$3~5\2sx$b\1k$a\1i$0\1n$a~5").

Definition amo_alignedbB : ltac2:(zQ "40!lc!ui7!se!irb>2bc$3>1e$2>2wd$1$0") := ltac2:(zQ "90!hge!ui7!u6!lc!ige!se!ro9!irb!mn5\2bc$7\1e$5\2wd$1M2\1x@1$2$0$3@3$6^3^2M1\2wd$1$0^1+2+3\1r$0@2$8^1Z$4").

Definition amo_newvalB : ltac2:(zQ "50!se!u6!i4!ui7!irb>2bc$4>2wd$3>3aop@1$1$2>3old$0>3src$0$0") := ltac2:(zQ "70!se!u6!i4!ui7!tn7!uif!irb\2bc$6\2wd$3\3aop@1$1$2\3old$0\3src$0M1\3aop@1$1$2$0^3\1o$2M3\2wd$3$0^5@4$5^6^1^3^2@4$4^6^1^3^2^1").

Fixpoint log_lookupB (bc : bctx) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookupB bc rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
      | RUnknown =>
          if ranges_apartB bc rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookupB bc rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookupB bc rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.

Fixpoint know_lookupA0B (bc : bctx) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0B bc in
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  (* [comment removed for export] *)
                  if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinsideB bc rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (l0 mod 2^64)%Z)
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (l0 mod 2^64)%Z) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  (* [comment removed for export] *)
                  if match erangeB bc len with   (* [comment removed for export] *)
                     | Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
                match img_bytes segs rk n with
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n sx hints acc
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
      end
  end.

Definition know_lookupAB : ltac2:(zQ "a0!hn8!lc!u0!hge!un0!se!hr8!unb!tt5!irb>2bc$9>4segs@1$0$4>2kn@1$0$6>2rb$5>2rk$3>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$8$7") := ltac2:(zQ "h10!hn8!lc!unb!hge!tt5!u6!uo2!se!u0!un0!uo9!up1!hr8!upa!uqb!ura!irb\2bc$h0\4segs@1$0$9\2kn@1$0$c\2rb$7\2rk$3\1n$8\2sx$1\5hints@1$0$1\3acc@1$0$4M2\1x$2$2@9$f^9^8^7^6^5^4^3^2^1\1v$7\3scs@1$0$4\6hints0@1$0$1@3$6^3^2^1\4acc'@1$0$4\6hints'@1$0$1M5\1x@1$5@1$0$3$2@5$d^a^9^8^7^6\2bs@1$0$3@3$6@3$e^6^7^1^3^2@2$a^2^1$b").

Definition sym_readB : ltac2:(zQ "c0!hu2!hn8!u0!usc!lc!u6!un0!se!mq2!tt5!ut6!irb>4segs@1$1$6>2ss$a>2bc$b>3scr$3>1a$8>1n$2>3sx'$4@1$5@2$0@2$0@2$0$7@1$1$9$3$2") := ltac2:(zQ "i34!hn8!hu2!se!tt5!usc!u0!jjd!lc!unb!uu2!jj6!uud!uv3!uv9!vg2!vgc!mib!kvd!u6!mr2!mqa!vh8!vi1!ho7!un0!vi5!vic!vj9!vk2!mq2!vka!ut6!vl5!vm6!irb&@2$1@2$1@2$1$2@1$0$3$4$5&@1$h2~0&\1x$8~1&@1$h0~0\4segs@1$0$h8\2ss$hf\2bc$i2\3scr$4\1a$hd\1n$5\3sx'$7M8~2@8$i1^5@1$hc^6@1$h3^3@1$h4^3^2^1@1$he^4@1$h1$3\1v$2\3scs@1$0$3\5hints@1$0$7@2$a~0@4$6@2$1@2$1$2@1$0$3$4$5@4$6@2$1$2@1$0$3$4@4$6$2@1$0$3@2$h5^8^3@3$b$3@3$f^8^6^5^2@3$c@1$e^7@1$9^7^1@1$d^9\3scs@1$0$3\5hints@1$0$7M8~2@9$i0^7^9@1$hb^8@1$h3^5@1$h4^5^4^3^1^2\1v$2\4scs'@1$0$3\6hints'@1$0$7@2$a~0@4$6@2$1@2$1$2@1$0$3$4$5@4$6@2$1$2@1$0$3$4@4$6$2@1$0$3@2$h5^a^3@3$b$3@3$f^a^8^7^2@3$c@1$e^9@1$9^9^1@1$d^b\4scs'@1$0$3\6hints'@1$0$7=1i$5@1$d^a=2rv$2M0\1x@1$0$2$2@1$9^9@1$h9^1\1e$2\1l@1$0$2^2=6reads'@1$0$2M0\1x@1$0$2@1$0$2@1$9^a@1$h1$2\1e$2\1t@1$0$2^1@2$a~0@4$6@2$1@2$1$2@1$0$3$4$5@4$6@2$1$2@1$0$3$4@4$6$2@1$0$3^2@3$b$3@3$f^c^a^9@3$h7$3@4$ha^a^9^8^2^5@3$c@1$e^b^1^4@1$h6^3~3~3").

Definition sym_stepB : ltac2:(zQ "70!hn8!un0!vn5!usc!vnc!ut6!irb>2bc$6>4segs@1$0$1>1i$2>2ss$5>3scr$3$4") := ltac2:(zQ "led!vo6!vqa!hu2!se!lc!tt5!vr0!hn8!u6!jse!vnc!u0!vr8!usc!kvd!mq2!vre!vs5!vsb!i4!mrb!vt4!hge!vu1!vv0!vv6!vj9!vk2!hgg4!ho7!hgh2!hgh6!rb!hgk3!hgke!hgl5!hgle!hgm6!hgmf!hgn5!hgnd!jj6!uud!ui7!vn5!hgo8!hgod!hgp6!hgpf!hgr0!tn7!hgre!hgsd!hgta!hgu1!hgua!hgv3!uv9!svb!vgc!uif!hhg0!mib!ige!un0!muc!hhga!spb!hhh1!hhh9!hhi1!hhi8!hhj3!hhjb!hhk3!uv3!hhka!to2!hhl6!hhle!hhm5!vg2!vka!uu2!hhn1!ut6!hhna!hho9!hhp9!irb!ru6!jm4!qoa!hhq3&@2$2@2$2@2$2$3@1$7$5$d$b&@1$8~0&\1x~1$a&\2p0~0$a&\2p1@2$2@2$2$3@1$7$5$d$a&@3$i6@1$0#5ZKv$he@2$i7@1$0#5Z&\3rs1@1$1@1$0#5\2rm@1$1@1$0#3$6&\2rd@1$1@1$0#5~6&\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5$6&\2rd@1$1@1$0#5~8&\3fmt$h1~9&\2rd@1$1@1$0#5\3rs1@1$1@1$0#5$6&\3fmt$h1~b\2bc$l9\4segs@1$7$k0\1i$ic\2ss$l5\3scr$d=1g>1r@1$1@1$0#5$3\1r@1$1@1$0#5@2$l4@1$h2^3^1=1p$h6@1$kf^3Mic\1i$ic$a^5\2rd@1$1@1$0#5\3imm@1$1@1$0#h4@3$c@4$h0^6^2@1$h4@2$h7@1$0#k0@2$i8@1$0#k0@2$jd@2$h5@1$0#h4^1+c@2$9^3+4@1$e$5^5\2rd@1$1@1$0#5\3imm@1$1@1$0#h4@3$c@4$h0^6^2@1$h4@2$h7@1$0#k0@2$i8@1$0#k0@2$9@2$jd@2$h5@1$0#h4^1+c^3@2$9^3+4@1$e$5^5\2rd@1$1@1$0#5\3imm@1$1@1$0#h5@3$c@4$h0^6^2@1$h4@2$9^3+4@2$h7@1$0#k0@2$i8@1$0#k0@2$9^3@2$h5@1$0#h5^1@1$e$5^5\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3imm@1$1@1$0#cM3\1x$3$a@2$j1^a@1^5^2\1z$h6@3$c@4$h0^8^4@1$h4@2$9^5+4@2$lb@2$la@2$9@2$ld@1$0#k0^1@2$h5@1$0#c^2-2@2$lc+2+k0@1$e$5^7\1n$b$6\2op$h3\1a$3\1b$3$6\2op$h3\1a$3\1b$3$6\2op$i0\1a$3\1b$3$6\2op$i0\1a$3\1b$3$6\2sx$4\2lo$b\1n$b\1e$3$6\2sx$4\1k$b\2i0$h6\1n$b$6\1c$k3\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3imm@1$1@1$0#d=2tk$h6@2$h7@1$0#k0@2$i8@1$0#k0@2$9^5@2$h5@1$0#d^1=1a$3@1^7^4=1b$3@1^8^4M8\1x@1$8$4$aM8\1x@1$8$4@1$8$4@4$ja^e^7^2^1\1t$4@2$i9$4^1M8\1x@1$8$4@1$8$4@4$ja^e^7@2$j1^e^2@2$j1^e^1\1t$4@2$i9$4^1@4$l7^e^7^2^1\1t$4@3$c@2$i4^cM4\1t$4$h6^1^4@2$9^9+4@1$e$5^bM7\1x@1$7$4$a@1$l1^a$6\1t$4\5dirs'@1$7$4@3$c@2$i4^dM4\1t$4$h6^2^5@2$9^a+4@3$hd$5@4$ka^2^9^4^3@1$e$5@3$kb^1@1$l3^c@1$l2^c\2sz$hf\2sx$4\2rd@1$1@1$0#5\2rs@1$1@1$0#5\3imm@1$1@1$0#c=1n$b@1$h9^5=3sx'$4Mhf\2sz$hf$4^6^5^5^5$jf=1a$f@3$hc^e@1^9^4@2$h5@1$0#c^3M8~2@7$j4^e^c^f^b^1^3^2\2p0~0M2~3^1\2p1@2$2@2$2$3@1$7$5$d\3nx'$bM2~4^2\2p2@2$2$3@1$7$5\4scr'$dM2\2p2@2$2$3@1$7$5$a^2\1v$3\3scs@1$7$5@3$c@6$h8@2$9^h0+4M4\0$4@1$7$3@3$i1@1$0#5^d~5@1$h2^h3@3$i5@1$h2^h3@1$i2^d^2@1$hb^h3@1$ha^h3^5@1$i3^h3^1^3$6\2sz$hf\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3imm@1$1@1$0#c=1n$b@1$h9^4=1a$f@3$hc^c@1^7^4@2$h5@1$0#c^2M8\1x@1$8@1$8$f$a@2$j8@1$i3^a^1\2r'@1$8$f@3$c@6$h8@2$9^8+4@1$h2^b@3$hd$if@3$id^2^3@1^9^5@1$hb^b@1$ha^b@1$j9^b^1@3$ia$5@3$jb^e^2^3@3$j3^e^2^3^a$6\2op$h3\2rd@1$1@1$0#5\2rs@1$1@1$0#5\3imm@1$1@1$0#c@3$c@4$h0^8^3@4$j2^b^4@1^6^2@1$h4@2$h5@1$0#c^1@2$9^5+4@1$e$5^7\2op$h3\2rd@1$1@1$0#5\2rs@1$1@1$0#5\2sh@1$1@1$0#6@3$c@4$h0^8^3@4$j2^b^4@1^6^2@1$h4@2$h7@1$0#6^1@2$9^5+4@1$e$5^7\2op$h3\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5@3$c@4$h0^8^3@4$j2^b^4@1^6^2@1^6^1@2$9^5+4@1$e$5^7\2rd@1$1@1$0#5\2rs@1$1@1$0#5\3imm@1$1@1$0#c@3$c@4$h0^7^3@4$jc^a$k1@1^5^2@1$h4@2$h5@1$0#c^1@2$9^4+4@1$e$5^6\2op$h3\2rd@1$1@1$0#5\2rs@1$1@1$0#5\2sh@1$1@1$0#5@3$c@4$h0^8^3@3$kd^4@1^6^2@1$h4@2$h7@1$0#5^1@2$9^5+4@1$e$5^7\2op$h3\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5@3$c@4$h0^8^3@4$jc^b^4@1^6^2@1^6^1@2$9^5+4@1$e$5^7\2fm@1$1@1$0#4\4pred@1$1@1$0#4\4succ@1$1@1$0#4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5@3$c@2$i4^9@2$9^6+4@1$e$5^8\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3imm@1$1@1$0#c@3$c@2$i4^7@2$9^4+4@1$e$5^6$6$6\2op$i0\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5@3$c@4$h0^8^3@4$l8^b^4@1^6^2@1^6^1@2$9^5+4@1$e$5^7\2op$i0\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5@3$c@4$h0^8^3@3$ke^4@1^6^2@1^6^1@2$9^5+4@1$e$5^7\2wd$ib\2aq$4\2rl$4\2rd@1$1@1$0#5\2rs@1$1@1$0#5=1n$b@1$h9@1$ie^5=1e$3@1^8^2M4\0$4$a@3$j0^e^1^7=1a$f@3$hc^e^1ZM8~2@7$j4^e^c^f^b^1^3@1$j7^8\2p0~0M2~3^1\2p1@2$2@2$2$3@1$7$5$d\3nx'$bM2~4^2\2p2@2$2$3@1$7$5\4scr'$dM2\2p2@2$2$3@1$7$5$a^2\1v$3\3scs@1$7$5@3$c@6$h8@2$9^h0+4M4\0$4@1$7$3@3$i1@1$0#5^c~5@1$h2^h3@3$i5@1$h2^h3@1$i2^c^2@1$hb^h3@1$ha^h3^5@2$i9$f^8^1^3$6$6\2wd$ib\2aq$4\2rl$4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5=1n$b@1$h9@1$ie^6=1e$3@1^9^3M4\0$4$a@3$j0^f^1^8=1a$f@3$hc^f^1ZM8\1x@1$8$f$a@1$i3^d\1r$fM4\0$4$a@2$l0^1^2@3$c@6$h8@2$9^b+4M4\0$4@1$7$3@3$i1@1$0#5^7~5@1$h2^e@3$i5@1$h2^e@1$i2^7@1$h4Z@3$hd$if@3$id^2^4@1^c^5@1$hb^e@1$ha^e@1$j9^e@1$je$f@3$ia$5@3$jb^h1^2^4@3$j3^h1^2^4^d$6$6$6\2op$k2\2wd$ib\2aq$4\2rl$4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5M8\1x@1$8@1$8$h3$a@1$kc^7\3aop@1$8$h3=1n$b@1$h9@1$ie^7=1e$3@1^b^4M4\0$4$a@3$j0^h1^1^9=1a$f@3$hc^h1^1ZM8\1x@1$8@1$8$f$a@2$j8@1$i3^f^1\2r'@1$8$fM8~2@7$j4^h2^h0^h3^f^2^4@1$j7^b\2p0~0M2~3^1\2p1@2$2@2$2$3@1$7$5$d\3nx'$bM2~4^2\2p2@2$2$3@1$7$5\4scr'$dM2\2p2@2$2$3@1$7$5$a^2\4vold$3\3scs@1$7$5@3$c@6$h8@2$9^h4+4M4\0$4@1$7$3@3$i1@1$0#5^f~5@1$h2^h7@3$i5@1$h2^h7@1$i2^f^2@3$hd$if@3$id^9^b@5$l6^ha^h2^c^2@1^h5^d@1$hb^h7@1$ha^h7^5^8@3$ia$5^1@3$j3^ha^9^b^3$6$6$6$6\2op$j5\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3csr@1$1@1$0#c$6\2op$j5\2rd@1$1@1$0#5\4uimm@1$1@1$0#5\3csr@1$1@1$0#c$6\3fmt$h1\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3imm@1$1@1$0#c$6\3fmt$h1\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3imm@1$1@1$0#c$6\2op$k6\3fmt$h1\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3rs3@1$1@1$0#5\2rm@1$1@1$0#3$6\2op$k4\3fmt$h1\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\2rm@1$1@1$0#3$6\3fmt$h1~7\2op$k9~a\2op$k7~a\2op$k5~a\3dst$j6\3src$j6~7\3dir$k8~c~c").

Definition know_lookupB : ltac2:(zQ "90!hn8!lc!u0!hge!un0!se!unb!tt5!irb>4segs@1$0$4>2bc$8>2rb$5>2rk$3>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$7$6") := ltac2:(zQ "a0!hn8!lc!u0!hge!un0!se!tt5!vl5!jt5!irb\4segs@1$0$4\2bc$9\2rb$5\2rk$3\1n$2\2sx$1\5hints@1$0$1\3acc@1$0$6@9$7^7^8@1$8^7^6^5^4^3^2^1").
End FPX_52.



Local Open Scope Z_scope.
Section FPX_53. Context {fx : XPropExec.FPState}.

(* [comment removed for export] *)
Definition gran : ltac2:(zQ "10!hge>1a$0$0") := ltac2:(zQ "20!hge!hhqe\1a$0@2$1^1+c").
Definition is_lit0 : ltac2:(zQ "20!lc!se>1e$1$0") := ltac2:(zQ "90!se!ige!u0!lc!hge!hhr8!i4!rb!m3\1e$0M0\1e$0$3^1\1z$4M4\1z$4$3^1$8\1p$5$1\1p$5$1\1n$2$1\2op$6\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2op$7\1a$0\1b$0$1\2op$7\1a$0\1b$0$1\2sx$3\2lo$2\1n$2\2e0$0$1\2sx$3\1k$2\1i$4\1n$2$1").
(* [comment removed for export] *)
Definition lit0_extent : ltac2:(zQ "40!hge!u6!hu2!hr8>1K$3@1$1@2$2$0$0") := ltac2:(zQ "h1a!hge!se!hu2!mib!u0!u6!mq2!lc!i4!rb!hhr8!jj6!jjd!jse!hr8!hhs3!tra&\2op$8\2a0$1\1b$1@1$3@2$2$0$0&\2op$9\2a0$1\1b$1@1$3@2$2$0$0&@2$b@2$2$0$0@4$c$0$0^3@2$d^3@1$f^1&\2l0$0~2&\2lo$4\2n0$4\1e$1@1$3@2$2$0$0&\2sx$7~4&\1k$4\1i$0\2n0$4@1$3@2$2$0$0&\2sx$7~6&\2k0$4\1i$0\2n0$4@1$3@2$2$0$0&\2sx$7~8\1K$eMe\1K$e@1$5@2$2$0$0^1\1a$6\1w$4\1v$1M6\1a$6@1$5@2$2$0$0^3\6a_base$1\2kk$0M1\6a_base$1@1$5@2$2$0$0^2\1z$0M0\1z$0@1$5@2$2$0$0^1@2$b@2$2$0$0@4$c$0$0^2@2$d^2@1$h0^5\1p$a@1$3@2$2$0$0\1p$a@1$3@2$2$0$0\1n$4@1$3@2$2$0$0~0~0~1~1\2sx$7\2lo$4\1n$4\1e$1@1$3@2$2$0$0\2sx$7\1k$4\1i$0\1n$4@1$3@2$2$0$0\1a$6\1n$1M6\1a$6@1$5@2$2$0$0^2\6a_base$1\2kk$0M1\6a_base$1@1$5@2$2$0$0^2\1z$0M0\1z$0@1$5@2$2$0$0^1M1\1n$1@1$5@2$2$0$0^4~3\2n0$4@1$3@2$2$0$0~0~0~1~1~5~7\1p$a@1$3@2$2$0$0\1p$a@1$3@2$2$0$0\2n0$4@1$3@2$2$0$0~0~0~1~1~5~7\1a$6\1n$1\1k$4M6\1a$6@1$5@2$2$0$0^3\6a_base$1\2kk$0M1\6a_base$1@1$5@2$2$0$0^2\1z$0M0\1z$0@1$5@2$2$0$0^1M1\1n$1@1$5@2$2$0$0^5~3\2n0$4@1$3@2$2$0$0~0~0~1~1~5~9\1p$a@1$3@2$2$0$0\1p$a@1$3@2$2$0$0\2n0$4@1$3@2$2$0$0~0~0~1~1~5~9\2lo$0\2hi$0@2$b@2$2$0$0@4$c$0$0^2^1\1e$1\1m$0@1$3@2$2$0$0\1e$1\2lo$0\2hi$0@1$3@2$2$0$0\1a$6\1n$1@1$3@2$2$0$0\2a1$6\2n1$1\2a2$6\2n2$1@1$3@2$2$0$0\1a$6\1n$1\1c$0M6\1a$6@1$5@2$2$0$0^3\6a_base$1\2kk$0M1\6a_base$1@1$5@2$2$0$0^2\1z$0M0\1z$0@1$5@2$2$0$0^1M1\1n$1@1$5@2$2$0$0^5~3\2n0$4@1$3@2$2$0$0~0~0~1~1~5~7\1p$a@1$3@2$2$0$0\1p$a@1$3@2$2$0$0\2n0$4@1$3@2$2$0$0~0~0~1~1~5~7\1a$6\1n$1@1$3@2$2$0$0").
(* [comment removed for export] *)
Definition ext_fits : ltac2:(zQ "20!hge!lc>1s$0>1e$0$1") := ltac2:(zQ "70!lc!hge!hiha!lu5!ige!js0!js7\1s$1\1e$1M0\0$0$0@2$6^2^1@2$5@2$3@1$2@2$3^1+1@1$2^2+1$4").
Definition ext_has : ltac2:(zQ "20!hge!lc>1s$0>1e$0>1g$0$1") := ltac2:(zQ "60!lc!hge!hiha!mn5!m3!lu5\1s$1\1e$1\1g$1M0\0$0$0@2$3^1@1$2^3$4@2$3^1@1$2@2$5^2+1").
(* [comment removed for export] *)
Definition kx_wide0 : ltac2:(zQ "20!lc!hr8>1K$1$0") := ltac2:(zQ "e0!hge!mq2!se!ige!lc!hu2!hr8!u0!u6!m3!ng8!hii3!hij0!hijc\1K$6M8\1x@1$8@2$5$0$0$4@1$d^1\1p@2$5$0$0M5\1p@2$5$0$0$4^1\1s$0\1e$0@1$a@2$b^2^1M6\1K$6$4^1\1a$1\1w$7\1v$2$3\1a$1\1n$2M1\1a$1$4^2\2kb$2\5a_off$0$9\1a$1\1n$2\1k$7M1\1a$1$4^3\2kb$2\5a_off$0@1$c^2\2lo$0\2hi$0$3\1e$2\1m$0$3\1e$2\2lo$0\2hi$0$3\1a$1\1n$2$3\2a1$1\2n1$2\2a2$1\2n2$2$3\1a$1\1n$2\1c$0M1\1a$1$4^3\2kb$2\5a_off$0$9\1a$1\1n$2$3").
(* [comment removed for export] *)
Definition kx_cand0 : ltac2:(zQ "30!lc!hge!hr8>1g$1>1K$2$0") := ltac2:(zQ "a0!hge!lc!hu2!u6!m3!hr8!hii3!hikc!hil8!hijc\1g$0\1K$5M3\1x@1$3@2$2$0$0$1@1$9^1\1p@2$2$0$0M2\1p@2$2$0$0$1^1\1s$0\1e$0M1\0$1$1@2$6^2^1@3$7^2^1^5$4@1$8^1").
(* [comment removed for export] *)
Definition kx_candf : ltac2:(zQ "20!lc!hr8>1K$1$0") := ltac2:(zQ "a2!se!mq2!hge!ige!lc!hr8!u0!ng8!m3!hij0&\2kb$0\5a_off$2@1$7@1$9^2&M1\1a$1$4^3~0\1K$5M5\1K$5$4^1\1a$1\1w$6\1v$0~1\1a$1\1n$0$8\1a$1\1n$0\1k$6~1\2lo$2\2hi$2$3\1e$0\1m$2$3\1e$0\2lo$2\2hi$2$3\1a$1\1n$0$3\2a1$1\2n1$0\2a2$1\2n2$0$3\1a$1\1n$0\1c$2$8\1a$1\1n$0$3").
(* [comment removed for export] *)
Definition kx_gkey : ltac2:(zQ "20!hge!hhr8>1g$0$1") := ltac2:(zQ "40!hge!hhr8!him5!hima\1g$0M0\1g$0$1^1#1\1p$1@1$3^1\1p$1@1$2^1").
Record kix : Type := KX {
  kx_kn : list kentry;                              (* [comment removed for export] *)
  kx_w0 : list (positive * kentry);                 (* [comment removed for export] *)
  kx_gran : ptree (list (positive * kentry));       (* [comment removed for export] *)
  kx_wf : list kentry                               (* [comment removed for export] *)
}.
Definition kx_bucket : ltac2:(zQ "60!hn8!hu2!hhr8!hr8!hge!himf>1t@1$5@1$0@2$1$2$3>1g$4@1$0@2$1$2$3") := ltac2:(zQ "a0!hu2!hhr8!hr8!hn8!u6!kvd!hge!hin7!himf!hio0\1t@1$8@1$3@2$0$1$2\1g$6M4\1x@1$4@1$3@2$0$1$2@1$3@2$0$1$2@3$7@1$3@2$0$1$2^2@1$9^1\1b@1$3@2$0$1$2^1@1$5@2$0$1$2").
Definition kx_add : ltac2:(zQ "60!hu2!hhr8!hr8!hn8!himf!hge>1g$5>1x@2$0$1$2>1t@1$4@1$3@2$0$1$2@1$4@1$3@2$0$1$2") := ltac2:(zQ "a0!hu2!hhr8!hr8!hn8!ho7!hge!hioc!himf!hip5!hio0\1g$5\1x@2$0$1$2\1t@1$7@1$3@2$0$1$2@4$6@1$3@2$0$1$2@1$9^3@3$4@2$0$1$2^2@2$8^1^3^1").
Fixpoint kx_build (kn : list kentry) (i : positive) : list (positive * kentry) * ptree (list (positive * kentry)) * list kentry :=
  match kn with
  | [] => ([], PTLeaf, [])
  | K :: rest =>
      let '(w0, gr, wf) := kx_build rest (Pos.succ i) in
      let wf' := if kx_candf K then K :: wf else wf in
      match lit0_extent K with
      | Some (s, e) =>
          if ext_fits s e then
            let g1 := gran s in let g2 := gran (e - 1) in
            let gr1 := kx_add g1 (i, K) gr in
            (w0, (if Z.eqb g1 g2 then gr1 else kx_add g2 (i, K) gr1), wf')
          else ((i, K) :: w0, gr, wf')
      | None => if kx_wide0 K then ((i, K) :: w0, gr, wf') else (w0, gr, wf')
      end
  end.
Definition mk_kix : ltac2:(zQ "30!hn8!hr8!hiq3>2kn@1$0$1$2") := ltac2:(zQ "92!hn8!hu2!hr8!hhr8!himf!uf!jpf!hiqb!hir2&@2$1@1$0@2$1$3$2@1$4@1$0@2$1$3$2&@3$5~0@1$0$2^1\2kn@1$0$2=1r@2$1~0@1$0$2@2$8^1#1@4$7^2@3$5@1$0@2$1$3$2@1$4@1$0@2$1$3$2~1@3$6@1$0@2$1$3$2@1$4@1$0@2$1$3$2~1@3$6~0@1$0$2^1").
(* [comment removed for export] *)
Fixpoint kx_merge (l1 : list (positive * kentry)) : list (positive * kentry) -> list kentry :=
  match l1 with
  | [] => fun l2 => List.map snd l2
  | (p1, K1) :: r1 =>
      fix go (l2 : list (positive * kentry)) : list kentry :=
        match l2 with
        | [] => K1 :: List.map snd r1
        | (p2, K2) :: r2 => if Pos.ltb p1 p2 then K1 :: kx_merge r1 l2 else K2 :: go r2
        end
  end.
Definition kx_select (kx : kix) (rb : expr) (rk : Z) : list kentry :=
  if is_lit0 rb then kx_merge (kx_bucket (kx_gran kx) (gran rk)) (kx_w0 kx)
  else kx_wf kx.

Definition know_lookupA0I : ltac2:(zQ "a0!hn8!lc!u0!hge!un0!se!unb!tt5!hiq3!irb>2bc$9>2kx$8>4segs@1$0$4>2rb$5>2rk$3>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$7$6") := ltac2:(zQ "e0!lc!hn8!u0!hirf!unb!hit1!kvd!hge!un0!se!tt5!hiq3!hitb!irb\2bc$d\2kx$b\4segs@1$1$8\2rb$9\2rk$7\1n$2\2sx$0\5hints@1$1$0\3acc@1$1$aM1\5hints@1$1$0$4^2M2\1n$2$4^4@9$3^9^7@1$5^8^6^5^4^3^2^1\2n0$2@9$3^a^8@3$c^9^7^6^7^6^5^4@1$6$0^2\1b$0\1l@1$1$0@9$3^b^9@1$5^a^8^7^6^5^4^3").

(* [comment removed for export] *)
Lemma gran_div : ltac2:(zQ "40!hge!jf!hiha!rg5>1a$0@3$1$0@1$2^1@2$3^1+hgg0").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_53"] "h07__arithh14__ffh28__varmaph35__with41ah51zp;1p;2p;3p;4p;7p;6g01D[j11Tg01E@j12Tg01gjj1=Tg01E^j2HTg01j=j24Tg008]j33Tg0097j25Tg052Aj2;Tg00f4j1:Tg00eTj17Tg052aj18Tg053?j19Tg053]j1GTg054Hj26Tg054kj4FTg055Vj7CTg056:j2BTg056\j2?Tg057Hj3>Tg057gj4@Tg058Yj2ATg0595j3<Tg003Vj6DTg059^j1ETf0R0#1#1p=0g00b@R1P1g01VBR2#1R3#2%=2#0#2R2'H,40f1R4%13#0#0#0#0#0#2R3'49310X511403R3,511;02g05:kR5#:%75%81%91%G1R5g05;Wg05<6R6P6g05<VR6P1g01TVR7,61g05=61612CFg05=]FC1B56P0f2R6g00;\R5g00<<R8'51?06=358dA>174C@b1b2b31A72P0b09<02ED%E0=313eW4o"). Qed.
Lemma gran_mono : ltac2:(zQ "30!hge!hiha!hiu9>1a$0>1b$0>0@2$2^2^1@2$2@1$1^3@1$1^2").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_53"] "h07__arithh14__ffh28__varmaph35__with44__x1h54__x2h61zh71Hh81ah91bp;2p;1p;4p;3p;8p;5p;6p;7g058Yj21Tg01D[j12Tg01E@j1<Tg01j=j23Tg059^j17Tg00f4j1DTg00eTj1@Tg052aj1>Tg053?j1=Tg053]j1;Tg054Hj24Tg054kj48Tg056:j2MTg0097j2LTg056\j2KTg008]j3JTg057Hj3HTg057gj4CTg05>=j2BTg05>Yj2ATg05?7j4?Tg05?Uj26Tg00nJj1ETg05@8j8FTg05@\j5GTg05AAj19Tg003Vj65Tg055Vj7ITf0R0#2#2p=0f1R1g05;WR2g05<6R3P3g05<VR4P0g05=]FIp=:g00b@R51110P5f2R6g01VBR7#2R8#2#0#0#0#0#0#<R9'3%76R:,10X65P51319f3R;/39/10X65P6P1P9g05:kR<#DR=%@<R<%>5R>%=5R?%;5R@P5g01TVRA,45g05BR1459C8':1M@4RBP0P6g00;\RCg00<<RD'L1K06=JCDdAH5A1CCRDb1b2b31BA9P0b0P=P<P51A56P1P>C?P?P@P2P3P3P4P51657g05=61658C8,:@R@%E3P@GFPBPDb1b2b3X45X5511011116[^45^55P0P6P;P1O3b0DG%71%91E5P:%96E5W7X95W8o"). Qed.
Lemma gran_between : ltac2:(zQ "90!hge!lc!m3!jf!hii3!hikc!hiha!hiu9!hiuf>1s$0>1e$0>1x$0>0@2$7^3^1>0@2$8^2^3>0@3$3$1@2$4^5^4$2@3$3$1@3$5^6^5@1$6^4$2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##<1p'0h02Hfh14__x1h24__x2h31bi001bh42e0h51ni011nh61Hh77__arithh84__ffh94__p1h:8__varmaph;5__with<4__x3h=1mh>1ri021rh?1Ah@1BhA2HehB2HshC1ei031ehD2n0hE1shF1xp;2p;1p;3p;4p;6p;7p;8g058Yj21Tg05>=j2KTg05C9j2UTg01G5j2dTg01E@j1ZTg059^j10Tg01F;j26Tg01T9j2=Tg00N^j27Tg05DJj2M!s/$jj3CTg00f4j1cTg00eTj1a!t:$Yj2BTg052aj1YTg05?7j4;Tg053?j1W!s/$]j1V!sA$Uj29Tg01D[j1ATg054kj4:Tg00nJj1T!s8$Hj2STg05F<j3FTg056:j2RTg0097j2Q!s8$\j2PTg057Hj3O!s/$gj4N!s\$_j2GTg00jFR0j2DTg00mNj1ETg008]j3@Tg00g4j1>Tg05GAj2?!s/$jj3LTg05HSj2b!ub$Tj3`Tg01gjj1JTg05I?j6[!tW$mj2I!s/$Qj6\!sA$cj3]Tg055Vj7^Tg05@8j8_Tg05K3j6XTg00;\R1f0R2g00<<R33@p=2f1R4/62#0p=3P4g05;WR5g05<6R6P6g05<VR7P2g05=]F^p=5g00b@R8!sR$=6P2C:p=<f3R9P5P6P6P7f2R:P4P2G_p=8A@842p=4P4!sE'P2EXp=H11:21K4:f4R;/U9#2f5R</d;P1!s$&2f6R=g01VBR>#ZR?'3f7R@#0RA'6/=?g00>4RBn010!s#$20000#2P1P1%0=RCf8RD#0RE'7P313@?RF,7C!sT3RG]0P213<?/6C/=?#2g00`91=42#211:4[RC11421=:4#2RH[119:\H1M42P4n20!su'1!sv$000X=8X58PC^=8^58P216FERFP?P4O311F?f9RF?C@=%0FR=/1A16F?RAg05:kRC#cRH%aCRIP81B8:RJP4%Y8RKC;%W8RL%V8RMP8198>RNg05BR%A>RO,98RPC:,5M%T6RQ1S8?RR9F8P,<N,5MC81RM7RNP2P:1Q13RP1P2:#2dg01TV=O84CNRSb8b:b;X18X281K2416:?,14[^18^28P2f:RTPFP@O3b75CD%0A,1Ef;RE#0RA,G=14=A17=A'D%0Tf<#0R='7P1P0f=#0R@,4A!xB$4P3f>RA/3?RU,7@RV!x,44%0ARA,4=R=PPW4P2O1%E=1G@U14@U/DVf?RV/3?,7AP1P0%0Vf@!s7$'4%24P4%0VfA!s5$RV!sg,VA@1B3RVp-0RPg00h4R0#>#>#>RA#>,?81?8A1?805L85L8g05KW'b=`CHPIP8!wU$4P91B89C;P9P8PJP9PKC;C;PLPMP8%J>#A,98R>g05LCRL%A!w^$K!w^$,HMPQPMP8P>PL%J!s@$O!s@/1<>K,5!s1&O>!s1&AF8KO/<R!s5&!|N+<E[C8!s$'PNP!x'0X<8W914:2g00>TRS[149:PS[11;:11;<16;</1?PD[[[[!xM&^<8^9PP2PSfB#0fD#0fC/3?P4P<PFPTPEO9b7'IWDP2O1n1021001!wx$21010311101b3b>W5!sHCb@b?b0b6W0P1PBP1P!tE$g00?1n011!xy,X41g00?MP3P2E\PS1IG2b6X0V!sM-100P4O1b3%099]<;#2eW0WAWBXF8XC8XE8o"). Qed.
Lemma kx_aluop_eqb_refl : ltac2:(zQ "50!lc!m3!jf!i4!qf>1a$3@3$2$0@2$4^1^1$1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##$Wp'0h01ai001ap;2p;3g00:Lj22Tg008]j31Tg0097j20Tg00<\R0P0g00;\R0f0R1/21g00<<R231P11002R2P!s$4n01100000:0!s#6W0o"). Qed.
Lemma kx_mulop_eqb_refl : ltac2:(zQ "50!lc!m3!jf!rb!s2>1a$3@3$2$0@2$4^1^1$1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##$Op'0h01ai001mp;2p;3g00F5j22Tg008]j31Tg0097j20Tg00GER0P0g00;\R0f0R1/21g00<<R231P11002R2P!s$0n0110000080!s#2W0o"). Qed.
Lemma kx_expr_eqb_refl : ltac2:(zQ "50!lc!m3!jf!se!t5>1x$3@3$2$0@2$4^1^1$1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##1]h01bh14IHx1h24IHx2h32oph42x1h52x2h61nh71xh82sxh93IHxh:1ih;1kh<2loh=1zp;2p;1p;3p;4p;:p;6g0097j2BTg00N^j2:Tg05Ljj1=Tg00MQj1DTg00]nj27Tg05MLj18Tg00O[j1?Tg00XYj26Tg00:Lj2>Tg05N1j1LTg00Phj3KTg00R5j3JTg00F5j2HTg05OKj1GTg00SBj3ETg00TOj3C!t:$Wj29Tg00Yhj24Tg05Pej1;Tg00U\j4ATg00Vij4@Tg00^jl:FTg008]j3<Tg003Vj6ITg00;\R0f1R1f0R2'6g00<<R33<p=3A<023p=1P0P3f3R4f2R5P1P2EIp=01451/42p=51423p=2g00`TR61322R7X76g00b@R8%12X00R91B03R:1:22%=2C0%D2R;/3;eW=g00aaR;P9P:1722R9%82R<C0%?2R=/3=eW!td$\R=f4R>/6>1655R?552#1X00R@A532?!s2$A533!s<%P:1611R3P2C01644P5C0R?1>>>%L>C0RAAK>41RB/3BeX27X56X17X46W3PAAJ>41RA/3A!sA0X3=g00GER=P@P?1H>>%G>C0R?AE>41R@/3@!sq3?AC>41R?/3?!sq3f5R=/9=R=17>>'41744R?;!uJ&A5=2?#!s2%%2=/42!s3+2#!s2'R=P:19>>R@%;>C01755RA%85RBC0P?%84C0P!uv$P>P4P5P1CAR>/3>eX97X76X6;X<;X8014@?1711R?7!tM&14@2#2/4!vs%%2@#2/4!vv&!tC$44%;4C0P9P<C0PAPBC01:11%=1C0!t:%P2C@R1/31eX6;X:8X;;X80P2M:FW7o"). Qed.

Lemma rel_lit_same : ltac2:(zQ "e0!lc!hge!jse!js0!hiv5!jp8!luc!jf!hjg0!hjgc!hjh6!se!hji1!lu5>2rb$b>2rk$1>2rn$1>2kk$1>2kl$1@3$7$4@6$c^5^4^3^5^2^1M0\0$0$4@2$5@2$3^2^4@2$3@2$2^4^3@2$2^2^1@1$9@2$d^4^2M0\0$0$4@2$6@2$3@2$2^4^3^2@2$3@2$2^2^1^4$8$a").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##'{h01bh12kkh22klh32rbh42rkh52rnp;2p;1p;3p;6g01T9j20Tg01FXj21Tg00Yhj22!s8$;j24Tg05QBj16Tg01mEj25Tg008]j33Tg0097j2;Tg00XYj2:Tg05RSj19Tg003Vj67Tg05Slj68Tg00`Tg00b@R0g00;\R1g00<<g05U:R2P1P2f0R3!s-$2R4f4R5'0f3R6,15R7f1R8,14R9'0'21454#6P1P210741095'5g05VKR9g05W\R7n010!s#$20000!s41R:g05Xm!s;1;3:X01!sy%861164R:1183R;!t?%68!t?':810;6'5P9P!t5A7,;21:55%95E7P5P6P4P5P8P3E8=327eX20X10X50W4W3o"). Qed.

Lemma rel_lit_other : ltac2:(zQ "90!hge!jf!se!lc!ige!hjib!t5!hiv5!hji1>2rb$2>2rk$0>2rn$0>2kb$2>2kk$0>2kl$0>0@3$1$3@2$6^6^3$4@3$1$7@6$8^7^6^5^4^3^2$5").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##'<h01Hh11bh22kbh32kkh42klh52rbh62rkh72rnp;2p;3p;1p;6g00XYj23Tg008]j31Tg01T9j20Tg01FXj22Tg00Yhj2:!s8$;j29Tg05QBj18Tg01mEj25Tg0097j26Tg003Vj67Tg05Slj64Tg00`TR0g00b@R1g00;\R2f5R3f2R4'3g00>4R531P2P5g05U:R5P2P5f0R6!s-$3R7f6R8'01283R91274R:'0':1987#8P2P5109710:8'5g05VKg05W\n010!s#$20000!s41g05XmR:!s;1;1:X12165:1387P6E7P8P3f4P7P4f1E4=15:eW0X41X31X20X71W6W5o"). Qed.

Lemma is_lit0_eqb : ltac2:(zQ "60!lc!jf!se!hij0!m3!t5>2rb$2>2kb$2>0@3$1$0@1$3^1$4@3$1$0@2$5^3^2@1$3^3").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##8]p'0h01Hh12H0h22opi002oph31ni011nh43kb1h53kb2h63rb1h73rb2h82sxi022sxh91ii031ih:1ki041kh;2kbh<2loi052loh=1pi061ph>2rbh?1ei071eh@1zi081zhA2z'i091ai0:1bp;1p;3p;2p;4p;6g05Z>j10Tg00MQj15Tg008]j36Tg0097j2>Tg00O[j1=Tg00Phj3<Tg00R5j3;Tg00SBj3:Tg00TOj37Tg00U\j48Tg00Vij49!sn$Qj6@Tg01E@j1CTg05[Nj1BTg00XYj2?!sJ$mj2ATg00;\R0f0R1g00<<R236p=2f2R3f1R4'?=601p=1f3R5/?3=604/A1p=3P0P3P4g00?MR6P2P1E@p=4g00`TR7%01R8#2R9P7f4R:%0:714^09!sW$b@R9%51R;#0R<#2P9P9P0P1P2g00>4R=P=n0110800030010106!s'$R>#2f7R?%54%0?31]0P4A6022P7g01TV#5R?=118f6R81>0>A1;?<eXA9P1O1g00aaR<1>0=R;%=1R>%0>R>71?eW3!sG&<\R@P;A<341RA%0ARA71?eX77X67W2P3P4P1O3P;A;341RB%0BRB!sH,X2@!sI'g00GERCP;A:341RD%0DRD!sr:7341RE%0ERE!sr/C!sI,P5!s2%C8RF%0FRF!sN$>7X3<X<<X80!sG'O4!sS-9R;%0;R;!sS$3<X99X:!sS1!w+$70008101!s'%13010010910:!s1D401021051!sn$!s4&4103101W0g05[lR?A60=2RGP0P=P0p-0P1g00>TR=g00?1!tQ$:00020000X?0RHP!yc&R2P=f9R6%C3#5%06RIP1C3b1W0W=P1O1P2P=P6%B3#5P!sA&X0GX=?P1O1!yW9P1O1W0W@P1O1%2>%=4#0?4H1P=P8%=3%08!t1'X3<!sK%AA<53!sM+f:RAA<:53%0AR!sS,57X4!xm/%2BA;!s]-PAA;:53P!sX?DA:!sX1:!sX8!y,+%2EA7!sX17!sXCFP:!xl%C8!uH+<RFf5RC!s@%C8%0F!uO-;!yz7%2;!sn+9!tM+FP!sj'9!tR-!z6C1!z6s!xQ%X;7W>o"). Qed.
Lemma expr_eqb_lit0_l : ltac2:(zQ "60!lc!jf!mrb!se!t5!hij0>2kb$3@3$1$0@2$4@1$2Z^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##-tp'0h03kb1h13kb2h22opi002oph31ni011nh42kbh52sxi022sxh61ii031ih71ki041kh82loi052loh91zi061zi071ai081bi091ei0:1pp;1p;2p;3p;4g00MQj12Tg0097j21Tg00O[j13Tg00Phj3<Tg00R5j3;Tg00SBj3:Tg00TOj34Tg00U\j45Tg00Vij46Tg00XYj27Tg05Z>j18Tg008]j39Tg00;\R0f2R1f1R2'7f0R3#839p=0g00`TR4P4g01TV#2R5?033P3g00b@R6P6P0!s3$<<g00>4R7P7n011060003001010:!s'$,10%23R8=058eW9P3O1g00aaR81107R7%33R9=059eW3!sC&<\R9P7A<123R:=05:eX14X04W2P1P2P3O3P7A;!sD3X29!sE'g00GE!sj$:!sj@4!sj>P7f3R!s4&C5!sL'44X38X88X50P!sQ'4P7!s2'C6R7=057eX38X66X7!sO1!v@$90008101061010130100107108!s1D401021051!sn$!s4&4103101W4o"). Qed.
Lemma is_lit0_true : ltac2:(zQ "60!jf!se!lc!m3!mrb!hij0>1e$1>0@3$0$2@1$5^1$3@3$0$1^2@1$4Z").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##3ap'0h01Hh12H0h22e1h32e2h42opi002oph51ei011eh61ni021nh71pi031ph82sxi042sxh92e0h:1ii051ih;1ki061kh<2loi072loh=1zi081zi091ai0:1bp;1p;3p;2p;6p;4g00MQj15Tg008]j34Tg0097j2C!s/$Qj6>Tg01E@j1ATg05[Nj1@Tg00O[j16Tg05Z>j12Tg00Phj3<Tg00R5j3;Tg00SBj38Tg00TOj3:Tg00U\j49Tg00Vij47!t1$mj2BTg00;\R0f0R1#2g00<<R234p=0g00`TR3f1R4;41p==A4012p=?f2R5=434/B1p=1P0P5P4g00?MR6P2P1E>p=3%01R7P3g01TV#5R8,=4^07!sN$b@R7%51#0P7P7P0P1P2g00>4R9P9n0110800030010103!s'$#?%54/=8]0P4A40221C38W0g05[lR:A4092R;P0P9P0p-0P1g00>TR9g00?1!sx$:00020000R<X50R=P!tw&R2P9%A5#5?181b1W0W7P1O1P2P9%@!s=+X0;X7:P1O1!tm9P1O1W0W=P1O1g00aaR:%61#0%64#2?3=1P9%6!t1,6!sN&<\R;A<541#0f3R2?<5!sU+f4R6?<2!sZ+X33X23W4P5P4P1O3A;!s]$A;2!sZ,A;6!sW3X4;!sX'g00GER;A8!s_%8!s_/86!t8>:!sW%:!sW/:!t8?P2!s0%C9#0!w-$5P4C9#2P<X90;31P9f5R<!s@%C9!sm+53X6:X<:X80!sh'O4!sr+7!sr-7!tV'P!sl'7!sl+6:X:7X;!sl1!w|$10008101!s'%23010010910:!s1D40104107102101!s4&6105102!xj%X53o"). Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_skip0 : ltac2:(zQ "h20!lc!hn8!hr8!vi1!kvd!jf!mrb!hirf!ho7!ige!u0!hge!un0!unb!tt5!hiha!hjj6!irb>2bc$h1>4segs@1$1$c>1K$2>4rest@1$1$2>2rk$b>1n$a>2sx$0>3acc@1$1$e>0@3$5$0@2$h0@1$f^4^6$9@3$5$d@9$7^9^8@3$8$2^7^6@1$6Z^5@1$3^4^3@1$4$0^2@9$7^9^8^6@1$6Z^5@1$3^4^3@1$4$0^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "#,+ep'0h01Hh12HCh24len1h34len2h41Lh52opi002oph62n0i012n0h73op0h83sx0i023sx0h91bi031bh:3leni043lenh;1Eh<1Fh=2loi052loh>1zi061zh?1ki071kh@2n1i082n1hA1ii091ihB1rhC2H0hD7__arithhE4cstrhF2kbi0:2kbhG3kb1hH3kb2hI2E0hJ2E1hK2E2hL2H3hM6__sat4hN!s/%5hO4__x1hP4__x2hQ1ni0;1nhR1qhS3sx1hT2H1hU2H2hV!sZ%3hW4__x3hX1ai0<1ahY1pi0=1phZ2kki0>2kkh[1xi0?1xh\2H4h]2H5h^4__ffh_8__varmaph`5__witha1mi0@1mhb2b0hc1ei0A1ehd2l0i0B2l0he2H6hf2Hahg!tT%6hh4__x4hi1ci0C1chj5cstr0hk2hii0D2hihl2i0hm2k0i0E2k0hn3lo0ho1vi0F1vhp1wi0G1whq1yhr1Ki0H1Khs2a1i0I2a1ht2a2i0J2a2hu3acchv2bchw2bkhx2n2i0K2n2hy4resthz2rkh{4segsh|2sxi0L2sxh}2wni0M2a0i0N6a_basei0O5a_offi0P2bsi0Q1di0R5deltai0S1sp%0p%1p%2p%3p&0p;1p;2p;6p;9p;3p;7p;4p;5p;<p;Bp;8g00eTj1zTg059^j1OTg05\Qk20dTg01:AR0k20!sE$]bj1GTg05C9j2FTg04QLk10`Tg05Z>j1\Tg00MQj1KTg00g4R1j18Tg01mbR2j17Tg05Slj64Tg05_6k10RTg00f4k10M!s:$Vl9:Tg01D[j1pTg01E@j1g!s/$^k20fTg01jZj2<Tg05`mj3;Tg05b:j1>Tg03jZj70Tg00XYk204Tg01T9j25Tg01FXR3j22Tg027^j2BTg05cEk300Tg05dUj3~Tg01=@k30!sC$ehk20ATg0097j2uTg05g6k20=Tg008]j3ETg00hSR4k10xTg00nJk10!v^$Icj3=!tD$;j2fTg05QBj1!sK$Yhj2rTg00ZFk305Tg00`9S00j2!vf$8YR5j29Tg05DJk20gTg05hKk10I!s0$ik40eTg05iLj4lTg05j3j1kTg05>Yk20!v8$2ak10cTg053?k10b!s0$]k10aTg05?Uk203Tg056:k20_!s0$\k20^Tg057Hk30]!s0$gk40\Tg05GAk20!tb$Gjk30ETg05HSk20[!x-$Tk30DTg054Hk20C!tc$Xk30!xj$gjk10Z!sD$kk40!xs$>=S01j2@Tg05k;j6q!w+$mj2tTg05lPk506Tg003Vj6ek701Tg05mej7TTg05[Nj1}Tg00O[j1ZTg00Phj3_Tg00R5j3dTg00SBj3YTg00TOj3aTg00U\j4cTg00Vij4STg01>Ok20@Tg01eMk10NTg05o;k10!s_$9Qj6|Tg060Kk20XTg0613k30W!s0$Wk20?Tg062Hk20VTg00mNk10y!z`$=j2w!s~$0k20U!sM$ik20TTg063Pk20STg0647k20F!s0$]k20GTg01?^k30QTg065Ck20;!s0$eS02k30:Tg066Im<0PTg05RSk10w!s:$nk10vTg01@mk20uTg01B<k20!y~$nlk30qTg01Lgk20!|e$N6k40oTg01OEk30LTg01PTk20KTg068Fk40lTg069Rk30kTg01SYk40mTg00kNk20n!~5$Ek20jTg06:am<0JTg06;FmB0i!y}$7k40hTg055Vk70sTg05@8k80tTg00;\R6f0R7g00>4R83Ep=3f2R9f1R:%O73=p=Jf5R;f4R<f3R=P9H0l?;:7p=Rf6R>P;1f<=P9CS!s;%H%77,2:p=L159:/r7p=[B0k<=9!sF%?g06;lR??E:7p=6AE6:7p=Mg00<<R@9E67p=Ag00b@RAPAP:P7H0m-0n9p=V15:7,r9p={15:7-0j9p=X15:7=E6@p=I12:7,F9p=^1F9:=!sr$Q!s;$29p=]1uA7p=Cg00aaRBPBPAPAP1P2P2P=g06=9P9P:P7N<0Jp=o!sF&A!sF$;P<P=!sE/n!sC&!s$%3P7P:P9P3P=P<P;P>f7R3f8R2f9R1NB0ip=mAEA:7p=W!sW$5P3P5P>!s~2Pp=yg01TVS03/97p=DPA!sC%H0hp=jPAP:g05=6P7H07p>02!s6$;WR5g05<6RCPCg05<VRDP7g05=]K0sp=iP=P5PCPCPD!st%L0tp=hP6!tI&@P7E|p=sP6P@P:g00?MP8!s:%vAE?9:/t7p=11u?7p=N%\7=E68p=bg05U:!tI$Xm!u<'Eep=U!w9$59p=PQ039EA7p>0!ub+!y?&>0Hg06=]g06>l#zg017aS04Q04#zg06?k#z%O=00d;#3Q04P420zAAREP6%G7RFP0!vf$6P7P6P61F:7S05AJ:72P@n010!s#$20000n200110=00012010S10AP4PEP6P!sl-Q05$0`!sR7RFQ04!t7$8g01U4RGP6P:!t4$10<!sP':10OS06PGP6P9%\:S07!sG78P!s$,!sQ$!sn99P8!s=$H000:3010<10G10F2!s1%;!s9&;1072010510D2010A10@3!s-%!s9'<10;4010I10810J10K!sb,C!sG'n10110?000210!uu$!s85!wL%?P:PGP?P9P5P?Q03#KRHf;RIf:RJ#8RK#7RLP:P7%7=E4PJ&0R7RM%8IRNP=P1&0M6ROERf?RPf>RQf<RRPHPIPKP1POP2M9:S0:Q!s%$n!tO'41010Q!x?%!vJ4>!t\$:g00`TRS!tg'!sz$LP9P:g01VBRL#pRT#gRU%pTS0;#p!s$&gRV+0fRW,<7RXE4A;H1O!tL%P6P?PPPHPI%>K!{@$=F0A;H2O!ti%!yv-RK!ty1R!sB%PKP6P?fARKPHf=RY%8RRZ#>S0<!{m$;!su$JOS0=PKf@R[PQPHPYPZPIPOPJ!v$$>!t72\P!s$%6P?fBR\PHPQ%8YS0?#>R]!|m$>!s|$IOS0@P\PK!u8$QQ0?PRPOPI!s{$A!s{2^P^!u6$400081010B101013010!y4%3!s1D40102!z1$110A!s4&7109101!wx-1!wx-9P6P?204H:S0BP6P?157IPSP?P=P6P?%7NR^,2R12:XS0C'5PJP=PRP:PNP1POFHR_P6P?Q0C/5RP[PPPYPHPRPNPJPOP1!u_$Dg06A<S0E!~m2!s40!xV$!~k$1B[<!~m,%8QS0F#7S0G,2PS0H12<:S0I'5!#3%25106P8!|>5P_Q0D!t;=\>!t;/[S0J,LKS0K12>:S0L!t6NRP;PQP=Q0?PIPOFHQ!xQ4_P!s$%!tM+fCR_/B3!tP/KS0M#7S0N,2\S0O123:S0P!tUNYP>PPP<Q0FPRPOFHP_P\P[PHPPQ0FPYPOPR!w]$Q!tk2`P`!z>xE!z>%!}e1100!s74!z`66P?%83R`,L2/579[:2P4%zAS0RP?B00I2`%82Ra=~37?;>OQ0E!v/2P!w^$IP1PHP2P`P>POP;M9:R`!y$2`PYPRPJPHP1PaP3POP>!vD$SP`PQPYPIPHPJ%81P2POP3!sA$T!|O&!|;%!#5D$RP^P9P:PXE4PIPZP<PJPOD?Q0DQ0D!xf$[PHPR%>N!sM$<F0PJPNP=P1!sM&!w[2N!#5%8N!sq$\PHPQP]P<P=P>F0PRQ0?P;PI!sq%!z;3]P!s$%6P?P_!x}&#>S0UP;P<P3F0PYQ0FP>PR!sf%Q!sf5!#4N~!xl6`!#<i81!s1$43!s-&!#<iG1!#<i1!sb+!#<i&1PJP1P3PHP>%8;P<POP=M9:'6]1P>PG!}e%B0B9:7#GR`!#A+0Q!#A$$Q!#A$FS0V!ss%P`PF!}w7!#>06!z$$!yz'QQ0?#7S0W!#=v$<E4PYPMQ0FP<PRPOERQ0A!s%%!#=QIQ0D'6]1^oS^pBP7!tm%20A=9S0X@0B!ui>K!uiIY!uiU%\<S0ZP61u67S0[%\;S0\/M7S0]P6%\3!s1$^!v1&_%8\R`#7P2P3%7>R]E4P\PM%8_S0_P>PKPOERfGRNfFR^fDRaPHP_P`PKPOP[!~'$`Q!s%$!vP8Q0`'6]4P:%\>R`#AS0a20=37S0bAES3HS0cPSPH!uZ&S&0xERbP7PAPbP7%72Rc,21Rd9VE1&0OERePe!t6$6000300!ui$!s'$Pe!s$/!sJ$N!||'610!#EF%010M!|f,!s1=4010L!{l$;!||&L!||';Rf!x=4%ONS0d9=:7!xBIe!uf&f!{,N!wt$fERf%8aS0f#7RgP:P1PcE4PaPM%8fS0gP2P_POERRhfIRifHRjP^PHPfQ0fP_POP\!ww$hQ!s%$!ww:h'6]1XFSP6P6123]R],F3AJ3]_!uS3!td$6P5152aS0iQ0_#7S0j,2aS0k%73R],22Rk3{Rl1fa2#xP6P5Q0k/52?Xkag05VKS0lg05W\S0m!#@r?5P?P7P!u0&!u3@XB5PlP6Q0[12fgS0n/5d9[1f/M7P615INS0o%8^S0p#7S0q,2NS0r1LIJRd'5Rl'r/M7!t=$6P5P:1fjRS0s#xS0tP6P5%8NS0u#7S0v,2jS0w/5RS0x1LRIRm;XjQ0lQ!uABNPM%8jS0yPIP^!|l$LRnfKRoPiPHPjQ0uP^POPfM9:RpPpPp!ub8/6p];P:15J^S0zQ0g#7S0{,2^Rq%71S0|,2JRr3{Rs#APf1fNIS0}$0RQ0pP1PaPOERPofJRtPjPHPNQ0pPfPOPaM9:RuQ0o@05l7Q0o#A%Al'`Q0015RjS0~#AQ0w/Img00>TRmP715QtS10#A%8tS11#7S12,2oS131LPQ'IQ001I:7199:[Rl19:7Rv1I9:Rw[19=9\w20g:7P:!|:$!uS%1!vH$000XaAXQAS14Pl^aA^QAS15P7PKfMRlP9O319KlS16Q14Q15P7fORwfNRx#8S17#7S18'2S191L_\RyP=O3Q19/9y%7_9^aa!y;%Lfa=Qf7P61LN^Ry=QN!~5$P:%7NS1:,2jRzfTS1;5JjR{!{j6m]1]<P:%7f9^^^R|#AfSR}9JNy#3P{%37X96S1<P7PjPzQ1;Q1;%8}S1=#7S1>'2S1?/9zQ1;%7}R{%gLS1@3]/9zRyP7X[AR~&0IvXqAX[AS1AQ1?Q1;P~Q1@,27!s:$BP{O1S1CO1Rv'2P~!s$$APAg06BI12:7H0e#C!vj'D!tR%Q1;#CQ1>PvP~P~%77#CX[BS1>Q1=Q1CQ1BP}P{%C{CoEnM:mPzP~Q1:O1,2jR{%C{1Wz{eGyP<ClS1:PyQ1;#kR{Q1;#7S1C#DRz%kiS1=%7i#DS1Eg05:kRv$0MS1F%zvS1G20<A9S1H&0cAS1I7j:&0bAS1J&0aAS1KQ1K203ALS1L203ATS1M+02'iRT&0OCS1NPTChQ1K00_DS1OP7P91u6@20^79#AdQ03>0]A:H0\S1Pb^b_b`XOAXPAS1Q197:19:9[^OA^PAS1RP7fXRDPnPJO3bDbjbEbIQ1:PyP{Pz!v5$Eg00h4Rz#8R{#8-09A209A{209Az60EA60EAg05KW+0[Q1F60DvS1:Q!u_%<Q1I7j920<A=S1S7j:Q1JQ!u[$Q03-0CAQ0;-03ARv!u[$S0;Q1N!sG&1LQ1@-0CA:08Av608AS1TQ1M&0ZL-03A608ARL!s^$!s[%PAQ1Lg05BRS1UPLH07'iS1VChChQ1OQ!v,1XWAXhAS1W%D=Q1@9]:<129=S1X'912=<,@9[!vF&^WA^hAS1YP7fWRL#7S1Z%7oS1[PnPDP9P=O6!v['P:EqCsAE6@8RvP6p-0P7g00?1S1\Pmn01103!|X'Xc6Rz/v7S1]Pm1tm7b0S1^b1W1W<%3|Q1^X1vS1_W<!s^-100P7PQO2b<b9bKb0bJb0WKWJP:P7O2!#3Y/!s/&b;31W;%3sQ0r/5I?XdN!~N$!#8A&7!#7i6S1`PjPM%8iS1aPRPNPOERRsPlPnPtPHPiQ0yPNPOP^M9:R|P|P|!#7\9|P7%NpR{P{!uu1b9W;!uO3O1b;b9PHPaQ0jPHP2P]E4!s5'2P]I06EeW1P2P7P<K01b4W4%3`S1bPS!#B1&P!#B,'AVE2kP!#Ax;Rk!#Az~!#Az1]!#Az5^S1c!#AzK1d!uW&]!#AzLQ07#3S0!#=t$HPfPgP9!#Ax%!#??F]4]1P3!tE&kQ!#CL'k!tPM%K:S1e#bS1fP!#f?&!wb'Id!wb>d!#Ja7t!vIIg!t8&d!twM!t9$:P@P8!#fD%!ta4#3S1h!vh&iQ0y#7S1i%K9S1jPY%7RRdE4PsP!{q@!vp$9!#is$JrQ1c9=Jr!#<P4Q1]Pm!t9+1iPHPYP!t,C?1|7b0X4vW1g05[lS1kAE688Rs!#Dz%tPM%8oS1lPQPiPOERPwPxPnPHPoQ11PiPOPjM9:RdPdPd!u8:dXB5RrPxPlPoPHPtQ1aPjPOPNM9:Rk#NRh!s<&#7S1m%g9#KRcPQ%7YR!~$%tQ1mPcPQP]1u68RcFTCUX4sW1WYP7O1Q1kPrP!sk&m%}9#KR{PQP!sc-!s5$P!s_'X1s!s`%!w{9!#5l$W4W1X>AP7O1%Z:S1n#bS1o!v5&^PMQ0uPJPf!v2$uPuPu!ut:uXB5PtPiPNPHP^Q0gPaPOP_M9:S1p#!s;&{%Z9S1qPJQ0|!u+$^Q0{Q!s7&!u-%W4X1sX6BP7O1g00<\R{A_=9:S0|#bS1r!uy-A_<=9S1s!uz0Q!s6%!ss/HSXGSW5!#r-$O3Ad=9:S1t#bS1u!su/d!su$v!su2v!su8X5{!sv'g00GERyAY!s}$w#bS1x!s}/Y!s}$y!s}2y!ttCa!su$z#bS1{!su/a!su$|!su2|!tt:y!sv'!#w>&CcS1}#bS1~!xR&nPM%8lS20P[PoPOERfQRMfPR]PxPHPl%8nS21PoPOPtM9:RrPrPr!xr:rXB5S22P]PwPlPHPnQ1lPtPOPiM9:RT#NS23!s=&#7S24!#v@'cS25P[%7PRC!uJ$nQ24Q25P[PC!uJ/FSX6BX=BX8!#x8&7O4!uO+SS26#bS27Q22Q!t7&!t2-SS22P[P!t//2!t/36BXAAX?!t/1!uc$A010811!#;B1!#`<K!#;B:P=!}:%!#>'/1P7O1b4b9W1XoSXpBXZAXFS!}f%!sP$S!#`n&N10OXXG!xS+!#_G%20@:7#GRc!#<H5RS28!#<HK29!sw%PcPFQ06!#_LM!#fN0Y%7ZS06!#fR&Q0@Q0>Q!#hh$PKPHPYQ0<!#fI&Q0=Q!#s23Z!#f@8Z!#e^-U!#fA&A;HRO!#eQ4ZP!s$%6P?PaPHP[%8PS0=#>!#f9&A;HYOPaP_!tb$[Q0=PQPOPYM9:S0<!st5!#fG~!#fG4Q0T'6]1^QS!#b;,9:S0@00@7#GRZ!#>W7P!xXI:!xX&ZPFP@!#b:J=S2;P6Q0[Q0Z!#YJ$M`7!xh$;!xh&\Q0NP2P3P!#z-$[OP^Pf!ww$\Q0MP[POPP!v}$NQ0!#kU$^!sB&#>S2<!sa$!x@%POQ0N!wJ2`!y+9`!so$j!#GD$_#>S2=PJP1P2!so$KOS2>PjPNPf!sH&P\POPKM9:S2?!#r,4!s$$6P?Pi!#^}%#>S2@PIPJP1!sw$\OS2A!#D]$!sa2!y7~1PfPaP\PHPKQ0JPPPOPQ!u8$B!#e;$Q0\#A20=>7AES>H!#e0-!#I}+!s2$3&0N7S2C,21R`9VE1S2D!#Iu5;!u=8!#IuQ1!#5Y21!#Fg<S2E!#KLC!tUlS2F!#6'5fS2G!#6'L!w#&Q2F!|R9S2I!|U7!|>$!#fS%!#O5$9P1PXE4Q2AQ2?Q2?!{5-2=!sD$2F0Q2>Q!zm4!#5}?t!#By%#>S2JP<PIPJ!z~$_ORZQ1p!sq2cP!s$%6P?Po!#aM%#>S2KP;PRPI!s`$aORcPu!s_2CPC!{^~1!#m]$1XF!#R5-;Q2C,239VE3!zy~!yJ4L!yJ6aRC!yIMM!yI'L!#6uL!#T~0Q!}c~!uh7Q!#St&!u&S?P:!#Ss,HPJPXE4PZ!#Sp$!#6^,2@!sC$9F0Q!#6T6g!{H9g!zf-2KPHPRP<F0P!z\5gP!s$%6P?Pn!#k&%!#7w$HPY!$45%fORgP!{v2S2LQ2L!{?~1Q2?!#{n%6P61F1`A=1`C!#h35A&0N:S2L!sN$2I7RC,FIQ1c9=I!sU6X>AP71<:WS2N&0Y:S2OE|!zl$2N,2JRC,FJQ2G9=JC!#r3;<9WS2G,2IRC,5q9[I^R`1f^I!#q}$15qI?XC^!#oVE!#K:$gPuPu!ww4%K=S2P!w{7!xa8!#Q&%`!#?f%r1<=WS2Q7PR9[RN!#r@%QiR`Q1i,2iS2R1<;WS2S,2QS2T'5RC!#r>3tP!uH%Q1m,2tS2U/5P1<>WS2V,2PS2W;Xt!u\EA;HjORqPkPk!u[$x!#UO&>S2XPHPP%K>S2Y!z%$NOS2ZPk!ufHk];P:Q0w1<<WS2[7PY9[YjS2\#AA;H^OS2]B05`C7%A`%AC!#q_$IPtQ2UQ2W'IPmP71IKnQ21#7S2W,2lS2^1<1WS2_,2\'I!#pJ&PaPw!#pa$aw!s:'%8]S2`,LMS2a1<YWS2b,2^RCP=O3Q2a/9C1<QWS2c9^NN!w[$1<PWS2d,2j=Qj7P61<KWS2e!vx$f=Qt!#pj%1<\WS2g,2oRCfVS2h5JoS2i!#pl<1<[WS2j9^iiS2k#AQ2ffUR`#OS2l5=t#3Q2iQ1<P7PoPCQ2hQ2h%8`S2i#7S2f'2S2m/9CQ2h%7`S2nQ!#pq$CS2oP~Q1AQ2mQ2hP~Q1BQ2nO1S2mO1S2p!#p\&Q1D!s{%Q2h#CQ2fQ2p!s>%>Q2iQ2mQ1BP`Q2nQ2n#C!#p@&CPC%CC1WCC!#p6&2mQ2oQ2h#kS2iQ2h#7#DS2p20XUVS2fQ03/@U%DV!s/$WS2q[[S2r%DURCQ1\B0WUV:UWfS2sQ1\%DWS2t[^fCS1\20?^WS2u%D^Q2t1<jWS2v#D[[S2w20VNWS2x&0>WS2y$0yS2z1wjWS2{-0UWQ2v'2,Wj[S2|20TjWS2}Q2q1<iWS2~#DQ2~/@W'`[S3020SiWS31Q03,@WS321<tWRC,@WQ03,9C!sL$320FtWS34Q2y1woW$0>[S3520GoWS36Q2y1<nW/Wn[S371wnWS38PA1<lWS39PAQ1QQ1RP7fcRCPDP_O3bDbBbRbLbUbTbCb0bVbMbNbEbIQ!vq&iQ2p!w^$rQ!v;$Q2uQ2wQ2xQ2|Q2}Q30Q31Q33Q34Q35Q36Q37Q38PAQ!t@%WQ1YP7fbS2p#7P:PDPCPIPRO6!tI=!#oD$PvQ!#ne&Q2k#3Q!#naf71|W;Q2\#3Q2R/5QQ2T;Xi!#nf&Q1`A;HiOS2TPdPdP6P?Pw!#c?%#>S2\PHP[%K3S2kF0PqPd!#3qGdP7PhPh!#nUM^Q0{PHPIQ2G!#`i'!s4$I06Eeb1W1XdA!#cN$]Pm!#Ef,2J!s]$1qF0P!#E]4Q1p;17b0X1v!#aL%!sf,!#6V$!#6Q$Q1sF0Q!#6I4?1k!sd&3SX2!#`F-!sn;v!snjy!snIy!snC|!sn\]!#_S&>S2iPHPKQ25F0Q2TPT!ss3T!ss&:!#_I6!sx3!ss'2!ssB!#_5~!#_587O1W1P3!#uY,Q0\!#GX2!#RY,>Q2C,229VE2S0\!#Gn~!#Gn2o!#r?=h!#RU~!tW1RCQ!#KJ&PC!#IELQ07!#Ql4=!#Ql?=!#Ql=C!#IJ8C!#3+0;!#Qg$!#3'5RCP!s$%!#E%/>!#Q]$P!#QX~!#QX=4]1P>!vy&hQ!#Us&Ph!w+N!#xh2!zr$1!zr$IS2>9VEIS2A!zu~!zu4M!zu@!#Rk4jS2m!#RlK3:!vBWh!zH$I!zH&jQ0vQ2PPY!zI%]PpPp!#OR,2@!sC%RF0P!#OI3Rh!zF9h!#7</%K;S3;PPPQ!#7?7RhP!s$%!#<w+2\Q2YP[PP!#<o6R!#<U&!zKz/6u!#|I%!#5Y+2!yY$JS3<9VEJS3=!yY~!yY33>!$%d'Q3>!xWO]Pm!xY4PH!xX=!sB$!xW^PH!xSQPH!xR~!xR@?1u!$$n&Q1k1vz:S3?!vL&Y!vL&tQ1m%g<#KS3@PPPXE4P!#QX22XQ!sB$!uj;!vS?!#>X&%g>#KS3APKP[!#>]7!vY0MPHPlQ21#>Rh%g3#KS3BP\PKF0A;HtOS3CPr!#7b~!vi7!$+Y$sX1v!$&V'Q!vl9}!vl$D!vl>D!vl=!#;:?!vl+}!vl$E!vl=!#;@-!vl$Ph%}!vg$F!vg%Q!vb~!vbL!#9$%103011110=!s'$!$,X3Q1oPS!w-$!$6V&!$+c$<S3GPI!w+$cQ1pQ1p!#>X/Q!sD$:!#>Y8!#j0?!#31&%Z>S3HPYP=!#357!#y/-l!$4R&>S3I%Z3S3JPQP<F0Q2]P|!#xr~!#?O6h'6P21vz=RZ!$5,'NQ0q%Z;S2]PRQ2NE4!#_V5Q!sC$1e!#_TK!#3i%!wn%PZ!#J-%!su2n!su7!s`&@BP7O11vz3Rc!sd&!#67&%Z1S3KP[Q0|!#6<6?1d7b0!#N63P!sm3Q!sj$1t!sjfw!sjEy!sjCz!sjN1vz1Rz!sn&!}}'ZIS3LP\Q1}!}|8?1r7b0X:SX@!$/;4!sr2Q!so$26!so?@!#NlA0!#NlrW4!#U'-r!~X2!$7H$>;<S3M!#6`=MPPP:!#6`8!#m@?!#6`&A_23>S3NPKP=!#6`8!#mG-!vm&A_123S3OP\!~W$!vq5RgPg!~W~1/6|PRP!~Q,oQ12A_3>;S3PP[!~S$Q!#[V32\Q!sD$!~T$!#[OH!zm&!~T2!su2n!{O>!xL%!|1+}PHPwQ17#>RgA_IJ1S3QPa!~V$A;HnOS3RP}fRS3S!wg$wQ17PlPOPnM9:RC!t03C!|Y,7!~15!t:$PgQ!t0$1tF0Q3RP!sj`w!sjFy!sjBz!sjP!}}'`PHPMQ2`#>RVA_YRIS3TP^!~x$A;HxOS3UP`Q1;Q3S!sP&PwPOPxM9:RU!t93U!#3=%6!#3=<!t>$PVQ!t4$!#3=$UP!so96!#3=~!#3=<!$A|2Q1u!#3G6d>;<S3V!#3G=V!#3G;S3W!{{8Q3W!#3I0d23>S3W!#3I;S3XQ!s%'!#3M/d123S3X!#3M;S3YQ3Y!#3O~!#3O7d3>;S3Y!#3O?Y!#3OpY!#3OVPgAdIJ1S3Z!#3J%!~@_Z!#3+eZ!#3+eZ!#3+aPVAdYRIS3[!#3#%!}q=!~bJ[!~b~!~brx!~b7Y!~b$\!~b>\!~b>]!~b:]!~b1Y!~b$]!~b>^Q!s%'!~b0Y!~b$^!~b>_Q3_!~b~!~b9Y!~b$_!~b@_!~bq_!~bZY!~b$`!~bf`!~bf`!~bf`!~beY!~b$a!~bka!~b~!~bg!#uT,{!~b7a!~b$b!~b>b!~b=2!#VB8Q2Z!~b1a23>S2Z!~b>cQ!s%'!~b0a!~b$c!~b>dQ3d!~b~!~b9a3>;S12!~b?!sD$!~bm!su%!~bVa!~b$d!~bfd!~bfd!~bfd!~bea!~b$e!~bke!~b~!~br~!~b2nQ24P3!%[f$CcS3fPKPXE4Q3CPTPT!}|0Q!sC$:!}w8Rq!{;8PqP6P?!#N:$xQ20#>S3gP1!$Vz$CcS3hP_!%RN%oOS3iQ3SPM!{[$xQ20PnPOPoM9:S3j!t=3P!s$%!y/-!$W-$P3CcS3kPa!#37$!y84RqPq!#35~/6dPQ!#35,lQ2W!ue%P;CcS3lP\!#3:$3iPrPr!#\y0lP\Q1e!#5?7!#3:9r!#3:5!su1n!#]p@!#3:/!{7&PR!$Yy$CcS3mP^!#3?%!{A;!#ap;!|,+mP^!#3?%!sjbw!sjFy!sjBz!sjP!~I'LPHP}Q3S#8S3n#>S3oPQPYPRPICcS3pPj!#Vp&]OS3qPLQ2hQ1;!s[%nPMPOP]M9:!|4$!tD0q!#c/+nBXS!#3l6!tI&oQ!t5$!#3m$!{'%!sp5!#c0'S!#3m~!#3m3!$mU7Q27!#3r>SS3r!#3r>r!#3r;S2T!#?\9T!#3t-!#3o,SS2T!#3o$Q3iQ!#3S2S3sQ!s%'!#3W7SS3s!#3W;S3RQ3R!#3Y~!#3Y?SS3R!#3Y>R!#3YpR!#3YbSS3C!#3YeC!#3YeC!#3YeC!#3Yc!#3O+SS3U!#3O%!~@=!#o;'!#32AU!#32FlAXm!#32~!#o<8!$@IE110;31!t/,!s1C41!tE01!$xX=1!$xX3:S!$xU51!$xU0!sA$!%Xt+Q9:7#GS3qQ!%X;&Q3qPFQ0!%X=P6P?Q!%hc'QPSP?P<!s;%HQ0C'5PYP<PPP:!%cq'S08!sF%C/5PQ0QQ!%hBL_;!%t1-OQ!%h0NQ08!$xB3!t&/f3!t&/kQ!%g|OPP>PKP=Q0JPQPOFHQ2B!t81S0LQ!s%'!tD/^2!tD/nQ!%gkO[P3P\P<Q0MPP!tD$!$uX2S0PQ0P!#7~w!%gW'!%cH-100!s74!$zH6!%]`$?B!$zK,Q0X@0Q!zP$0PQ!%\z&Q0PPFQ2!%vqKZ!$`}%]P6Q0^!$:r-!$u$-!$j3~!#38+!v@&!$v,%!%\:Y!tUn;!$kb,;PFP:!~EJ!%t%%1!}k%i!$IP%!s3$n121XS0i'5P_P3PfP1Q0fP\!~D%n!sW&/5fQ0h!~DNi!{z0w?PR:!~CMn!$m&3!t%/oJ!t%-2U?PQ!t%L!uT%}Q0pPaPOJ0HS0}!$/32S0nQ!s%'!tE/nI!tE-13?PP!tE8S0i!tH8^PJQ0sQ0uPf!tH&s!$n>4;Q2;!~H~1!$NV01!tA&!s:2!$nc%!%#H$a!}6-3!$S]/!$SS~!{_3!}3~!}3M0\!$OI'Q0\!$FUL20=2:AES2!%'$>1Q!$OL~!vn~!vn^PQ!$Ou&Q0P!vnM!#@<,Q0zPSP?P!#5-%r12IXS0z'5Q0}!sF&/5NPu!#4gA!~H2lR!~H-24,2nS0n?P[!~N:z!~N8NPIPiPYQ0yP^!#6J$}!$>z2S0rQ!s%'!tN/xY!tN/^?PK!tH92^!tH8jPRPtPQQ1aPN!tH%r!#jN30BQ0B!#3p~!$C+0100!s77!%'k/Q2D!$PE+2D!%%c\!|V~!{&42A!$X`5iS2D!%r<LB!ui'A!{iQ204HHS2A!{N%o!%&]%!s3$w12RXS0o'5Q0s!sF&/5jPp!#=WMn9Q!#:h8Q!#:W4!z{0<Q!zV9Q!zE62^Q!s%'!sj/w!#JA-20#7S2^,2xS0s?P\!#>'LiPYPoPPQ11PjPOFH!#nn2S0iQ0i!{l~1!#?B/100!s63/6u]1P2!yP$2>,FIQ2>Q0d5=I!%+B6Q!%+>&Y7S2>,FYQ2>Q2D5=Y!%+A9Q2NQ!%+9/R!s^$R!s^$m5=R!t466P@!wQ$7!yN$1!xJ$Q2UQ2Q,2QS2>'5!#4\%Q2>/5tPk!yjCk!s6A/6kX96Q2G9^YY!#Ip$2>=QQ7P6Q2S,2[S2>=Q[!%#/%Q2V,2K=JKl!u18?15\xS!tn&0s1<3W,2\!#F[$nP[PxP\Q20Po!x|$!#FX&xQ3j!u;B!#`93Q3j'6S0i!%$<$Q2[9^PPS0s#AQ2>=J[n#320;KlQ161@lK15KlS2>40:!v[$Q0219_w1@w!&9X$!}m%2a1<JW,2fS16'5S0oPwP_PMPfQ2`Px!u%+16/5MPU!w=CU!w,3UP:19a]Q2aQ16+0;!s/%'9Q16Q2a'@Q0o40:Q3S%8M'LS0o1<IW7P^!t}$Q3n,L}S161<RW,2NS2a'9!sh&!yF%:P}PNP`PiQ1;#8S2aQ3S!#9t$P!uT%c,2iS0L/5`S08fYS0OPDQ2hPHP`Q2aP}POQ3SM9:S0I!wTC0I'6P:Q1?Q2b,2jS0C'9Q0PQ0IQ0LQ2l5=iQ1<P2PiQ0L!t,$#7S2l,2`S3qQ0L'9Q1CQ1@5]`!s4$S3i!%+E$3q!%+B$1CO1S3qO1S3t,2`!%+C'P`P`%C`Q2lQ3t!%+?'aQ3q!s\$;!s}$C!%+@'!#V+'#C!s-%'WeGyP7ClS1CQ3i%k!t_$2n#DS2n!%$]-20?\WS3t%D\Q2t1<aWS2l!%'e$t20V_WS3uQ2z1waW!%'X$l'2,Wa[S2z20T!sT$Q2q1<fWS3v#DQ3v!%'X%2q20S!s<$Q321<^WS3w,@WQ3wQ03'9'`[S3220F!s?$Q2y1wN!%'U$0320GNWS3xQ2yQ2v/Wj[RWQ2{PAQ2~!%'K+Q2pQ2hPK!%'K']b\bL!%&$/CQ!ut$Q!uq$!ul/Q3tQ2tQ!uQ$Q!u8$Q!tv$!tl%Q3xP!t?0!%'J%a#7P:Q2hQ2p!%'I/!tG6P1!%'I,31WUP7O1Q0CQ1?'@Q0L00;`Q0L/9`Q0L,@`Q0840:Q2d,2tQ2h'5!{s%2j,2oRW/9L1@L!$DX$:f]f\fZS02PHQ0O%8DS08PLPOQ2hM9:RW!{:4/6WP:Q2e,2nS2h/9D%NWWL!t_$2h,@DQ0E=E?WQ2g,2lRWQ0O5JlQ1<PRPlPWQ0O!s%$8#7S2h'2S0L,@WQ0O%7DS0CQ1@3],@WS1?PAPAQ01P~Q011@:7$0I!%~[$PWPW%CW1WWWe!z]$O!{c%0CO1S0LO1RW!%4~-!t?&O#CQ2hPW!{d'08Q0LQ1BPDQ0CQ0!{c,N<0PP<ClS0LQ1?Q0O#kS08Q0O#7#DRW!%13^!z$%ffS2hQ02Pf!z&+e!xc$Cb0!x_$g!z&$!tM&8P!tA`FQ1GQ1HQ!%|v/VQ1NQ1V!%{h912:9,@7Q1X,@:!%{T+P7P:!y[$hPYO4!u/=PY!zj-'t!y1%n2002!%0l$!#@x$00011000bbb9!{5%!sI31!sI0TP7O11@]a%NU!s3%!sV80!sV'1W<Q0s!$qR%Q0i/t!%+$$!%4b59!%4b$Q2A&0wH!%2/8Q!#F-$15YiS0i!#Cz+Q1q,BlQ!#Mb8Q!#MQ4!s6C!$hn%!%2p4!tO&Q2>!tK/s,BM!&OA-wS0},L]?Pa!#OZOoPPPlPKQ21PtPOFHRW!#tJ2!s6C!#tj%!%3J>!u89v,BM!v]:P!tT~!tT2y!tT~!%4n6!tT9|!tT~!tT>15_wS0z!tX-25,B}!#d6-o?P^!yh:o!t}8lPKPwP_Q17Pn!yh&!#~51!s6C!$9@%!%7_C!vi'!u712,B}Q!tj:!tY^!%8E~!%8E>1P7P:!%8E$1W4Q1b!#`]'!#`i1!#v=J6%\2S0\!vQ$7Q!#d{:X96RWP6P8PWQ0`#NQ0\P:Ee204H2&0v2EeW1!#xf4P9O2!#xh%wB!#xkG!zW&!%lh&u:7#GRW!%la7I!#WCH\!sr%PW!v2M1F9:P6Q0[AQ=97P6AQ;<!&@q&OYS2;9=>;!#N|8Q0W,2Q/5>9[3QRWP4Q0RP?Q0?:00KQQ0F=~Y7?;R!&\,8!&Y?3Q0A'6S0A!%Oy%F<=S0?#AQ289=;<#3Q06,2Y/5;9[>!#Q1$1MW7P6151[S06Q0=,L[/52RW!%U\$!#LU$!tc'J:00aKQ0M=~[7?;P!tc:!#y;2Q2B'6!%TT$H/539[2PS0H#A!s~+=:00_[Q0J=~P7?;Q!uc;<Q06@05W7Q06#A%AW!%T{%JKQ0K/I1!%Ty$R_Q0k/IR!%Te'PP^!%Te$P^!s:'Q0wP[P=O3Q0w/9[Q2D9=\K!#EA$\PKPiQ2R/9K%7jRWQ1@5]i/9KS2D!%Ri%RP~Q1BPWO1S0kO1S0K,2i!#MI+iPi%CiQ1iQ0K!#Dc'yQ0kQ1BPjPW%CW!%R_&KPK%CK!#M8$RWQ2D!&A;$!#Cw&PnPfP;O3bDbEbIP!sG/:Q1GQ1S!&A$$!s+$!#C'&!&@c/TQ!&CW%!&@B,Q1UQ1MH07'i!&@;;%D9!&@5$=/991@9=!&@+,P7Q1[PaPnP:P9O5!tk&!#CC-!&>gNQ0H#3Q0<#N!%M_:!#Bq$?!#Bq'A!#BqDW1XkAX=A!tK%!~}'r!~}%Q!~CWQ0S#NS0SW1XaAXcS!t$/B0q9!#4$9Q2;!#dGJ!tbW:#N!ua'XcS!#5e2p!ufaW1X}S!$0Q+!si%!#:[%H0o!t%$!%{i'!t%P>#NS0>W1XxSXtGX@SXsG!$5j,!$1c'L!vu&!$1b'PWPFQ09!$1aO!$1R$!$<o$PQ0G!&i{'QQ0=P;PY!&gz%Q0QP6!&%o-9P:P;!&hJ&<!&hJ:!$p^8P!#S'$f!%z%%#>P<P=P3F0PPQ0JP>PQ!st$!#6&2RWP!s$%6!%~3'2<P;P<P2F0P[Q0MP3PP!tW%N!sa5!$@Z~!$/8<iA!$/82L!w}'Y!y4-@!$/5YSP?P>!%Mj-1P2!x-$_Q0fP3P\!vh%!%Mt41P2!w8$\Q!&e?&!sN$!x-O!%M~'!&$g%PaQ!&a;&D?S0g!%6Y4!x//!%N4'R!%Nd%f!&[c'D?S0p!%NB3!x1~!%NB,P:Q0aQ0bQ!&gB0!#}6+Q3>!#{v~!%G=JRW!&Iz+W!%vUQ2!%;r,P9!%vV$Q0p!%;o5!sD$1F0Q!x<8!y3?!%Gz'<!%S[%^!&C_'D?S0uP!y2?!%;y$3IP;!%H_%NQ!&c7&D?S0y!%;}3!y2~!%;}'!#z;/o!$68,o!#z;[!%M^~!yG63:!yGZ:!%>g,PH!%B7$Q0u!%w;6IP9F0Q!}u7!yD?!x_+HPY!&=$$!xR8!y7+!%N0,QP;F0PjQ!&Xh&D?S1a!%8%3!y7~!$$n%'6]1P3P6P6Q3<,FJQ3<Q1c5=J!#wb?R7RW,FRQ2m9=RW!#w_JIRW,FIQ0d9=IW!%|r:Q0~Q0wQ2G,2RRW3{R0Q!&m\$Q0x?XWj!%|kJQ1aP|P|!wn4Q2P!wo8!%m79|XB5P0!#:\%iQ2RQ2Q,2Y3{!%|g%PoS0iQ13Q2S,2PS2S'5R0!%|^3n[!&r#&n/5[Q2V,2[S2V;Xn!uEFoQ21PPPtPOD?RW!$Z;3PHP[Q2YF0PtQ!&TG&D?S1l!$ZH2!uX:T];P:Q10Q2UQ2[,2Q3{S2U#APiQ11PYPj!su%1Q0i@0507Q0i#A%A0!#Nh%[nQ0nQ2V!%|e$Q0r#AQ19Q2_,2_!%|W,fPM!#Np$fM!s:'Q16Q2b,2NR0!&m}$6/90Q2c9^jj!w7%2d,2i=Qi7P6Q2e,2oS2e=Qo!#|5'g,2nR0=JnDS2g!%|6<Q2j9^ttS2j#AQ2e=JoL#3Q2g!%|&$nP0PD%8LS1<#7S2g,2DS2e/90Q1ZQ1@5]D/90S1@!#P7%e!#v[%ZO1S2eO1S1A,2D!#P8+DPD%CD!t+$A!#P8&1<Q2eQ1BPL!sz$Z!%{t+0P0%C01W00!&m+'ZQ1@%kDRDQ0C#DR0!#mzeeR~Q0O!%yJA!tG$PDP0!%yHed#7P:Q0OP~!%yFUj!%yFkdW;Q2U#3Q13/5PQ2S;Xo!%yF,PnQ!&T}&D?R~!$`=2!%r[$kF!#eF5!|Y:rP7Q23Q23!%yFM!%`l%RQ2GE4R0!s8'R!%yH&P5P?P0Q0y!%a-6RQ1jF0Q!#?~4!to:p!%z?8!sx1q!sx8?1p!%z=9!#47/1sF0Q!#4&4!%v'+!%yM<!sn1v!snjy!snIy!snC|!sn[!$ix,HP\Q25F0P~!$0Z6!%~>'!#iZA!sv22!svD!#hw~!#hw>!&pq-Q!&pn+Q2FQ1dQ!&I[8!%vp&!#Ic/=!#Ic?=!#Ic=^!{o8P^!{]1!&Hw%!{\6RIP!s$%!#?,/>!#IV$!#Cu6IPI!#C8~!&pc3Q2E!$D_,E!%vsbJQ2C,2R9VER!#IZ~4!&R9IReQ!&q@'e!%v'TR!%5q,Q2PPQ!y\$11!%5m4!sC$YF0Q!#HS5e!yZ9e!#3'/Q3;!%o|$!#3'5R!vd'!$qs-2Y!%ic$!#9S4!'<_'!%5Z|!%v$-Q2MQ!$HN+M!%tXV!w-/PH!w,=!sB$!w+:@!w+9@!#713!w';@P!s$%!#=X1!w&:@!'_#%!%m1~!%tX'!%pf+Q!$|k,Q3@P[PXE4P!#IK4!sB%!u`;!vI>!#8l+Q3A!%p$$!#8l5!vK0!%71'BP_P\F0PlQ17PKPnPOD?R@!%1&3!z]~!vY%d!%tH>!v`1D!v`>D!}G>!~1>!v`/E!v`=!~2/!v`+F!v`&!vS~!vSK!%t9[jQ0vQ3GPR!}|$!#EN5!sC%:!#;v8p!vx9p!~f0Q3HPQP=!~g9kPk!#3?'!%MK+JPPP<F0Q11!&#[3oPo!vy~1/6uP1!%'w,iQ1iQ2]PY!%'m$!#Ve5!sD%1e!#VfL!#35%!%'n1!sv2n!sv8!sa&!%'o1!%+Q'KPK!%su$W!$229!%&x;!si01t!siew!siEy!siBz!siOz!%EA2LP_Q1}!}U7!$1K%!%sj@!sn026!sn>!%si~!%siU!#6%$M!#6%=MP[!~/$!#6%5|!~/9|!#6%2NP\P=!#6%8|!|0$|!vc1OP_P<!vb7R!'3d&!%7#}Y!%7#1Q3PPK!~-$P!#U]3!sB%1e!#U^K!%6sA!st$n!{/>6!%6r7Q3QPf!~%%wQ2`P_PxPOD?R|!%4X?7!%60=QPf!~6%!sibw!siEy!siBz!siO!%5u4TPN!~7%MQ3nPfP]!v8$1!%6s<!%Om=!s|1!~E$!so;!%Om~!%rq_!~O%V!~O>V!~O=u!~O9u!~O3W!~O=!#pq$u!~O1X!~O<!';4&!~O~!~O5Y!~O>Y!~OpY!~O[Z!~O'!}W]Z!~BeZ!~BeZ!~Bf[!~B'!~5c[!~5~!~5qx!~58\!~5>\!~5e]!~5R^!~5~!~5V_!~5>_!~5p_!~5[`!~5e`!~5e`!~5e`!~5fa!~5ka!~5~!~5f!%qo=!~5%b!~5>b!~5=!%Y38P!%Y21Q2Z!~5=T!t@$T!~51c!~5<!%Z`$!~5~!~5612!~5=!sB$!~5l!st%!~5Wd!~5ed!~5ed!~5ed!~5fe!~5ke!~5~!~5q!%qB2xQ2^Q3fP\!~5$@Q3jQ3j!}M2!sE$:!}M9!$90>!%h\$]Q0}#>RWQ3hPa!~<$xQ0}P\PlPOD?RKQ1;P}!{@$]Q0}PxPOPlM9:Rl!t82!&\X-!xt+kPf!~_$!xs4!&`3~!~_%rPP!~_-wQ18Q3lP_!~_%K!&Ze'!#4Z'lP_!~_%!#4[3!~_:C!~_6!st1n!#Z|?!~_0!zj,mPN!~`%!zj;!#^g;!sj1!~a$!sjcw!sjEy!sjCz!sjO!}r&Q0O!%-L%#>RhQ3pPi!~h%}Q2aPNQ3S!z[$YQ0I!s~1Q0I!$$@$!%pO?!t,&P!t$&!~y$!sr>!%pQ~!%pQd!#3%$r!#3%@r!#3%<~!{F8P~!#3%,PWQ2T!~|&KP!~X3lP!s$%!~X0s!~X<!%j4$!~X~!~X7R!~X>R!~XpR!~X\C!~XfC!~XfC!~XfC!~XbPhQ3U!~S'!~ED=!~EDU!~EI!%od~!%od~!s14!%od_iA!$uzO!'i>'K:7#GRvQ!'hW'v!$f:NT!'da4Q0@00K!s{&:!s{W>!%r':!$j>%!%r'/!sA$7010:!+LZ%!+MQ,;!s9&;10721!+MQB!+c<2!sb+!+c<'!~b$2P3Q04@0D>;PHP<%8=R=P9POP:M9:P2P3P!s>$P!s;,'6eW1WuX|6XQBXzAWyWrW{Wvo"). Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_skipf : ltac2:(zQ "h10!lc!hn8!jf!hr8!ige!kvd!hirf!ho7!u0!hge!un0!se!unb!tt5!hij0!hjk3!irb>2bc$h0>4segs@1$1$a>1K$3>4rest@1$1$3>2rb$b>2rk$9>1n$8>2sx$0>3acc@1$1$d>0@3$2$0@1$e^5$4>0@3$2$0@1$f^8$4@3$2$c@9$6^b^a@3$7$3^9^8^7^6^5^4@1$5$0^3@9$6^b^a^8^7^6^5^4@1$5$0^3").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "#$'Mp'0h02HCh13Hrbh21Lh31ai001ah41Hh52kbi012kbh62kki022kkh71ni031nh81bi041bh93leni053lenh:2opi062oph;3rb1h<3rb2h=1ei071eh>2n0i082n0h?1ci091ch@2hii0:2hihA1ki0;1khB2loi0<2lohC1pi0=1phD2rbi0>2rbhE3sx0i0?3sx0hF1vi0@1vhG1wi0A1whH1Ki0B1KhI2a1i0C2a1hJ2a2i0D2a2hK3acchL2bchM2bkhN1ii0E1ihO3lo0i0F3lo0hP1mi0G1mhQ2n1i0H2n1hR2n2i0I2n2hS1rhT4resthU2rkhV4segshW2sxi0J2sxhX2wnhY1zi0K1zi0L6a_basei0M5a_offi0N2bsi0O1di0P5deltai0Q2k0i0R2l0i0S1si0T1xp%0p;1p;6p;4p;3p;9p;2p;7g00eTj1GTg05Z>j1@Tg06Bmj1YTg04QLj1CTg01mbj14Tg05Slj6;Tg05_6j1\Tg068Fj4LTg00f4j1ZTg05`mj35!sJ$Vl90Tg01D[j1ATg01E@j1H!s/$^j2aTg01jZj2`Tg00MQj1BTg05b:j1:Tg03jZj73Tg00XYj2FTg01T9j21Tg01FXj22Tg01:AR0j2[Tg027^j2=Tg00Yhj2KTg05cEj3JTg05dUj3ITg0097j2PTg008]j3?Tg06D>j3XTg003Vj6ETg05mej7W!sS$Qj6N!s/$mj2DTg05[Nj1VTg00O[j1UTg00Phj3TTg00R5j3STg00SBj3RTg00TOj3OTg00U\j4QTg00Vij4M!vI$Tj3_!u>$;j2^Tg069Rj3]Tg00;\R1f0R2g00>4R33?p=9f6R4f5R5f4R6f3R7'^f2R8CMf1R9;52p=<A]678?592p=8g06;lR:??92p=61P:2p=7%@2=?13p=>g06=]g06>l#Gg017aR;%G;g00`TR<g00b@R=g00aaR>g06?k#G%@6R?#9f7R@#Y#9P;P;P1P2g01U4RAP1P8%@9#Cn0110000012010110MRBg00<<RCPBP3!s$+CP3!sQ$B000:3010010A10@2!s1%3!s9&310;2010<10:2010710G3!s-%!s9'01034010C10H10D10I!sb,9!sG'!u#$:P9PAP:P8g05U:RDP:f=REf<RFf;RG#4RHP9P2%47E;PG%\2RIPFP7CLf:RJ%Z1RK35fARLf@RMf>RNPEPFPGPJPKf9ROM90RPPPPP!uM$T00041010O!v'$0!v542!tX$9P<P:P8PDP:!st$HP8P9g01VB#ARH#H%AH#A!s$&H'a,`2RHE;g01TV#BRQ?5JK!tB$1P:PLPEPF%:GP8P9P7F3A5QOK!t]$!tQ%20000RR!tm1P!sB%PRP1P:fCRRf?RSPN%:ERTP6P7P5!so$GKRUPRfBRVPMPSP!uq%KPGM90RW!t02XP!s$%1P:fDRXPMPS%:NRYP5P6P4!su$FKRZPXPRPL!su+KPFM90R[!ss2\P\!u#$500081010R1010830106!xH$4!s1D4010?!yE$8107!s4&;10E108!w]-1!w]-8P1P:1FE9!s-$12F!wm$7P1P:%4FR\,2ER]129HR^'1PGP7PEP9PFPJPKF<R_!s\%^EPVPL!vL+GPKPJM90R`g06A<Ra!u`1!s41P1P:g00hSRb1[==RcP11=V6P0P=P=P1P2%4SS00,2MRd1269Re'1n200110=!y{'<10KP3n1!x^'210!sD$P_P`!t<5PbP!t3$X4!t3/LS01,2V1249R_!t1NEP5PSP7PNPFPKF<P!xE3fP!s$%!tG+fERf/=@!tJ/V,2RRg12@9Rh!tINNP4PMP6PSPE!tI$fPX!wN$!z#%KPEM90Ri!t^2jPj!y}xQ!y}%!}<0100!s63!zE6<P:PJP=P:P2!ye%8J%4O,2J/19'KPb%G=RjP:AJNJOAIOJ2f8Rk;5KPa!v22N00!up$!#4Y$OPkPKP@M90Rl!xs2M!vQ$!sM'KPkM90RmPm!tk$K000300!w'$!s'$PlP!s#'`!yf$10>!v['K!v[[F!}Z7!|N$!u2'@PKP4M90RnPlPnPm!}e&!}U%DP:!sS$\P8P9PHE;PFPEP6PGPKD8P`P`!z-$VPNPE%:F!sK$6F3PGPFP7PJ!sK%!y/2\!#6,8\!sp$X!vR$YP6P7P4F3PEPNP5PF!so$!{X3YP!s$%1P:PfPLPM%:S!#5j%@F3PNPSP4PE!sa$i!#5Z~!#5ZGn!#=181!s1$53!s-&!#=1G8!#=11!sb+!#=1&8!z1$!xJ%4P5PKP6M90'6]0PkPA%9BRB!xS$!xM%MPS%4NRn!#=?$6E;PNPIPSP6CL?5EKP[P[!wA$!#<pF/6`]0^F<^G>P2%@7#C#9R\P?P11P12S02%@5=?12S03P1%@@=?12Ro%C9#9RpPDP:fFRqPf%4XRrPOPk%4@E;PXPIPfP@CL?5RKRIfJRsfIRtfGRuPqPfPXPRPKPVM90RvPvPv!t{8/6vRw]0]2P9%@4Rx=?1CRy%CC#9RzPDg05Xm!v-$2PIP!sm@XSDPtfHRI!tK+VPKPLM90S04#7S05PfPX%4RR{PkP@%44R|E;!sQ$!s7$P|P1%@fR|%92X81PM1FfkS06AXfk9S07EEFWEEW0W2%9xRx%C3R{#9R}P1P{P1p-0P2g00?1g00>TR{!tu$4!{A'X=1S08g00?MR~P3P2ENS09P{1Dw2b4W0W2!sV1P2P8O2b2b8W0XF<XG>X6=X5<P9P2O!sR%S!{/'L10MX3A!~D$2O3PAA?1C3Rw!#383SPN%4E!#39'ZPWPW!}]$RPSPNPT!#3-'UP!#@y2U!~|9U!~D,!~|,A5QEKRU!~<4TP!s$%1P:PqPVPL%:M!~u'A5QNKRT!x%$R!#:d'KPN!x,$:!sp2ZPZ!#3-~!#3-4/6m]0^7<P2P1PCQ08P!x3&R~P{!#FX,LPMQ00!uK$HE;PTPiPi!vA05P6P7!w$$i!w$OuPRPV%:LRU!#3B$!vO$SKPuPq!{P&LPMPKPSM90RT!vL5!s$$1P:PIPXPR%:VS08!{Z$!wu%MKPIPu!|D+LPKPMM90RZ!sp1S0;Q0;!w@~8/6[/D2b4X0wX9<!{Y61!{Y1!sA$PA!#65%1P:1FM!#FI&S!w^$6!s4%d^PNP6PMP9!#Ae&Rd!s@%^MPiP!#EyC!#Dc&f5!#C?+11ge!#C3Kd!x_3!s|/u!#D=,12fr/1_!t#LMP4PVP7PLPSPKF<P!xl3_P!s$%!t=-Ik!#ET-f,2qR_/1h!tALLP@PRP6PVPM!tA$!y=2RhPh!#E:~!#?X/100!s63!}u7`^0B^A>!}y%?P1Q02Q03P1!yJ%qO!xz%kf!yJ$@!s4$2OHR?,1_PXP@PqPOPfPR!#Ld-?qfKR?Ps!|I$!#9i$KPRM90RB!yfM?!wQ0I,2t12F9!#LQOB!t+;fMRB/=J!t//s,2?12N!t/OqPOPIPG!~}$KF<PBfLR_PsPt!un&KPfM9!uX2R[!#@,$!tZ-NRc/=G!tZ/?,2_12S!tZOuPJPtPFPIPq!tZ$cPBP?!tZ+KPq!tX5?P?!zJ~8Pv!z:1R?!s83/6vRB^0p^2oP9P1P|!v3$2P!sO7X81R?P1P3P?Q05P|PMEEQ06Q07EEX0zX2yQ!#>s$B2b4X0}X2x!#>u%1!sj$1!#>u+X0\XM>!#6CG!#>v%A?133R\P<%>!#NS$9!#NS-5E11]6'KPbPjP:AJLEFAIFE2?5G!#NH8!#Uh$8!#Uh0]!zj2RPVPMP7!#Y]0xPx!#NH9]!#YA%6!#YA0]P!s$%!#R_$5!#R_0]P]!#Nr~PLPMPNP9!#^_&PO!#IJ$1PG%B2#>!{V'PCP3!#a?%!uN4#!w0%!#:W%@S12Sn/14'KRn!w5'RSNAINS2?5E!w58Ra!v9%%B9!v:1j!w82!vB$%B8!vC1bPb!ti9/6j]1P9P~P{!zv$nP!t7&PQ!t61Q!t61/6Q!#=_$1wg05[lRQ!tH&H9#B!tJ0#7X1\WCP2O1!sI&V!sI8XCQP2O1!y0:2O1W1XY!s/$%U2#>!z>%%U9!z?0#7W1X>>P2O1g00<\RGAT892#>!#EO$AT789!#ER/!sW$<<X;<W:!|7+S!sY/S!sY=X!#c%%2O3g00GERGAR!sa/R!t<HO!sY/O!t<HP7!s0%CQ#>!#C`%6!s:%CQ!#Ch/!sd$D<X>>XO>XE1!s_'O4!si+M!si4M!si5>>XN=XA!si1!wq$7!},03!},SJ10<103!},&J!},'3P4O1W0X@=XB=!t<$2%7lX0\RlXP=X=<!s:'PX0\!sL%X=<!v=+lXX<!#Dm'%7WX0\RWXR<XJAXQ<XIA!u~-!#E3&!#D{$!#I[,!#M]&SPMP5PN!#Ww$!#Ie18P9P5!#XC%6!#XC9i!#Io8i!#Io+PU!wB$@F3PMPLP4PS!so$!#Cp2i!tM$i!#I^+Q08P5P6PkF3PLPVP@PM!s_$Z!#Me~!#MeH`^0w^?=!#Bn$!#MZ&!#Q\$RPVQ01P4P5!v}$LPVP6!u/&!#PL&!v4'4P5P6!v4&7!v4:T!v}9!so%tPfPX%:R!#Lz&PVPRP5PLPKD8Q04!sq2LP!s$%1P:PsPqPf%:X!#Zn$F3PRPXP4PV!tR$v!s_2!#W\&!w#zQ0:'6!#MN'?=!#>4NPA16mm^0\!wQ%W!sb9!#Bw%!#N5/!sA$;010:!#^%%!#^x,3!s9&310;21!#u'R1!#u'3P2O1PJPOA_;k!#^{$6P7PKP8M90PJPOP!s;3'6eW0W1WKXW1W7WUWDWTWHWVWLo"). Qed.

(* [comment removed for export] *)
Lemma know_lookupA0B_filter0 : ltac2:(zQ "h10!lc!hn8!vi1!kvd!mrb!hr8!hirf!u0!jf!hge!un0!unb!tt5!hiha!hjj6!irb!hjm3>2bc$f>4segs@1$1$a>1l@1$1$5>2rk$9>1n$7>2sx$0>3acc@1$1$c@3$8$b@9$6^7^6@3$h0$5@1$e@1$d^4^5@1$4Z^4@1$2^3^2@1$3$0^1@9$6^7^6^5@1$4Z^4@1$2^3^2@1$3$0^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "#$93p'0h02HCh11ai001ah22kbi012kbh32kki022kkh41ni031nh53acch61lh73leni043lenh81ci051ch91ei061eh:2hii072hih;2loi082loh<1vi091vh=1wi0:1wh>2IHh?1Ki0;1Kh@2a1i0<2a1hA2a2i0=2a2hB1bi0>1bhC2bchD2bkhE1ki0?1khF1mi0@1mhG2n1i0A2n1hH2n2i0B2n2hI4resthJ2rkhK4segshL2sxhM2wni0C6a_basei0D5a_offi0E2bsi0F1di0G5deltai0H1ii0I2k0i0J2l0i0K2n0i0L2opi0M1pi0N1si0O3sx0i0P1xi0Q1zp%0p;1p;3p;9p;2p;6p;4p;7p;5g00eTj1HTg059^j19Tg05\Qj1Ej2CTg06ERj3DTg00MQj1gTg00g4j13Tg00f4j1RTg05_Vl90Tg0097j2NTg008]j3B!sJ$Tj3FTg01mbj15Tg05Slj6<!s\$6j1\Tg068Fj4GTg05`mj34Tg01D[j1ATg01E@j1Q!s/$^j2ZTg01jZj2YTg05b:j1>Tg03jZj71Tg00XYj2PTg01T9j22Tg01FXj2=Tg01:AR0j2XTg027^j2;Tg00Yhj2ITg05cEj3KTg05dUj3LTg01=@j3MTg05ehj2WTg01>Oj2VTg01?^j3OTg01@mj2eTg01B<j2dTg00nlj3cTg01Lgj2_Tg01N6j4^Tg01OEj3UTg01PTj2STg003Vj6T!w#$ml9]Tg01Qcj5`!u+$;j2aTg00Vij4bTg069Rj3[Tg06;lR1f1R2f0R33Bp=81N13p=@g00;\R4g00<<R57B3p=ff2R6/=2/23p=?f6R7f5R8f4R9f3R:'aP6Cb?423p=:%53,=2p=JA[9:6!s;%71C23=B45p=6g06=]g06>l#Hg017aR5#HR;g00b@R<g00aaR=P5g06?k#HR>f7R?P7%99#E=D52g01TV#gR@P9%3:RAP6%R4RBP3M90P?P7P2P@P9PAP6P!s;%'8]5X6;P7P8%R5P@P:%36P2!sD&#@X5>f8RAP?%98!t1%P@P8%39RCP:!sL&PAP?!t#$8P!s;,'8^5>%97S00/C:P41N43%9?/C9=B43P4f9RC#9S01/C7=B43f=RDf<REP4P;P2f:RF#9RG!tA$7S029F5?Q02n010!s#$20000P@PF%3CS03PAPBP9M90PDPEAF5?7P@PFQ!s?-'8]0P2%9A/C8RH#fP1PEf;RIP8P@PC%3ARJP?PBP:M90S04P5P1P?g01U4RKP1P6g05U:RLP1P@f?RMf>RN#3RO#5RPP2P3%5:S05E<S06PN%\3RQ%3MRRP:CG?4FBS07P8P8P8n0110P00041010F!uC%!s;$0000120101102PKP1P2g00`TRSP1P6P!tH$PMPPP6P2g01VB#ARP#Q%AP#A!s$&Q'Z,Y3RPE<S08A4@FBRT!tE$4P1fBRUP@PM%>OP6P2P:F1S09A4@CBRV!tf$!vw-RW!tv1G!sB%PW!sp$DRWP@fARXf@RY#3RZ#>S0:P9P:P8F1R[A4@IBR\P?!s{2]P!s$%4P1fER]P@PU%3XR^#>R_P8P9P7F1R`A4@EBRaPA!sd2bPb!tc$400081010J1010K3010L10010>!s1D4010O10810K106!s4&?10H10K!wJ:6P4P11P@2Rb!s0$23MS0;PSP1P:P4P1%5RRc1=2PRd5?YS0<PNP:PYP2PRPFPBF:Re!s^%dYS0=P7g06A<Rf!uR1!{<24P1g00hSRg1X<<RhP4fCRi/;9P0P<P<P4P3%3URj#5Rk1=92Rl5?in200110M!u8'810Qg00>4Rmn1!x;'210!sI$S0>PeP7!tF5PgPhP41;]7!t:/WRn#5S0?,=]Ro1=72Rp'2!t?7P!t:8@PYP8PUP:P^PEPBF:S0A!xM4qP!s$%!tS+fFRq/;?!tV/]Rr,JqRs1=?2Rt!tQOBPXP7PiP9PjPD!tQ%CPC!tQ2uPu!yxxI!yx%!|s0100!s63!z@-1!z@&!yP$2E%3IRu#5=?E3'IRvPg%H<RwP1AKNEu%3ERx=LI3?4?BPf!ut2E00RyP6!xX26P:P6P9!{H&!{3%!#3g$YPc!~}$PE<RzPMPZP9PIPBD7S0DP7P7!wf$iP@PY%>RS0E!sS$9F1S0FPNPRP:PFPBD7R{!yt3R|!#3Y8|!sx$!~k$P_P9P:P7F1S0GPYP^P8PE!tJ%H!yF4|P!s$%4P1PqP@Pi%>jR|P8P9P?F1S0IPXPjP7PD!t]$}!x[4~P~!#3U~!x;66!s:$;000:30!sh$:109!xi$10431!s-%10?!{1&72010610@3!s-%!s9'010K4010<10A10=10B!sb,5!sG'!#:^$!xO&LP1Q06Q07PUPXPIP@PMPOPDPBPCM9!v%$!v'&!#:7JPS!s~,8PTP~P~P4P1Q09PV!sq$!w0/V!xg9V!x%$[P\PWPiPDP@PXPZPMPBPIM90R[!sl3P!s$%4P1P`PaP]PWPN!yL$^PYPBPEM90R`!s[5!xS~!xS7!#9&'Pb!v0%!#8z,Q0<Pe!s/%=PiPUPE!}#$RPNPBPFM90RRP!#8hCQ0>PePR!s?7@Q0AP!uy3eP!s$%!sH$BQ0CPqP]PMP@PiPjPXPBPDM90Re!vX~!#5b6~!#5b1~!#5bFPvPyPMPNPAP@PEPuPFPBP7M90Ru!v-2uPYPMPCP@PDPxPIPBP?M90RyPuPXPYPFP@PN%3DRvPEPBPAM90RV!#5d3zQ0DPRPR!vZ%FP{!w=3R{!{A9{!sX%GQ0H!wV4{P!s$%!sH$IP}P!w@3}P}!zr~!zr7u!#4G81!#4Gw'8X61P516G3P5P1P!|A'!#9u+2P3Q05E<PMPQPZ!#Gh$IB!wO$R!#4TYPzP\!x8'!#:\$Q!#:Y%:F1PT!xF4T!xF9T!#:J38F1Pa!xR4TP!s$%!#::'P|!#F^&A4@DBRT!xd4\P\!xd~!#4XE123Y!#FU-ZS0E=?XdPMP:PXP2PZPIPBF:R\!sT%dXP[!#4\D!#D~&W!#F:/iRz#5Rc,=WRG/2l!#CMJP\P[!t1=q!#F1,12sp!s|LXP8PiP:!#DH&!wa4sP!s$%!t:+fGRs!#Ep1qR\,JsRu/2t!tFLUP7PWP9PzPN!tF$sPqPYP@PWPzPUPBPNM90R}!#3E4!#7>~!{p0100!s63!#Ez;D%5x=?D3'IPgPwP1AKMDxALEv3?4A!#Em7Py!x:2yPVPyP~!#Ek5X!}d'PE<PYP^P9!#DF$P[P[!w]$W!sK%:!#Ed&PMPZP:!#F7$!yJ3R[!~;9[!}e0!#E_%PXPjP8!#Ds$!y/4jP!s$%4P1PsP@PW%>zRj!#EY&PUPzP7PN!sa$!x53[!td$!~M~!wm4y!#83~!#832Ry/8y]0P7PK%9YRyAM623'6!xI$!xC'iPk!#Y/$9E<PUPQPzP9CG?4NB!#@@$!#89IR[/8[]0^<S^==P3%9iR[1W:6RZ?M!tB$!t<%WPcP9P:%56E<PiPQPnP6CG?4MBP}P!#<a&!t<3#@W0X<SX==X3<X2SP2P3O2!sQ$N!tR'C10DX1K!z8$3O3PK%9NRQ1V!uf+!{11U%5^!{1+TP`P`!#9J/!z~'!#9J4a!zt9a!z<,Pj!zt'A4@NBS0:!z54aP!s$%4P1fHRaP@P]%>n!#Yt%?!s_$MBS0EPaPsPXP@P]PnPiPBPMM90R^!st2xPx!{'~!{'6Rx/8x]0^4SP3%9XRx1W62R{/V3'!w+%2!yr-9P:PPE<Q0:!#F~&!~;06F1P!#<u4!#>7?!vN$P_P7P8P9F1Q0EP^!#>8<fIRTP@Pq%>rS0EP?P7P8!w$$YBPTPaPUP@PqPrPWPBPYM9!#S#$!sr/kPk!v}~K!{C$7S!{@61!w8%!{@'!sA$PKAO623,6y!}{&!#>w-i!wC$9!s4%GdPUP9PWP2!#:x&RG!s@%dWP}!#>qLs8!#=f-u!#>dLG!{]3!s|/T!#=M/a#5=?T!#>iLWP7PqP:PrPYPBF:P!wy3pP!s$%!t?+fJRp/;A!tB/T,JpRG!#>gN]P?PsP9P\PX!tD$pPTPiP@PsP\P]PBPX!#Lp5RlPl!#>g~!|H0100!s63!}s6e/8e]0^E=!}v$AOZ23,6[!#e6%!yS&:W!#I'%4P11=9PRe,2oPiP6P]P9PnPM!yf$o!sS%e]P^!yfMa:!wL/sRe#5=?a!wLMo!~K3!t'/p!zk/=C2,2G!xMN9PsP7!xM+!x83GP!s$%!yk,KRh/;!#ex/p#51=F25?h!tELqP8PaP?PePU!tE$hPpPWP@PaPePqPBPUM90R0!tZ5!yl~K!}p0100!s63#@W0XD=!#4eG!#=#%%9DR=1e23'!yk%26N%5v=?N2!#F%+YNvALDO3?4C!#F%8V!u}1!tU$:<X;<!tO%1d23,6=%@VRVW0XF<X9!ti&%9MAc623'6%@R!s['X9S!tl'1_!s`$PVW0XMS!#6l+!#FH$3C^,6x%@`R`W0XHSXAKXGSX@K!sF'O4PKAU!#7>/!#70$!#A'+!#?R&iPnP8PM!#Ed$P}!#>u/6P2P8!#F0%9!#F09}!#;`8!so%TP@PqQ0EP9P:P?F1PWPrP7PY!sp$|!#f8=pP@Ps%>\!#f8%AF1P]P\P?PX!sa$!{q3TPT!#;Y~!#4c5T/8T]0^8<!#4c$U!#4c%!#w:-]Q0?!u4$PE<!uo$:!uo&^P^!#>v/8P9P:F1!wQ$6!wQ&!#?#2^!w,9^!vL,P|!#?2&!vI$9!vI:uP!s$%4P1PhP@Pa%>ePAP?P7F1PqPeP8PU!s_$!~A30!s8$!#?]~0X8<!}yOPK1S23,6Q18~~!#D,%1S{3,6xP`!#@S:!#Hm1!sA,?010:!#Kz%!#Lq,3!s9&3!#LqG3!#Lq73!#Lq+3P3O1PEPIQ01#E=D58R2P@PCP!$#L+P9P:O1RKETPEPIAF57!sH4!s>&8!s>2RJ'8eW0AB4HmP1Q04PDPEQ02!$%&2/83X61PKPJPEPIP7P8PC!xr$:P3M9]ETW!xY%>!#6n'3O1b0bBPCPAQ00#EAF5:6R65D5P@P7%38R8P9!$'}&CPAP6P@!s~$!s;''8eX5>W>XI;X?5P:D`XL4W4WJW6WKWCo"). Qed.
Lemma know_lookupA0B_filterf : ltac2:(zQ "h10!lc!hn8!kvd!jf!hr8!hirf!ige!u0!hge!un0!se!unb!tt5!hij0!hjk3!irb!hjm3>2bc$f>4segs@1$1$9>1l@1$1$4>2rb$a>2rk$8>1n$7>2sx$0>3acc@1$1$c>0@3$3$0@1$d^5$6@3$3$b@9$5^9^8@3$h0$4$e^7^6^5^4^3@1$2$0^2@9$5^9^8^7^6^5^4^3@1$2$0^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "#$>3p'0h02HCh11ai001ah23acch32kbi012kbh42kki022kkh51ni031nh61lh73leni043lenh81ci051ch91ei061eh:2hii072hih;2loi082loh<1vi091vh=1wi0:1wh>3Hrbh?2IHh@1Ki0;1KhA2a1i0<2a1hB2a2i0=2a2hC1bi0>1bhD2bchE2bkhF1ki0?1khG1mi0@1mhH2n1i0A2n1hI2n2i0B2n2hJ2rbi0C2rbhK4resthL2rkhM4segshN2sxhO2wni0D6a_basei0E5a_offi0F2bsi0G1di0H5deltai0I1ii0J2k0i0K2l0i0L3lo0i0M2n0i0N2opi0O1pi0P1si0Q3sx0i0R1xi0S1zp%0p;1p;3p;9p;2p;6p;4p;7p;;g00eTj1FTg05Z>j1fTg008]j3?Tg00f4j1STg05_Vl90Tg06BmR0j1BTg0097j2N!sL$Tj3ATg01mbj14Tg05Slj6:!s^$6j1cTg068Fj4ETg05`mj33Tg01D[j1@Tg01E@j1P!s/$^j2YTg01jZj2XTg00MQj1WTg05b:j1<Tg03jZj71Tg00XYj2CTg01T9j22Tg01FXj2;Tg01:AR1j2VTg027^j29Tg00Yhj2ITg05cEj3JTg05dUj3GTg01=@j3LTg05ehj2KTg01>Oj2MTg01?^j3TTg01@mj2eTg01B<j2dTg00nlj3bTg01Lgj2_Tg01N6j4]Tg01OEj3QTg01PTj2OTg003Vj6RTg06GJl;\Tg01Qcj6[Tg06ERj3^!u5$;j2ZTg00Vij4`Tg069Rj3aTg017aR2f0R37^0p=Dg06;lR0f1R4;?3p=71N03p==g00;\R5g00<<R67?3p=Uf2R7/;4/23p=>f6R8f5R9f4R:f3R;'ZP7C`?343p=8%43,;4p=HAa:;7!s;%6%B3=?56p=5g06=]g06>l#F%F2R6g00`TR<g00b@R=g00aaR>g06?k#FR?%f:g00>4R@5?5P2f:RAf9RB%D4RCf7RDP8P9P:%S5REP3M90PAPBP4P!s>&P!s;%'7^2?X66PBf8RF%S2!sD&;!sF&#=X2?f;RGPAPCPF!sd&!sw&GPAP4!s;2!sw$%B;P51N53%B:=?53P5%B8=?53f@RCf?RHP5P6P4%D8RI9A2DPIn010!s#$20000f=RJf<RK!t0$EP:M90PCPHAA2D8PJP!s>/'7]0P4%B9RL#UP0PHf>RMP9!sJ&BPEP;M90S00P2P0PDg01U4RNP0P7g05U:ROP0fBRPfARQ%4CRRP4P3%4;S01E:S02PC%c3RSPQP;CE?3AES03P9P9P9n0110R00041010G!u4%!s;$0000120101102PNP0P4P<P0P7POP0PPPQPRP7P4g01VB#@RT#P%@T#@!s$&P'Y,X3RTE:S04g01TV#WRU?3AERV!tH$5P0fERWPPPQ%<CP7P4P;F1S05A3UBERX!ti$!vk-RY!ty1H!sB%PY!sp$GRYfDRZfCR[%<PS06!xk$9F1R\A3UGER]PD!sv2^P!s$%5P0fHR^PWPZ%<[R_!yO$8F1R`A3UKERaPF!s`2bPb!tZ$400081010K1010M3010N10010>!s1D4010Q10810M106!s4&?10I10M!wD:7P5P01CP4S0!s1%23QS08!wZ$;P5P0%4QRb1;4TRc5>PS09PCP;PPP4PQPAPEF8Rd!s^%cPS0:P8g06A<Re!uS1!s41P5P0g00hSRf1V==RgP5fFRh/9:P1P=P=P5P3%4ZRi1;:4Rj5>Wn200110O!u5'810SP@n1!x&'210!sD$S0;PdP8!t=5PfPgP519^8!t1/hS0<,;YRk1;84Rl'2!t6M=PPP9PZP;P[PKPEF8S0>!xA4mP!s$%!tO+fIRm/9D!tR,1H^YRn1;D4Ro!tMMRpP[P8PWP:PZPJ!wK$qPB!tK2rPr!yfxJ!yf%!|X0100!s63!z--1!z-&<P0PHP=P0P3!yI%7H%4M=>H4'IRrPf%F=RsP0AJPHMAGMH3?3FEPe!uv2F00RtP;!xR2:P:!t@$S000300!vG$!s'$P;!~w$9P9P8!y0$10C!v0'S!v0[L!|p7P7P;P7P:!|f&!|P%OP0P[PPPbP7P4PTE:RuPQPPP:PGPED6RvP8P8!y7$hP[PP%<QS0?!sR$:F1RwPCPQP;PA!sR$x!{@3Ry!#4l8y!sw$^PWPZP_P:P;P8F1RyPPP[P9PK!ss$z!zl4{P!s$%5P0PmPhPW%<ZR{P9P:PDF1R|P[PZP8PJ!se$}!z-4~P~!#4n~!#4n57!s:$;000:30!sh$:109!z<$10431!s-%10?!|Z&72010610@3!s-%!s9'010M4010<10A10=10B!su&4105!sG'!#;i$!xJ&OP0Q02Q03!w%$GPPPQPCPHPEPBM9!v%$!v'&!#;JTQ04PVP~P~P5P0Q05PX!sq$!w0/X!xd9X!x$$\P]PYPhPJPZ!z7$QPEPGM90R\!sl3P!s$%5P0P`PaP^PYPM!uF$[PPPEPKM90R`!s[5!xS~M!#3;5!#:C'Q0!s,&!#:;,Q09Pd!s/%:PhPWPK!uj&CPEPAM90RXP!#:%CQ0;Pd!uN$!s?4=Q0>P!uz3dP!s$%5P0PpPqPmP^PH!tL$ZP[PEPJM90Rq!s[2pPp!#74~!y:0100!s63!#74DPrPt!v[$B!{0$MPJPEPDM90Rt!v82ZP[PA!{W&MPEPFM9!#9d+!#6~4t!{3$~P~P!yS'!#6~zPPQPF!u2&KPEP8M90RpPtPpPr!#7;3uPv!{e+wPx!xn3Rx!|s9x!sW$yPz!y,4zP!s$%5P0P|P}P!xp3}P}!|I~!|I7p!#5v81!#5ve1!#5v3'7X60P2%53P2P0P4!#6$+!#;F%4P3Q01E:PQPSPP!#JQ$GE!wJ$X!#JNZuP]!x3+hP[PPQ!#<'%;F1PV!xB4V!xB9V!#;u39F1Pa!xP4VP!s$%!#;g'P{!#IM&A3UJERV!xc4]P]!xc~!#6-?1C[4!#IH%P!#IE-PR]=>[cPQP;P[P4PPPGPEF8Ru!sS%c[P\!#62D!#Gv&Y!#I%/WRb,;hRp/2j!#FIJPuP\!t,=m!#H},12nl!s|L[P9PWP;!#GE&!w^4nP!s$%!t:+fJRn!#Hh1m^Ru/2o!tBLZP8PhP:PWPM!tB$nPmPCPY!#8h%EPMM90R}!tW2|P|!#8f~!{i0100!s63!#8f9C!#Ht/C%4H=>C4'IPfPsP0AJ[CHAGHC3?3B!#Ho7Pr!xB2!#AF&!#8m4r!~`%PXP\!xx$!#8m|tPrPtP~!#8X3ZP[P]!#Hm&PPP[P:!#GJ$P\P\!y8$YPZP[Q06!#Hf&PQPPP;!#I8$!z}3R]!#3k8]!#3=/!#Hb%P[PZP9!#Gy$!#3B6!s$$5P0PnPYPh%<WR]!#H^&PZPWP8PM!sa$!yl~!#3}It!#9b~!#9b2Rt/7t]0P8PNAL743#5!xC$!x=%hPWPi!#]@$:E:PZPSPWP:CE?3MEPqPq!w-$!#9dF!t4&^<<^=>P31K;7Rt?L!t=$O!y+$hPbP:P;%47E:PWPSPhP7CE?3HEP}P!#>-&!t73#=W0X<<X=>X4=X3<P4P3O2!sQ$P!tM'D10EX1N!z-$3O3PN1M!u\+!zy/WPZ%4[!zz+VP`P`!#:k/!zo'!#:k4a!ze9a!z,,P]!ze'A3UMERa!y}4_P!s$%5P0fKR_P^PY%<hRS!zb'A3UHER|P_PnPQP^!#5b%EPHM90Rz!ss2yPy!zr~!zr6Ry/7y]0^5<P31K74Ry/M3#5!v}$4!ya-:P;!v|$a!yT$!}|37F1P!#>64!#?P?!vG$PS!#gt$F1P|Pz!}v5!s$$5P0fLR|PmP^%<YRV!#gt$!vw$CEP|P_PPPm!vw&EPCM90RU!#U+4!vu~M!{4$7<!{161!w0%!{1'!sA$PNAT!}f/5P01Ch!#@5&W!wA$:!s4%pcPZP:PhP4!#<?&Rp!s@%chP}!#@0Ln9!#?%-u!#@#Lp!{U3!s|/|!#>h,%4n=>_!#@&LhP8P^P;PYPCPEF8P!wx3lP!s$%!t=+fMRl/9F!u>-H|_Rp!#@&NYPDPmP:P^PQ!tB$lP|P[Pn!yS&EPQM90R[!tW2uPu!#@&~!|C0100!s63!}h6q/7q]0^F>!}k$ATt!yb$!y\$Y!yN&;h!#J>%5P01;:TRq,2kPWP7PY!ye$H!ya$k!sS%qYPz!yaM_;!xc/m=>n!wGMk!~B3!t#/l!zb/;B4,2p!xHN:Pm!yh$!xH%!x33pP!s$%!yd,NRg/9!#i~/|1;A45>!{%M^P9Pn!yi$P!tC$gPlPZP_!yg&EPPM90R1!#XQ~!ye6}!ye2!s62#=W0XE>!#4[G!#<f%1e4!#8_&Q!#G8-;QA>QR7!#G6+ZQCAGCQ3?3A!#G68!#`Q1!#RR'!#G64~P\!s$&`P`!#G6~!v-$:=X;=!v$%1d43#5%=rRrW0XG=X9!vA&Ab7!s@%X!sW'X9<!vA+_!vA$rW0XO<!#86+;!sF%C]#5%=`R`W0XI<XBNXH<XAN!sE'O4PNAQ!#8_-!#8O$!#B<+!#@h&WPhP9PH!#Fk$P}!#@3/7P4P9!#G7%:!#G79}!#<~8!so%|!zt$VP:P;PDF1PhPYP8PC!so$!#7C2UP!s$%5P0PlPnPm%<^RUP9P:PFF1PYP^PDPQ!sa$!}@3VPV!#<x~!#6,5V/7V]0^8=!#6,$Qt!{5+!#Y5$^PYQ0<!u3$TE:!un$;!un&!#]`&!#@:&9P:P;F1!wO$7!wO&!#@D2z!w'9z!vK,PU!#@P&!vH$:!vH:[P!s$%5P0PgP_Pn%<m!$&%$F1P^PmP9PP!s_$!#3i21!s8$!#@{~0X8=!#3INPN1O43#517~~!#EB&Oy3#5P`!#Ao:!#Iz1!sA,?01!#Mt63!#M8%3!#MtG3!#Mt73!#Mt+3P3O1PHPM%D9RN!$+Z1P:P;O1R<ERPHPMAA28!sH4!s>&!$,<2RN'7eW0A?5L@P0Q00PCPHPI!$-01/73X60P<PNPHPMP8!$-',;PDP3M;\ERW!#>Y$>!#88'3O1b0bCPKPGAA2;7R;#DPB!yH%!$0^&KPGP;!s;2'7eX2?W?XK6X@2P8P4E[W>W2XN5W5WLWJW6WMWDo"). Qed.


(* [comment removed for export] *)
Fixpoint tagged (kn : list kentry) (i : positive) : list (positive * kentry) :=
  match kn with [] => [] | K :: rest => (i, K) :: tagged rest (Pos.succ i) end.
Definition all_gt : ltac2:(zQ "40!hhr8!hn8!hu2!hr8>1i$0>1l@1$1@2$2$0$3P") := ltac2:(zQ "70!hhr8!hr8!hu2!uf!hn8!hjo5!hjqa\1i$0\1l@1$4@2$2$0$1@3$5@2$2$0$1\1t@2$2$0$1@2$6^3@3$3$0$1^1^1").

Lemma filter_tagged_gt : ltac2:(zQ "90!hhr8!hr8!hu2!lc!hn8!hjr1!hjrc!hjm3!hjqa>1P>0@2$2$0$1$3>2kn@1$4$1>1i$0>1j$0>0@2$8^1^2@2$5^2@3$7@2$2$0$1^5@2$6^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##5op'0h04__x1h14__x2h21ih31jh42Hjh57__arithh64__ffh78__varmaph85__with94cstrh:5cstr0h;2knh<1th=1xh>2IHh?1Kh@1PhA1bi001bhB4resthC1yp;2p;1p;3p;4p;<p;6p;5p;7p;8g01:Aj2\Tg00eTj19Tg06HgR0j25Tg06IEj24Tg06ERj32Tg06JTj23Tg000Lj3@Tg06Kcj2ITg00f4j1>Tg06LDR1j1;!s:$Tj3A!s:$dj1BTg01E@R2j10Tg05>=R3j21!s1$Yj2VTg052aj1UTg05?7j4TTg053?j1N!s/$]j1M!sA$Uj2:Tg01D[j1LTg054kj4?Tg00nJj1HTg056:j2GTg0097j28!s8$\j2FTg008]j3JTg057Hj3K!s/$gj4ETg01FXj27Tg05hKj1DTg066Il<O!t1$Hj2PTg05jXj3QTg06MLj4RTg06N7j6STg01Qcj5[Tg01SYj4ZTg055Vj7YTg05@8j8WTg06:al<XTg05[lR4g017aR5f1R6f0R7CZp=6P6g05;WR8g05<6R9P9g05<VR:P7g05=]FYp=<f3R;P8P9P9P:f2R8P6P7GWp==P4P4g00b@R<P<P1P2P2P;g06NXP!sK$M<Xp=C1\45R1g00;\R=[%95R>P51576R?f5R@14;8RA521,36[^34^24X;>A@457RB,58X<1,I1f4RC%>5/48!sP%eX4?X34X24f6RD=21A,36\?!sf%f7RA168@O1P=P=P=%91P716CAf9%;C,4D521RE5A1PEn010!s#$20000,3;P7P115;BX<116;DRBf8%;;RE,4@521%B;RFg01TVRG%0;RH'1RIPFPIg05:kRJ#>RK%9JRJP<1V<8P6%U<CTRL%N<RM%M<RNP<g01VBRO,:<RPg05BRRQ%L!s5$RC?,<NRS%H9R9PSC=1GN:R:P7P8g00<<RT,8=1F78=J=TdAK<G6CERGb6b7b8X0<X1<1176RT1168[^0<^1<P7%0D%0@PCO3RDb5b:b9A@45B,58ePCPEP8158E%08RB%0ORO,7HR='1P4P<P0P2P3%06%07'1#DXC4X=4P8PB18<BPEP=177OX=<P;PH18<HCCM<OPFP!v1$PKPJPLPMPNPSP9P<PPPQ1P<O9Q<!u_%C=P:P!u4178O,16\T!u2&!t~&CRO3RDESPDn01!wv%20100bAAA5@C/489!xo%!y+,W>XB>X?5P7D[W;W@o"). Qed.

Lemma kx_merge_cons_l : ltac2:(zQ "90!hr8!hhr8!hn8!hu2!ho7!hjs7!jjd!jf!hjr1>1p$1>1K$0>2r1@1$2@2$3$1$0>2l2@1$2@2$3$1$0>0@2$8^4^1@3$7@1$2$0@2$5@3$4@2$3$1$0@4$6$1$0^5^4^3^2@3$4$0^4@2$5^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##;Kp'0h01Hh12l2i002l2h22p0h32H0h44__p1h54__x1h64__x2h71li011lh82r1h91Kh:2K2i022K2h;7__arithh<4__ffh=8__varmaph>5__with?1bi031bh@2b0hA4cstrhB5cstr0hC1ki041khD1pi051phE2p2i062p2hF2r2i072r2hG1ti082gop;2p;1p;3p;4p;5p;6p;7p;8g01:AR0j2ZTg00eTR1j1>Tg06JTj26Tg00fTj30Tg06O>j25Tg008]j32!sA$4j1BTg01b6j2KTg0000j48Tg0097j2:!s8$Lj3ETg06Hgj27Tg06POj5V!s/$nj2UTg06QRj2=Tg06R0j29Tg065eR2j3RTg06Ldj1CTg01E@j1;Tg05>=j2<!s/$Yj2PTg052aj1OTg05?7j4NTg053?j1M!s/$]j1LTg01D[j1J!sJ$Uj2@Tg054kj4ATg00nJj1ITg05I?j6HTg056:j2G!s/$\j2QTg057Hj3F!s/$gj4STg058Yj2TTg01SYj4YTg055Vj7XTg05@8j8WTg05[lR3g017aR4f1R5f0R6CYp=3f2R71556504p=1A0456p=4P5g05;WR8g05<6R9P9g05<VR:P6g05=]FXp=?f3R;P8P9P9P:P7P5P6GWp=D1Z34R<#>R=16;6P1P<f5R>/66%>4R?f6R@/3>f4RA50</55A1>A532]0P5%B<RB,6AP1P<P<P41K34RCP6C8,4>A1>6B52?P;A1ABB,:?P0P3P4f9RDP<P4PCA0<56REC8'4A1DEB52?^7=P6f<RF1375=0<6RG;1B,:?X8=XC4X23P5P6O2n2001105000120105104X2<!sC&101101000200!sD&113>A=0<;/5BA1A;B52?eW0!ta%16DEf:RE/3Df8RB50<A0<75RH'5A1DBH52?]0!ti$16FGP<f>RGAE346'7XG<13;7RHP5P6DVf=RIAE34H'71UGA17GA1=AG19GA3Rf?/9>g00;\RGP2f@R2/7@1=@2PGP?P5fARJf7RK,3B=0<@712R2P?^1=RB!w#$?P6fCRL!vZ%fBRMC8'4!u7%P?P5PGP?fH/95fGfFRN;1AP>P7O1,46R>n!v,$!v0%00!v\3610!vS&0!vS07X1=p?1000108P@O1,4K!sp1=2?2P517JK1:?2W3P6O11=KJ%CMg01TVRJ%;M'<%CD%;D,<Jp-0RMg00b@R2g05:kR@#B%>@P21P27P5%O2CN%M2%L2R@P2g01VBRO#J,@2RPg05=61@2OROCA,?@%I9RQP@P2POg05BRPP!s=$PQP@!{M+AEHCDCD1G@:P6P7g00<<R@,:G1Q67=2G@dAF2J5CSb<b=b>X52W6W41T561<57PA[[^52^62^4MP6P!wO+!wK&ERCC8,4N!wL2K/95fJfI!wJ$!wAgDO1,4EfDf;R>/3E=0<D71L52?%;>%;CP;PKO5b;bBbA!wJ%n2002103!tH&!t+$!s'$b@b?b013IF=0<>A0<H!{M&F>H!{y%XF=X:4XE!|x71!|x@!sD%1P6O1W0X1=W8X94XD3o"). Qed.
Lemma kx_merge_cons_r : ltac2:(zQ "90!hr8!hhr8!hn8!hu2!ho7!hjs7!jjd!jf!hjr1>1p$1>1K$0>2l1@1$2@2$3$1$0>2r2@1$2@2$3$1$0>0@2$8^4^2@3$7@1$2$0@2$5^3@3$4@2$3$1$0@4$6$1$0^5^4^2@3$4$0^4@2$5^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##9jp'0h01Hh12l2i002l2h22H0h34__p1h44__x1h54__x2h61Kh72K1h87__arithh94__ffh:8__varmaph;5__with<1bi011bh=2b0h>4cstrh?5cstr0h@1li021lhA2l1hB1pi031phC2p0hD2p1hE2r1hF2r2i042r2hG1ti052K2i062goi071ki082p2p;2p;1p;3p;4p;5p;6p;7p;8g01:AR0j2YTg00eTR1j1>Tg06JTj26Tg00fTj30Tg06O>j25Tg008]j33!sA$4j1BTg01b6j2KTg0000j4;Tg0097j2<!s8$Lj3ETg06Hgj27Tg06POj5V!s/$nj2UTg06QRj2=Tg06R0j28Tg065eR2j3RTg06Ldj1CTg01E@j1:Tg05>=j29!s/$Yj2PTg052aj1OTg05?7j4NTg053?j1M!s/$]j1LTg01D[j1J!sJ$Uj2@Tg054kj4ATg00nJj1ITg05I?j6HTg056:j2G!s/$\j2QTg057Hj3F!s/$gj4STg01SYj4TTg055Vj7XTg05@8j8WTg05[lR3g017aR4f1R5f0R6CTp=2f2R71556504p=1A0456p=4P5g05;WR8g05<6R9P9g05<VR:P6g05=]FXp=?f3R;P8P9P9P:P7P5P6GWp=D1Y34R<#>R=16;5P1P<f5R>/66%>4R?f6R@/2>=0<;,55A1>5;33]0P7f4RA%B<RB'6P<P41K34RCP7C;,4A,<?12>A=0<7,5BA1AB753?eW0P0P3P4f9RBA0<56'6A0<75RDf:RE/2Bf7RF50<'5A1BDF53?]0^@=P6f<RD1275=0<6'6P<f>RGAE346'7XG<12;7RHP5P6DVf=RIAE34H'71UAG17AG1=GA18AG3Rf?RJ,8>g00;\RKP2f@R2,7@1=2@PKP?P5fBRLfARM'2=0<J91F@P?^1=R@P1P<P?P!u`$PCf8C;,4B!uC%P?P5PKP?18G5A1IDAP>P7O1,46R>n010!s#$20000n2001103000120108105n1011!sI'20103104X1=p?1000106PJO1,4MRG!sr1=3?GP517FM%CLg01TVRN%:L'9%CB%:B,9Np-0ROg00b@RPg05:kRQ#B%>QPP1PP7P5%OPCN%MP%LPRQPPg01VBRR#J,@PRSg05BRRT1@PRRRCA,?Q%I9RUPQPPPRPTPS!s:$PUPQ!yg+AEHCDCD1GQ:P6P7g00<<RQ,<K1Q67=3KQdAFPN5CSb9b:b;X4PW5W319561957PA[[^4P^5P^3OP6fEROfDRP!wO$L91EBP!wJ3;RCC;,4D!wL3M5A12JAP!wChLO1,4P53?%:C%:OP;PFO5b8b?b>W2P6O11=MF1<?G!s4%n20021!tF+!s-$!s'$b=b<b0A0<H5RH12ID=0<E'5A1DHE!|$%XE=X74XD3P5P6O2!t}01!th$7XC<!sC&!u-$2!u-&!sD%!tN$W0XF=WAX64XB3o"). Qed.

(* [comment removed for export] *)
Lemma kx_merge_filters : ltac2:(zQ "d0!hr8!hhr8!lc!hu2!jf!hjm3!hn8!jpf!hjrc!ige!luc!m3!hjs7>1P>0$0$2>1Q>0$0$2>2kn@1$6$0>1i$1>0>1K$0>0@3$4$2@1^5^1$b@3$4$2@1^5^2$9@3$4@1$6$0@2$c@3$5@2$3$1$0\1t@2$3$1$0@1^6@3$7$1$0^1@2$8^3^2@3$5@2$3$1$0\1t@2$3$1$0@1^5@3$7$1$0^1@2$8^3^2@3$5$0\1K$0@2$a@1^6^1@1^5^1^3").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##?Xp'0h01Kh11th22HPh32HQh41ih51lh61bi001bh73HPQh87__arithh94__x1h:4cstrh;2knh<1xh=2IHh>1Ph?1Qh@4__ffhA8__varmaphB5__withC4resthD1yp;1p;2p;3p;6p;4p;7p;5p;<g00eTj1ATg01:Aj2LTg01b6j3]Tg06IEj2;Tg06ERj31Tg06O>j23Tg01mEj22Tg008]j30Tg00f4j1CTg0097j26Tg06LDR0j1>!sC$Tj3<Tg003Vj6=Tg06HgR1j2HTg01E@R2j17Tg01FXj2@Tg05>=R3j29Tg05hKj1V!sv$dj1D!sC$Yj2UTg053?j1T!s/$]j1STg05?Uj2RTg054Hj2QTg05jXj3K!s8$kj4MTg055Vj7NTg056:j2J!s/$\j2OTg057Hj3P!s/$gj4ITg06MLj4GTg06ROj5BTg06Shj5\Tg06U@j5[Tg01Qcj5ZTg01SYj4WTg06:al<XTg066Il<YTg00;\R4f0R5g00<<R630p=8g00>4R79045p=:g017aR8f1R9;15p=5g05[lR:P8P9P5CWp=?A<895p=4P:P:g00b@R;P;P0P2P2f3R0g06NXf2R<P9P5M<Xp=FP:P;P1P2P3f6R3f5R2f4R1P0P!sJ&Yp=EP4\8R=%A8R>P8P2P5O1R?#8P2P9O1#:[^081L:8R@P3A]:85RAO1X1@1;<9RB31RCP2P!s9%=1@B'3P3!si$D/2?X08/5<50>[^4:X;>P1!sA$E#8P1!t+-2?EX08%C8'5,6>W7X4:%8DP3!sI,f7RE!t3&R?=1@B/3CPE!ss$C/2D!t60%8CPE!sa,PEP1O1P41645RDf8RBP2O1=045P4f:RFPE!s4'%A@RGP91?2BRHf<RI!t@&%>2,;ERJ51@RK5<@RLPKn010!s#$20000P4PGPFPBO1RKf;RM!ty'N=1@JRJ9<@HRHPJ!s[1'3P4P>129KPIP5O1PM!uF$O'2!uE$ERP,4BRQPP!s]150>]2P9f9RRP3O1RS#8P4P7!tQ$5P!t44,3L!t5%65P!sr7X64P>%>1RP,;3RL91@NRNPF!u8'J=1@LRL'3RH,4EA0>5QX5>P>PFP5O1,2O!tz$3RO14B5=0>QX5>14EORQ,6>PHP2PPP0O2E=1?1E=<@N/3LR2P1PEPNPLPJP3PPP11H1P%71RJg01VBRL#7RN,@JRH'9%79%75'9#VXD:X<:RTP1PJ16;JRUPPPH1@5NRHX<;RPP1PJPUCFFE%D1g01TVRU/9Jg05:kRJ#C%AJ1U;9%T;%S;RJg05;Wg05<6RVPVg05<VRVP;1R;LRLg05BR1Q;N9K;LCMg05=]FN1JJVP5P<16461O5<#8dAP;U9CIb@bAbBX9;R<195H^9;RHP5%73O1b8b:CGDBD\E=!wQ&7PQPO!wQ190>2ePRPEO1R2P0!{C$2E=W2%:SP2P4PDA04K5P4PIPF!zp%f?!za-B,;FRK51@!xw$91?BMf>RG!x6'D=1@K!z|$!zz3!zE'79!zE&G!zE$G!zE&FRI,4MRKPI!zE53P9PMPRO1RI#8P>%>ER2,;RRS91@DROf=RQ!~x,SRS'3RV,4FA0>5K!y\%Q!y\%G!t9$RRG14M5=0>K!y\$FGRK,6>PVPBP2P3O2R3E=1?EF=<@S,3ORMPEPFPOPSPDPRP2PE1HE2%7ERD1@DNRN'9PTPEPD16;DR;P2PNPPPEPDP;!y;%E19UDP<P!wp$R!wp-[!wp'76PKPG!wp4MeW3%:IP!vY'7!sL8VeW3n01!s<%20100P5O1b3b6W2!s>01!s>$2b6PB!vN&1410R1/;9R951@A1@?9'3PBP5O1/2C!vL$150>eW7X4:W=XC>X08P5DZW;X?=W>o"). Qed.

(* [comment removed for export] *)
Definition narrow_in : ltac2:(zQ "30!lc!hge!hr8>1g$1>1K$2$0") := ltac2:(zQ "90!hge!lc!hu2!ige!u6!hr8!hii3!hikc!hijc\1g$0\1K$5M4\1x@1$4@2$2$0$0$1@1$8^1\1p@2$2$0$0M2\1p@2$2$0$0$1^1\1s$0\1e$0M1\0$1$1@2$6^2^1@3$7^2^1^5$3$3").
Lemma kx_cand0_split : ltac2:(zQ "80!lc!luc!jf!hge!hr8!hjj6!hil8!hjt4>1g$3>1K$4@3$2$0@2$5^2^1@2$1@2$7^2^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##5|p'0h01bi001bh11Ki011Kh21ei021eh31gh41oi031oh51pi041ph61si051si061ai072a1i082a2i095a_offi0:1ci0;2hii0<1ki0=2kbi0>2loi0?1mi0@1ni0A2n1i0B2n2i0C1vi0D1wi0E1xi0F1zp;1p;2p;3p;6g05]bj1?Tg01:AR0j2>Tg00hSR1j17Tg05C9j26Tg05Icj33Tg04QLj12Tg05Z>j1:Tg01mEj20Tg0097j24Tg06VXj18Tg003Vj69Tg008]j35Tg05\Qj2=Tg06W7j2<Tg06XIj1;Tg00;\R2f1R3f0R435p=1g00b@R5g017aR6%?41>55R7#7P1P!s&%2P4P0P5P5!s0$2P21634R8f69334R9g00<<R:n010!s#$20000n2001104000120105102!ss5%28!sO7R;P6P2f2R<g00>4R=g01U4R>P2P3P:n01106!sV'=109R?P>P2P<%:3!sC6@P=!s$+!sM$!si8>P=!s<$1000:3010610D10C2!s1%@!s9&@10<2010>10;2010210?3!s-%!s9'610@4010710A10810B!sb,:!sG'n10110E000210!uu$RA!s:5!wE9P8P9!t|$!w6C=!sx5/0A'1!sw+!s}2f7!x@$AP!x;G!ta3A!taG/0;!tM$8!s[$2P2P4f3f:73<R8!tD3!sE%P8!s~3%24'0!sl$2f993<3R<1184X02142<10<=%8<E9%2:,0<,1<e142:%2=,0=952:e!xU$!st+b0X25X65P3P4O2!u&3F10FX57P4O1P6!z=$=P?P!yh1!yN~!yN5,0=,42!xF%3!xF-b41=341<34%;!v=$eW1W3o"). Qed.
Lemma narrow_not_wide : ltac2:(zQ "80!lc!jf!ige!m3!hge!hr8!hil8!hjt4>1g$4>1K$5>0@3$1$0@2$7^2^1$3@3$1$0@1$6^2$2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##3Wp'0h01Hh12H0h21ei001eh31Ki011Kh41bi021bh52e0h61gh71oi031oh81pi041ph91si051si061ai072a1i082a2i095a_offi0:1ci0;2hii0<1ki0=2kbi0>2loi0?1mi0@1ni0A2n1i0B2n2i0C1vi0D1wi0E1xi0F1zp;1p;2p;3p;6g05]bj1?Tg01:AR0j2>Tg00hSR1j1:Tg05C9j27Tg05Icj32Tg04QLj14Tg05Z>j19Tg0097j28Tg008]j33!s8$mj26Tg06W7j2=Tg06XIj1<!sA$Qj6;Tg00;\R2f0R3g00<<R433p=1g00>4R59323p=0P2P5f1R6g00?MP4P3E;p=5g00b@R7g017aR8%?31>77R9#:P1P9!s&$2P3P0P7P7!s0$2P21763R:f69263P5n010!s#$20000n2001104000120105100P5n10110E000210!sD$#1!t&&6!t&,%4:R1!sg88P2f3R8P5g01U4R;!s^$4n01106!sO'=109P;P2f2R<%96!sC65!s$+;P2P<!sg85!s:$1000:3010610D10C2!s1%@!s9&@10<2010>10;2010010?3!s-%!s9'610@4010710A10810B!sb,:!sG'R;!v760[!w6+!w<0P:f7!w8K#1!sb+6P!vq8!t5%:!t#$2P2P3f:928<!t'3#1%46!sR$f992<6#11825UA3254R4P2p-0P3g00>TR<g00?1!v]$2!se'R8X52/53P<%45#0/63b1W0!sJ1b4X27X97P6P3O2!tz3F10FX89P3O1P8X2!ss&0;!sq$X04!v_%3!v_-b71=63#1%<6#0[eW3W6o"). Qed.

Lemma kx_gkey_inj : ltac2:(zQ "40!hge!jf!hio0!hhr8>1a$0>1b$0>0@3$1$3@1$2^2@1$2^1@3$1$0^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##3op'0h01Hh11bh22H0h33Heqh42b0h51eh61ah71th82a0h91fi001pi011zp;1p;3p;2p;4p;6g06YZj11Tg008]j32Tg0097j2=Tg01E@R0j14Tg01D[j18!sC$mj23Tg05[NR1j15Tg01gjj17Tg06Zjj4>Tg00l0j66!s/$Mj6?!s^$Qj6<!s^$lR2f1R3f0R432p=0g00b@R5g01TVR6;24p=;g01VBR7=224p=:P2P7f2R8g00?MR9P3P4E<p=9P5%13%14R:'0A2583[^15P4P5%16R;/0:%;3[P410;;1=56W0%44#1R<,0;P4%83R=#:P2p-0R>P4g00>TR?P?g00?1R@n011000003!s,$!s2%0X52RA%88RB;94P?f3RC#4RD#;/34b2b3W0X12P4O1%54#1RE!t9%73RF#:%78RG=9A4P?%5CRH!s[5!tB$1000300!s/$!s'$X45P5%48#1/0:A25D3[P4%43RI#1/0;P2PBP7P4C>%:B%8C!t0%f4RJ#4RK=256!t5+%1DRL/0<P5PKPKPIP5\2RIP5P4f5RKO1X9IRMP0P01=I0E6P2P5P0PJP3P2!s$&4f6R0P4PK!v=:72%8JRNP=P4E6E6E?!uR+10LEP410NFP2%8KP2P>P4P?P@P?!w1<P9PGP4E<P?%40=25H!vOLX6!sF$P5%5!vV+H!vV$53R:!vV'G!vV'G%7!vV&%5JRA!vS2HRH/0<P4%7JR</0=P2%7!u7'@P?!u7AB!u7&50=25D!u7310HEP5PAPAP:PIP5PMP1P11=I1!wE&1!wE1P4P0!wC>P<PF!w@4!vCC!sF:85o"). Qed.
Lemma kx_bucket_add_same : ltac2:(zQ "a0!hu2!hhr8!hr8!hn8!hip5!ho7!jf!hge!himf!hju2>1g$7>1x@2$0$1$2>1t@1$8@1$3@2$0$1$2@3$6@1$3@2$0$1$2@2$4@3$9^3^2^1^3@3$5@2$0$1$2^2@2$4^1^3").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_53"] "p'0h01gh11oh21th31xi001xi011bp;2p;1p;3p;4p;6g01:Aj2?Tg00eTj1>Tg06[Fj14Tg00hSR0j13Tg06\Tj20Tg00fTj32Tg00kNj2:Tg00f4j15Tg008]j31Tg0097j26Tg06YZj17Tg06]fj48Tg06_3j39Tg0051j4=Tg003Vj6<Tg06`@j3;Tg00b@g05[lg017a'?R1%>1R2#4%32R3f1R4f0R5f2R6'0521R7,:2P0P2P2P5P5%51n10110000021010100f3,049216512X131627P2%76R3P7P5C8=923P2P3P7P5C=E<A;645/06=127eW2W3W0o"). Qed.
Lemma kx_bucket_add_other : ltac2:(zQ "a0!hu2!hge!hhr8!hr8!hn8!jf!hip5!hjud!himf!hju2>1g$1>2g'$1>1x@2$0$2$3>1t@1$8@1$4@2$0$2$3>0@1$7@3$5$1^4^3@3$5@1$4@2$0$2$3@2$6@3$9^4^3^2^5@2$6^2^5").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_53"] "p'0h01Eh11Hh21gh32g'h41oh51th61xi001xi011bp;2p;1p;3p;4p;6g01:Aj2@Tg00eTj1?Tg06[Fj17Tg008]j30Tg00mNj14Tg00hSR0j1:Tg06YZj12Tg06_3j33Tg00f4j16Tg06\Tj21Tg0097j25Tg00fTj38Tg06]fj49Tg06aOj3>Tg006>j6=Tg003Vj6;Tg06`@j3<Tg00b@R1g05[lR2g017a'@R3%?3R4#7f3R5f2R6501#4%:4R7f1R8f4R9#2R:534P0P4P4f0R0P0%63n10110000021010100f5R;,16504X471189R7,54P4%25R<11859836R3P8C9R==34:P4P:P<P3P8A02:<R<P8A>;90O1W0%4<eE=E;11=9=047eA<568/19=047eW1W5W6X31W2o"). Qed.
Lemma kx_bucket_leaf : ltac2:(zQ "90!hu2!hhr8!hr8!hn8!kvd!jf!hge!hjv3!hip5>1g$6@3$5@1$3@2$0$1$2@2$8@1$7@1$3@2$0$1$2^1@1$4@2$0$1$2").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_53"] "p'0h01gh11oi001bi011xp;2p;1p;3p;6g01:Aj2<Tg00eTj1;Tg00hSR0j12Tg00nJj11Tg00f4j1:Tg008]j30Tg0097j23Tg06bcj14Tg06YZj15Tg06_3j36Tg007Kj27Tg003Vj68Tg06\Tj29Tg00b@g05[lg017a'<R1#;R2#2R3%12P0P2P2f0R0P0%:1R1n10110100021010000=021X131321%42R3%50R45621724E81930=021eW0o"). Qed.

Lemma kx_build_spec : ltac2:(zQ "h11!hr8!hu2!hhr8!hn8!jf!himf!hjm3!jjd!jpf!hjvc!hjrc!hge!hip5!hir2!hjk3!hil8!hjt4&@2$1@1$3@2$1$2$0@1$5@1$3@2$1$2$0>2kn@1$3$0>1i$2>2w0@1$3@2$1$2$0>2gr@1$5@1$3@2$1$2$0>2wf@1$3$0>0@3$4@2$1~0@1$3$0@2$d^5^4@4$7~0@1$3$0@4$7@1$3@2$1$2$0@1$5@1$3@2$1$2$0^3^2^1@2$9@3$4@1$3@2$1$2$0^4@3$6@2$1$2$0\1t@2$1$2$0@1$f@3$8$2$0^1@2$a^6^5@2$9>1g$b@3$4@1$3@2$1$2$0@2$c^4^1@3$6@2$1$2$0\1t@2$1$2$0@2$h0^2@3$8$2$0^1@2$a^7^6@3$4@1$3$0^2@3$6$0$e^6").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "#$I4p'0h01gh11Hh22H0h31bi001bh41li011lh52NWh62WDh72gri022grh82w0i032w0h92wfi042wfh:2e0h;2HEh<1ri051rh=2HFh>2Hbh?3NE1h@1ei061ehA1thB3wf'hC1ihD1pi071phE3w0'hF2knhG1AhH1BhI1ChJ2EQhK3HeqhL2IHhM1Ki081KhN2NEhO3NE2hP4STEPhQ3gr'hR3gr1hS1ni091nhT1oi0:1ohU4resthV1si0;1si0<1ai0=2a1i0>2a2i0?5a_offi0@1ci0A2hii0B1ki0C2kbi0D2loi0E1mi0F2n1i0G2n2i0H1vi0I1wi0J1xi0K1zp%0p%1p;1p;2p;3p;4p;6p;5p;7g00eTj1cTg01:AR0j2[Tg06[Fj1iTg06d1j2OTg008]j30Tg01b6j3qTg06XIj1;Tg06W7j2>Tg00f4j1dTg06bcj1tTg01SYj4<Tg00l0j6CTg06IEj2UTg06ERj3=Tg00`9j29Tg06\Tj25Tg0097j2MTg06eBj1fTg06fYj4L!sA$Qj6BTg06LDj1PTg05]bj1ITg05C9j2TTg059^j1:Tg01E@j1eTg00N^j2ETg06`@j34Tg06BmR1j17!u+$Tj31Tg05Icj3QTg04QLj1ZTg05Z>j1sTg00hSR2j1rTg00kNj2bTg05F_j2_Tg00jFS00j2\Tg06g4j3`Tg003Vj6Dj7kTg00mNj1WTg06hOj2pTg06Zjj4o!v6$Mj6n!uO$mj2l!sJ$nj5XTg00nJj1jTg06jJj6mTg01Qcj5hTg01F;j2gTf6R3f5R4f4R5f3R6f2R7f1R8C<f0R9C<p=21U899=67p=J1578=069p=8g017aR:?=19p=AA0345A0789,96'9p=NA0678/99p=K1989,97p=VA=7899056p=]P3P4P51M67P8P9EDp=GA1:89p=31g89#:p=?g05[lR1P:P8P!t[$6P1P:P7P8C<=169p=SP6P!sg$C<9045p=R%P9,U8!u#%Hg00;\R;?089p=@!to'p=a!sL%p=Yg00b@R<!sH%Fg00>4R=90;9p=^%c:R>P:1[1:R?#cR@%i@RA1[@ARB/[>RC1O56PBP>P@PA!tU%F2RD30P@P6P?Aq1:9RE#;XA?RFP4P5CJ!s@$9P?1>8EXA?RGP3P4CJC8^0<P>P8%A4FN[^9>]7]8^C1S01XF>%d:RH/O6=0CDPCP>P0!tD$>P9P9n2001107000120107101RIX@CS02!tj'%d?RJ%t@RKPHF2RL!u&+6P7C<RMP8C<P9ECA0>H8PCPA!t/&AP9P0!sO$AP8!t951107!tM8N!tM$3P!t7,5P6P7F2P8ECA0AK6PCP@!t3&@!t3+@P8P8!t3LO!t3$4!t3-4P5P6F2P7ECA0@J4A0@J3P@PJf7RL90AKA0>HLRPP@P7f;RQ,UHRR9=?FRSP@f:RTP9f<RU,UHRV9=?GRW!w^$f8RX%AHRY50>RZ'9CK[[X8@A0AK3PAPKA0@JSRS1579S05=0@W^0<;VZ\PX7AA0>H3P>PH15K9RK!sD&A0>9Y5VSX9>P?PFPHPTCJRS90@JA=?GRRR90@K^0<RWA0>HYRH'91M@SPWPHP@PJ!vS$?1>7EXA?S06PVD]X4@P@PRPK%f9FGX0<1M>YCLCLPLP9EBW1!s-49O1b2!s+/W1X9>X7AX8@XC1Q011334!z6&%P5,O3PC1MC9%P4,OL=0C9!x2%f9RY%PL'O!s9$C!xG&CP8!xG&CP8P21[<<RKPCf?RR#IP0P<P<PCP9P;PC1T89RV!yD-;PA%:8RJg01VB#eRH,?9RW'ERSfBRP,6RRZ=4J6R[A4WZ[n010!s#$20000P;P>%7PR[13P4P4!sC1R\F!{}+A1?Z5P6P\F2!sK1!z-3;106P;PC%;R!tr+?PUPRP8CS!u8$>%7R13R7P7!t==!#4U$R]P\C<!t>2!{M$J000210!tF$!tP01103102!s:&J!s:'7104!t&+LP3C<P4ERP@PXP?PF13UQR\PYCJP@15X9R^P?PGf=R_/3U/UTD]!#3y$3%A\FN]1]>!wu,%PQ,O_!t&$8P9ER!xA$!x7%7P2PKPCfAR\!x33P!x/2PSfDR`,6\Ra!wr$bA4Wab!wr7`13`3P3!vY2b!wp0a5P6Pb!wpM\!wp,f>RbP\!wr/\13\6P6!t?2a!t?&]Pa!whY!tA+QPTC<PY!wT$UP?PFf@Ra/3RR]P_CJ!s;$9P?PG13\aPb!#8N+T%A]!wS%^4>P9%Pb,Oa!#8D%!w>$%IP!w;<3!w;&ERD,6PR]=4J4RcA4W]c!w;7D13D5P5!uz2c!w;0]3P4Pc!w;MP!|i/6P7P;P>P[13P8P8!t72[!t7&MP[!w3E!uZ+bP_C<PU!vw$5P?PF%PaS07,UPD]S08!s<$!vx$fCR[P\CH!vx$%AP90>7P@PR!|%%[PRMPa!wP$R!wP'`[P\!wP,_%AMFNQ!sy$4!sI%P`PP!sw+`90>5!wZ$;fGRM#IRZ!w_&;!w_$;PVAQ896P=!vZERcP=!uj5R],M;X0<1>9M/@!}d$!t=$P!t7-%ZVRZ!sy8]P:P;PMP=g01U4RdP;P8g00<<Ren0110<!sT'C10?S09PdP;P7%s8!sD7:P=!s$+!sN$P!sk8;!uc$108000:3010<10I10H2!s1%9!s9&910B2010D10A2010610E3!s-%!s9'<1094010=10F10>10G!sb,@!sG'!vQ6d,M;%;M/@dfHRd#I%rKRf1Mf9fIRg#I=0f9P2PKfKRh!s4&!|f&P8!|e<a!|e&LRifORj'6Rk=4JRRlA4Wkl!|h7jRl13jbP!#5B1S0<!|k0kaPRQ0<F2S0=!|oKi!#9v,gPiP_CSPU!tD%i13iQPQ!#6C<P_PU!#6@5!|{=dPMC<fFRbERfNRm,>9!z@&6P!zp8'@^0<%;mS0>!sO+!zF%mP=Q09Q!y_/Q!yE~!yEJ'@P@PhP;P@%;jP?PFPmPiCHR]91?kP]!xI2@Ph!y2$@fPR],>9RkfMR2/6]Rc!~|$jP2CHRn51?Pn!sa1!#3Z&gP;P>Pl%AmRl,3jP!yS2FN]6]5]1];!zL'%I21bK950fPC!z^+8!z^2\!z^%A4JcaRJA4WcJ!zS7]13]RPR!zQ3?!zQ0c\PaQ0?F2S0@!zQF!s_&fJRcPgC<PdER!#4J'6!#5[+7!#5[F,@k!yT$]!sh-!#517!w|$2!wO$QRZ#;16mZR0!x,$]PmCHS0A51?S0BQ0A!x142!x1&RRk,>916jkS0C!x,$ZPjCHRV51?PV!x,9h!vg%ZRV%A]RJ,3ZP!w02CaS0DCK!x5+9%I]!uC$8P9C<,bK50f!#Fm$78!x-+P!#Fk$7RJ1?8HRW'EA4J0\!x9$0!x96PV13ZaPa!x83E!x800PP\Q0EF2S0F!sj2!tG'2PiPhF2S0G50CfSR0,>9P;P;1T56RVAQ569!x#3!~@&0%ZV'@1T45P;1M;91T34/@9P;1TXL/@9PC!zb$!uZ,g!uZ%YRV1?XHRJ'EfURWfXRS'6Rl=4VdRVA4JlV!zx7S13SMPM!sA1RV!ue0lgPdPV!#522!z_+TRVP0C<PkERfZRJ!u_&P6AQQT!u[;J%Z!z&$fWRn!yJ$[Ro#;16SoS0H!z,$JPSCHRp51?Pp!z$4n!z$&\Rp,>9fYRq/6pS0I!z'$oPqCHRr51?Pr!z'9W!ur%oRr%AJRs,3oPs!#359=P81TL3S0J=0;e!#7d,!w:$XRs1?LHRt'E16VnRu=4sMRsA4tus!w47nS0K13n!#:\5L!w8,P0PkPZF2S0M50C1>9qS0NAQTY9!v[&qS0O%ZeS0P'@!tV%QRs1?T!tV&nJS0Q=4scRsQ0Q=4t!tY3APCP>PIX:CS0!#N2+i!vr$>Pr13ocPc!to3S!to-nfVRrPWF2S0TP6ECQ0S=0>WPCPAPN!s}$U!{o-8!ur%p13phPh!s~3!z%-PSPnPrF2S0WP5ECA0A8nPCP@PO!sz$X!sN+m!#F{$f]RO#713OiPi!x,2!sz,qPSPnF2P4ECA0@mqA0@jJP@P]A0A4o!sm$aRN#7S0Y13N]!#:82RI=0>oRsP@!tB$@fbRt#;f_Rv/6tRw1YNvS0Z9=?FRx51?S0[Px!sh2yP@f^Rz!zq&cS0\,>9f`R{Q0\'6S0]1Yt{R|9=?GR}51?P}!sg2}!zv%!vd$tS0^%ANR~,3tP~!vk3_90>pRp!#Y=-5JPAP4A0@0yRyQ05=0@}^0<;Vp\sX7A!s|%{S0`13{jPj!sx3a=0>JS0bP>PIA0@^}^0<R}Q!t8$95VyX9>P;Q0PP@P0P;P@P9Q!uy5P}P>P;P>Q0^13tZPZ!sE1Q0_FNX3;1Y{zS0[9=?FS0c90@k15L9S0dP;P@1>9tS0eQ!w3$GR}91?w!vH3S0f50@!tp$!t=%Y%A{S0g,3NQ0g!vt2x90>IS0h'9S0iP2P}Q0hP;AQ[P9S0j15X8S0k!uI']Q06==?|S0l!xT$mQ0!#?G150@X3;%:[R|1?PHR}'_1F|}1E|}S0n'\%:`1?[H'EP;Q00%:D1?`H'FP!}x$P8%:MRIQ0\ff'6Ry;4rR^1?bHRs?4y^!vl25!td$;P;1E5IR^Pe1E5!~B215r5Rs91?y!#502C8P8%:b1?DH'FS0o1_5IS0p1F5I/\^S0q%:d,E4S0r!tw&g,F3S0s%:hR^fgfj'6RI;4JS0t/5XS0u!t['P8Pe1?cHRe,EXS0v!t_3JX!t_$I!t_3S0w50@P8%:c,FLS0xP<P^P@%:iRyfhfkRp'6R~;4oS0yP915o991?~S0zC8X0<P@15J^91?IS0{15oy91?~90@9X4@S0|P@Q0{Q0t/5^S0{A`^IJFGS0}PXP9EDW:P9O1Q0x#WS0~P@Ps!z$$?hHS10,EYS1115oY!u-$~!u-3!t3&1_XeS121FXeQ0v'\S0vQ11!vZ$1?iH,FTS1315zUR!t'$P8fn,6pRp=1?s!v%414!v%$1?2H,FQS15P<PU1pmH#:S16%:jRyP9P<PyQ16PXCoEn1FUy15v_S16flfo'6R_Q1651?50@P4P9O1'lbK!u_&15#WS171M@sS18WSP9O1n102100105!#I3&610109b3b<Q0uPXP^PIPJP9DXEDW?!sY;1!sY&WJ!vq%o#WQ0pQ0qQ!y_&Q0sP@Q0t94eIR4PXQ0wC8P8Q!x^'Q10Q0y74~P9Q!xJ+!x'$|Q0}154^P^PePIQ0tP5DXED!x11~Q12Q!wA,Q131?mHRIA4ypzRe74p/5US13Q!w%&Q!vz$I%:]R^,F9#WP@1?]HS14fmfp'6R4%:Z?44{34P815{891?4C8]?X0<1FIy#WP@A4^_vR~1?jHRH'5S0091?_Q14,5{91?4S14!y;&P@15vHS11A1?49!tR%!s=$Q11!sZ$00PHP^P_PvP9DXFGA4H_~/5HA`H_~!w>$UP9P5Fk!x8'7P@15eURHQ16!t3&R!{$%~Q18PHPUPyPpPz!vJ%Q13PUPIPpPe!x7&O!x761!xj/!xY81!xY0N!sHC!~w$AQ0nA4|wkR|A4}w|!{Y1!#;\$Q0j15k9R|91?wP|!#;F4eQ0d=0@}!sx$@AQ`[8R}Q0]1508Re51?Pe!#BN3@AQD`7Rpfd,6NRIP?1>6EXA?Q0\PNCHRE51?PE!t:2E!wx+Q0l!}g$pA1?I9P9!sO1=0@E!sM$!sJ$}Q!#8`5PePmP8O1FGQ0kP9EDbPQ0ePYP9O1EDX0<P>Q0g!#;^+!t24Q0_50>XB>P>PxP]PhFGCLCLP@Pk!vS%P16zNRtQ0c51?RYQ0c!sg3iCKe%;NRePLEDPo!#nZ%!s-3!#nj3bRW6W5W1W=Q0J#^!#J&,udR}PMQ0LF2Q0M50CQ0N#^^0<Q0O%Z=RE'@PCP>Q!#E/+Q0Q=1?hPc!#?Q$J13JgP!#<{2I!#C8,rPWPV!#sp&>IVPCPAQ!#E$+Q0H=1?iPhQ0SF2Q!#EX$A0AhrPCP@Q!#DU+Q0I=1?2RIPiQ0VF2Q!#E,&@ISP?PJPOPmCS=0@qP@P?PoPzPjCSA0AjJQ0b!#Cw&PeP!vw5ReP@POP9Q0fC8!#sy$oxRo!#BV-mqPAPjQ0bA1?tkRz=0@eReQ05Q!#@3&;Vo[!#B`'v13vmPm!y{3>qP>Q0aQ0f90@|^0<R|A0>9x5VeX9>P;PEP@Pz!tv$9!tv6Q0h,9|CKX3;16O{R|=1?ZRzP?PFPvPOCHRO91?|R|50@15Z9Re!#BI%NRqQ0[9=?GRo91?tPo!#@|3^0<RIQ0a!{#%`%AvRv,3{P!#>71Rp50>Ry'9RHP@POA1?t9=0@YXE@P@P|PZPiFGPIPyP;P=!{A$8!#BS&6Q0Z5=?Ry!~t$y!#@V2X3;P@PoA0@9y!}A%oPePiP9O1FGPqPX!|w-Pv!tu%Y13N!~&6>x!|t%pPjPc!|t+!vv%EP|PO!~82H!|e${P3EDPJ!|S&!s-3!|c4!|a'n0110001020101P9!#}V$O4b=b3!sJ&;X@<XV<P8P9O!#tI&701!#os$K10KXDKP9O1%Ic%jK!#]Y$;PC%;h!#cI,dPhPUCSPQ!yx%h13hTPT!wd2f!}/-UPQPf!#U=:PMPbC<PDER1>92!~Q$%;2P:P;P2!#b_~!#b_I'@Q0>P;!s$$CP9Q0@!#`R,!#_]$Rf!uP:iPhPcF2RQ50C!#^=&P8Q!#]{5Q0DCK]1P9Q0=!se+hPcPgF2Rg50C!#5R$2Q0@PQP9ECQ0?=0>cRc!#4s$3Q0FQ0G!$'0%\iRh!#4b$!#ya'Q0C=1?[RUPP!w|%k13k\P\!w|2k!w|-mP2PiF2Ri!$&y%UmP?P]P0P`CS=0@jP@P?PZPVPDCSA0AD]R!#iJ%rR213rDPD!t'2K=0>]RJP@P71YrVRV9=?FR391?uR{P@P!#=J%1>9S1YnWRS9=?GRH91?lPH!sr2H!#Qq'Q0K%ArRO,3n!|]3RO90>ZRZ'9R|!#6?+`jREPAPDA0@}{R}!#Qq$H^0</9!sR$\J!#6;'W13W`P`!~44jRzP>PKP@PdP9P!tZ&>P9POCaRH,9}X9>160rR}=1?MP?PFPWP0CHR091?}R}50@15M9Rp!uf&nRxA=?GVRV91?u!#cQ2!#5j%NP;P>P2%AWRW,3rPW!uc2r90>KR2'9RvP@P0A1?u9=0@{!#5g$}PMPPFGPN!zE$=!u1$!#5g+==?SRS!w0$S!#5e8VA0@9S!#5e$VPpPP!#5e%xPT!#5e-W!wY&13n!#5e6O!#5e$rPDPaFGCLRrCLP]!#5/%!s-3!$-h5!#r>,!#q<$=0Cg!|&&Pf!|%%P!{z'!#f',!#e+$!|0&P!|'3P[PPPkF2P!{Q'[mA0@`jP@PDP@P7P3P|CK\J\UX8@!yQ&d3R3/9Z!yC%>PK193HX9>A0@M0PvPPP!uP+X1z!s/'E!uR?!#7e16O1!#7]+!#om$:01!#G0$701P9PL!#8,%;bTb6b5P@PP!#{o$bDRDP[CJ!s8$!#{o%MbP`!#{o+a%ADFNeWIWHWGP\Q07!#8{$P8O5EmW1W>XB>XQAXE@!#8z81107XDB!sC97!#9u$7O2b>bD!$3f0WLXU>XM:P9DhWFo"). Qed.

Lemma kx_select_eq : ltac2:(zQ "d0!hr8!hn8!lc!hjm3!jf!hge!se!hiha!hij0!hjj6!hjk3!hitb!hkg2>2kn@1$1$0>2rb$6>2rk$5@3$4@1$1$0@3$b@1$c^3^2^1M2\0$2@1$1$0@1$8^2@3$3$0@1$9@1$7^1^3@3$3$0$a^3").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##7zp'0h02Hbh11th21li001lh31Kh41gh51pi011ph62w0h71Ah81Bh91Ch:1bi021bh;2grh<2knh=2rbh>2rkh?2wfp;1p;2p;3p;4p;5p;6g00eTj1FTg06d1j2=Tg01:AR0j2BTg06[Fj1ITg0097j2TTg008]j30Tg05Z>j1;Tg000Lj36Tg01b6j35Tg06kOj4?Tg06l]j1ATg059^j14Tg06\Tj21Tg06mmj1DTg06O>j22Tg06o;j1CTg05\Qj1:j2RTg01SYj49Tg06XIR1j1ETg06IEj2<Tg06ERj33Tg06W7j2>j1KTg01mEj2STg070Ij2QTg06Zjj4NTg071`j5LTg072?j1JTg073Wj5HTg003Vj6@Tg0750j6MTg06jJj6GTg076Fj1OTg077Uj3PTg017aR2f1R3f0R433p=7g06Bm=324p=8%F2R5g00`Tg00b@R6f2R7g01VBR8'=g05[lR9/B2R:#FR;%I;R<'BR=/B5R>1T>4f3R?/=8=0>4P0P=P5f5R@!s7&g00;\RAP5%;@R@f6RBA6=53RC96;<A5;<CA5=53C?RC#Af4RD#4RE'1%DC'2%CCn010!s#$20000PAP5P@%:E/7B%8B!sC1505]0P3P0P;P<f9R0/=8P=P5P3P4C950>P!tT$0R0f:RE!s@$7P3C9R@96=5!t_2@C?R@#Af8RC#4RF'1%D@'2%C@!tB-1!t_&0%:F/7E%8E!t_6^25P4f<RE!t\';P<!tF%!td&A5924R9#EX1:R>f=RF/<853:90;?R011?41>39X1:R@f>!sA%50;^46%8FRG9053!uN%EREf;#4RH,17/2?P3!vY6E%:H/7FPG!sB1RG50511D4f?RD/<893:@!t2'D905?%;DPA!s$$5P4f7R6f@#4R@'1/2CPB!t764%:@fBRI'7RJ%8I!v64P4P;1>@9X1:fARK/<8RL53:RM124C=05JX2;P;A3:>LRL%4K/>9X1:1<I853:/24!sI$6;P51>@4%E4'SR:X32RI/7KA054JX25P2PI%4DRD#:PA1R@4P:1Q@4CNX32PKDL12ML%KDP1PKP8%JDDHE@P6P?E@11BDP7PDO1E@!vf$1!u/$!x`$b:W9W8X70PFP8P?P7P3P4EMEG!w#%PF!xS+?P7C9!yw$?!yw$F!yw'FA5=5?C?R?#A/1H%D?'2%C?!yp1=05GeW0X?5X;<X6;P3P4O2n200110!s$$21100101X5=!sC91100P4O1b0b5%O7?P34!yA%3%44#:/77%87!wa4eW>W=W<o"). Qed.

Theorem know_lookupA0I_eq : ltac2:(zQ "e0!hn8!lc!u0!jf!hge!un0!se!hr8!unb!tt5!hkgd!hkg2!irb!hirf>2bc$c>2kn@1$0$7>4segs@1$0$5>2rb$6>2rk$4>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$9@3$3$8@9$a^9@1$b^8^7^6^5^4^3^2^1@9$d^9^7^8^6^5^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##5+p'0h01Lh11ni001nh22rbh33acch41bi011bh52bch61hh75hintsi02!s/%h82hsh92knh:1li031lh;2rkh<4segsh=2sxi042n0p;1p;9p;3p;2p;7p;6g00eTR0j16Tg076Fj17Tg078gj1;Tg05_Vl90Tg077Uj3ETg00f4j1@Tg0097j2:Tg05Z>j15Tg059^j19Tg05\Qj18Tg06ERj33Tg00g4j14Tg008]j32Tg05g6j2DTg00MQj1CTg07:5j7?Tg003Vj6<Tg07;Tl9>Tg07=3j3=!tL$Tj3ATg07>Hl9BTg06;lR1f1R2f0R332p=1g06=]g017aR4#6R5g06>l#6g00`TR6g00b@g00aaR7g00;\R8%68R9g06?k#6P0P8!s&$1P3P7P1f4R0f9R:f7R;f8R<#7#;R=f6R>f5R?P0f3R@P3P2M90f:RAP<%7:?E;>RBP;P>P?P0%@8RCf2RDM90n0110000020010104f;REP:%7A#;P<!sX&DP@M90n101102!sR%20!s4$3P:P;P<!s~%P!tF''1P2P7P7!u%$:P;P=!sG$3P@PC!sG$PAP<P!t^%2P0PCP!tY8!t&-!sa,'1P@!s;$;P?P0g00h4PDPCP3M90,:1P5P8P5%5;R=%9>#8=34:g06BmRF=34:n0!t1%!u=$0PEP:P3P<P;%42RGP?PC!u`$!s>$A!uu$!s;,'1X:5P=P81:83%5<=283P8%5A=283f>R=f<RGP8P5P2%9A#8f=R5534A34F5!tE4A%40RFP<PCP>M90P=PGP5PEPAP!s;,'1]0P2%5:RFg00<<5281DA3g01TV#CRH926AP6PHf?RHP5%9E!ud$=P3PE%4?R4P:PCP;M90PHP5P!s>$P!s;,'1X26!tF&AP0P<P>F?PEP3E<b0W0g00>4928F!te$GPAP:%4@!w;$3M9>W!wt%1!uI+3O1b0b4PBA=:;>E<X17P3O1!xB30!sq$EP:!yr%AA823P0!x%%X89X68P2P3O2!z&%3!s_$1!z&+<%7;!z%+DP2P3M9B!x{,!s;,0'1eW3W7W=W1W;W2W<W9W5o"). Qed.

(* [comment removed for export] *)
Definition know_lookupABI : ltac2:(zQ "b0!hn8!lc!u0!hge!un0!se!hr8!unb!tt5!hiq3!irb>2bc$a>2kx$9>4segs@1$0$4>2kn@1$0$6>2rb$5>2rk$3>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$8$7") := ltac2:(zQ "h20!hn8!lc!unb!hge!tt5!u6!uo2!se!u0!un0!uo9!up1!hr8!upa!uqb!hiq3!hkgd!irb\2bc$h1\2kx$f\4segs@1$0$9\2kn@1$0$c\2rb$7\2rk$3\1n$8\2sx$1\5hints@1$0$1\3acc@1$0$4M2\1x$2$2@9$h0^a^9^8^6^5^4^3^2^1\1v$7\3scs@1$0$4\6hints0@1$0$1@3$6^3^2^1\4acc'@1$0$4\6hints'@1$0$1M5\1x@1$5@1$0$3$2@5$d^a^9^8^7^6\2bs@1$0$3@3$6@3$e^6^7^1^3^2@2$a^2^1$b").
Lemma know_lookupABI_eq : ltac2:(zQ "e0!hn8!lc!u0!jf!hge!un0!se!hr8!unb!tt5!hki0!hkg2!irb!hkj3>2bc$c>2kn@1$0$7>4segs@1$0$5@3$3>2rb$6>2rk$4>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$9$8@4$a^3@1$b^2^1^2@3$d^3^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_53"] "##3'p'0h03acch12bch25hintsh32knh41lh51nh62rkh74segsh82sxh91xi001xh:2x0h;2x1h<2x2h=2x3h>2x4i014acc'i022bsi036!s}$'i04!s0%0i053scsi061vp;1p;4p;3p;5p;6p;7p;8p;9p;2p;:g00eTj12Tg076Fj10Tg07?_j4?j5Jj6@j7=j8:l99l:ETg07A6j3;j4Hj5>j6<j78j8Il9FTg05_Vl97Tg05`mj33Tg07BLj55Tg05dUj36Tg07Caj2GTg008]j34Tg0097j2ATg07>Hl9BTg07Dnl9CTg003Vj6DTg002Tj51Tg06=]g017a#2g06>l#2g00`TR0g00b@R1g00aaR2g00;\R3%23R4g06?k#2R5g06;lR6]0R7]2R8]8R9]5R:]6f2R;f1R<#0f0R=P<C?A;;=<P1P:f3R:%0;P<P;P=DJP:!s0%CHP2P9f4R9%0:P;!s=$=E@P9!s2'D>P3P8f5R8%09P:!s?$<P=F=P8!s4,E<P4P7f6R7%08P9!sA$!s?$G:P7!s6/F8P5P6f7R>%07P8!sC$!sA&M99P>!s91GIP6f8R?P7!s@$!sQ-7R@P6P6P=A3;<=RAg00hSRB%21RCP6f9RDf:P?P>P7D5A67>=?3;<1G<=REn10110000021010200RFg06A<RGn!s@'33010610510420!sW$300!t@$DP>P?P7!t],M97PAPFP!sdC546X46!sj$@PAPBPCP6P?!sv$7P8D5A687!tu$P!tq6!t+D,A6P?%0>RG!tj/P=M9B!u~%!s;1CEDP?PG!vw4:EP!w46F546eX>5D1X=4D1X<3D1X;2D1X:1D1X90D1W7W3W1o"). Qed.
End FPX_53.

Local Close Scope Z_scope.
Section FPX_54. Context {fx : XPropExec.FPState}.


Definition sym_readBI : ltac2:(zQ "d0!hu2!hn8!u0!usc!lc!u6!un0!se!mq2!tt5!ut6!irb!hkk4>4segs@1$1$6>2ss$a>2bc$b>2kx$c>3scr$3>1a$8>1n$2>3sx'$4@1$5@2$0@2$0@2$0$7@1$1$9$3$2") := ltac2:(zQ "i44!hn8!hu2!se!tt5!usc!u0!jjd!lc!unb!uu2!jj6!uud!uv3!uv9!vg2!hkkb!mib!kvd!u6!mr2!mqa!hkl7!vi1!ho7!un0!vi5!vic!vj9!vk2!mq2!vka!ut6!irb!hkk4!hkm0!hkn2&@2$1@2$1@2$1$2@1$0$3$4$5&@1$h2~0&\1x$8~1&@1$h0~0\4segs@1$0$h8\2ss$hf\2bc$i0\2kx$i1\3scr$4\1a$hd\1n$5\3sx'$7M8~2@8$i3^6@1$hc^7@1$h3^3@1$h4^3^2^1@1$he^4@1$h1$3\1v$2\3scs@1$0$3\5hints@1$0$7@2$a~0@4$6@2$1@2$1$2@1$0$3$4$5@4$6@2$1$2@1$0$3$4@4$6$2@1$0$3@2$h5^9^3@3$b$3@3$f^9^6^5^2@3$c@1$e^7@1$9^7^1@1$d^a\3scs@1$0$3\5hints@1$0$7M8~2@a$i2^8^7^a@1$hb^9@1$h3^5@1$h4^5^4^3^1^2\1v$2\4scs'@1$0$3\6hints'@1$0$7@2$a~0@4$6@2$1@2$1$2@1$0$3$4$5@4$6@2$1$2@1$0$3$4@4$6$2@1$0$3@2$h5^b^3@3$b$3@3$f^b^8^7^2@3$c@1$e^9@1$9^9^1@1$d^c\4scs'@1$0$3\6hints'@1$0$7=1i$5@1$d^b=2rv$2M0\1x@1$0$2$2@1$9^9@1$h9^1\1e$2\1l@1$0$2^2=6reads'@1$0$2M0\1x@1$0$2@1$0$2@1$9^a@1$h1$2\1e$2\1t@1$0$2^1@2$a~0@4$6@2$1@2$1$2@1$0$3$4$5@4$6@2$1$2@1$0$3$4@4$6$2@1$0$3^2@3$b$3@3$f^d^a^9@3$h7$3@4$ha^a^9^8^2^5@3$c@1$e^b^1^4@1$h6^3~3~3").


Definition sym_stepBI : ltac2:(zQ "80!hn8!un0!vn5!usc!vnc!ut6!irb!hkk4>2bc$6>2kx$7>4segs@1$0$1>1i$2>2ss$5>3scr$3$4") := ltac2:(zQ "lfd!vo6!vqa!hu2!se!lc!tt5!vr0!hn8!u6!jse!vnc!u0!vr8!usc!kvd!mq2!vre!vs5!vsb!i4!mrb!vt4!hge!vu1!vv0!vv6!vj9!vk2!hko1!ho7!hgh2!hgh6!rb!hgk3!hgke!hgl5!hgle!hgm6!hgmf!hgn5!hgnd!jj6!uud!ui7!vn5!hgo8!hgod!hgp6!hktd!hkuc!hkvd!hlgb!hlh6!hgta!hgu1!hgua!hgv3!uv9!hli5!hkkb!hlj7!hhg0!mib!ige!un0!muc!hhga!spb!hhh1!hhh9!hhi1!hhi8!hhj3!hhjb!hhk3!uv3!hhka!to2!hhl6!hhle!hhm5!vg2!vka!uu2!hhn1!ut6!hlk3!irb!hll2!hkk4!hlm2!ru6!jm4!qoa!hhq3&@2$2@2$2@2$2$3@1$7$5$d$b&@1$8~0&\1x~1$a&\2p0~0$a&\2p1@2$2@2$2$3@1$7$5$d$a&@3$i6@1$0#5ZKv$he@2$i7@1$0#5Z&\3rs1@1$1@1$0#5\2rm@1$1@1$0#3$6&\2rd@1$1@1$0#5~6&\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5$6&\2rd@1$1@1$0#5~8&\3fmt$h1~9&\2rd@1$1@1$0#5\3rs1@1$1@1$0#5$6&\3fmt$h1~b\2bc$l7\2kx$l9\4segs@1$7$k0\1i$ic\2ss$l5\3scr$d=1g>1r@1$1@1$0#5$3\1r@1$1@1$0#5@2$l4@1$h2^3^1=1p$h6@1$kf^3Mic\1i$ic$a^5\2rd@1$1@1$0#5\3imm@1$1@1$0#h4@3$c@4$h0^6^2@1$h4@2$h7@1$0#k0@2$i8@1$0#k0@2$jd@2$h5@1$0#h4^1+c@2$9^3+4@1$e$5^5\2rd@1$1@1$0#5\3imm@1$1@1$0#h4@3$c@4$h0^6^2@1$h4@2$h7@1$0#k0@2$i8@1$0#k0@2$9@2$jd@2$h5@1$0#h4^1+c^3@2$9^3+4@1$e$5^5\2rd@1$1@1$0#5\3imm@1$1@1$0#h5@3$c@4$h0^6^2@1$h4@2$9^3+4@2$h7@1$0#k0@2$i8@1$0#k0@2$9^3@2$h5@1$0#h5^1@1$e$5^5\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3imm@1$1@1$0#cM3\1x$3$a@2$j2^b@1^5^2\1z$h6@3$c@4$h0^8^4@1$h4@2$9^5+4@2$lc@2$lb@2$9@2$le@1$0#k0^1@2$h5@1$0#c^2-2@2$ld+2+k0@1$e$5^7\1n$b$6\2op$h3\1a$3\1b$3$6\2op$h3\1a$3\1b$3$6\2op$i0\1a$3\1b$3$6\2op$i0\1a$3\1b$3$6\2sx$4\2lo$b\1n$b\1e$3$6\2sx$4\1k$b\2i0$h6\1n$b$6\1c$k3\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3imm@1$1@1$0#d=2tk$h6@2$h7@1$0#k0@2$i8@1$0#k0@2$9^5@2$h5@1$0#d^1=1a$3@1^7^4=1b$3@1^8^4M8\1x@1$8$4$aM8\1x@1$8$4@1$8$4@4$ja^f^7^2^1\1t$4@2$i9$4^1M8\1x@1$8$4@1$8$4@4$ja^f^7@2$j2^f^2@2$j2^f^1\1t$4@2$i9$4^1@4$l8^f^7^2^1\1t$4@3$c@2$i4^cM4\1t$4$h6^1^4@2$9^9+4@1$e$5^bM7\1x@1$7$4$a@1$l1^a$6\1t$4\5dirs'@1$7$4@3$c@2$i4^dM4\1t$4$h6^2^5@2$9^a+4@3$hd$5@4$ka^2^9^4^3@1$e$5@3$kb^1@1$l3^c@1$l2^c\2sz$hf\2sx$4\2rd@1$1@1$0#5\2rs@1$1@1$0#5\3imm@1$1@1$0#c=1n$b@1$h9^5=3sx'$4Mhf\2sz$hf$4^6^5^5^5$jf=1a$f@3$hc^f@1^9^4@2$h5@1$0#c^3M8~2@8$j0^e^c^h0^f^b^1^3^2\2p0~0M2~3^1\2p1@2$2@2$2$3@1$7$5$d\3nx'$bM2~4^2\2p2@2$2$3@1$7$5\4scr'$dM2\2p2@2$2$3@1$7$5$a^2\1v$3\3scs@1$7$5@3$c@6$h8@2$9^h0+4M4\0$4@1$7$3@3$i1@1$0#5^d~5@1$h2^h3@3$i5@1$h2^h3@1$i2^d^2@1$hb^h3@1$ha^h3^5@1$i3^h3^1^3$6\2sz$hf\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3imm@1$1@1$0#c=1n$b@1$h9^4=1a$f@3$hc^d@1^7^4@2$h5@1$0#c^2M8\1x@1$8@1$8$f$a@2$j8@1$i3^a^1\2r'@1$8$f@3$c@6$h8@2$9^8+4@1$h2^b@3$hd$if@3$id^2^3@1^9^5@1$hb^b@1$ha^b@1$j9^b^1@3$ia$5@3$jb^f^2^3@3$j4^f^2^3^a$6\2op$h3\2rd@1$1@1$0#5\2rs@1$1@1$0#5\3imm@1$1@1$0#c@3$c@4$h0^8^3@4$j3^c^4@1^6^2@1$h4@2$h5@1$0#c^1@2$9^5+4@1$e$5^7\2op$h3\2rd@1$1@1$0#5\2rs@1$1@1$0#5\2sh@1$1@1$0#6@3$c@4$h0^8^3@4$j3^c^4@1^6^2@1$h4@2$h7@1$0#6^1@2$9^5+4@1$e$5^7\2op$h3\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5@3$c@4$h0^8^3@4$j3^c^4@1^6^2@1^6^1@2$9^5+4@1$e$5^7\2rd@1$1@1$0#5\2rs@1$1@1$0#5\3imm@1$1@1$0#c@3$c@4$h0^7^3@4$jc^b$k1@1^5^2@1$h4@2$h5@1$0#c^1@2$9^4+4@1$e$5^6\2op$h3\2rd@1$1@1$0#5\2rs@1$1@1$0#5\2sh@1$1@1$0#5@3$c@4$h0^8^3@3$kd^4@1^6^2@1$h4@2$h7@1$0#5^1@2$9^5+4@1$e$5^7\2op$h3\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5@3$c@4$h0^8^3@4$jc^c^4@1^6^2@1^6^1@2$9^5+4@1$e$5^7\2fm@1$1@1$0#4\4pred@1$1@1$0#4\4succ@1$1@1$0#4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5@3$c@2$i4^9@2$9^6+4@1$e$5^8\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3imm@1$1@1$0#c@3$c@2$i4^7@2$9^4+4@1$e$5^6$6$6\2op$i0\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5@3$c@4$h0^8^3@4$la^c^4@1^6^2@1^6^1@2$9^5+4@1$e$5^7\2op$i0\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5@3$c@4$h0^8^3@3$ke^4@1^6^2@1^6^1@2$9^5+4@1$e$5^7\2wd$ib\2aq$4\2rl$4\2rd@1$1@1$0#5\2rs@1$1@1$0#5=1n$b@1$h9@1$ie^5=1e$3@1^8^2M4\0$4$a@3$j1^f^1^7=1a$f@3$hc^f^1ZM8~2@8$j0^e^c^h0^f^b^1^3@1$j7^8\2p0~0M2~3^1\2p1@2$2@2$2$3@1$7$5$d\3nx'$bM2~4^2\2p2@2$2$3@1$7$5\4scr'$dM2\2p2@2$2$3@1$7$5$a^2\1v$3\3scs@1$7$5@3$c@6$h8@2$9^h0+4M4\0$4@1$7$3@3$i1@1$0#5^c~5@1$h2^h3@3$i5@1$h2^h3@1$i2^c^2@1$hb^h3@1$ha^h3^5@2$i9$f^8^1^3$6$6\2wd$ib\2aq$4\2rl$4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5=1n$b@1$h9@1$ie^6=1e$3@1^9^3M4\0$4$a@3$j1^h0^1^8=1a$f@3$hc^h0^1ZM8\1x@1$8$f$a@1$i3^d\1r$fM4\0$4$a@2$l0^1^2@3$c@6$h8@2$9^b+4M4\0$4@1$7$3@3$i1@1$0#5^7~5@1$h2^e@3$i5@1$h2^e@1$i2^7@1$h4Z@3$hd$if@3$id^2^4@1^c^5@1$hb^e@1$ha^e@1$j9^e@1$je$f@3$ia$5@3$jb^h2^2^4@3$j4^h2^2^4^d$6$6$6\2op$k2\2wd$ib\2aq$4\2rl$4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5M8\1x@1$8@1$8$h3$a@1$kc^7\3aop@1$8$h3=1n$b@1$h9@1$ie^7=1e$3@1^b^4M4\0$4$a@3$j1^h2^1^9=1a$f@3$hc^h2^1ZM8\1x@1$8@1$8$f$a@2$j8@1$i3^f^1\2r'@1$8$fM8~2@8$j0^h2^h0^h4^h3^f^2^4@1$j7^b\2p0~0M2~3^1\2p1@2$2@2$2$3@1$7$5$d\3nx'$bM2~4^2\2p2@2$2$3@1$7$5\4scr'$dM2\2p2@2$2$3@1$7$5$a^2\4vold$3\3scs@1$7$5@3$c@6$h8@2$9^h4+4M4\0$4@1$7$3@3$i1@1$0#5^f~5@1$h2^h7@3$i5@1$h2^h7@1$i2^f^2@3$hd$if@3$id^9^b@5$l6^hb^h2^c^2@1^h5^d@1$hb^h7@1$ha^h7^5^8@3$ia$5^1@3$j4^hb^9^b^3$6$6$6$6\2op$j5\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3csr@1$1@1$0#c$6\2op$j5\2rd@1$1@1$0#5\4uimm@1$1@1$0#5\3csr@1$1@1$0#c$6\3fmt$h1\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3imm@1$1@1$0#c$6\3fmt$h1\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3imm@1$1@1$0#c$6\2op$k6\3fmt$h1\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3rs3@1$1@1$0#5\2rm@1$1@1$0#3$6\2op$k4\3fmt$h1\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\2rm@1$1@1$0#3$6\3fmt$h1~7\2op$k9~a\2op$k7~a\2op$k5~a\3dst$j6\3src$j6~7\3dir$k8~c~c").


Lemma sym_readBI_eqf : ltac2:(zQ "h10!hu2!hn8!u0!usc!lc!u6!jf!un0!se!vj9!mq2!tt5!ut6!hktd!irb!hlmc!hln6>4segs@1$1$7>2ss$c>2bc$e@3$6>3scr$3>1a$a>1n$2>3sx'$4@1$5@2$0@2$0@2$0$8@1$1$b$3$2@4$d^3^2^1@1$f@1$9^2@3$h0^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_54"] "##9pp'0h01nh11ah23acch32bch45hintsi00!s/%h51li011lh62rbh72rkh84segsh92ssh:2sxh;3sx'h<1xi021xh=2x0h>2x1h?2x2i031ei046!sv$'i053scsi064scs'i071ti081vp;1p;2p;4p;3p;5p;6p;7p;8p;9g00eTR0j1=Tg01:Aj2BTg00hSj1VTg07FHj10Tg076Fj17Tg07GUj4Xj5Uj6Qj7Nj8[Tg07Hhj3Wj4Rj5Oj6Mj7ZTg07A6j3^l9FTg07J:j1LTg043Tj1<Tg044aj1?Tg07KFj1KTg00f4j1JTg07LUj8ITg07Mij29Tg07O7j38Tg07PHj1;Tg07QVj1:Tg07Rej35Tg07T5j1>Tg00kNj24Tg00O[j1DTg07UBj4C!t1$Tj3GTg00g4j1ETg00nJj1PTg008]j3HTg0097j2STg07?_j4TTg07VSj3]Tg003Vj6\Tg002Tj5@Tg0044j3YTg01SYj4ATg06?kR1f1R2f0R33Yp=2g00`TR4f2R5P2P3CAp=1P5g07WmR6!s8'3P5g00aaR7!s8'6g06>l#=g07Y=g06=]P6g01U4R8g00;\R9%=1R:,B4R;/B6R</B7R=#VR>];R?^07R@]1P!tA$%02#7CXAW523P8P@f3R@P5P2%05#7P3DUP!s5$P3CRP7P?f4R?P@P5%0@#!t]$EQP?!sI'DOP9P>f5RAP?P@%0?#7!s?%FNPA!sM,EMg00b@%=9g06;lRB^2:]4^:9^07]7^64RCf6RD%0ARE5^?PBP>PA%LD%<@%?!tk%K?%J1RFGIRGf8RH/95A8HDARI/2251:f7RJ#;RK%:JRL;5353;f9RM#>RN56<,4=RO!s|$5%<ARP%?AR!u<%3P2O6f:RR!sw$RHJ!su%%;M%:M!sn&;#>!sj&SP0P4P4%:HRT%>RRR#DP2n10110200020020103101RUA8MJDRVPJPDPAPUCC=G12'!t'%HRUP0P4%=4RWPT%J4RXP3!sn77!tQ%%ER!tP&Y%P=RZn!sP'33010810610420!s-%00P!sG551!sz%510000!v%$GP!v1%JPM%0HPPP!v0+M9FPSPYP!t6d5H>X5C!t4$?%LA%<5%?!zB%K@PFGI19J5A8JA?!w<'D%:D!ui&>H!ui%!sd$DPH%0J%<?%?!yk%!tt%19M512V251:A5UT353;=6<R,4=!wo%PL%DN!wh;R!w_$?PR!wa%,2I51:!s^$WPLP!wW;=5K!wX%!yn&!vCe,S>P?%7ERZPDPECTA]?EDE\!tl&Z!|R'G[!s8&!s6&FZ5H>eX?9D@X>7D@X=8D@X<6D@W3W9W8o"). Qed.
Lemma sym_stepBI_eq : ltac2:(zQ "c0!hn8!jf!un0!vn5!vj9!usc!vnc!ut6!hlo3!irb!hlmc!hlp2>2bc$9>4segs@1$0$2>1i$3>2ss$7>3scr$5@3$1$6@6$8^5@1$a@1$4^2^4^3^2^1@5$b^5^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_54"] "##u}p'0h03scrh11ai001ah22bch31ii011ih41ni021nh51oh64segsh72ssh83sx'i033aopi042aqi051bi061ci073csri083diri095dirs'i0:3dsti0;1ei0<2fmi0=3fmti0>2i0i0?3immi0@1ki0A2loi0B3nx'i0C2opi0D2p0i0E2p1i0F2p2i0G4predi0H1ri0I2r'i0J2rdi0K2rli0L2rmi0M2rsi0N3rs1i0O3rs2i0P3rs3i0Q4scr'i0R3scsi0S2shi0T3srci0U4succi0V2sxi0W2szi0X1ti0Y4u!tu$Z1vi0[4voldi0\2wdi0]1xi0^1zp%0p&0p;1p;2p;3p;4p;5p;7p;6g00eTS00j1WTg01:AR0j2[Tg00hSR1j1OTg07Hhj3lj7CTg01D[j17Tg07ZOj1?Tg01gjj1M!s8$mj2DTg01E@j1NTg07[Uj2mTg00MQj15Tg07\5j14Tg01FXj22Tg00f4k101Tg07]@j13Tg07^Mj20Tg07_Zj2JTg07`mk200Tg05[Nj1}Tg07aSj2z!t<$^j2wTg01jZj2qTg07b1j4RTg00kNj2YTg07cHj4aTg07PHj1`Tg07d]j4_!tN$Tj3XTg07QVj1^Tg07KFj1]Tg07Rej3\Tg07enj3@Tg07gAj1ITg07hSj3jTg07i6j3L!s/$cj1KTg07jnj3>Tg07J:j1<Tg07FHj19Tg07l;j1=Tg07mHj2VTg07nYj3GTg07T5j1UTg07O7j3TTg07ohj3HTg081<j4ETg082Lj2STg0836j4PTg084Gj3iTg085Tj4hTg086cj3gTg087oj3BTg089Ej1QTg08:Rj1fTg08;_j2eTg00nJj1~Tg08<oj1|Tg08>?j5dTg008]j3cTg0097j2yTg076Fj1xTg07GUj4vTg08?Sj3rTg003Vj6sTg08@jj6tTg08B=j5uTg08COj2bTg08D5j4pTg08E@j3ZTg08FPj2oTg08G\j6nTg0044j3{Tf2R2f1R3f0R4'b'Sp=kf5R5f4R6f3R7P2Cp?Z34p=11234,b2,S7p=:1o72!s>%;f7R8f6R9P5P6P7P2En!s?%8g08Hn?X34p=Ag06?kR:?{34p=Fg01TVR;9@34p=6g06=]g06>l#Wg08J=R<g07Y=g07WmR=g01U4R>g00aaR?g00;\R@g00`TRA%W:RB'[RC/[=RD/[?RE#O]8]4]1^0=S01Al736Q01g08JiRFP<PFP7P6P3g01VBRG#7RH#7RI#7!s$%RJ#?RK%MHRL#7RM#7#?/D4%MG#7!sS$N#N'mS027kK#5S03%46RO%NIRI'2RP&01:RQP7E1S04P6P3PKPKQ02POC:#5PPP!sB&5P6P3%5PPKPKPO%MM!t4$S06C:!sI'7PAPFf8RM%35RO/03RR'JS08P9P7%49S09/2IRS#5200K4%?NRN/D3RT'2%}H'z%NH%NJ'w'qS0:PQP5E1g08L9RJP!s$-n0110]00081010^101023010C100105!s1D4010V10A10210;!s4&@10>102S0;P1P@PFP1P@%O@RHf9RUP7%39RV/02RW10V3RXCR1Y@4RY!sS$HPUP71JUW1JUXCRPYPUP7PWPXCan1!t{'21010X00!s85P8P@g00b@RZP4PKPK%48R[%MG#?R\/D3S0<C:12[IR]!uq$X00020000PQP9C;Q00P@PF%`5PJPMP@PZ!x0%%4MR^1D\2S0=C:12^IS0>!sg23P5%3MR^/0610^7C_=X:Q%^8%]85\4C;!t{-002010X109!u85S0?P1PEPFP5P9f:R\%38R_/03S0@1DN4RN3@S0A%I6R`g08MIP@!}+$7P7g00>4!td$W00040!s#&RaO4P0PDP?PFP4P0PCP=PFP3P0PAPBPFP3f>Rb#4/2IRcP@%WARd%?LRLg00?M9jL;Re7LUS0B%3bRf%KURg=>f3n01!t/%!uv$%<bRh%9bRiP6%=bP4P2G8n200110F00012010Z10R!s:&E!s:'F10Q!s:&D!s:'E10BS0CPJ!v>2D00P1%O>RjPF%=9A@UWN'VP]P_10_7S0D=@\TRk10_27G`%<8'A%98%U8P4AT\k`AH\k`'FP9G8!t&4I00S0EP9P2!z1$X%5NRkCEPS!|K%S0F!sB-?G/S4#5S0G!sH/H!sH,10V4R!sC0IP5P2PMg00=HS0JPRPkCP%45/2IRlPQP6E1S0KP9P21SL4#5Rm9i7X!sf,L!t',PGCP!s?,MP8P]!z~%S0NP5P!st$C;S0O!~C$!s]/h!s],PP9P2Ag7XG!s:,QP@PF10_4Rn=B\6S0R!zJ,16\nS0S%Q6#IRn%f6Ro!ynCPcP@PdALLMeS0TPf%KMRc!yQ5PhPiP6fARi10f8'6,Y>!yUgU!yU8J!tJ2@PFf;Rf10^3Rh;B5P1P>PF%=M!s@$<Rp%3URq/02Rr'6Rs,e4%4U/2I!uP&7eS0VPq%K7Rt%5;R;5>q!|#2Q9#IRu10q35Gs%<U'A%9U%UU%~>S0WATpsuAHpsu'FPM!zV$!to1!u;3H!u;5S0XP1g00<\#ORqPF%|9Rv!u6$=Rw%3\Rx/02Ry;B9S0YP1P!|L$\16wy'VS0Z!xR&UP\%3f/07,6bS0[%Q8#IRy%f8Rz!xWCfBR{#4!v4,feS0\%3{Re%KfRL=>e!xa2fER|10e\'6R}%Qb#IR~P|PbPMP310eUDd3G%<{'A%9{P6P8AH|}~,F!y'8[!y'NR}!y&:!~i4!wMD300!#<7-P!#<E41000S2010J10?!s-33!s-%N10?40106!s1$O10?5010W10V!sE$M!sE&W!sE+4!#<j$!sB-!s4+S!s4,N10O!t0&!sMC5010<10G10U!s:%!th-0000!sT1!sb5\10410K!t+%6!s72N10O7!sY%!s=3!sp07!s4,Y!s4&=!v>0=!uw+!su&!sE+O10P10L6!s=5L!sm0L5!sH3!s7I:10T!sj+40108!sH+3!t-,!#E,$Q04Q05Q07Q0;Q!#=^'UP8P\P9Q0AP`PaFCQ!#:w8Q0EQ0FQ0HQ0IQ0KQ0LQ0MQ0NQ!#7m$Q0PQ!#7F$Q!#7<'!t$+SPnPoFCQ!#5JHQ0XP1PqPFPv!sv%!~r&Q!~i+wPfPbP\Q0[PyPzFCP!|F~!|F~!|F~!|F~!|F~!|F~!|FY3cW5!|J$2P7P3Q03%47R</2IR}PQP2E1P7!#MZ+<C:#5P!s?-%5}PKPKP<Q!#MO%2E1PAPF%36/03R<,J8P5P7%5lQ0:!#BA$P!#Lm~!#Lm/!#Lj+PHPMP710O2R}PRCRPY!s<-JM}Q08!s;$MP7P}PR!#LXI9P@P!#LS%Q09Q0<C:PS!#LC35!#LC,6PJP8!#LC+P[Q0=C:P]!#L7410_6Q0D!#L2&9%]9!#L2N!#3L%MP9PUP5A@UXN!#5Q$!#?+@%4w/2IRaP@PdQ0B%3wRXA>Xg!#K03wRg%9wR:P6%=w!#DYd!#K,8!#A\$5A@M}N'VPSPV10V7=@UTRT?G`W%<9'A%99%U9P4ATUT`AHUT`'FP5!#J|8!#Iv$P7PRPkCE!#Ht$E1!s<,Q0G!s=710O4RO!s@-6P2P8Q0JP<PkCP!#VR&P5P2Ai7Rm!sh5POCP!s<+9!#Id$C;P6!sa%C;!{r$!sT/h!sj/Ag7RO!s7+@PFABUG6!xQ116UG!#9y$!xPAP!xJ&TPXA>Xc!xG2PgP:P6f@10X!#I|j!#IyJQ0@=B\!#Is'8!#Lv$^2,6fR>,e4Q0>!u0%VP^A>^t;!si1AG>uh%<M'A%9M%UMQ0WATf>uAHf>u'FP8!#INX!#=<-ABpr9!zT'U/Vs!wH&pP\PwPU10x7,6w!#=E%!|uBi!#Hx%Q0\%3iRdA>dL!wR2fDRL10d\'6R\PL!#Hh&dUDd7G~%<i'A%9i!#Hi$L\!#Hif!#?G~!#?G~!#?G~!#?G~!#?G~!#?G~!#?GQ,yFP7P3P6%93#xRJCvAr736EsP6PJP7P2P3P4Et!#i/$P3P4Du5cFeW0W7W3W6W2o"). Qed.

Lemma coeffs_divkB_eqf : ltac2:(zQ "a0!hn8!hge!lc!hu2!jf!hlpf!se!hr8!hlqd!lm2>2fk@1$0$7@3$4>1m$1>2ts@1$0@2$3$1$6$2@1$8@1$9^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_54"] "p'0h02tsh12IHh21ah32a0h41bh51ei001eh62fkh71kh81lh91mh:4resth;1zi011zi021pp;1p;2p;3p;6p;4p;5g00eTj1?Tg01:AR0j2OTg02cgj10Tg08N5j1Aj2Jj34Tg08OJj1Nj2Fj31Tg00f4j1@Tg0097j2;Tg00fTj3:Tg01jZj25Tg01D[j1MTg01E@j1ITg02Acj2Hj1DTg01E^j26Tg01e0j29Tg01mEj27Tg00Yhj28Tg02C3j2<j1ETg08P\j1CTg003Vj6=Tg01SYj4GTg01Qcj5BTg002Tj5>Tg008]j3KTg00N^j2LTg00;\R1f1R2f0R33Kp=2g01TV,L3p=3g017a#?g00b@R4g00`TR5,O4R6#?R7P1]0%03#A%N3P7P1%02/J31F23P6f3R8#0f2R9;43A1893'2X07%@69192,;1P0P4P5f5R0#0f4R:;43A10:3'2f6R;#0A:692R<740A1;0<'2[^87P3f8R<#0f7R;;43A1<;3'2P1f9R;?1<2R015:;#3R=g01VB#M#IR>f:R?#0/H8'6,9:/5;#3'7/831<?8,6>,9:/5;#3,7=A1?;9R?'8R@'2X41P4^55RA%E;P3P8O1,6>,9:/5;#3,7=/8?/2@X;A158<#31<;9,6>,98/5<#3'7/80,;1%0;R1#D%C;E=A41<2P3E=P4P5P8P9CG=:62R9941<A1;<9'2eW1X:7X25X74P2P3O2n2001102000120101100X36P3DBX07D>X94D>W6o"). Qed.
End FPX_54.

#[export] Hint Rewrite coeffs_divkB_eqf : bceq.
Section FPX_55. Context {fx : XPropExec.FPState}.

Lemma lin_lowbits_knB_eqf : ltac2:(zQ "90!hge!hn8!u6!jf!se!hr8!hlrd!hlse!lm2>2fk@1$1$5@3$3>1e$4>1k$0@1$2$0@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_55"] "##,1h01bh12fkh21kh31mh42tsh51xh62x0p;1p;2p;3p;6p;5g00eTj1;Tg00hSj1JTg02cgj10Tg08R0j1=j2Hj3DTg08SHj1Ij2Gj3ETg01:Aj2ATg08OJj1?j32Tg01D[j1>Tg01E@j1<!s/$^j28Tg01_Wj19Tg01b6j3:Tg000Lj31Tg01jZj24Tg00kNj27Tg08T]j25Tg008]j33Tg0097j2FTg08N5j1BTg08Unj1@Tg003Vj6CTg002Tj56Tg017a#;g00`TR0g00b@R1%J1R2]2f0R3#0#=%I3P1P2f1R4#0/H31G431A10#;R5g00;\R6]4^31R7f2R8#?P6P2P3g01VB#>#<R9/84R:%98R;9:15R<O2A115;/4:,71R;158:R=n010!s#$20000P6P2f3?2:<P;P!sB2532X07P6P21893R9%94R69:15528A1156/49,711549!s_1,F2%08R9#B%@8ECAD943AE843532eX61D6X50D6W1o"). Qed.
End FPX_55.

#[export] Hint Rewrite lin_lowbits_knB_eqf : bceq.
Section FPX_56. Context {fx : XPropExec.FPState}.

Lemma lin_nowrap_lB_eqf : ltac2:(zQ "a0!hn8!hge!lc!hu2!jf!se!hr8!hlu1!hlv0!lm2>2fk@1$0$6@3$4>1c$1>2ts@1$0@2$3$1$5$2@1$8@1$9^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_56"] "##+|p'0h01eh12fkh21oh32tsh41xi001xh52x0i012hii022loi031pp;1p;2p;3p;6p;5g00eTj14Tg01:AR0j23Tg02cgj11Tg08WGj17j2Aj3>Tg08X]j1Dj2<j3?Tg00hSR1j1;Tg028nj12Tg01bSj30Tg01T9j28Tg01G5j29Tg00Yhj2:Tg008]j36Tg0097j2CTg027^j1BTg02i6j1@Tg003Vj6=Tg002Tj55Tg017a#4g00b@R2g00`TR3,32#4R4g00;\R5]3f0R6#1#7%D6P4P5f1R7#1/A61<761322R8#;^03R3f2R9#2R:P1P8P5A0697P0P2P2P5P6g01TV/87g020<,96':n2001103000120102101R0g00>4R;n10110000!s=$0300!s|%f3#2?0!t#$!sJ6565X23!tN':76!sM9,C5%19R;#B%@9E=A>;76A?976565eX54D5X42D5W1o"). Qed.
End FPX_56.

#[export] Hint Rewrite lin_nowrap_lB_eqf : bceq.
Section FPX_57. Context {fx : XPropExec.FPState}.

Lemma mkSrlB_eqf : ltac2:(zQ "80!se!hn8!jf!hge!hr8!hmg1!hmg9!lm2>2fk@1$1$4@3$2>1a$0>1s$3$0@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_57"] "##>Fp'0h01bh11eh21ch32fkh41oh51sh62tsh71xi001xh82x0i013dtsi022hii032l0i042l1i052loi061pi072p0i083rtsp;1p;2p;3p;4p;6p;5g00eTR0j1HTg02cgj15Tg08Z0j1Qj2aj3ZTg08[?j1Kj2Xj3YTg01:AR1j2;Tg00hSR2j1PTg028nj1Oj2@Tg01_Wj16Tg01`dj1>Tg04QLj1FTg01D[j1ITg01E@j1`!s/$^j29Tg01b6j3CTg08\Kj2GTg00Yhj20Tg02IEj2Vj1_Tg000Lj37Tg01j=j22Tg08]\j28Tg02;Gj14Tg08^mj2BTg00f4j1NTg01SYj4=Tg08WGj3Mj1TTg00nJj1LTg00N^j2ATg02JYj2?j1JTg08X]j3Ej1RTg008]j3:Tg0097j2STg08`?j1UTg003Vj6<Tg08aYj1^Tg027^j1]Tg02i6j1\Tg002Tj5DTg00MQj1[Tg04MSj3WTg00b@R3f2R4f1R5f0R6C=p=3g00CE%[67W5p=1g017a#Hg00`TR7P7^53%56#Q%K6P3P7%55/a61X561;33R8#PR9^17R:%O4g00;\R;P7%64R<#>#FR=g01VB#I#`R>/95R?1;37R@#HRA=C3<RB'G'0RCf3RD#5/V4RE'0A73A</2?18?B53A#4R<P1PAPAP7P;1;AARF10=E1B?BRBPAPA%N@R?P?C=R?n010!s#$20000P0P@P7P5f4RE/1DRG!s7&4f6RHf5RI'1RJP2P8P7P;P9f9RK#5f8RL#6973ARM;MERNPHA3AME#4ROO1%L8RP!t421P3P3P7P6P;P7f:RQ,9>RR,25RS126R'A18RL93AS#4f;/1Q!se1n2001106000120105102RSf7RR,1LRTn101!sU%210!sM$!s8%8!sf%20107104!s;%1!s;,6103!t%&0!t%'1108!u22;P71?D4RU,0CRVP!w0-PF10=UPBP!vs2RU!vu'P!vn+P!vd-AEKME1@KOROP!vH3SP!uF~!tk$W5:7X4:P;!zS%J4P;!w`$4O1RX,0C!uX4X!uX5!uVAPNP!uO~!uO;=:7WX0:P;^6A^23R:%R!uQ%!wz/!w`BPHPMPEO2!u6~!u6EP7%65R:!~|$W19>6RTAC3A:RS'G'01?45RO!~b%:/2T18TS!~b$!w|1WO1BTS!w~;11D4!uv'11IE!ux,%6R!~7$9=ELEA3A9E#4,@LP!~0@19>KR>,25R;126>'A18>L93A;#411QK!~+E11RH!v|~000,S7%54RR#T%U4E<%_R%^4E<%]R%\4E<AZR56AY4565:7eX83DDX77DDW3o"). Qed.
End FPX_57.

#[export] Hint Rewrite mkSrlB_eqf : bceq.
Section FPX_58. Context {fx : XPropExec.FPState}.

Lemma lowbitsB_eqf : ltac2:(zQ "90!hge!hn8!u6!jf!se!hr8!hmh3!hmhd!lm2>2fk@1$1$5@3$3>1e$4>1j$0@1$2$0@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_58"] "#$-9p'0h01oh11xi001xh21zh31eh44IHe1h54IHe2h62e1h72e2h82opi012oph91ni021nh:1ki031kh;2sxi042sxh<3IHeh=2fkh>1ii051ih?1jh@2loi06!s+$72a0i082a1i091bi0:2b0i0;1ci0<2e0i0=3op0i0>1vi0?1yp;1p;2p;3p;6p;4p;:p;5g00eTj1aTg00hSR0j1`Tg02cgj18Tg08c1j1Zj2Aj3PTg08dBj1_j2@j3?Tg008]j32Tg00MQj1QTg01jZj27Tg01D[j1YTg01E@j1W!s/$^j2BTg0097j2:Tg00O[j1ITg02C3j1Gj2\Tg01T9j24Tg00kNj2TTg08R0j36j1DTg08SHj30j1ETg08ePj1FTg003Vj63Tg02Acj1Cj2[Tg08P\j1JTg00Phj3>Tg01FXj2X!s/$;j2VTg08flj2OTg08gJj2RTg00N^j2NTg07aSj2STg00R5j3MTg00SBj3=Tg01e0j2^Tg00TOj3KTg00U\j4LTg00Vij4HTg00^jl:]Tg002Tj5UTg00b@R1f0R2'Tp=5f6R3f5R4f4R5f3R63Pf2R7f1R8;?232p=;P1P41A561@78P2DUp=<1\82,47p=11[!s0&9g017a#ag00`TR9%`1R:^?1R;%82#Z%_2%87R</A21@7252;X39P:P<%Q2R=P7P=g020<R=,78R>g01VB#Y#WR?/B2'7#5,::P:%86R@%Q8RAP2P6PAP2F;eX11E<X21g00aaRA!sz$I2R<P7P<P1^39R<%G6g00;\RBP:P2%I7RCO1,48g01TVRD,T1RE%85?6C8n010!s#$20000PBP:A185CRFPEA05!sF3RG52:X2<P:^:!t9$H%E6PBP:PFPEP2PCP8O2!sY1=2:GX0HPBP:%I8RG9126PEA06G!sO2,::%D@%F6E3%C@%J6E3P:P@PG!ur$G!ur,W9g00<\RG1A@21@6252;R@%84RC!w4$4!s7$FP:%83RIA>568RJP3PJP;f7RJ/@5PGP:P3P0P1P:P2P8O1RK!s4%f9RL#8RM?P57RN1X82RO1B?6RP'7#5RQ!v?$>J35RR997MPEA6MR7RS!vE2Tn101!s8%21010?!vy%f8RU#8RVA>346RW598PEA6VW8RX!sg2Y!sg2000!t}&!tw&PN1V82RN/7P#5RKP!t@7!sk7Y!s$$9P:P6!so&8P7O1RZ17>PR[,O2#5R\!su4>00PT!u9$;R]#8R^A>LU3R_595PEA6^_5R`!u92aP!s$%BP:f<Rb#8Rcf:Rd?>LJRe594PEA6ce4Rf!s^2gPgn0110900081010;101023010=10710:!s1D4010410610210<!s4&3105102!uv4Z1R2[#5Rh!uk:!u>'!tf~!tf$!tb%BP:172=R=1B?7Ri'7/NDRjPE!t{+S!t{$[!t{7!~&2!u1~!u11!t&$1000:0!s#51!|{/A?U48Rk!s3'L57RlP!|c%17LRRmPEA0LR7!y%2n!|]9A18UWRoPEA0UW!#4X2p!|P<!tM&PlPKP!t$7!s`7p!s$$!yM-A?L37RqP\!si4>00Pn!tm%5]_RrPEA0]_5!tm2sP!s$%!sN$4beRtPEA0be4!sN2uPu!x%~2!uM3PqPh!uH:!u$'!t`~!{n1P!{],qP[!td7!{W2!tr~!{WN0Ru52:X0;P;1@J7Rn!{g/!z;+ZPQ!#7ZK!s`3!#8<^qP\!#5>~!#6~UqP!#6x~!z0_!#6a~!z0o1=2:uX0;P<%GJRg!z-8!#6e%P8PRO1,47PEP!#@C2S!#6d8P2PWO1,48PEP!#@52X!#6cG!t#7!s`7X!s$$!zl3S!y26S!tg$6P_O1,45PEP!#?c2`P!s$%BP:P5PeO1,44PEP!#?R2f!s8$!yp}!uF5h!uF:!u#'!t`~!{R@S!{RD!tr~!{RN0!{R$2<PH%EJRf!{R@mPEP8PRP7!#KZ2RR!{Q:oPEP2PW!#L44RW!{PH!s~7!s`7W!s$$!{P3R!y06R!tf$rPEP6P_P5!tf4_P!s$%BP:PtPEP5PeP4!sL4ePe!wx~2!uD6h!uD:!t~'!t`~!{N@R!{ND!tr~!{NT0H!{G$4!#EJ&J52Ru!s3'U68Re17Oi#5!#F23!{7&A>457RO912JPEA0J!yU5!{=<!t5&Pe17N!t0;!sd7!vY%9P:P7!|/'17>iR>,O2!sm6>00Pp!ty%UJ4RN916dPEA0dN6!ty2NP!s$%sPs!w\~2!u56R2>!u0<!td~!{647PBP:1B?8,7=/NDRD!{@+k1S!tr;!{D2!u$~!{DO,::%8JRs#DRN%FJRpE3%CsR>%JJRkE31As7R=P8!s0$5P!#[Q$sPOP2PJPO!#[Q,5X79W4X69W8P:PIAM568ROP3POP<Pg!~^$2AM346RO!#@R%A6VO!#^48UOR?PEA0U!sF3R_!#^4%HPf!sy$?PEP2PO!#^'7_!#^'%AM457R_!}1+_!#^,4PNPpE3P>Pk!uV&_!uV$_!uV,X5FX79X4@X69X8Gg00GERG!u`$=568R_P3P_P;P!#K&&9P:P4!#5L1Z1^82RZ!#[o$P!ti$=J35Rn!#]W'n7RM!~vB!y_5_!sp%LU3R_995^!#[M&^!sp2OP!s$%!sT$dLJRO994cPEA6cO4Rc!sT2?P?!yO$7!zS88109!s1D!|U@!tT$346R?998V!x|$?8Ru!tT2RP!s$-!{/+8!sK'!s#'!w;>lP!w0%17LnRRPEA0Ln!#W|2L!w&DL!#VE+L!#VE8]P!s$%!#VE%OR[PEA0bO!#VE2bPb!vv~2!|P'?Rb!|P$?!|P3qP!s$-!vp-!s#2Rh!#SA%<Pg!v|EP8Pn!#L;&!{#3M!v{DM!#Jb2!zx3^P!s$%!#Jb$O!#Jb&!zq3c!s8$!vy~P:P2P?!#NA&!zj3uP!s$-!vx==2:h!#4q&!vwERPEP8Pn!#G`5!#Y|FBP:PL!#F0G[PEP5PO!#F05OPO!vt~!vt%bPEP2P?!#Id5?P!s$-!vsB!#C&'9!y>$BP:P!#=/+e17Zi#5Pq!vUDq!|R$=UJ4Rq!#A;'q6!|V:]P]!v=~!~-%=457R]!#:_']2!~2Y!#;/2=P8!#;5%]P2PJP]!#;58!#=g%K568R]P3P]!#=g,K346R]!#=g+]!#=g9]R=PEA0U!sF3Rq!#=g1=!xx$]!#=g7q!#=g&K457Rq!v-+q!#=gEq!uX$q!#=g;P:PIP5P6P7P8CLRGP3PG!u^,P3P4P5P6CLRg!uc,g!uc:gRV!uc$!sF3RU!uc2V!uc$g!uc8U!uc&!tG%P7CLRU!uh+U!uhFU!uh$U!uh-<FX39X9AX@AX;BP:PC!uf%P2CHRCP4PCP<%G3!ui&!tF'HR4!ui+s4!ui9J4Rs!tg$!sF3RJ!ui'%E!t#%s!uj$4!uj8J!uj'!wO'HR89123PEA038!#zD6I%F3E3%CI%J3!un$IP8!wu$8!un-9AX>1X:!uk$2M:]X39DUW=o"). Qed.
End FPX_58.

#[export] Hint Rewrite lowbitsB_eqf : bceq.
Section FPX_59. Context {fx : XPropExec.FPState}.

Lemma lsplit_divB_eqf : ltac2:(zQ "90!hn8!hu2!hge!se!jf!hr8!hmi9!hmj6!lm2>2fk@1$0$5@3$4>1m$2>2ts@1$0@2$1$2$3@2$1@1$0@2$1$2$3@1$0@2$1$2$3@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_59"] "##2}p'0h02tsh12IHh21ah32a0h41ei001eh52fkh61kh71lh81mh91pi011ph:4resth;1zi021zi031di041rp;1p;2p;3p;4p;6p;5g00eTj1ATg01:AR0j2@Tg02cgj11Tg08ggj1Cj2Lj34Tg08i;j1Nj2Hj30Tg008]j32Tg00f4j1BTg0097j2<!s8$Tj36Tg01jZj25Tg01D[j1MTg01E@j1KTg02Acj2Ij1E!s;$^j2:Tg01e0j29Tg01mEj28Tg01SYj47Tg02C3j2=j1FTg08P\j1GTg003Vj6>Tg01Qcj5DTg002Tj5?Tg00N^j2JTf0R1g01TV'Jp=3g00b@R2g00`TR3f1R4P1C7p=;g017a#AP21@23R5#AR61@66R7]0%11#C%N1P6P7%14/L11H41P5f3R8#1f2R9;41A0891527X06%B59094,<7P0P2P3f5R:#1f4R;!sN$:;1527f6R<#1A6594R=74:A0<:=527[^76P1f8R=#1f7R>!sY$=>1527P7f9R>?0=4R?P0P6P6P7P1g00;\R@P7f;RA,5<#3RBg01VB#M#KRCf<RD#1/I:':,9</5A#3'8P6P61;<:RE=65!ux$RF!sv$4A65E1C7REn010!s#$20000n20011!s9$120103104!tQ'f:RG?0>9RHP@P71=D:,:C!t:',8BPFP!stFRD527X97P2^43RI%F>!uY+!s~$P9P:O1!t$W=27DX;I!su+?!tu$5:G#31=A;!sy$:/5G!v7,:;R;!v7'!v5+;1C7!t;E,<7%1>R;#E%G>E>A4;=4P1E>1;89=654R994;=A0>=9527eW1X:6X23X62P4P1O2!sz01102100X35P1DDX06D?X82D?W5o"). Qed.
End FPX_59.

#[export] Hint Rewrite lsplit_divB_eqf : bceq.
Section FPX_60. Context {fx : XPropExec.FPState}.

Lemma and_high_splitB_eqf : ltac2:(zQ "90!hge!se!hn8!hu2!jf!hmk5!hr8!hml6!lm2>2fk@1$2$6@3$4>2bk$1>1j$0>1c$0>3dts@1$2@2$3$0$1>3rts@1$2@2$3$0$1$1@1$7@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_60"] "##2[p'0h01ch13dtsh21eh32fkh41jh51oh63rtsh71xi001xh82x0h92x1h:2x2h;2x3i012hii022loi031pp;1p;2p;3p;4p;5p;6g00eTj1<Tg01:AR0j2>Tg02cgj12Tg08jLj1Bj2Hj3Ej4Cj5@j6MTg08kdj1Tj2Fj3Dj4Aj5?j6NTg00hSR1j1STg028nj1Rj2;Tg01D[j1QTg01E@j1G!s/$^j27Tg01jZj24!s/$=j25Tg00N^j2:Tg01F;j26Tg01e0j29!s8$Xj28Tg04MSj31Tg008]j3=Tg0097j2ITg027^j1JTg02i6j1KTg003Vj6LTg002Tj53Tg01SYj4OTg02;Gj1PTg00b@R2f2R3f1R4f0R5CO#Pp=0g017a#<g00`TR61>26#<R7P6^67R8]1R9^02R:^42%25#B%T5P2P:%24/H51F45P2P9%23?E45AD345P7P8f3R8#2P3P4P5CCP8!s0&AP7P6f4R9#2!s:'D@P9!s2+?1>22R:#S^26R;f5R<#RP1P:P6P5g01VB#Q#GR=/79,48R>=074R?O1P0P2P2!sK%0;\R@P6f7RA,7=RB,54RC155B':f6RD14DBRE'6RF19CB'8=07<g00=HRCA07F<g00EIRFA07E9f83131n010!s#$20000n2001103000120102101RE168>=073A1F?<51CR>n101!s^%210!sV$!u>%1;D?PEP!sF65=6X5;!sL&7=8,43R:=075R1,;<!uY,P@!sF$DRD,54R=155D':14<DR@,6<R019=D!uN$9A0709A07@8=1FA51C!uAE163:=074A1F1951C!tu5,I6%2<RC#J%K<ELPC!x,,EMP<!s4-N5=6eX;7D3X:7D3X92D3X82D3X76D3W3o"). Qed.
End FPX_60.

#[export] Hint Rewrite and_high_splitB_eqf : bceq.
Section FPX_61. Context {fx : XPropExec.FPState}.

Lemma and_low_splitB_eqf : ltac2:(zQ "90!hge!se!hn8!hu2!jf!hmm9!hr8!hmn9!lm2>2fk@1$2$6@3$4>2bk$1>1j$0>1c$0>3rts@1$2@2$3$0$1$1@1$7@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_61"] "##1;p'0h01ch11eh22fkh31jh41oh53rtsh61xi001xh72x0h82x1h92x2i012hii022loi031pp;1p;2p;3p;4p;6p;5g00eTj1=Tg01:AR0j2>Tg02cgj12Tg08m9j1Bj2Mj3Ej4Cj5KTg08nPj1Qj2Fj3Dj4Aj5LTg00hSR1j1@Tg028nj1?j29Tg01D[j1PTg01E@j1O!s/$^j25Tg01jZj24Tg02;Gj10!s8$=j23Tg00N^j2;Tg01e0j28Tg01F;j2:Tg04MSj36Tg008]j3<Tg0097j2GTg027^j1HTg02i6j1ITg003Vj6JTg002Tj57Tg01SYj4NTg00b@R2f2R3f1R4f0R5CNp=1g017a#=g00`TR61>26#=R7P6]5R8^02R9^32%25#B%Q5P2P9%24/M51F45P2P8%23?E45AD345P7P6f3R8#2P3P4P5CCP8!s0&A1>22R9#@^16R:f4R;#?P1P9P6P5g01VB#P#OR</58,43=174#0R=O1P0P2P2!sK%0;\R>P6f6R?,5<R@,34RA135@';f5RB/4@RC18A@':=17;#0g00EIRAA17C;#0f736n010!s#$20000n2001103000120102101RCA6A=;R@n101!sS%210!sK$!t|%19B=PCP!sF65<6X4:!sL&5<3,44=175#0R9,9;!u?,P>!sF$BRB,34R<135B';14;BR>18<B!u4$8#0A17>8#0=6A?!u,EA6A98!ta5,G6%2;R9#H%I;EJP9!wU'DKP;!s2+L5<6eX97D7X82D7X72D7X66D7W2o"). Qed.
End FPX_61.

#[export] Hint Rewrite and_low_splitB_eqf : bceq.
Section FPX_62. Context {fx : XPropExec.FPState}.

Lemma narrow_maskB_eqf : ltac2:(zQ "90!hge!hn8!u6!jf!se!hr8!hmob!lm2!hmp9>2fk@1$1$5@3$3>1a$4>2k'$0@1$2$0@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_62"] "##/^p'0h01eh12fkh22k'h31oh41xi001xh52x0i011hp;1p;2p;3p;6p;5g00eTj1LTg00hSR0j1KTg02cgj15Tg08odj1?j2Ij3GTg0919j1Jj2Fj3HTg03Pnj1Bj2;Tg01G5j21Tg01D[j10Tg01E@j18Tg092Kj14!s8$^j22Tg01FXj27Tg01k:j16Tg00N^j2>Tg00Yhj23!sJ$;j2<Tg00kNj2:Tg00nJj1ETg008]j3=Tg0097j2ATg03Oaj1CTg03f`j1DTg003Vj6@Tg002Tj59Tg017a#Lg00`TR1g00b@R2%K2R3]2f0R4#5#?%J4P2P3f1R5#5/I41F54P3^01R6f2R7#Bg00;\R8P3g01TVR9/15g01VB#0R:#8R;%45'2R<,75R=%6=R=,2;R>'>'3%0:#0!s$&8R:,1='3R=P0P2P3P4P7O1P8P3%47,2;R?,77#6,2;,14g020<R@/<?,:2%E2R?n010!s#$20000RAP?n101!s:%21010100P!sL2P8P3P!t=&f3/;7P!s]H5=3X36P8P31194%44,2;,74R9%69R9,2;'>'3119:'3!t&%1;75!sU%4>1<@<,:2!tY4!tFF,A3%57R?#C%D7E@AG?54AH7545=3eX52D9X41D9W1o"). Qed.
End FPX_62.

#[export] Hint Rewrite narrow_maskB_eqf : bceq.
Section FPX_63. Context {fx : XPropExec.FPState}.

Lemma mkAnd0B_eqf : ltac2:(zQ "70!se!hn8!jf!hr8!hmq9!hmr2!lm2>2fk@1$1$3@3$2>1a$0>1b$0$0@1$5@1$6^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_63"] "##jnp'0h01ei001eh11jh21bi011bh32bkh41ch51mh61oh72tsh81ah93dtsi023dtsh:2fkh;1ki031kh<1pi041ph=3rtsi053rtsh>1sh?1xi061xh@2x0hA1zi072a0i082b0i091ii0:1li0;2l0i0<2l1i0=2loi0>1ni0?2opi0@2p0i0A2sxi0B1vp;1p;2p;3p;4p;6p;5g00eTR0j1RTg02cgj16Tg093Wj1bj2~j3^Tg094gj1Zj2zj3vTg02C3j1fj2FTg01jZj25Tg01F;j2:Tg01D[j18Tg01E@j1CTg01k:j17!s8$^j2@Tg00N^j2UTg01G5j2ETg00Yhj20Tg01T9j24Tg01_Wj1ATg01`dj1NTg04QLj1LTg01:AR1j2MTg01b6j3OTg08N5j3aj1pTg000Lj3>Tg01SYj4=Tg02;Gj1QTg00f4j1[Tg08ggj3Kj1dTg00MQj1;Tg08Z0j3Ij1mTg08jLj6Yj1e!uS$Xj2DTg08c1j3Xj1jTg08R0j3Hj1`Tg08m9j5Wj1kTg07aSj2VTg08OJj3Gj1}Tg08i;j3Bj1uTg08[?j3?j1xTg08kdj6Tj1tTg08dBj3Sj1wTg08SHj3<j1yTg08nPj5Jj1qTg00hSR2j1|Tg0097j2lTg0964j1hTg003Vj62Tg097Oj1gTg098kj1iTg09:Cj1cTg09;Xj1nTg08ePj1oTg08Unj1_Tg02Acj1rTg08P\j1sTg002Tj5PTg09<kj3]Tg04MSj3\Tg008]j3{Tg00H1f1R3f0R43]p=3g00EI?\34p=9g00`TR5?{34p=1g017a#RP5P5^25%64#b%Z4P5P5%63/~41z34g00b@R6^05R7f2R8#fP5P5P3g00;\R9P5g020<R:154:R;':R<g01VBR=#8R>#CR?%7<R<'@R@'U%8>#8!s$&CR>,E<'0RAP9P5P3f3RBO1RC,4<PBP9P5%ABRD#NRE#LRFf4RG#6RH1M65RI#RRJ=O6DRK7a@'0P6PJA>6JDRD15D@':PKC=#QRDP1PJPJP5P91MJJRLPEPJPJ%[IRMPKC=RNAKH@Kn010!s#$20000ROP0PIP5P3158:,::#7RP,@?#;RQf6RR#6f5RS;IP'3!sO&815G!sO&T!sO%Uf8RV#6f7RW;IT'3f:RX#6RYPV15R:RZ!sS%[f9R\#A9>6JR]PSPGEYR^n101105!t\%2010@10<!s;%2!s;,410;n2001106000120102105R_!uC1!s401!vt$C=R=,D;R`%7`R`,@?R?'U1E`>'0RaP9P514`Cg01TVRC#;RbP2P6P5AXHB`Rc%;4Rd!wv$E19B8Re!sD&HHB`Pd!w5'AKH?K!vd+9SGRf!vI+9WRRgPYPV1DZ=#7RZP]PGDW!um>:!um1RY!uo3:105Rh!sS%600021010B!us20!sF5Ri!sH1!us$EC;%7;/D=R=/4>'0R>/0FR;!u^,=153:,V4#;R:Pe!s|5Pe!yf2H!wY<101PePf!s$%19RSRCPCn011!sI$8111031010>3010?107108!s1D4010A10=10>100!s4&310910>!}p%!x-$!}+$1FGBRj,4<Rk!}&%AGG@K,0FRlP!|K-PLPEPNABG!|:4m!xT'A?RSP,3QRn!xX'A?VWT,3URoPXPVP[P!{I%T!{Ga!{E?Rp!uP$!{''jRjP!z|'SGB`RqP!zy&P!zu'<GB`Rr!zw-BG?KRs!uK'P!zu+Pg!u;$!zk%J!zkM!zi7!zgU!ze5P;!u8,=P!zFIX!zFIP!zB~910>Rt'1XA7P9^7J^56R7%}8!zV3P!zM&P3P@PKO2Ru,0FPDP!#54C!xk%PjPbP!~;3H!uu~!uuN/1tX27%|6R7^;6^05RH%y!uw=l!ulR!y+$Pc!{P3P3PBP`O2R_PdPh!z@o!t$$=O2!zCI!wJ~!wJR6HP5^>6^85RH%x!wGA!~|&P!#>X'PBPSPPO2,3Q!#3$'SPWPTO2,3UP^!#5:|!x]Jr!xUG!#;zDP!#3:~!wwR0HP7^1!|@$7%w!wwS!#:5'Po!weOR^!wgh!}+H!w3~!|+U7PL!#7F'u!w3I!#>e%Pu!uM2!vaiq!{J8!tJ'3P?PKO2PY!#<_w!w_~!w_S<7P5^=JR7^9J^46^16^35RK%t!wjIm!{w8W!#B~+O5!#4j~!xFTs!x@~!x@~!x@O0KP7!x8,7%q!x81p!vTX!#F?6W!#F?&O4!#F?~!wD~!wDw7!w4$4!#M&-B8RA,4<P8!#W+$8R<#NR7#LRtAO6J<Re9GB!#Vt,<R<15<@':PeC=#Q!#5f/7!s2$MPeC=ABB@!#AD1!#MS+SGP!#?2,A?WRT,3UP\PWP[%AV9>6JRV!#MV~!}V114`A!#MR+B8`!z,&71983R7!s?&<!s?%!#MR'B?e!#UK+GBR!s4'8PC!u@$ZPV!#MT~!#F:L10>t!u:,=P:P7!s]5P7!#F9M7Pe!s$&fPf!zr~>,l5%68Rf#k%h8E2%ef%g8E2%df%i8E2%jf%c8E2%mf%n8E2%`f%o8E2%pf%_8E2%rf%s8E2A^f34Av834'1eX@5DPX?5DPW:o"). Qed.
End FPX_63.

#[export] Hint Rewrite mkAnd0B_eqf : bceq.
Section FPX_64. Context {fx : XPropExec.FPState}.

Lemma mkAndB_eqf : ltac2:(zQ "70!se!hn8!jf!hr8!hmrd!hms5!lm2>2fk@1$1$3@3$2>1a$0>1b$0$0@1$5@1$6^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_64"] "##3wp'0h01ah11bi001bh21ei011eh32fkh42k'h51oh61xi021xh72x0i032a0i042b0i051ii061ki072loi081mi091ni0:2opi0;2sxp;1p;2p;3p;6p;5g00eTj1GTg02cgj11Tg09>6j1;j2Fj3BTg09?Ej17j2?j3CTg00hSR0j1<Tg0919j1:j34Tg01jZj29Tg00MQj18Tg093Wj32j1>Tg094gj30j1ETg008]j33Tg0097j2DTg09@Qj1=Tg003Vj65Tg08odj1@Tg09Aej1ATg002Tj56Tg017a#Gg00`TR1P1^11R2f0R3#1#;%73P1P1f1R4#1/F31?43g00b@R5%<5]4^01R6f2R7#:P1P1P4P0P5P1P4f3R8g020<,93R9O2f5R:#1f4R;%83R<32%1;?287R=n10110200021010800P=f6R=#1?2:;R>P!s$$f7R>#1?2=:R?P?n01100000810106101093010:103104!s1D4010;107109101!s4&6105109!u>/A4;89R?A0:;<A0;87R@!t}6@A0=:;R@P!s$$A0>=:R>P>!ts~9R>531X56P2^01R2%E7!wE0?P7P;P<O2P4P8P7O2R?!u-6?P8P:P;O2R?P!s$%;P=P:O2R=P=!u4~9=31>X22!u%$3!w0'879A0;8<A0874R<!t~6<A0:;8R;P!s$%@P@!ts~9,D1%17R@#>%=7E5%@@%A7E5AB@43AC743531eX71D6X61D6W3o"). Qed.
End FPX_64.

#[export] Hint Rewrite mkAndB_eqf : bceq.
Section FPX_65. Context {fx : XPropExec.FPState}.

Lemma mkAndKB_eqf : ltac2:(zQ "70!se!hn8!jf!hr8!hmsf!hmt8!lm2>2fk@1$1$3@3$2>1a$0>1b$0$0@1$5@1$6^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_65"] "##P=p'0h01ai001ah11bi011bh21ei021eh32fkh41xi031xh52x0i042a0i052a1i062b0i072b1i082b2i091ii0:2i0i0;1ki0<2loi0=1mi0>2m1i0?1ni0@2opi0A3op0i0B3op1i0C2sxi0D1zp;1p;2p;3p;6p;5g00eTj1GTg02cgj13Tg09C>j1<j2Fj3ATg09DNj19j2Cj3;Tg09?Ej1=j30Tg01jZj22Tg07aSj24Tg00MQj16Tg01D[j11Tg01E@j15!s/$^j2:Tg00N^j2ETg01F;j2DTg008]j37Tg0097j2BTg09>6j1>Tg09E[j1?Tg003Vj6@Tg002Tj58Tg017a#Gg00`TR0P0^10R1f0R2#3#<%92P0P0f1R3#3/F21C32P1^00R1f2R4#=P0P0P4P3f3R5P4O2R6P6g00<\R6!s?$5f5R7f4R8O2R9P!s$30P0P!t/$P7P7P5g020<R:,23R;122:R<'4#6R=O2P7f7R>f6R?O2R@P>f9RAf8RBO2RCP!s$%Bf:RDPAO2REPEn0110100081010;1010?3010A104107!s1D4010C10<10?102!s4&;10910?P8P?P7O2RFP?PBP>O2RGP!s$%CPC!tH$6!tH'>!tHp!t&$@000:0!s#6P9g00GERH!w?$0P0P3!s+&@P@P!wU%C!s$-!wC,Ag00;\R@P0127:g01VB#1RI#5%1I#1!s$&5,2;':R;'ERIPAP51D:;/4<#6R<O2PAf;R;PDO2R:n!w?$0002!td$:P;f=R:f<RJO2RKP!s$%Jf>RLP:O2RMPM!wt;B105108!s1D!vR;:10?PEPDPJP;!t8%!s$$KPK!t@$7!t@'9!t@l!y6$C!xv+A!wr<!wI%!zh'!yF+D!yF/3!y0,5!s1<!tX@FP!zX34!t8'=!t8/5!t8d!~60!zf+8!zb5PFPF!sF$0!uj5@!uj$6!s1&4!s1<!tX@0P0P4A0854RFPF!{^%A0?78!s5$!s$1!{i,7A0B5=A0B>?R9A0DAB!#3_&A0;DARGPG!#3Z~A0>?7R?A0AB>REP!s$%!#3T~!#3TDFP!#3O49P9!#3O@P@P0PIA0J5<A0J;DRD!~l2DA0L:JRAP!s$$f??0L:RLPL!~a~?PGA0:J;RJP!s$%APA!~^~!~^O!yl'!~^{?P!yb3!~^{!|f0!~^>FP?P?!~^N1!~^S570X21!zn%A0543R1P1!~d'785R7P!s$3!z~,8A0>5=!vU6!~UzPF!#63'!#8Y3!~K~!zM57!~K6?P?!~K&E!s$-!vK,B!~K';5<!{-$!~F/GP!||3!~;{CPD!s$&JPJ!~6~!y'&!~6B!#7`9!#=ns!yM3!~6{!|80!~6>7!#=nQ!~6T,B0%34RF#>%?4E@AAF32A;432570eX50D8X40D8W3o"). Qed.
End FPX_65.

#[export] Hint Rewrite mkAndKB_eqf : bceq.
Section FPX_66. Context {fx : XPropExec.FPState}.

Lemma or_disjointB_eqf : ltac2:(zQ "80!se!lc!hn8!jf!hr8!hmu3!lm2!hmv1>2fk@1$2$4@3$3>1a$0>1b$0$1@1$7@1$6^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_66"] "##/pp'0h01eh11bh22fkh31oh41xi001xh52x0h61zi012hii022loi031pp;1p;2p;3p;6p;5g00eTj1LTg02cgj13Tg09Fnj1@j2Kj3FTg09HCj1<j2Jj3GTg01:AR0j2ITg00hSR1j1?Tg028nj1>j28Tg01T9j2=Tg01D[j1;Tg01E@j1:Tg02Acj29j1A!s;$^j21Tg01G5j20Tg00Yhj22Tg02C3j25j1HTg008]j34Tg0097j2CTg08P\j1BTg003Vj66Tg027^j1DTg02i6j1ETg002Tj57Tg017a#Lg00`TR2g00;\R3^12f0R4#3#@%<4P2P3f1R5#3/K41J54g00b@R6/I6R7#?^02R8f2R9#>P1P7P3P4P5O1P0P6P6P3P4g01TV/=5R:g01VB#;#:R;f6R<#3f5R='9'1,04'2n2001103000120102101g00>4R>n10110000!s;$0300!t9%f3R?/85R@!t<,15<=,1;,04,2:!sy7P!st6R<543X38P6!uD$%H9!uA&!t#-P?P=O1!t%T=43<X68!sv%1894!sx,f4,5!tzU,C3%39R>#A%B9E6%D>%E9E6AF>54AG954543eX52D7X42D7W2o"). Qed.
End FPX_66.

#[export] Hint Rewrite or_disjointB_eqf : bceq.
Section FPX_67. Context {fx : XPropExec.FPState}.

Lemma mkOrB_eqf : ltac2:(zQ "70!se!hn8!jf!hr8!hng1!hng8!lm2>2fk@1$1$3@3$2>1a$0>1b$0$0@1$5@1$6^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_67"] "##K+p'0h01bi001bh11ai011ah21ei021eh32fkh41xi031xh52x0i042a0i052b0i061ci071ii081ki092loi0:1ni0;2opi0<2sxi0=1yp;1p;2p;3p;6p;5g00eTj1NTg02cgj14Tg09IUj1Aj2Mj3ETg09Jcj1=j2Jj3FTg09DNj1Hj3KTg09Knj19Tg09M;j3?Tg00MQj17Tg09Fnj35j1CTg01jZj2<Tg09NFj1LTg09HCj33j1ITg008]j36Tg0097j2G!sM$dj1BTg003Vj68Tg09C>j1@Tg09P=j1DTg002Tj5:Tg04MSj3;Tg00Phj3>Tg00=HR0f1R1f0R23;p=0g00D]R3?>12p=1f3R4f2R5;K1=;02p=2g017a#Ng00`TR0P0^00R6%42#A%=2P0P0%41/M21J12P6^10R6%H5g00hSR7g00b@R8P0%95R9P7P8P0P9A?312#7R3g00;\R:P0f4R;#4R<?5451045R=P:P0A5<54P=P0P0P5P5P;g020<,<2#L#7R<O2%72R>'0!sG$;P4P;P<O2/0>f5R?/1;R@f7RAf6RB'1RCP!s$$f8RD/1AREPEn011010008101061010:3010;104105!s1D4010<10910:102!s4&810710:!ta$BP?PB!ta&PCf9RF/1DRGP!s$$f:RH/1FRIPI!tW~:RJP!s$%0P0PAPBPA!t_'EPI!s$%f;/1HRHPH!tV~:RKPK!t-$0!t-yn!u/$00020001!s4210110300021010=01P:P0%44RK?5511051RL!z/%K15PL!vJ$1P1P4!vJ'0P0P4P5!s7+11;4RK11B?RMP!s$%CPC!v^~!yg%?P;P?!tb'MPE!s$&GPG!tI~:RNP!s$%JPJ!x1~!x1L!s/$1!#3S&!s-+3!x0$3;45P=!s1&!#3D,?P;P<P>C2!#33%B!s6+@!~w%PCP!~r~!}A&!~t%DPB!tJ&C!~j%PGP!~e~!tJ$BP!s$%!~e%FPA!tP&!~d+P!~_~!tP$!t-'!yTzRH!~aUA3451P!~Y%34!~Y-;P4!yD-4P?!s6+KP!~O~!~O6AP?!tH&!~N~!vh2!zR'BPB!wx~:RB!wx?RE!~R5R?560X26P:^00!#?Q$I5!~g9P1P4P5O2!~j%P1P5P4!s4$!y=VP2P5P1O2!y@%P2P1!t$$LPB!#4aP=60?X06!tw%%91R!s1&P6P3PE!za;5121012RE!s5&21PE!y3$2P4P5!ze-5P;!s6'1145P@!s$&MPM!yE~:!#?F%J!zU+!#8m~!w2L,G0%45RG#C%B5E8%@G%D5E8AEG12AF512560eX50D:X40D:W3o"). Qed.
End FPX_67.

#[export] Hint Rewrite mkOrB_eqf : bceq.
Section FPX_68. Context {fx : XPropExec.FPState}.

Lemma conc_tryB_eqf : ltac2:(zQ "90!hn8!se!u6!jf!hge!hnh1!hr8!hnhc!lm2>2fk@1$0$6@3$3>1e$1>5cands@1$0$1@1$2$4@1$7@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_68"] "##8np'0h05candsh11eh21oh32IHh42fkh54resth61si002hii012loi021pi031vi041xp;1p;2p;3p;4p;5p;6g00eTj1BTg00hSR0j1;Tg02cgj11Tg09QQj1Ej2Sj34Tg09Rcj1Uj2Oj30Tg008]j32Tg00f4j1DTg0097j2>Tg09T2j15Tg09U@j2ATg04QLj1:Tg01:AR1j2TTg027^j2Rj1LTg01F;j2=Tg01T9j2QTg09VPj1NTg09W]j39Tg01G5j2JTg09Xij43Tg01D[j1HTg01E@j16Tg01j=j2G!sw$Xj2@Tg05_6j1ITg09Z6j5?Tg00kNj2FTg028nj27j1KTg02i6j1MTg003Vj6<!uM$Tj3CTg01Qcj5PTg002Tj58Tg017a#Bg00`TR2%B2R3g00b@R4#;R5]0f0R6#1#E%U6P3P5f1R7#1/S61O76P2f3R8#1f2R9;46A0896525X03%D29097,>5f4R:#1?486A0:86525P5f5R;?0:7R<g00;\R=P5%58R>P6P=P51A8;#:R?P6P01T44R@P5f6RA#1/R8P1P4P4P5!sQ&=67g09[I'QRBP0P4P5%N7RCf8RD59AREP=P5P=P=1J79RFg00<<RGP=P=f7RHf9RIP6P7C3PHPIP61=79RJg01VBRK#H#6'G,@9RLC3g00>4RMn010!s#$20000!s41RN!t:$!so$P9%6K,@J#IRJD?RK1F46ROP:!sX1!s648n101104000210103!s:$!tB120011!s2$120!sU$0P6!s^22!tj3!t62=P5P>A0A;9RP!s3$?PPP0P@P517A!w$2P!vu&P!vi%!u[%KPOf:?0IARK!t%2!s62A0ID;RI!uN6I!uNERKPP!uPQRN525X25%;@^12RE%K;!uc%P!u^2P6P8O1P!t/T=25NX2!v%$%59P<!zm%9:#:P<!v`';9!v`9A9;CH!zN'PFP!zE$PAPD!zA&!s0%LC3PM!x+D!sR%9PJD?PO!vj3!s63A0DH:RH!wK6H!ysF<!v@Q,>5%1;R<#L%M;E<A4<:7P6E<AC297R994<:A0;:9525eW3X53X62P6DPX03D8X12D8W4o"). Qed.
End FPX_68.

#[export] Hint Rewrite conc_tryB_eqf : bceq.
Section FPX_69. Context {fx : XPropExec.FPState}.

Lemma concretizeB_eqf : ltac2:(zQ "90!hn8!u6!jf!hge!hni9!se!hr8!hnj6!lm2>2fk@1$0$6@3$2>1e$5@1$1$3@1$7@1$8^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_69"] "##'Ph05candsh11eh22fkh31oh41xp;1p;3p;2p;6p;5g00eTj17Tg00hSj1BTg02cgj10Tg09\Zj18j2<Tg09]nj1Aj2=Tg09Rcj1:j36Tg09T2j13Tg09_?j14Tg09`Qj15Tg09a`j11Tg008]j32Tg0097j29Tg09QQj1@Tg09bkj1?Tg003Vj6;Tg002Tj5>Tg017a#7g00`TR0g00b@#BR1f0R2#0#8%A2%70P1]0^10R3f1R4#:g00;\R5P1%34R6%44R7P2P4%54#1R8O2n010!s#$20000P5P1P6P7f2?648!sB1521X33P!sq$2%42%52#1964!si2,91%04R5#@%?4E;1<521=42521eX40D>W2o"). Qed.
End FPX_69.

#[export] Hint Rewrite concretizeB_eqf : bceq.
Section FPX_70. Context {fx : XPropExec.FPState}.

Lemma foldKB_eqf : ltac2:(zQ "70!se!hn8!jf!hnk5!hr8!hnkd!lm2>2fk@1$1$4@3$2>1e$0$0@1$5@1$6^1@1$3^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_70"] "##B9p'0h01ei001eh11oh22fkh31xi011xi021ai031bi042e0i052hii061ii071ki082loi091ni0:2opi0;1pi0<2sxi0=1vi0>1zp;1p;2p;3p;6p;5g00eTj1FTg02cgj11Tg09dAj1:j2@Tg09ePj18j2ATg01:AR0j2ETg00hSR1j16Tg028nj1;j23Tg00N^j29Tg00MQj15Tg09\Zj22j1=Tg09]nj20j1DTg008]j34Tg0097j2CTg09f\j1<Tg003Vj67Tg027^j1>Tg02i6j1?Tg002Tj5BTg017a#Fg00`TR2P2f0R3#1#:%83g00b@R4/E4R5#6^02R6f1R7#;P2P2P7f2R8P1P5P2P7P8O1R9P0P4P4P2P3g00;\R:P21973R;%57R<P1P4P2f6R=#1f5R>'2%53R?P>n10110100021010=00R@n!s6$00020000n200110;000120108105!su&3RA#1/28P?P8!so5!s82;00!u$&Af4RBO1RC!u&,P:P2P;P!tv'8RD#1f7RE'2P?PE!t&6!tqJ%1>/2BP?PB!tnGRFP!s$%!tv%BP>O1RF!tt<9RG#1/2DP?PD!tqX@!tQ6@P@n01!sa%81010>101093010:102103!s1D4010<!t1$9104!s4&7106109!yU%P!yS&13A8R@!uW;10=>P!y:9H!wGK10A!y5R13>BRI!tb=DE!y%a10>!y#:RJ!wV6KP!s$%!tj&=>RL!tj=G!xz]H!tJ6HPH!xz~9RH542X16%64^02R6%D7!y51P!y1<PF!y/:>!wMKP9!y,QP!y%<P=PEO1!y'aPC!#3&KCP!s$%!td%!x{<PEPD!td$!x}Y>!tH6>P>!x}~9=42HX16!xq$3P7!{X'87!uY6J!||M87P?P7!~^OBA!|p=E=P?P=!~\_BAP?PA!xYHAP!s$%KPK!w?~9,C2%17RK#=%<7E7%>K%?7E71@K31A73542eX32DBW2o"). Qed.
End FPX_70.

#[export] Hint Rewrite foldKB_eqf : bceq.
Section FPX_71. Context {fx : XPropExec.FPState}.

Lemma lin_branchB_eqf : ltac2:(zQ "a0!se!lc!hn8!u6!jf!spb!hr8!hnl7!hnm4!lm2>2fk@1$2$6@3$4>1c$5>1a$0>1b$0@1$3$1@1$8@1$9^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_71"] "##EVp'0h01bh11ah21eh32fkh43negh51oh63posh71xi001xh82x0h92x1i012ahi022bhi031ci041pi052p0i061zi072z0p;1p;2p;3p;6p;4p;5g00eTj1YTg00hSR0j1ATg02cgj14Tg09h4j1Fj2Uj3Kj4CTg09iHj1Xj2Tj3Ij4RTg01:AR1j2=Tg028nj1Ej29Tg05[Nj1DTg00f4j1W!s/$Tj31Tg03XUj33j1MTg01mEj2:Tg00kNj25Tg00nJj1STg01D[j1QTg01E@j1>Tg01gjj17!s8$^j2JTg01G5j2?Tg00Yhj2HTg03Yfj30j1GTg008]j3<Tg0097j2LTg03bdj1NTg003Vj6@Tg027^j1OTg02i6j1PTg002Tj5;Tg01SYj4BTg09jYj4VTg00`TR2g00b@R3f1R4f0R5CBp=8P2P3P5g01TVCBp=6g00;\R6P6g04QLP5CVp=2g017a#Yg09k=R7%A6R8^02R9^12%45#F%X5P2P9%44/U51T45P2P8f2R9#4?K45AI9451=33R:#A^22R;f3R<#EP7P8P<P6P8f4R=#4R>1=23R?g01VBR@#DRA,84%W?RB31RC%69=1?BRD33RE189A!s4$F%64!s/$G53>':P7P6P<g00>4RHg00<<RIP!s$&n0110300060!s#-,56RJP6P8P6P6A3>DGRKA3>GDPHn01!sJ%20000!t%%PIPH!s$'!sw=>%S6RL!sf1!s41RMPMP0P:P8P5P9O1P1P3P3!s4$!s<%<P=!s<06P8%Q@#>%7@#7!s$&>'JR@,?<1?5@'HR@P7P8f9RM!vr$:RN#4ROf7RP/8!vK%Qf8RR#6!s2$S33156IRT!t$$6P!s;$U93OS156HROP!u5AV#2RWPWPVPWPWPW!v%9!sj0100n2001105000121107102PLn101!sL%21!sD%!sN&4!sN'6101!sN4400!tP$6P8PEP!u=$PKP!u-CK%2K!t{21!sH%!zM,A0=CDRKA0=FG':P!y4,0=DGREA0=!y46>!tGBWPW!xH%19=9RW!x^319P=RP!x^1P!x?$P!x=$A0NQS!u\%A0NSU!u_DN#2R=P=PNP=P=P=!wg~!wg?=P=!w_&!wg%E!u-DE%2E!wg9RE5<8X5;g03T[R;P6^4;]6R;%G<!x&,P5PCPDO2RKP5PFPGO2!x0/P5PDPGO2RJP5PGPDO2!x6T>P>!}X&!x24P!x->f6RPPQPSO2!v$&PPSPUO2!v-DS#2RQPQPSPQPQPQ!x6~!x6?QPQ!x60J!u-DJ%2J!x69=<8EX0;!v:$9P6P8185A=1?B=0<GR;%65=1?BRE90<C!#7x%9PHP!#7nD!}^,<GERCA0<EG!#7l79!#7lG!uWBHPH!}q'<4!~,6<!x{8R!ug%P!ug&MUP!#7#-90M!~8EU#2RMPMPUPMPMPM!y$~!y$?M!{>%P;!y$&C!u-DL%2L!y$9,L8%4<RL#M%N<E@%OL%P<E@PLP9P4P5CCP<!s0&R5<8eX92D;X82D;X77D;W3o"). Qed.
End FPX_71.

#[export] Hint Rewrite lin_branchB_eqf : bceq.
Section FPX_72. Context {fx : XPropExec.FPState}.

Lemma decide_branchB_eqf : ltac2:(zQ "a0!se!lc!hn8!u6!jf!spb!hnn3!hr8!hli5!lm2>2fk@1$2$7@3$4>1c$5>1a$0>1b$0@1$3$1@1$8@1$9^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_72"] "##X#p'0h01oh11ai001ah21bi011bh31ch41ei021eh52fkh61xi031xh72x0h82x1i042a0i052ahi062ali072b0i082bhi092bli0:1ii0;1ki0<2loi0=1ni0>2opi0?1pi0@2p0i0A2sxi0B1ti0C1yp;1p;2p;3p;5p;4p;6g00eTj1PTg00hSR0j1=Tg02cgj11Tg07b1j1?j2Nj3Cj4JTg09koj1Oj2Gj3Aj4KTg01:AR1j2@Tg028nj1>j20Tg09mCj3;Tg00XYj27Tg09nTj15Tg09oej36Tg0:17j53Tg00nJj1MTg09h4j48j1ETg09iHj44j1BTg008]j3:Tg0097j2DTg0:2Jj1FTg003Vj6<Tg027^j1HTg02i6j1ITg002Tj59Tg00kNj2LTg00;\R2f0R3'Lp=2g017a#Pg09k=R4g00`TR5%=2R6^25R7]1R8%13#?%O3P5P7f1R7#1/N31G73P5P6f2R9#1?C73AA973g00b@R:/@:R;#=^45R<f3R=#>P5P6P9!s+%f5R>?;73#2R?P2P6f4R@/7=RA%5>#2RBP0P2P6A6>@=RC%23RD!s8%P0P;!sl$@O1P1P:P:P6P3!s<&>f6RE!s>/f;RFP@P=P7P3D3n200110@000120109108RG%M2RHn101103000210!sI$!sS&?!sS'6105P!sN3?00PD%1EP>P@P=C8!sE2B00!s86010!s#$2000!uJ$17E>RIf7RJ#5#2RK!ur'JE>RLP!uo1@PE!uo6Jf8RM!uo0=!umBNP!ujbMPJPEP>!ujWROP!s$%!ur$JERP%5M#2RQ!uo'MJERR!uo2>PJ!uo6Mf9RS!uo0>!uoBT!uocSP!uq$!uoXUPUn011!s;$81010C1010=3010>104107!s1D4010A10<10=102!s4&;10:10=!vo%=9RU%5@#2RV!vo'@=9RW!vo27P=!vo6@P>!vm0:RX!voBY!voc!wx%9!|L]>@RZ%5E#2R[!ug'E>@R\!ug2=!uQ1!s<&E!yn1f<R]!ugB^!ugc!|G$P@!yXX_P!s$%OPO!y`$0!y`$1103!y`q!#7Q,P?!vc$AP!#7;%PC!vw110E@!vu310SEPG!vG_RGPD!vF%P=C4!#3kW2P6PIP!#6M%PL!u+3ME!u+5FMP!#5p_RNPD!~~%P>!u+XFP!s$%2P6PPP!#5h%PR!u23SJ!u25]SP!#53_RTPDP!#54&!u2W]P]!#54~!uv$UP!#5'%PW!v23>=!v25M>P!#4N_RYPD!zB%P9!v2Z2P6PZP!#4H%P\!u+3J>!u+5XJP!#3k_R^PD!zB%P@!u+XXP!s$%FPF!#3l~R_5:6X0<P8^34R8%B!#3~JGPDP9!w^%O3!#9,X!~x8NPDP@!vX%!s~WRNP!s$%!}t;T!yd$!|p$!t-XMPM!|p~!|p=YPDP7!{l%!w6\!{j7^PDP=!zf%!v-X>P!s$%NPN!zf~==:6_X08!zU$7!s+%A;@73#2P]P!|:3!wb~1797%5=#2!#@u&=97!#3V2@9!#3V4J!#=6-S!#@m@!#@k`!y:%P7!#3|V!#J3%OPXPX!x<~=,D6%1=RX#E%F=E<%HX%I=E<PXP9P7P3CJ!u9%P3CK5:6eX85D9X75D9X64D9W5o"). Qed.
End FPX_72.

#[export] Hint Rewrite decide_branchB_eqf : bceq.
Section FPX_73. Context {fx : XPropExec.FPState}.

Lemma mkSltB_eqf : ltac2:(zQ "90!se!hn8!jf!i4!spb!hr8!hno3!hnob!lm2>2fk@1$1$5@3$2>1c$4>2op$3>1a$0>1b$0$0@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_73"] "##:6p'0h01ai001ah11bi011bh21ch32fkh41oh52oph61xi021xh72x0h82x1h92x2i032a0i042b0i051ei061ii071ki082loi091ni0:3op0i0;2sxi0<1zi0=2z0p;1p;2p;3p;4p;6p;5g00eTj1GTg02cgj12Tg0:3bj1<j2Fj3=j4:j5ATg0:51j16j2Dj3;j49j5BTg00hSR0j17Tg09koj18j41Tg04MSj30Tg01E@j1ETg00MQj15Tg008]j34Tg0097j2CTg07b1j1>Tg0:6=j1?Tg003Vj6@Tg002Tj53Tg017a#Gg09k=R1g00<\R2g00`TR3P3^13R4]0R5]5f0R6#2#<%66P2P5f1R5#2/F61D56P3P4f2R4#2?=56A;4!s9$3f3R7#2P4P5P6C:P7!s0&9g00;\R8#7^13^03^21R9f4R:#8P3P3P4!s+%f5R;?0:7R<P0P8!s8$6R=P:P7O3!s6$6g01VB#E#5g01TV#5n0110400020000R>P<n1011!s5$210!sB$!sr&:f8R?P=P;O3P>f7R@?0=;RA!sV5RBP!s$%!s^%;f9RCP@P=O3P>A0?@=RD!s[6EPE!t[$100081010=101093010:103104!s1D4010;108109105!s4&7106109!t[&5P;P7P4!tY%:74RE!uf<7P@P;P:!sQ%=;:RF!u+6GP!s$%BPB!u4$0!u4'<!u4q!xS-P!xK'@P!xI$C1P!w}8!xs+CP!w}$!sN$!wu7AP!s$%!sT$f:P!ws$!sT$!wn7DPD!wn~!wn'=!wn%!tT$!wi6R=!sN&?!wk%!sN$!wf7FP!s$%APA!wf~9543X4!wl%5!s+&EP=P!tL3!vR~P3P;P:P4P5C1P>A0745!{@6<!s$&FPF!v,~9,C3%2:RF#>%?:E@PF!#4w&DAP!#5''DB543eX93D3X83D3X72D3X61D3W3o"). Qed.
End FPX_73.

#[export] Hint Rewrite mkSltB_eqf : bceq.
Section FPX_74. Context {fx : XPropExec.FPState}.

Lemma mkAluK0B_eqf : ltac2:(zQ "80!se!hn8!jf!i4!hr8!hnp5!hnpf!lm2>2fk@1$1$4@3$2>2op$3>1a$0>1b$0$0@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_74"] "##Lmp'0h01ei001eh11ai011ah21bi021bh31ch42fkh52opi032oph61si041sh71xi051xh82x0h92x1i062a0i072b0i081ii091ki0:2loi0;1ni0<3op0i0=2sxi0>1zi0?2z0p;1p;2p;3p;5p;6p;4g00eTj1aTg02cgj11Tg0:7Xj1Ij2`j3Lj4VTg0:8ij1Dj2Uj3Hj4[Tg08[?j1Fj39Tg04MSj32Tg0:3bj5=j1OTg00XYj28Tg00MQj1<Tg09Knj1@Tg01jZj2ZTg01E@j1?Tg01F;j2TTg00N^j2RTg01gjj1QTg01D[j1KTg0::7j2;Tg09IUj3Jj1ATg09>6j3Gj1]Tg09C>j33j1_Tg0:51j56j1NTg09Jcj3:j1MTg09?Ej3>j1ETg09DNj30j1CTg0097j2BTg0:;Fj1PTg003Vj65Tg0:<Yj1STg09P=j1^Tg09E[j1YTg08Z0j1WTg09;Xj1XTg002Tj57Tg008]j3\Tg00`TR0f1R1f0R23\p=4g017a#ag00<\R3P0^20R4^10R5%12#I%D2P0P4%11/`21U12P0P0f2R4#1?L12AH412g00b@R6P0]6^10R7f3R8#FP3P0P8A2841R9P9P9f4R:#1R;g0:=kR<g00AAR=P4P1D=R>P;g0:>]R?g00AmR@!s>&Ag00;\RBP01841RCg01TV#<RDg00hSREP6P0%@4RFA2:84RGP0P0P1PBP0g020<RH,Z2g01VBRI#?,THRH'RRJg00?iRK%<HRH;28PGn010!s#$20000PGf6RLf5RM;2:RNP!s$$f7RO?2LMRPPPn011!sQ$8101091010;3010<106107!s1D4010=10:10;100!s4&910810;n10110500021010>00!tk1RPP!ul$PFPG!s0%%QI#K#?RI,;1RQP1P8P2O2P9!sp2400!t&5P9PBP0PCP4AJ;41!t92;!vm$4!s+%%1LRR?G:8A3R8:RRf8RS#1RT?3MLRUP!s$$f9RV#1?3LORWPW!vE1?!vEp%1M?384RX%1O?3M:RYP!s$$A3TLMRTPT!tK$1!tK'>!wjq01103000:0!s#6!{`%P!{[$P:P<P!{K%6P:P?P!{?%6P!x44PQA9M8!w}JRQ!x#-::!x#4G!x#/A>L:8RFA0L8:A0SMLRZP!s$$A0VLORVPV!wo~;A0M84A0OM:RVP!s$$A0SLMRSPS!wi~;RS!wkAR['4X07P5%E8!ww0>PAPPPQP9P!{d0P4P:P8O2PR!{P%PUP!{H~810;PX!{8%PYP!{5~!{5E/4[X05P5%C!vGIFP4P8P:O2P:PMPLO2RFP!s$%MPLPO!s6%!vW~;P1P8P4O2P8PMP:!tN-:PLPM!tN-!vm~!vmFM!vm;!~6&P2P4P1O2!~91PS!t,Gg09k=P5^53]3R5%N!t912!#4B&O4P2!#4B&O4!tM&G!t1I!sx$4A2412R5P5P5P8!s}$1P2D6P8!s}$!s2%BP01812R@PD!#:O%@1RDP9!yF$2!ue$JA2KH4P9!ub29A2M:8RHP!s$%NPN!#<h~!#<hB!u3%PDP9!s0%1;2IA9:42P5!#<YG5!ua$@P1A:81!xE3!#@F$!s+$A>M84A0M48A0O:MROP!s$%ZPZ!|E~;A0:41A0L:8RLP!s$%!#8i&!|7~!y}=,B0%18RV#O%P8E5%AV%S8E5%_V%^8E5%]V%Y8E5%WV%X8E5PVP4P1P2CVP8!s0&['4eX90D7X80D7X73D7W4o"). Qed.
End FPX_74.

#[export] Hint Rewrite mkAluK0B_eqf : bceq.
Section FPX_75. Context {fx : XPropExec.FPState}.

Lemma mkAluKB_eqf : ltac2:(zQ "80!se!hn8!jf!i4!hr8!hnqb!hlgb!lm2>2fk@1$1$4@3$2>2op$3>1a$0>1b$0$0@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_75"] "h01eh11ah21bh32fkh42oph51xh62x0h72x1p;1p;2p;3p;4p;6p;5g00eTj1FTg02cgj10Tg081<j1:j2Ej3;j4@Tg0:?Oj16j2<j39j4ATg09ePj18j21Tg0:7Xj47j1BTg0:8ij44j1DTg008]j33Tg0097j2CTg0:@\j1=Tg003Vj65Tg09dAj1>Tg0:B1j1?Tg002Tj52Tg017a#Fg00<\R0g00`TR1P1^21R2]1R3f0R4#0#:%64P1P2f1R2#0/E41<24P1P1f2R5#0?;24A9524P1^01R6f3R7#8P4f4R8#0P7P5P2C7O1P8P7P5P2C4,18R9531X06P3^40R3%D7P4P7P5P2O3,18=319X03P7P5P2P4C4,17,C1%07R3#B%=7E5%>3%?7E5P3P5P2P4C@P7P5P2P4CA531eX71D2X61D2X50D2W3o"). Qed.
End FPX_75.

#[export] Hint Rewrite mkAluKB_eqf : bceq.
Section FPX_76. Context {fx : XPropExec.FPState}.

Lemma mkMdKB_eqf : ltac2:(zQ "80!se!hn8!jf!rb!hr8!hnr4!hlm2!lm2>2fk@1$1$4@3$2>2op$3>1a$0>1b$0$0@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_76"] "##:;p'0h01ah11bi001bh21ei011eh32fkh42opi022oph51xi031xh62x0h72x1i042a0i052b0i061ii071ki082loi091mi0:1ni0;3op0i0<2sxi0=1zp;1p;2p;3p;4p;6p;5g00eTj1ITg02cgj12Tg085Tj1<j2Hj3=j4DTg0:CDj18j2?j3;j4ETg0:?Oj1:j41Tg09Knj14Tg09<kj30Tg0:DPj19Tg00MQj15Tg01D[j1GTg01E@j17!s/$^j2FTg01F;j2>Tg008]j36Tg0097j2@Tg081<j1ATg0:E_j1BTg003Vj6CTg002Tj53Tg017a#Ig00GER0g00`TR1P1^11R2]0R3f0R4#2#<%84P1P2f1R2#2/H41?24P1P1f2R5#2?=24A;524g00<\P3]4R3f3R6#:g00hSR7g00b@R8P1%45R9f4R:?065R;P0P1P6A0652R<P!s$'1P1P2P7P8P1%94R=P5g00CER>P:%54R?O3P;n10110300021010700P;f6R@f5RA;0:RBP!s$$f7?0@ARCPCn011000008101091010:3010;104105!s1D4010<10810:101!s4&710610:!u&1P!u#%EIRDP:g01VBRE#G#7/F4%7E'>#5RE!u9;!u+%PBP!u$~610:!t&$200080!s#2!td2=00!uL&9P!wu&P!wp8P=P@P>P:P?C1!uR~!wTW@PDP:PE!tf~!w:t561X23!{j&42P<!wA$5A0524R3P!s$'1P1P4!u^+AP>P6!wF$<!u^6<A0A:6R:P!s$%BPB!uc~:!tk6DP6!wK$!tk8P!tf~!wK[,@1%26RB#A%B6ECPBP5P2P4CDP6!s0&E561eX71D3X61D3X50D3W3o"). Qed.
End FPX_76.

#[export] Hint Rewrite mkMdKB_eqf : bceq.
Section FPX_77. Context {fx : XPropExec.FPState}.

Lemma zband32B_eqf : ltac2:(zQ "80!lc!hn8!jf!se!hr8!hnrc!lm2!hns6>2fk@1$1$4@3$2>1d$3$0@1$7@1$6^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_77"] "##,gp'0h01eh12fkh21oh31xi001xi012hii022loi031pp;1p;2p;3p;6p;5g00eTj1;Tg02cgj14Tg0:G3j1@j2DTg0:HDj1=j2ETg01:AR0j2:Tg00hSR1j1GTg028nj17Tg01_Wj15Tg000Lj33Tg01b6j36!s/$Sj31Tg01D[j1<Tg01E@j19Tg01gjj10!s8$^j2ITg02O\j1HTg01G5j28Tg00Yhj2FTg008]j32Tg0097j2CTg027^j1BTg02i6j1ATg003Vj6?Tg002Tj5>Tg017a#;g00`TR2g00;\R3f0R4#4#@%=4g00b@R5/:5R6#G^02R7f1R8#7R9P1P6P31:52#;R:%58R;535R<A65:;R;514P0P5P5P3P4g01VBR0#<#9%00#!s$%9'IR0#H/881840'Fn2001103000120102101R0g00>4R=n10110000!s=$0300!tN%f2#7?1<;P0P!sJ6523X27!sP%%54R6935:A65:6519!sY9,C3%48R=#B%A8E?1D=41E84523eX32D>W1o"). Qed.
End FPX_77.

#[export] Hint Rewrite zband32B_eqf : bceq.
Section FPX_78. Context {fx : XPropExec.FPState}.

Lemma mkAluwK0B_eqf : ltac2:(zQ "80!se!hn8!jf!i4!hr8!hnt2!hntd!lm2>2fk@1$1$4@3$2>2op$3>1a$0>1b$0$0@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_78"] "##7Wp'0h01bh11ah21dh31eh42fkh51oh61xi001xh72x0h82x1i012hii022loi032opi041pi051vp;1p;2p;3p;6p;4p;5g00eTj1NTg02cgj10Tg0:IRj1?j2Mj3@j4HTg0:Jdj1;j2Aj3>j4ITg01:AR0j2=Tg00hSR1j1<Tg028nj1:j27Tg04MSj33Tg09Knj16Tg0:L3j1LTg00MQj1KTg0:M?j2JTg0:G3j28j1DTg084Gj32Tg0:HDj21j1BTg008]j34Tg0097j2CTg0:NQj1ETg003Vj69Tg027^j1FTg02i6j1GTg002Tj55Tg017a#Ng00<\R2g00`TR3P3^03R4]1f0R5#0#?%;5P3P4f1R4#0/M51A45P3P3f2R6#0?@45A>645g00b@R7/=7R8#<^33R9f3R:#:P2P3P:P1P7P3A3:64R;#6R<%L5#KR=P1P8P3P5P;O1R>P0P7P7P3P5g00;\R?P31J45R@f6RAf5RBf4RC33RDP?P3f7RE#0/8DPDA2ABCRFn010!s#$20000!s422001104000120102101P?P3%0C/8;P;A2:64RG!s[2101!s6%210!sc$!s82500RHPHPG!s$1n01103000:0!s#6!v0/P<P!uz&17C;RH!ux,P?P3P@P!ua$11EDPDP!uWX11C;P;P!uPWEPE!uPQRE543X59P?^23R9%B:!ub9P!u^:P:PDO1!u`[P>!u^Z!v>$!u^O=43EX09!uS$6!{A'645R9#6!x>,:9!u\3A3BC:R@!w]%A@P@A2BC:!xDY:9P9A2!tC$!uiV?P?P9!s$1!uiA,C3%0:R9#D%E:E9%F9%G:E9P9P6P4P5CHP:!s0&I543eX83D5X73D5X62D5W4o"). Qed.
End FPX_78.

#[export] Hint Rewrite mkAluwK0B_eqf : bceq.
Section FPX_79. Context {fx : XPropExec.FPState}.

Lemma mkAluwKB_eqf : ltac2:(zQ "80!se!hn8!jf!i4!hr8!hnua!hlj7!lm2>2fk@1$1$4@3$2>2op$3>1a$0>1b$0$0@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_79"] "h01eh11ah21bh32fkh42oph51xh62x0h72x1p;1p;2p;3p;4p;6p;5g00eTj1FTg02cgj10Tg0836j1:j2Ej3;j4@Tg0:Ofj16j2<j39j4ATg09ePj18j21Tg0:IRj47j1BTg0:Jdj44j1DTg008]j33Tg0097j2CTg0:Q4j1=Tg003Vj65Tg09dAj1>Tg0:B1j1?Tg002Tj52Tg017a#Fg00<\R0g00`TR1P1^21R2]1R3f0R4#0#:%64P1P2f1R2#0/E41<24P1P1f2R5#0?;24A9524P1^01R6f3R7#8P4f4R8#0P7P5P2C7O1P8P7P5P2C4,18R9531X06P3^40R3%D7P4P7P5P2O3,18=319X03P7P5P2P4C4,17,C1%07R3#B%=7E5%>3%?7E5P3P5P2P4C@P7P5P2P4CA531eX71D2X61D2X50D2W3o"). Qed.
End FPX_79.

#[export] Hint Rewrite mkAluwKB_eqf : bceq.
Section FPX_80. Context {fx : XPropExec.FPState}.

Lemma extK0B_eqf : ltac2:(zQ "70!se!hn8!jf!hnv4!hr8!hnvc!lm2>2fk@1$1$4@3$2>1v$0$0@1$5@1$6^1@1$3^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_80"] "##4^p'0h01ei001eh12fkh21oh31xi011xi021ai031bi042hii051ii061ki072loi081ni092n0i0:2opi0;1pi0<2sxi0=1vi0>1zp;1p;2p;3p;6p;5g00eTj1HTg02cgj15Tg0:RJj1;j2:Tg0:SYj16j2CTg01:AR0j2GTg00hSR1j1=Tg028nj1<j24Tg00g4j10Tg01nBj27Tg01D[j11Tg01E@j12Tg01mbj18Tg01e0j29!sA$^j2FTg01j=j2ETg01G5j2BTg008]j33Tg0097j2>Tg027^j1?Tg02i6j1@Tg003Vj6ATg002Tj5DTg017a#Hg00`TR2P2f0R3#5#;%63g00b@R4/G4R5#=^02R6f1R7#<P2P2P7f2R8P8f4R9P!s$$g00aaR:P2P8g00;\R;P2g00h4#0!s$/,77R<P1P5P2P9P3O1P0P4P4P2P3P;P2P;P4f6R=g01VB#1R>#2R?%1>#1#2%89'9'FR>/E?P>n0110<00020000,B3R>f3R?f8n010!s#$!s?$n200110;000120107104R@f5RAn1011!sR$210!sH$PA!sb1P=!t3$7!s6%10109!sI$10=00081010>101083010:102103!s1D4010<!tV$8100!s4&6105108!vx%P8P8!vr%P9P!vo$!v8$!vT&14=3P@P!u5~!u5\532X26!u;$3P7P7P?!s$&!u;6A3!xg2>P?f7!x&EP9!uo69!uo2A!uo59!uo~8,>2%57R9#?%@7EA1:931C73532eX32DDW1o"). Qed.
End FPX_80.

#[export] Hint Rewrite extK0B_eqf : bceq.
Section FPX_81. Context {fx : XPropExec.FPState}.

Lemma extKB_eqf : ltac2:(zQ "70!se!hn8!jf!hog6!hr8!hkl7!lm2>2fk@1$1$4@3$2>1v$0$0@1$5@1$6^1@1$3^1").
Proof.
ltac2:(KReplay.run1 (kr_t_XAxSymExec3B ()) ["FPX_81"] "h01eh12fkh21vh31xp;1p;2p;3p;6p;5g00eTj1BTg02cgj11Tg07Mij16j2<Tg0:Tej15j2=Tg09ePj1Aj20Tg0:RJj2;j19Tg0:SYj23j17Tg008]j32Tg0097j28Tg0:V0j1:Tg003Vj64Tg09dAj1@Tg0:B1j1?Tg002Tj5>Tg017a#Bg00`TR0P0f0R1#1#6%51P0^00R2f1R3#AP1f2R4#1/;3O11343,04R5520X02P0^20R2%73P1P3O1,04=205X021331,03,80%13R2#9%:3E4%@2%?3E41<211=31520eX30D>W1o"). Qed.
End FPX_81.

#[export] Hint Rewrite extKB_eqf : bceq.
Section FPX_82. Context {fx : XPropExec.FPState}.

Lemma flat_scB_eqf : ltac2:(zQ "90!hn8!u0!jf!hogd!hr8!mq2!tt5!hkkb!lm2>2fk@1$0$4@3$2>1a$5>1n$1@1$0$6@1$7@1$8^1@1$3^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_82"] "##0+p'0h01eh12fkh21nh31oh41xi001xh52x0i012hii022loi031pp;1p;2p;3p;6p;5g00eTj1;Tg02cgj16Tg07O7j1Dj2Nj3ATg0:WCj1@j2Mj3JTg01:AR0j2ITg00hSR1j1CTg02?=j1Bj2=Tg043Tj1<Tg044aj17Tg01FXj21Tg01T9j25Tg01mbj1?Tg01D[j10Tg01E@j1>!s/$^j2LTg00Yhj28Tg00f4j1KTg05b:j14Tg0:XQj22!sA$Tj33Tg008]j3:Tg0097j2ETg02=ij1FTg03iBj1GTg003Vj6HTg002Tj59Tg017a#;g01U4R2g00aaR3g06?kR4#;R5]2f0R6#6#D%@6P3P5f1R7#6/N61M76g00`Tg00b@R8/I8R9#C]0R:f2R;#BP1P9P5P6%<;R<O1P0P8P8P5P6g00;\R=P5g01TVR>f5R?#7R@,17'5116@f4R@#?'1g01VB#0RA#>%0A#0!s$&>'LRA'5'8%K4RB%4@,2?=34Bn010!s#$20000n2001103000120102101R?%47,2;=34BRCn101!sX%210!sP$!u%%f3RD/=<P?P!sI65:5X3:!sO%%<7,=;!uO,P=P5%7@R=,17,5>116=%?D'1/5A'8PB%4D,2@!txI%46,27!sR$!tQ4,E5%6;RB#F%G;EHAAB76AJ;765:5eX53D9X42D9W1o"). Qed.
End FPX_82.

#[export] Hint Rewrite flat_scB_eqf : bceq.
Section FPX_83. Context {fx : XPropExec.FPState}.

Lemma wr_coveredB_eqf : ltac2:(zQ "90!hn8!hr8!lc!u0!jf!mq2!hoh7!lm2!hoi4>2fk@1$0$1@3$4>2kn@1$0$1>1a$5>1n$3$2@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_83"] "##@}p'0h01bh12knh21xi001xh32x0h42IHh51Kh61ah72b1h82b2h91ei011eh:2fkh;2k1h<2k2h=1nh>2n1i022n1h?2n2i032n2h@1ohA4resti042a0i052a1i062a2i071ci082hii091ki0:2k0i0;2kbi0<2kki0=1li0>3leni0?2loi0@1mi0A2n0i0B1vi0C1wp;1p;2p;3p;4p;5p;7p;6g00eTj1STg02cgj10Tg0:Ybj1Pj23j3=j4ETg0:[6j1Gj24j3<j42Tg008]j31Tg00f4j1OTg0097j2BTg002Tj55!sA$Tj3;Tg043Tj1DTg00XYj2CTg044aj19Tg01T9j26Tg00Yhj2ATg03Jej2Rj1FTg01mbj18Tg01FXj2:Tg00MQj1@Tg03jZj7Nj1ITg03L2j2?j1KTg03kkj7>j1HTg00hSR0j1LTg045mj1JTg003Vj67Tg03h1j1MTg01Qcj5QTg017aR1#SR2P2g01U4R3g00aaR4g00;\R5]=R6]6R7f0R8#0#P%G8P1f2R9#0R:/381498517X12P3P6f1R;#0%O1R<'314;<P4P5A=:<8A<9<8f3R:P<P;P8C2,B5X34D5X23D5%0!sr%:8517!so$4R6#0A;19;!sq%6!sq$f5R<!s=$:9R=;=8A<<=8P7f6R=/4:P1P5P<P:P<P6O2R>P9P6P:O2R?P>P?P?P>P3P5P;P5!s$%%D=R@/C;%9=RA,68'ARBP0g00b@RCP5f;RD#0RE/R9f7RF#9%8=':1:;8RG'6RHg00>4RIn10110000021010=00PIn0!s8%020000g00<<RJ!tC$EP@PA%8<RE#@RKP;P8P9FNRLPJP6P=P<O2RM!sd1!s4410400012010;10<PMP>P?!s>$9000:3010410C10B2!s1%A!s9&A10:2010?10820!u,$@3!s-%!s9'410>40105102106103!sb,7!su'!w-%f:R?PFP<P6C2RFf9P=P6P:C2R>PFP>P>PF!w41PBP0PCP51?D9PHP!vVFRMP!vS%DP@PAP!vL'>PJPDf8RDP=P<C2RN!vNRNPFP>!vN~!vN4RO515X07g00`TR7%LC]9RP%K=!zo&FP!vQBP6P9O1!vSI!vQ&LPJP!v7~!v7i=15OX@PP5^?7^<C^87^>7^;C^77R7%H!v>A!y3'6!y3/O6!un~!unq07!uU$6P>PDP<P:P9C2RD!s4$D!#4X4<R7/C;%9<R<,68'A!|Z'?91:AE/6G!y2N?P7P<%86#@!|`-F!vSRFP>PD!vS~!vS4,B5%0=RD#I%J=E7%FD%M=E713D:P9E7PDA;16:R6P;P8CEP=P!s0%2515e!#9`+W4XA2X51P8DQX12D5W:o"). Qed.
End FPX_83.

#[export] Hint Rewrite wr_coveredB_eqf : bceq.
Section FPX_84. Context {fx : XPropExec.FPState}.

Lemma storeok_scB_eqf : ltac2:(zQ "90!hn8!u0!jf!hr8!mq2!tt5!hoj3!lm2!hlh6>2fk@1$0$3@3$2>1a$4>1n$1@1$0$5@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_84"] "##+wh01nh11ah21bh32fkh42knh51lh61xh72x0p;1p;2p;4p;3p;6p;5g00eTj17Tg02cgj10Tg07ohj1;j2Ej3@Tg0:\Gj18j2=j3ATg0:Ybj4<j1CTg00f4j1:Tg0:]Xj23!s8$Tj32Tg0:[6j45j19Tg008]j31Tg0097j2DTg0:^ij1BTg003Vj64Tg04@Wj1>Tg04Aej1?Tg002Tj56Tg017a#7R0g01U4R1g00aaR2g06?kR3#7R4]0f0R5#0#;%85P2P4f1R6#0/E51=65P0f2R7g00;\R8P4f3R9#0P5P7P6C<%:3R:1376=23:R;n010!s#$20000P8P4P9P9!sQ$5P:P!sF2R<514X50P8^02^11^40R0%97!s^$5!s^%O3!s^5=14<X2!t,%7P7P6P5C5P:1365=23:!sS1,D4%07R:#C%B7E4%>:%?7E4A@:65AA765514eX72D6X61D6W3o"). Qed.
End FPX_84.

#[export] Hint Rewrite storeok_scB_eqf : bceq.
Section FPX_85. Context {fx : XPropExec.FPState}.

Lemma conc_exprB_eqf : ltac2:(zQ "70!se!hn8!jf!hok0!hr8!hkvd!lm2>2fk@1$1$4@3$2>1e$0$0@1$5@1$6^1@1$3^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_85"] "##1Yp'0h01ei001eh12fkh21oh31xi011xi021ai031bi042e0i051ii061ki072loi081ni092opi0:2sxi0;1vi0<1zp;1p;2p;3p;6p;5g00eTj1?Tg02cgj12Tg07_Zj14j2=Tg0:`Aj13j2<Tg00hSR0j1>Tg09]nj1:j20Tg00MQj15Tg008]j31Tg0097j26Tg09\Zj17Tg09f\j18Tg003Vj69Tg002Tj5;Tg017a#?g00`TR1P1f0R2#2#4%32g00b@R3#>^01R4f1R5#:P1P1P5f2R6P0P3P1P5P6O1%52R7P6n10110100021010;00!sK%f3R8f4R9O1P7P9!sL5R:P!s$%!sy%9f5R:!sR$:!sR6;P;n0110000081010<1010830109102103!s1D4010:107108104!s4&6105108!uW%P!uU&1086P!uP>10:9!uJ:;P!s$%!ux%6/0:!uG::P:!uG~8511X24!uM$2P5!u,'65P7P5!uM=98P7P8!t|68P!s$%!wM~5108,61%25R;#7%85E91=;21<52511eX31D;W1o"). Qed.
End FPX_85.

#[export] Hint Rewrite conc_exprB_eqf : bceq.
Section FPX_86. Context {fx : XPropExec.FPState}.

Lemma enum_branchB_eqf : ltac2:(zQ "a0!se!lc!hn8!u6!jf!spb!hokc!hr8!hll2!lm2>2fk@1$2$7@3$4>1c$5>1a$0>1b$0@1$3$1@1$8@1$9^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_86"] "##-ip'0h01ah11bh21ei001eh32fkh41oh51xi011xh62x0h72x1i023posi031vp;1p;2p;3p;6p;4p;5g00eTj1HTg00hSR0j15Tg02cgj10Tg07cHj16j2>j3<j4;Tg0:aQj1Gj2=j3:j4CTg09]nj17j23Tg0:bcj32Tg01jZj28Tg00N^j29Tg04QLj1FTg00kNj2ETg00nJj1DTg008]j34Tg0097j2?Tg09\Zj1@Tg09f\j1ATg003Vj6BTg002Tj51Tg017a#Hg09k=R1g00`TR2g00;\R3#5R4^12R5]0f0R6#0#6%G6P2P5f1R5#0/>61=56P2P4f2R7#0?<56A:756g00b@R8#5^22R9f3R:#7g01:AR;P2P3P4A2:75R<P0P8P4P7P5O1P3P3P5g020<,86g01TV'9R=#FP=n0110200!s&$0,E3R=%D3R>n10110100021010300n20!s9'120100102P!tB&P!t=&f6/35P=P!seJ544X49!sk'A2756!sn&5!snP,?4%0:R>#@%A:EBP>P7P5P6C;P:!s0&C544eX72D1X62D1X51D1W3o"). Qed.
End FPX_86.

#[export] Hint Rewrite enum_branchB_eqf : bceq.
Section FPX_87. Context {fx : XPropExec.FPState}.

Lemma to_saddrKB_eqf : ltac2:(zQ "90!hn8!jf!hge!se!hr8!mq2!hola!lm2!hko1>2fk@1$0$4@3$1>1e$3>3imm$2$5@1$8@1$7^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_87"] "##4Yp'0h01eh12fkh23immh31oh41xi001xh52x0i011ai021bi032e0i042e1i051ii061ki072loi081ni092opi0:2sxi0;1vi0<1zi0=2z0p;1p;2p;3p;6p;5g00eTj1ETg02cgj14Tg07enj1;j2Dj3?Tg0:d4j18j2Bj3@Tg00hSR0j1<Tg09]nj1:j23Tg0:eDj15Tg0:fTj21Tg00MQj10Tg04MSj32Tg05ehj29Tg008]j37Tg0097j2CTg09\Zj1ATg09f\j1=Tg003Vj6>Tg002Tj56Tg017a#Eg00`TR1g00b@R2g01U4R3]2f0R4#4#;%84P2P3f1R5#4/D41B54%<2^01R6f2R7#:g01:AR8P1P2P3%57R9P1P3P5f5R:f4R;'1R<P0!sk$3R=g00=HR>%0;72:R?O1g01TV#0/94R@P<n10110000021010;00!sa%P:f7RAf6RB#052>RCO1P@11ABRD!sY5REP!s$%!sa%Bf8RE%0A52>RF!s^%EARG!s^6HPHn0110300081010=1010830109!sT$2!s1D4010:107108104!s4&6105108n20!tA'12010310<P!vW&P!vT&P!vJ&13B?P!v/>13ECP@P!ut7DP!s$%!w:%9/3FP@P!ue7GPG!ue~!ue8573X36!uk'%55!ul%11;=R8!u$%%0=92>;,3:P@P8!uv;%0:92>B,3AP@11B:!uU6BP!s$%DPD!u]~!u]8,C3%47RD#A%=7E>A?D54A@754573eX52D6X41D6W1o"). Qed.
End FPX_87.

#[export] Hint Rewrite to_saddrKB_eqf : bceq.
Section FPX_88. Context {fx : XPropExec.FPState}.

Lemma amo_alignedbB_eqf : ltac2:(zQ "90!lc!hn8!jf!ui7!hom6!se!hr8!hkuc!lm2>2fk@1$1$6@3$2>1e$5>2wd$3$0@1$7@1$8^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_88"] "##,,p'0h01eh12fkh21kh31oh42wdi002wdh51xi011xh62x0i021rp;1p;2p;3p;6p;5g00eTj1DTg02cgj10Tg087oj1:j2Cj3?Tg0:gcj15j2<j3@Tg00hSR0j1;Tg08SHj19j33Tg01D[j16Tg01E@j12Tg01gjj17Tg00N^j28Tg008]j34Tg0097j2BTg08R0j1ATg08ePj1=Tg003Vj6>Tg002Tj51Tg017a#Dg00`TR1g0:i6R2g00;\R3]4f0R4#0#:%54P2P3f1R5#0/C41<54g00b@R6%;6]2^01R7f2R8#9P0P6P3P4P8P2P6P5g01VBR9#6#2R:%79#2R9n0110000020000R;O2g01TV,84R<g00>4R=n10110100021010200!t#%f3?38;P<P!sH6543X37!tO&2P6P4P:P!t;29385!sd9,B3%08R=#A%=8E>A?=54A@854543eX62D1X51D1W1o"). Qed.
End FPX_88.

#[export] Hint Rewrite amo_alignedbB_eqf : bceq.
Section FPX_89. Context {fx : XPropExec.FPState}.

Lemma amo_newvalB_eqf : ltac2:(zQ "a0!se!hn8!u6!jf!i4!ui7!hon5!hr8!hlk3!lm2>2fk@1$1$7@3$3>2wd$5>3aop@1$2$4>3old$0>3src$0$0@1$8@1$9^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_89"] "##/fp'0h01eh11ah23aopi003aoph31bh42fkh53oldh62oph73srch81xh92x0h:2x1h;2x2i011oi022wdp;1p;2p;3p;4p;6p;5g00eTj1ITg00hSR0j1HTg02cgj10Tg08>?j16j2Fj3=j4:j5CTg0:icj1Gj2>j3;j47j5DTg0:?Oj18j44Tg0836j49j1@Tg0:Ofj45j1ETg008]j32Tg0097j2BTg0:k4j1?Tg003Vj63Tg081<j1ATg0:E_j1<Tg002Tj51Tg017a#Ig0:i6R1g00<\R2#HR3g00`TR4P4^74R5]5R6]2f0R7#0#6%G7P3P6f1R6#0/F71>67P4P5f2R5#0?=67A;5!s9$4f3R8#0P5P6P7C:P8!s0&7P4^34^14^62R9f4R:#8P0P2P4P8P1P4f5R;f6R<#0P7P8P5C9P6!s0%O3R=n0110200!s&$0P6n10110000021010100!sr/P;P<!sl&5!s0+4R<!slER>524X09P9%E:!sy2=P!sgF=24>X09!sa&5!sa$:P;P7P5P6C5!s0+4!sq27!sq5,B4%0:R;#@%?:E3%A;%<:E3P;!vr'DCP!v~+DD524eX;4D1X:4D1X93D1X81D1W4o"). Qed.
End FPX_89.

#[export] Hint Rewrite amo_newvalB_eqf : bceq.
Section FPX_90. Context {fx : XPropExec.FPState}.

Lemma log_lookupB_eqf : ltac2:(zQ "d0!hn8!lc!u0!jf!hge!se!hr8!hoo2!unb!hgp6!tt5!hkn2!lm2>2fk@1$0$6@3$3>3log@1$0$9>2rb$5>2rk$4>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$a$8@1$b@1$c^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_90"] "##BUp'0h01li001lh13logh21xi011xh32x0h42x1h52x2h62x3h72x4h82IHh91ah:3acch;1bi021bh<2b1h=2b2h>7e_addr0h?5e_vali03!s/%h@7e_widthi04!s1'hA2fkhB5hintsi05!s/%hC2k1hD2k2hE2kbhF2kkhG1nhH2n1hI2n2hJ2rbhK4resthL2rkhM2sxhN1vhO1wi066a_basei075a_offi082bsi091di0:6!ts%i0;1sp;1p;2p;3p;4p;5p;6p;7p;8g00eTR0j1:Tg02cgj10Tg07LUj1Wj24j3Fj4@j5Bj6Mj7Ij8[Tg0:lIj1Rj23j3Aj4?j5Nj6Lj7Hj88Tg008]j36Tg00f4j1VTg0097j2DTg002Tj51Tg05ehj22Tg01mbj1=Tg05Slj6CTg05_6j1UTg068Fj4GTg05`mj3>Tg0:mZj4JTg05dUj3KTg04;>j7Qj1STg0:nnj2<Tg05b:j17Tg0:oEj4;!tX$Tj39Tg04<Tj7Ej1PTg04TYj1TTg003Vj6OTg01Qcj5ZTg07nYj3YTg08HnR1f1R2f0R339p=Xf3R4f2R5;Y2=913p=5g017a#:%:1R6g00`TR7g00b@R8g00aaR9g00;\R:%::R;g06?kR<#:R=g06;lR>]:R?]BR@]MRA]GRB]LRC]JRD%03#W%R3P1%05RE/43135356DX16P7PC%02%V1RF'4132FP8PBAFEF3AA5F3P9PA%04PFP2P3C@P!s0'?P:P@f4RE#0RGPFP5P2P3DBPE!s2+NP;P?f5RH#0RIPFP4!s>%EMPH!s4-LP=P>f6RJ#0PFPE!s>'FIPJ!s60Hf7RKPFPH!s:,G8,D>X7=D1X6;D1X5:D1X49D1X38D1X27D1P114G313E356D1X52RG,4I13HG56D[^06P3g01U4RGPGf:RG#0!v;$G356Df;RI#0!t='C5!v>%IF!s`&^?7^@9P3f=RF!s]&F356DP7PCf>RC#012HERL!se+M'413CMP8PBf?RB#012JHRM!t/%C5RN;F3AABN!w9$f@RA#012KJRN!uj%C5RB!wJ&APB!wJ-AR@#0f8RB/2KRAPJPHPEC5RO!wY+@PO!wY0BR?#0f9RO/2BPKPJPHC5R@!wf-?P@!wf2CR@#012GOP!sX$C5R?!wr0@P!s6/HPDfDR?/3Kg05U:R@P>PJPH%=ERPf<RQPI%=GRRECRSPE%U3RTPHPGCG?>54RUP3!u:%!su%O6RVg00hSRW%:8RXP>12QIRYPGPOPBC5!uf&JAKEH3?>54g06A<RZn10110100021010800R[P:P>fER\#0!s\$PPQPIPRFQPVP0P:P>P5!tJ,1<:5RVPM%7EPY%7GC;=9<2RYO6!sP$2P5!v%%PH1<:ERMPA%7J12CF%7Q!sR$4RCO6PZn0110200!s&$0!td%5!s5%20102100n!tu$!sI+!u-'410109!s@%P@P>PSPUP\PB!v</G8RAP!uN$P\!uJ0EPA!uJ+!sZ/VPYG8!u8%fGPG!u:'PMPCG8!t|HRC!t~FRM56>X0DP:^I8^D8^=7^H8^C8^<7RD%!yx$!uG%!u5'3!u5/O6PAP!t6G=6>MX;D!st$HPE%=4R@PIPG%=ORDECP4PTPEPOCG?>25P?PK!#3F0RTPWP!yi$IGRXP!{D$!|v$!}$%JAK4E3!sa$!yf6!u,$?!sQ$!tB$PDFEPT!w<&2!t;/1<:2PL%74PX%7O!y4$3!wL+FPO!wJ&E1<:4PN%7H12FQ%7I!sP$5!w^J!vLF,D>%0?RZ#S%T?EO14ZKPJEOPZPB!v60[P?!s82856>e!#6i@W8XK6XN7XO9XF8XE7P2P3O2!tW$;000121106107W>!s{%O3!sB,3110:104103X91P3DZX16D1WAo"). Qed.
End FPX_90.

#[export] Hint Rewrite log_lookupB_eqf : bceq.
Section FPX_91. Context {fx : XPropExec.FPState}.

Lemma know_lookupA0B_eqf : ltac2:(zQ "d0!hn8!lc!hr8!u0!jf!hge!un0!se!hoof!unb!tt5!hirf!lm2>2fk@1$0$2@3$4>4segs@1$0$6>2kn@1$0$2>2rb$7>2rk$5>1n$3>2sx$1>5hints@1$0$1>3acc@1$0$a$9@1$b@1$c^1@1$8^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_91"] "#$Gip'0h02knh11xi001xh22x0h32x1h42x2h52x3h62x4h72IHh81Ki011Kh93acch:1bi021bh;2b1h<2b2h=1ei031eh>2fkh?5hintsi04!s/%h@2k1hA2k2hB1lhC1nhD2n1i052n1hE2n2i062n2hF1ohG2rbi072rbhH4resthI2rkhJ4segshK2sxi081ai092a1i0:2a2i0;2bsi0<1ci0=1di0>5deltai0?2hii0@2hsi0A1ii0B1ki0C2k0i0D2kbi0E2kki0F2l0i0G3leni0H2loi0I3lo0i0J1mi0K2n0i0L2opi0M1pi0N3sx0i0O1vi0P1wi0Q1zp%0p;1p;2p;3p;4p;5p;6p;7p;8p;9g00eTR0j1FTg02cgj12Tg05_Vj1ej2rj3Cj4Lj5Jj6^j7Xj8Vl9gTg0;0Vj1cj2pj3Ej4Kj5_j6Yj7Wj8Ul91Tg008]j3@Tg00f4j1NTg0097j2TTg002Tj53Tg01mbj16Tg05Slj6D!tF$6j1dTg068Fj4QTg05`mj30Tg01D[j1>Tg01E@j1M!s/$^j2bTg01jZj2aTg00MQj1`Tg05b:j1:Tg03jZj7Bj1lTg05ehj28Tg00XYj2RTg01T9j29Tg01FXj2ATg01:AR1j2qTg027^j2Ij1iTg00Yhj2ZTg05cEj3[Tg05dUj3\Tg069Rj3HTg03kkj74j1mTg028nj2?j1nTg00hSR2j1oTg045mj1kTg003Vj6GTg02i6j1hTg01Qcj5j!vN$Tj3STg0;1jj4f!tk$;j2OTg00Vij4PTg017aR3f1R4f0R53Sp==g06?kR6f4R7f3R8f2R9P4Cf;S5p=51A94/95p=<f6R:f5R;1O78P9CP?045p=;P7P81O94P5CPp=]AH789!sA%7%F3R<g06>l#FS00g00`TR=g00b@R>g00aaR?g00;\R@%F@RA%F6R6g06;lRB]9RC]?RD]KRE]CRF]IRG]GRH^0<%25#e%c5Q00P<PH%24/r51p45P3%28RI?C95AE8955@HX0<P=PG%29%N3RJ7C4AE94JP>PFPIP9PJP5CLP8!s0&KP?PE%27RIP8PJP4P5DJP7!s2+_P@PD%2;RKP7PJP9P4P5E^P;!s4-YPAPC%2:RLP;PJ!t#$4P5FXP:!s60WP6PBf7RM#2RNP:P!t4%!sB$GVPM!s82Uf8ROPMPJ!t9$!s<&M91,TBX66D3X5AD3X4@D3X3?D3X2>D3X1=D3ACI85AE7855@HP=PG1=94RG9CK7AE;7G!u}$LP;1=89RL!v%$:P;PL!v%'PNP:1=78RN!v&&MP:PN!v&/OPM1=;7RD!v++OPMPD!v+/f9RC#2PO1=:;RD!v1-CPOPD!v12:RD#2PC1=M:RN!v30DPCP!s8/UPHf;RN?EDMP3PBPCg01U4REPBP9g05U:RLPBPNPD%6CRFP4P5%68S01EDS02PC%d5S03PDP8CQ?0MOS04P;PN!t5$OPMP:O6RGPGPGn0110000041010=!s1$0!s;$800012010D10EPEPBP4P=PBP9P!tH&PFP9P4g01VB#>RK#M%>K#>!s$&M'b,a5RKEDRIg01TV#`RJ?0MORPPGPGP@PBfARQ#2!u:$:CRR!uo$8FBS05A0J:MRSP0P@PBPM!u0,%N@RTP:O6!s?$4f=RUf<RV'8S06%:NRW1878RXP;POD5=0J5S07PMPUPV!sh$5POO6!uS$200!s&$0n101104!s5%2010210@n0!v2%!sI%RY!vC1>!sB%PY!u;$CRY#2!t0$W!x,$;FBS08A0JOCRZ!u8&C!tR-TPO!u5+?R[f>R\'8S09%:UR]18:;R^PMPD!u5':PCP[P\!se$5PD!u5W_P!s$%@PBfDR_#2R`P\PU%:VRa!}%$:FBS0;A0JCDRb!u%&DPO!tD&NPTPCO6Rc!u'&@Rd/8[S0<%:\S0=18M:RePOPN!u%'>PDPd!u'&5PNO6Rf!u'UgPg!s[$G00081010F1010K3010L108102!s1D4010N10H10K103!s4&B10A10K!{H-1!{H-9P@PB1RN4S0?!s1$95DS0@!{^$8P@PB%6DRg1A4KRh5<NS0APCP8PNP4PDPMPOF;Ri!s^%hNS0BP:!xc&!}'$O6Rjg06A<Rk!uc1!s41!w,$21q>>RlP@fBRm#2Rn/I7P1P>P>P@P5%6U1A74S0C5<\n200110M!}e'H10QS0Dg00>4Ro!w2%!t'$10!sL$Pi!xQ&O!tm-T!tm$p!xQ%PNP;PUP8PVD]Rq18\US0EPaPXP:PCD5Rr;05S0F!y8-5!y8$s!xUT!ub%PlP@1I`:!uW/[,AdS0G1A:4S0H'9!u\9IP!uW6A0qCDS0J!{0+!zx&PUPMP[P;P\Q0<Q0=P^!zt%RqP5F;RtP!zeVuP!s$%!u>+fERu#2Rv/IM!uE/d1AM4S0K5<Q!u@9L!u@7PVP:P\P7PUPDPNF;S0M!uK&N!~u-TPDO6Rw!u[&\POPdP:P[18Qd%:[PePCPVD5Rx!u\$yPNPQ!}U&5PVO6Rz!ulU{P{!}SxC!}S%PG!t>-100!s63!}s6=!{6$>PBP5!}6%9O%6M=<O4'ZR{P2%F>S0NPBA[\OMA\MO5?0;:Pk!w:2;00R|P8!#;k&P;P7O6R}!zs27!#<5+P;O6R~P~!ta$Q000300!x'$!s'$P}PG!s$&jPj!sJ$7!vQ'Q!vQ[I!#4~6P9!u$,P8O6RG!tJ$~!#5+%!#4n$LPB!}d$gP9P4PKEDRgPDPNP7POPCD7R~PjPj!y]$nPVPN%:DRn!sQ$7FBS0OPCPDP8PMPOD7Rj!#3K'!#3;%AHNV;Rp?0r5RrP!~iU!#3D%!#<T3s!t,$`!{R$aP7P8!#:M$PA0pCDRp!~C6\PMPqP5D7Rq!~1WfP!s$%@PBPv!|6$]!vt$MFBS0QPVPUP:PDPND7Rv!}D+!}4,[POPxP5D7S0RP!|jVz!s[&!#;?~!|J1!#D2$1000:30!sh$P10O21!s1$G3!s-&10B!#4\%?2010310J3!s-%!s9'810K4010910510:106!sb,<!sG'!#FK$!zU&LPBQ02Q04PQPdPU!#Ev-M91!#EwOS04!#Ez3IP!#EB'PQ!t'$!#E;&4P!#E3+!tI1T!tI$S02!x?%Q07PYPmP[!#Dr-!sG$7!xIFS0S!xL3!{K9z!t<$Y!#Du/4P!#Dm+!tQ1T!tQ$Rz!tq':PuP_PQ!#DV-M91Rx!tpH:!tp2wP!s$%@PBP_!}+&!#DS$4P!#DK+_PYPd!#DO-M91!#9y&Q0>fFRfPuPm!#D6-M91Rc!taFR`!~w3!#3T%!{x~!#D9:Q!#D5$Q!#D1-Q0APi!s/%BPmPQP\!#Ck-M91RsP!#Cg?S0B!#A-,?m7Q0DP!#C/@!t51T!t5$S0A!w6'F!wV25!wV$S0F!xpH>!#Br;?_:Q!#BB8Q!#B=,!xe&PtP!xMGS0T!xN2tP!s$%!tF-uMQ!#AH8Q!#A8,!{[1T!{[$S0U!t\&yfGPfPY!#@{-M91!#KQGS0V!tq2yPy!#A#~!#A#TS0W!#A&2P{P|!u`$N!#@M-M91R|!xO2dP[PV!#@R-M91!#CZ'!#@S4|!#@S'!}@'!#@SyRy!x:$D!#@Y-M91RtP|PtP{!#@Z3gP~Ps!#>_%m!{_$!#@=&4P!#@-'Q!|5'PrQ!{wHRr!xk2}!#7Z8}!#5y/!#@#$4Pp!{}4q!{}HRq!tD3P!s$%@PBPu!#?m/4P!#?^'Q!{U'Q0R!#@zG!{f$!t5/uPu!#6[~!zx5Pt!#?U~!#?U2Ru5@BXBH%ol^==RH%nN!#?h$Q!#>n@Q05PSQ!#=U3!xy?Q08PZQ!#<>3!x6-Q0;PbP`!sG5!wH~!#:}OQ!#:8-P:P7O1!#::;Q!#9-<POP:O1!#90<Q!#8Q3iP!s$%!si,CPMO1!#8S<Q!#7I3iPi!#7I~!#QJUyP!#4gEQ0OPjP!#3y2i!y~9!#?]%PPpPq!v`=Q0QPvPf!v>~!~G~!~G[=@BuXFHP@^E=^A>^<=^D=^@>^;=RH%m!~TI!#h7%!#JD%O6!~a7!wa?!#fe%!#I8%O6!~n7!{Q/O!#H--O6!~{6`!s8$!w|~!w|3Q0W!zwI!#as%!#<`%O6!{+6r!vI9r!ur07P8!ur$!{95qP!s$%!#Lq$!#;H,O6!{F6f!#;F%!vH~!{F~!{FI:H!{,$O!#SE+PDPC%6ORHP4P5Q01EDPOQ03PC!#rW$:MP{P!#C`&0!#rDTDPCPH!#[t&PS!ss$@PBPd!tF$:O!#SU&A0J;:!#?{%:!#E61TP;M91!sA$418VNPnPXP;PM!#mE$!#LI15PMM91!#Y+TT!z%9T!#DJ/!#S^&P!#DJ3Q0EPaP^PMPC!te%!#DYH!tS2P!s#&!#Tz-!#SA&!#Tz+!#Te'9P]PePO!#rJ&Px!t@UJPJ!{[~!#p4AD4!#p1%C!#R{+A<DFhPOP8PDP4PCP:PMF;RF!sO%hDPGP!#obE!#Oj$Q!#oW/VQ0C5<U!#j[6!#@-7F!w6&MQ!#Zi&PDP;PVP8PND]RFQ06PWPXP:POD5RX;05Q!#ZqG!t~=Y!#n~/\Q0H5<[!t~KA0FOC!y93PVPMP\P;PU!yC%^!yC%R^P5F;!yEW]P!s$%!u+-_!#ne,Q0GQ0K!#pz8!w'8NP:PUP7PVPCPDF;!#Li3UPOP[P:!#q#'ePCPND5Re!u7$c!u7U[P[!#Ck~P{!#Ck1{!#n7GM!#n7/M%6:=<M4'ZP2Q!#n2$UM:A\:M5?07;!#n26Pt!ym2|P|!#T;9t!#7w$P{!#dJ'!#mhzU!xE$!#T7'P9!#U|$tP{P|!#>W3IPCPDP7!#m3$!#eK77F4POPCP8P:PMD7!}U4AHDN;RR?0X!}@XRX!#8P8X!#e03:F4A0R!||8UPMP^P5D7!|kWxP!s$%!#dg2MF4PNPVP:PCPD!uo+!|3/\POPe!tE$!{yVc!s[&!#8Q~!{Y1{!#A-~!#A-2,TB%2NR{#l%kNEG%i{%hNEGAC{DMP:EGP{PD1=OMRO!$8L0g!z9$!s;215@Be!$8b@W7XH<X83P5DjX0<D3WJD3W>o"). Qed.
End FPX_91.

#[export] Hint Rewrite know_lookupA0B_eqf : bceq.
Section FPX_92. Context {fx : XPropExec.FPState}.

Lemma know_lookupAB_eqf : ltac2:(zQ "d0!hn8!lc!hr8!u0!jf!hge!un0!se!hopf!unb!tt5!hkj3!lm2>2fk@1$0$2@3$4>4segs@1$0$6>2kn@1$0$2>2rb$7>2rk$5>1n$3>2sx$1>5hints@1$0$1>3acc@1$0$a$9@1$b@1$c^1@1$8^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_92"] "##3Zp'0h03acch12fkh25hintsh32knh41lh51nh62rbh72rkh84segsh92sxh:1xi001xh;2x0h<2x1h=2x2h>2x3h?2x4h@2x5hA2x6i014acc'i022bsi036!t4$'i04!s0%0i053scsi061vp;1p;2p;3p;4p;5p;6p;7p;8p;9g00eTj12Tg02cgj10Tg07A6j1?j2Oj3@j4=j5:j69j7Mj8Dl9JTg0;3;j1;j2Ej3>j4<j58j6Nj7Lj8Cl9KTg0;0Vj1Al95Tg05`mj33Tg07BLj54Tg05dUj36Tg07Caj2BTg008]j37Tg0097j2FTg05_Vj1GTg0;4Nj1HTg003Vj6ITg002Tj51Tg017a#2R0g06>l#2R1g00`TR2g00b@R3g00aaR4g00;\R5%25R6g06?k#2R7g06;lR8]0R9]2R:]9R;]5R<]7R=]6R>^30R?f0R@#0#?%;@P0P>f1R>#0/O@1E>@P2P=f2R=#0?@>@A>=>@P3P<f3R<#0P=P>P@C=P<!s0&<P4P;f4R;#0!s:'D:P;!s2+8P5P:f5R:#0!s<,E9P!sJ-ENP6P9f6R9#0!s>/FMP!sN0FLP7P8f7RA#0!s@1GDPA!s82CP?^81R?f8RB#AP8P8P@PB!sM1O8A3=>@RCg00hSRD%23REP8f:f9RF!sS%D4A69A@?3=>1B>@RGn10110000021010200RHg06A<RIn!s@'33010610510420!sW$300!tR$F!tR3M95PCPHP!sdC578X4?!sj$!sh2P@!sj%DPE!t//D4A6:9!u0$P!u+6!t?D,F8%0BRI#G%HBEIPI!tD5J!tY7K578eXA7D1X@6D1X?5D1X>4D1X=3D1X<2D1X;0D1X:1D1W1o"). Qed.
End FPX_92.

#[export] Hint Rewrite know_lookupAB_eqf : bceq.
Section FPX_93. Context {fx : XPropExec.FPState}.

Lemma sym_readB_eqf : ltac2:(zQ "h00!hn8!hu2!u0!usc!lc!u6!jf!un0!se!hr8!mq2!tt5!hoqe!ut6!lm2!hln6>2fk@1$0$9>4segs@1$0$7>2ss$d@3$6>3scr$3>1a$a>1n$2>3sx'$4@1$5@2$1@2$1@2$1$8@1$0$b$3$2@3$f^2^1@1$e^3@3$c^2^1^3").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_93"] "##A,p'0h01li001lh11nh21ah34segsh43acch51ei011eh62fkh75hintsi02!s/%h82knh93logh:2rbh;2rkh<2ssh=2sxh>3sx'h?1vi031vh@1xi041xhA2x0hB2x1hC2x2i056!su$'i063scsi074scs'i081tp;1p;2p;3p;4p;5p;6p;8p;9p;7g00eTR0j14Tg01:Aj2?Tg00hSj1VTg02cgj12Tg07Hhj3hj4Wj5Rj6Oj7^Tg0;5ij3[j4Uj5Pj6Mj7YTg0:Tej1Lj2;Tg07J:j1KTg043Tj19Tg044aj1=Tg07KFj1ITg00f4j1JTg07LUj8Xj1bTg07O7j3@j1_Tg07PHj16Tg07QVj18Tg07Rej33Tg07T5j17Tg07FHj1GTg07A6l9Qj1eTg00O[j1ETg07UBj4C!t:$Tj3BTg00g4j1DTg00nJj1NTg0:lIj8Hj1TTg0:WCj3>j1STg0;3;l9Fj1gTg008]j35Tg0097j2fTg0;78j1cTg003Vj6<Tg0;8Rj1`Tg0;9jj1\Tg07Mij1ZTg0;;?j1]Tg002Tj5:Tg0044j3aTg01SYj4ATg00kNj2dTg06?kR1f1R2f0R33ap=0f7R4f6R5g00aaR6f5R7g07WmR8g00`TR9f4R:f3R;f2R<CAP2CAP3CA'dp=1g017a#4R=g06>l#4R>g07Y=P8g01U4R?g00;\R@%41RA,?9RB/?8RC/?6RD#VRE]>RF^16RG]2%2<9h23A[23<P?PGP<P2%2;P3CWP<P2P;P3CUP6PFP;P<%2:P2P3DRP;P<P!s2%PP@PEP:P;%27!sX$3EOP:P;P!s4'MP9^?9RF%L5g06;lRGPE%24%K7RH%9;RI%=;RJ!tF$I:RK%J1RLGXRMPDPCPBPAP;P<O1f:RN#2?@57/02%64RO%84RP;33RQf8RR#7RSG1PGPEf9RT#2PR%G4RU%97RV%=7RW!tb$3P2M9QRX!t&+7!t&$<RY#2?@R4!t&$T%8T;33RZ%7NR[G1!sS+0P9P9%8RR\%7TR]#EP2n10110400020020!s4$0R^f;R_#2?@45P4P5P7P^CC=B12R`'0%6RRaP0P9%49RbP\%J9RcP3!sp78;33Rd%D]ReG1%NDRfn!sK'33010310710520!s-%00P!sG5610220!s-%00PGPEP4PHPIP!w9$PKPLGHRg!uZ'1;N<RhA>N57RN/02PQPSG1Ri!s^$TPRPUPVP!vj-F!s_,Y<RjA>Y!vc$PZP[G1RY!vY+^A>_45Rk/0`PdPeG1RlP!uCdRm55EX5FPA^16^2?RF%S5!tx$!yS,hP;P5P7O2!uC+!sG$!xp,jP7PRP4!sG%!u,$!u',P:P4P5O2!u++!u&e=5EmX0Fg08Hn#4g00b@%4@PG^4A]7^=@^16];^:9RF]9Re%T!uF%3!wx1O7P!wX%XPYPl!tckePF^8=^3>R>%g!tF%g!t6&<!xh3O8!tHo>!t3$5%K:%9<%=<P2P3%I;PLGH!yv,T<A>T7:!}Y$5%85;33%74!x>&RP4%G5%9:%=:P;P<!z\4_<10k2A3a\3P]!~23PP%ES!~';A!}w$:PA!}y%,0N!s[$bPPP!}m;=3O3%DS!yFg,fE%25Rf#e%c5E<%bf%`5E<%_f%\5E<%Zf%]5E<!tp$f!up$2P3F^!s6$5!s6+Y55EeXC@D:XB6D:XA?D:X@8D:W<W3W6o"). Qed.
End FPX_93.

#[export] Hint Rewrite sym_readB_eqf : bceq.
Section FPX_94. Context {fx : XPropExec.FPState}.

Lemma know_lookupB_eqf : ltac2:(zQ "d0!hn8!lc!u0!jf!hge!un0!se!hr8!hor9!unb!tt5!hos7!lm2>2fk@1$0$7>4segs@1$0$5@3$3>2rb$6>2rk$4>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$a$9@2$b^1@1$c^2@2$8^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_94"] "##/Th01lh14segsh23acch32fkh45hintsh52knh61nh72rbh82rkh92sxh:1xh;2x0h<2x1h=2x2h>2x3h?2x4p;1p;2p;3p;4p;5p;6p;7p;9p;8g00eTj12Tg02cgj10Tg0;<Qj2=j3Jj4>j5;j67j79j8DTg0;=fj26j3Gj4<j5:j68j7Ij8ETg07A6l9Hj1?Tg0;3;l95j1FTg008]j33Tg0097j2ATg0;78j1@Tg003Vj64Tg04@Wj1BTg04Aej1CTg002Tj51Tg017a#2R0g06>l#2R1g00`TR2g00b@R3g00aaR4g00;\R5%25R6g06?k#2R7g06;lR8]2R9]4R:]9R;]6R<]8R=f0R>f1R?#0'=16>?P3P<f2R<#0=J?>AG?<>P4P;P<f3R;#0P?P>C>P<P;!s0$<P5P:P;f4R:#0P<P?P>D;P;P:!s2&:P6P9P:f5R9#0P;!s<%E7P:P9!s4+8P7P8P9f6R@#0P:!s>'F9P9P@!s6-IP0f7RAf8RB#0PAP>P@P9!sF'M9HPBPAPB!s;15RC538X00P=^72^50^11R1%FAP>!sS3O8=38CX01PAP@PA!s?,P>M95,A8%0AR1#?%@AE4%B1%CAE4P@P1!sP/GD!sb3GE538eX?7D1X>6D1X=5D1X<4D1X;3D1X:2D1W1W3o"). Qed.
End FPX_94.

#[export] Hint Rewrite know_lookupB_eqf : bceq.
Section FPX_95. Context {fx : XPropExec.FPState}.


Lemma sym_stepB_eq : ltac2:(zQ "c0!hn8!jf!un0!vn5!im3!vj9!usc!vnc!ut6!hot7!lm2!hlp2>4segs@1$0$2>1i$3>2ss$8>3scr$6@3$1$7@5$b@1$a@1$4@1$5^2^4^3^2^1@4$9^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"] "#%FYp'0h01ei001eh11ai011ah21bi021bh31oh41lh51ni031nh62opi042oph73scrh82wdi052wdh93aopi063aoph:1ci071ch;1ii081ih<3immi093immh=3oldh>1sh?4segsh@3srci0:3srchA2sshB3sx'i0;2aqi0<3csri0=3diri0>5dirs'i0?3dsti0@2fmi0A3fmti0B2i0i0C1ki0D2loi0E3nx'i0F2p0i0G2p1i0H2p2i0I4predi0J1ri0K2r'i0L2rdi0M2rli0N2rmi0O2rsi0P3rs1i0Q3rs2i0R3rs3i0S4scr'i0T3scsi0U2shi0V4succi0W2sxi0X2szi0Y1ti0Z4u!uw$[1vi0\4voldi0]1xi0^1zp%0p%1p&0p;1p;2p;4p;3p;7p;5p;6g00eTS00j1iTg00hSR0j1YTg07FHj15Tg01Vgj14Tg09kok10bj4MTg01D[j1>Tg07ZOj1JTg01gjj1\!s8$mj2LTg01E@j1WTg07[Uk207Tg00MQj19Tg07\5j1=Tg01FXj26Tg00f4k10[Tg02cgj1?Tg07]@j17Tg07^Mj21Tg07_Zj2dk10GTg07`mk20UTg05[Nk10STg07aSk20P!tL$^k20NTg01jZk20MTg00kNj2QTg07cHk40Bk10FTg07PHj1kTg07d]j4l!t[$Tj3UTg07QVj1oTg07KFj1jTg07Rej3mTg01:AR1j2cTg07enj3[k10!tr$gAj1!tZ$Hhj7Ak30=Tg07hSk30aTg07i6j3b!s/$cj1ZTg07jnj3HTg07J:j1!uQ$l;j1ETg07mHj2!tr$nYj3!se$T5j1_Tg07O7j3vk10LTg07ohj3gj1~Tg081<j4fk10RTg082Lj2^Tg0836j4uj1|Tg084Gj3tTg085Tk40Zj1{Tg086cj3sTg087oj3ek10CTg089Ej1]Tg08:Rj1rTg08;_j2XTg00nJk10YTg08<ok10XTg08>?k50Tk10?Tg0:`Aj2Rk10<Tg0:aQj4qk10;Tg0:d4j3Ik108Tg0;5ij7Pk306Tg0:WCj3Dk10@Tg0:?Oj4Ok10JTg0:Ofj4Tk10ATg0:CDj4pk10ITg0:gcj3Kk109Tg0:icj5nk10:Tg0:\Gk10>j3VTg0097k205Tg0;?8k304Tg003Vj6!tS$@Nk103Tg0;Afk10DTg0;C@k10ETg0;DWk100Tg0;F0k10HTg0;GGk10KTg0;9jj1}Tg0:k4k10OTg0;H_k10QTg0:E_j1zTg07b1k10VTg0:6=k10WTg08B=k50`Tg0;J2k40_Tg08COj2yTg08D5k40!x+$E@j3`Tg08FPk20!wV$G\j6wTg0044j3xTg008]k30\Tf2R2f1R3f0R4'y'^p>02f5R5f4R6f3R7P2H0^?`34p=01634,y2,^7p=C20]72!s?%Bf7R8f6R9P5P6P7P2Ew!s?%2P9P5g08HnR:?U67P2P3P4Ewp=hg06?kR;?x23=`74p=;g01TVR<9[34p=NAa723=U:4p=:AV2349x;7p=@AI34<p=<g08JiR:@0\34p=3g06>l#ig08J=R=g07Y=g07WmR>g09k=g00`TR?g00;\R@#YRA^2?]1]:S01%53#4RB$0bQ01P=P:P7P6P3g01VBRC#>RD#>RE#>!s$%RF#JRG%\DRH#>RI#>#J/L4%\C#>!sS$J#W+07S02802G#9S03%=6RK%WERE'6S04&0[;RLP7E0RMP6P3PGPGQ02PKCC#9Q04P!sB%NP6P3Q04#9PGPGPK%\I!t8$S05CC!sJ&IP?P:%55#4RK#?RO%75S06/13RP'dP9P7%=9S07/6ERQ#920UG4%JJRJ/L3S08'6&0SD+0P%WD%WF+0N+0MS09PLP5E0S0:g08L9RFP!s$-n0110]00081010^1010330104101102!s1D4010W10D103100!s4&C10B103S0;P0P@P:!s+$AP6P7%79S0</12RDQ0</13RRO3S0=1Q@4RS!sN-59S0>#4RT#?RU/dDS0?1dURS0@O3PSPUP7PDPRH0BS0An1!u;'21010Y00!s85P8P@g00b@S0BP4PGPG%=8S0C%\C#JRV!v_$DCCQ0C/6ES0E!v6$Y00020000PLP9CBS0FQ0!uG$%k5PFf8RWP@Q0B!xa%%=WRX1LV2S0GCC16XES0H!sm23P5%7WRX/1611X7Cl=U;L%o8%j85m4CB!u--002010Y10>S0I!uF60%i;RV,c?RY/c>RZg00aaR['cR\P:f9R]P8%58S0J#4R^#?R_P9%78R`/13S0K1LJ4RJ5[_%S6Rag08MIP@!~I$7P7g00>4!u0$X00040!s#&S0LFAP1PZP[P:P4P1PYP>P:P3P1P?PVP:P3f>Rb#=!v`$MP@%i?S0N%JHRHg00?M:0aH<Rc7b]S0O%7bRd%Z]S0P=Hd3n01!t4%!vG$%GbS0Q%5bS0RP6%EbP4P2G2n200110H00012010[10T!s:&G!s:'H10S!s:&F!s:'G10ES0SPF!vf2F00ReP0g01U4Rf#YRgP:%E9S0TA[UDJ'FS0UQ0EP`11`7S0VQ085[_Rh11`2S0W7aa%G8S0XQ0J%_8S0YP4FhS0ZAv_haAg_haS0[P9C;!tH4K00S0\P9P2!{1$R%9JS0]CfPQ!}c%!s@-JC/^4#9S0^!sE7!|T$4RC!sB-5P2POg00=HS0_PPQ0]Cu%=5/6EROPLP6E0S0`P9P21^H!t#$a9t7R!se'Ri!t',PCCu!s>'S0bP8Q0E!{q%RjP5P!st$CBRkPFPF!s\/H0Z!s],cP9P2As7RC!t1+UP@P:11`4Rl=e_6S0dP0P\P:P]P8P_P91N_l%]6#SS0e%r6S0f!z7CQ0MP@Q0NAbHWcS0gPd%ZWS0h!yq5S0iQ0QQ0RP6Q0R#4S0j#?11d8S0k'N,Qf!z%e!y~7PF!tU1RdP@P:%5WS0l#4Rm#?11X3S0m;e5S0nP0PfP:%EWS0o!sO%]S0p#4Rn#?Ro%7]Rp/12S0q'NRq,X4S0r%=]!}/$s!v#'7cS0tPp%Z7S0u%9<S0v5Hp!v+3w%]9#SRr11p3S0x5aq%G]S0yQ0p%_]S0z&0YfS0{FhS0|AvoqrAgoqrS0}PW!{?$!sv0!uq4J!uq5S0~P0g00<\S10#YRoP:&0X9RpP@P:f:Rs#5#4Rt#?Ru%7sS11/12Rv;e9S12P0P!}Z$sS131Nuv'FS14!yS%f=Ruf;Rw%5w#4Rx#?S15PsQ15%7w/17S16'N%]8#SS17%r8S18FAS19!ynAfBRy!#5#$1:!vv'wcS1;%7yRc%ZwS1<=Hc!yz31=%5yS1>#4RH#?Rz11csS1?'NS1@%]b#SR{PzPbPWP311c]S1AI0TS1B3a%GyS1CQ1>P6P8FhS1DP4Q1@=gz{P2C;!zU3\!zUe!#4G3!xBD600S1E!#?+-P!#?:48000S2010L109!s-33!s-%P10940107!s1$Q1095010X10W!sE$O!sE&X!sE+4!#?_$!sB-!s4+U!s4,P10Q!t0&!sMC5010@10I10V!s:%!th-00!#@_$!sT,!sb5510;10M!t+%6!s72P10Q7!sY%!s=3!sp0<!s4,Z!s4&A!v>0A!uw+!su&!sE+Q10R10N6!s=5N!sm0N5!sH3!s7I?10:!sj+4010=!sH+3!t-,!#H2%MPNPIP?P:1RKPS1FQ0:P!#EC~!#EC01G!#EC/T!#DP$CMS1HPS!s;,1RTD1RT!s?$IPS!sN+q!#DtFQ0FQ!#Bl6S1J!#:`,^P9Q0K=I^JS1KPaQ0LFPQ!#?e8!#4~$Q0TAITDJ'FQ0EP`Q!#?P$I^RzPaQ0WQ0XC:Q0JQ0YP4AD^zaP^PzPaC@P9G2!}y7S1LP9P2!uS$RQ0]CO!#<j'z!s?/^!s?-y!s?,PC!s>-cP5P2PKQ!#?2&T!#>6$E0R|Pi!sZ0T!sZ+}PjP!#>T+!sF'p!sF+~PUP@P:AK^l6S1M!vZ11<^lS1NQ0eQ0fFP!#>7CQ!#=h-jQ0k'<!#=]gS0j!#=`FP@P:Q0m=Km5!#=L$Q!#=I$Q0q,<nS1O,X4Q0sQ0wQ1OPrQ0xQ0yC:Q0pQ0zQ0{Q1O=DnrPn!sE$C@PW!xB$!#<ECS1P!sM3S1QP0PoP:Pp!v}%tv9S1R!y{&131<tv'FS1S!w7&uPwPxPsQ16,<xS1TQ17Q18!w9D1:Q1=Q1?,<HS1UP{PH!#:i$Q1ADnQ1CC:!#:^%P4PHQ1UP{C@S1V!wV7!#:^NS1W!#:an!#:^~!#:^~!#:^~!#:^~!#:^~!#:^aRx'3W3Q10P?^2?^1?S1X]6S10&0JBQ10!#:~-Q!#W{0Q!#9T0Q0?Q0@CMPSQ!#W>H!#9H;0@PeQ!#P1%6!#7m%O3!#Og/!s=&^!s=7PC!s<,S0?Q0`PiQ0b!#7>&Q0cPUPdQ0~Q!#CP~!{p~!{p~!{p~!{p~!{ph/3xW0g00GEQ!{i%X&0IBQ1X!{i2Q!z]'zPyPc!yt5?!yt~!yt~!yt~!yt~!yt~!ytvQ10&0A!#6U5!yj1P5P2P7!#EL&O3!#EL&PiQ0?!z#'P~!y~~!y~~!y~~!y~~!y~~!y~vPV^5[^1fS10&0@!z-;!#N?&UQ0ZP5PhPaO2S0~Q!#f6<!z]&|PiP}!zF1!#Il$n!#I|1rQ0|P8PqPrO2S0[Q!#^w\!{K~!{K~!{K~!{K~!{K~!{Kn4Q10&0>!{CGAD^haS0@Q0~!{@oADnqr!|?&!{=Z!#Qi-Q!#fa&Q!#fU&Q!#eyBQ1DP4f@S0[Q1@P{O2!#dV~!#Ps~!}f~!}f~!}f~!}f~!}f~!}f@P?^0?S10&0<!}k3P?!s2$PO1!#df~!#df3!#R'=P6PDO1P6PRO1!#R1e!#4>0Q0@AV^ha!#{e<@!#4>VQ0~AVnqr!#4;ZRq!#4=fQ1@=VH!#qh~!#48SRh!#4:~!#4:~!#4:~!#4:~!#4:~!#NGg01&0;B!$;&+!#>z$!#pV0!~q-Q1IPSQ0=!~baQ!~6@qP!ze~!ze~!ze~!ze~!ze~!zel3Q0BPf]<^0?Rh&08B!zk2Q!#vy/_P9P5Q0KPJO2!#vx$A!#vxBP6PDPJO2!#v{%P5!#v}$O2Rq!#v|7qaP^Pq!#v|>!{F<@P:Q!$4Z2P5PlP<O2!#uE%A!#uENf<RqQ0kP<O2!$4#~!#uE5!#<i0P8Q0qP<O2Rd!#uC'Pd!#uB5ADndrPnPd!#u?N!#JNI3PWPvP<O2'F!#u5+Q15PsP]Q16!w&$!#u6$A!#u6G0[Q1?!uK$<P{Q1B!#u/2P<P{C@!#u'b!#K3~!#68~!#68~!#68~!#68~!#68~!#68TX>hg0:i6RhP@]8^0?R<&09!#6=CQ!$-1&!#67:RHQ1L!#59>P5PlP6O2!s~3!$'X&AQ!$&78R_!#3r6P9Q0mP5O2Q!$$~4!~h/!~\$9O!~m+S!~c2Q!$$m'ARw!~_H1U!~V4Q!$$Td!~O~!~O~!~O~!~O~!~O~!~O~!~O\2<P?^@?^=?^9o^8hRh&0:!~O7!}xCQ1MP!}C4Q!$2{0Q!$2v+!|y'!|eN0[!$2Q'O4!|p~!|p~!|p~!|p~!|p~!|p~!|p~!|pP0h%Y\^B@!#s`$^7>RhB0673!#<D<5!#<@+O4!#<@9!}DF!ss-!#<5%O4Q!$?FH!}nE]!#;d,O4Q!$;m~!|P~!|P~!|P~!|P~!|P~!|P]3h!|9$2P7P3Q03%=7R=/6ERhPLP2E0P7!$of+=CC#9P!s?-%9hPGPGP=Q!$oY%2E0!$oW$6#4R=%76/13Rh'RP5P7%9OQ09!$+b%!#jl~!#jl;PKP7Q06/12RxPPCM!#jy'KP71RKxQ1F!s;$KP7PxPP!$PPHP9!$mI$4!vD%7Q0DCCPQ!$n,35CB!$n&'6PFP8!$n$,Q0CQ0GCCQ!$ne33P511`6Q0V!$mq&9%j9!$mq<!tn6!#3Y$WP9PTP5AITRJ!$Qx%!#>[@%=u/6ERRP@Q0NQ0O%7uR;Q0P=H;!$lJ3uR`%5uRGP6%Eu!#XDy!$a^%5AIKxJ'FPQQ0<Q0</17Q085ITRxPaPD%G9C:Q0>%_9P4ADTxaPTPxPaC@P5!#[b95P2!x`$P!$S]$!$4D&!s=-^!s=96/14Ra!sB-6P2P=Q0_PhQ0]CT!$xx'P5P2Q0a9t7P!sn5Pa!$T/+P9!$Ch$CBP6!sd&CB!|2$!sU/p!sk/As7Pa!s7+@P:AKTC6!xc11<TC!$T'HP!x]'gP;Q0h!xZ5P`PGP6%4G11;8!$TEi!#]{LK=K^!$TB%%E8!$n2$X2,<mRf,X4Q0H!u4&tPXQ0uQ0v5HX!sn2fPrQ0m%GWC:Q0l%_WQ0{ADmfrPmPfPrC@P8!#^Ce0q=Kn9!zr']Q1O!#^B'qPsPtP]Q11/17,<t!$TQHfARV#=/6E!uX%1;%7VR@Q1<=H@!}E35VRE#4R?11@s'<RsP{P?!$hi&@]Dn%GVC:PE!#^u%?Ps!#^u~!#@0~!#@0~!#@0~!#@0~!#@0~!#@0~!#@09-05:%?BR::0=73B04B73E8&0?:&03BE8&0C:&0D!s0$1:&0E!s0$F:&00!s0$G:&0HBE8%~:&0K!s9$L:%}BE8%|:&0OBE8%{:&0Q!sA$R:%z!s/$V:&0WBE8P:P!%5$%I0`!s1'H0_'3eW7WAW;W?o"). Qed.
(* [comment removed for export] *)
Lemma sym_step_know : ltac2:(zQ "c0!hn8!jf!vj9!usc!ut6!un0!vn5!vr8!hr8!tt5!vnc!hot7>4segs@1$0$5>1i$6>2ss$4>3scr$3>3ss'$4>3scs@1$0$9>4scr'$3>0@3$1$a@4$b^7^6^5^4@3$7^3^2^1@3$1@1$0$8@1$2^4@1$2^6").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"] "#'3[p'0h01Hh12H0h21ei001eh32rdi012rdh43rs1i023rs1h52opi032oph63rs2i043rs2h73ss'h82_Hh93immi053immh:3_H0h;1pi061ph<3fmti073fmth=1oi081oh>2e0i092e0h?1li0:1lh@1bi0;1bhA1ni0<1nhB2rmi0=2rmhC1si0>1shD2aqi0?2aqhE2rli0@2rlhF1wi0A1whG1ii0B1ihH1mhI2o0hJ5shamti0C!s/%hK2sxi0D2sxhL2szi0E2szhM1ci0F1chN3csri0G3csrhO3diri0H3dirhP3dsti0I3dsthQ2e1i0J2e1hR2e2hS2fmi0K2fmhT1ki0L1khU2loi0M2lohV2o1hW4predi0N!s-$hX3rs3i0O3rs3hY3scri0P3scrhZ4scr'i0Q!s-$h[3scsi0R3scsh\4segsh]6signedi0S!s0&h^3srci0T3srch_2ssi0U2ssh`4succi0V!s-$ha4u!wu$W!s-$hb1vi0X1vhc1zi0Y1zi0Z1ai0[6a_basei0\5a_offi0]3aopi0^3appi0_2b0i0`2b1i0a8bv_is_wfi0b;bv_un!tm'c5dirs'i0d2hii0e5hintsi0f6!s/$'i0g2i0i0h2l1i0i3nx'i0j3op0i0k2p0i0l2p1i0m2p2i0n1qi0o1ri0p2r'i0q2rsi0r4scs'i0s2shi0t1ti0u4voldi0v2wdi0w1xi0x1yi0y2z0p%0p%1p%2p%3p&0p;1p;4p;3p;2p;9p;6p;8p;5g00eTR0k10PTg0;J2k40uTg08E@j36Tg01D[j1wTg07ZOk100Tg01gjk10U!s:$mj2ETg01E@k10TTg07[Uk20DTg08COk20;Tg07\5j1CTg01FXj2:Tg00f4k10fTg00MQj1NTg07FHj14Tg01Vgj17Tg07]@j18Tg07^Mj20Tg0:`Aj2|Tg07`mk20FTg05[Nk10mTg07aSk20=!t\$^k20kTg01jZk204Tg00hSR1k10<Tg09kok40CTg00kNk203Tg0:aQk40\Tg07PHj1aTg07KFj1[Tg01:AR2k20LTg07J:j1?Tg0:d4j3OTg07gAj1iTg0:Tej2!uz$QVj1KTg07T5j1FTg043Tj1JTg044aj1ZTg0;3;l9_Tg00O[j1kTg07Rej3BTg00g4k10^Tg00nJk10dTg07hSk30cTg07i6j3!vt$icj1GTg07jnj32Tg07l;j1STg07mHk207Tg0:?Oj4rTg084Gk30@Tg0:Ofk406Tg0:CDk40?Tg086ck30>Tg0:gcj3qTg08:Rj1\Tg08;_k20ETg08<ok10bTg008]j31Tg0;KAS00k105Tg08D5j4A!s<$dk20jTg08G\j6PTg0097j2o!s/$mj2nTg08FPj2LTg0:WCj3vTg07nYk308Tg082Lk20MTg0;LGk20iTg00ckk40aTg01SYj4mTg0:fTk20KTg09]nk20HTg05ehk20tTg028nk20JTg01T9k20ZTg01mbk10hTg00Yhk20gTg05b:k10YTg0:XQk20XTg0:\Gk30RTg0:lIk80WTg07d]k40q!z}$Tk30!wr$44k30!w:$UBk40eTg089Ek10pTg0:ick50!ul$l0k60V!uv$Qk60`Tg04MSk30!v%$JiR3f1R4f0R531p=320M45#Np=Vf5R6f4R7f3R8f2R9CA?645p=`1:45-0;9p>0_!s2'-0M8p=s1L89!sL%zg06?kR:P7P8P9P4H0q<0B5p=l%K4=B95p>0[f7R;f6R<%J6%Z!sO&P5L0Wp=jAv894>0S:5p=D%a9?B45p=gP<g00aaR=P6g07WmR>g00`TR?!t7%CmP4CmP5Cm-03;p=>!tN,e>0B:5p>0GP;P<P6!s@%EP!t~%91094=O85p=~g08HnR@B08894!u+%^Av678B0R94560S:p=YP9g00=HRAP4P5H06p>0Ag01TVRB9O45p=R&0p5#ip=<1045=O9Bp=5g01U4RCAO45B+03p>0l!tY'1045I0op=U!t6%:0S:8p=XA6894=135p=W20;45-0M9p>0]P8P9%N4P5CAp=bP3P>P6A678!vd$J0Vp=MA1>45p=@P3P<!sC3HP3g07Y=RD!s@3IA1D45p==!v\'CA=1D5p=cPD!v['CA!wv'J0`p=e1E45,:9-0;8-0M7p=]%C4/:5p=Qg08L9RE!u9%pP3PE!vZ$?MS01!sg+h!u}'P4%S5EPp>0:PD!s9'!sK&yB0S:45p={!xF3:0S:6p>02P<P=P6P>P!y$0&0^!y&+x%G4=295p=}!xQ%%?560B@p=fP<P6B0B@7!tC&EPp=uB0B:45p>0NP?g00b@R@P5PBCmp=tB0nA!sB$I!yi,P4Cr!wZ%d203C5p>0s!xp'-03Cp>01!sR,!sI$!ue$Q1:<!s=+!tJ$>0!y'$:0889p>0O!xQ$!v-+Vp>0rg06>l$0Pg08J=RA&0P:RF!tZ'H0uA6945'3PAPAP3P5f8RAP4g01VBRG#wRH#wS02#w!s$%RI$00RJ&0UHRK#wRL#w$00RM/E5&0UGS03#w!s]$N$0TRO+0DRP-0;J'VS04%CARQQ02$0TRR':RS&0f:RTP;E`PAP4B0_JPQ,VJPSP!s;+%NSPJPJPQ&0UL$00RL/E5S05Cs!sJ&?P3f9RQ#4#7RS%8Q/04RU'|f:RVP8%CVS06/:RRW#NS0720FJ5S08&00NRN/E4S09':&0mHRX+0=&0TH&0TI+0kS0:+04S0;PTPQE`PE!s$/n0110w00081010Y1010<3010310Z10;!s1D4010D10M10<100!s4&L10g10<P1g00;\RIP3P1PI&0<IRH%4V#7RYP8%8VRZ/09R[10Z4R\H0C203I5R]P1PIPHPYP81|Y[1|Y\H0CP]PYP8P[P\H0\n1!u,'21010t00!s85f;R^PIP@P5PJPJ%C^R_&0UG$00R`!vM$<Cs1:_RS0=!u{$t00020000PTPVCzP0PIP3%aQPEf<Ra!sp$4!sp%aRb1E`9S0>Cs1:bRS0?!sh24P6%8aRc/0710c8PTDl%[^:0[5^Cz!ty-002010t10c!u65P120L?FRd00L>Re00L=RfP3g06;lRg&0<fRh%4^S0@#7S0A%?^RiQ0A%8^Rj/04S0B1EN5S0C3ORkPk%i7S0Dg08MIS0EPI!}2$8P8g00>4S0F!u8$E00040!s#&S0G%[VS0HPTGjPfPePdPFf>Rk#4S0I#7Rl/T9S0JPl%8kS0K/07S0L1EN8S0M5Ol%i;S0NP4CDf=Rm%Km;g5Rn%FkS0OG>PgPh%4mS0P#7Rof?RpQ0P%8mRq/08S0Q1EN9S0R5OoRr#J%Zr%i<S0SQ!u2$<P6P6P6Q!u,9TP5P4M9_!u&+@Rr#4S0U#7S0V/T9RsQ0VQ0V%8rS0W/0<S0X1EN6S0Y3O%iQS0ZP4CD%apS0[@0[p5Rt%FrRuG>!sz'P0P?P?%KkS0\%FpS0]#kP4!xI4010:Rv%4pS0^#7Rw%8pS0_/06S0`1EN7S0a5OwRx%iAS0bPxQ0b!uX%AP;P;P;!uX:cPvP4I0GCD%akS0dP0P?&0P?RxQ0\&0f?S0eP5!t\7t;B5RyQ0]$0^RzG>&0dfR{!~d+33010X10r10f20!s-%00P!sG5R10e21!s-%00P2PeP=P3P5P2PdP>P3P4P2P?PFP3P4fBR|#CS0f/:RS0gPIPx&00KRKQ01:0cKBR}7;QS0h%8|R~%GQS0i=2~4n01!ug%!|c$%?|S0j%4|S0kP7%S|P5P9G9n200110m00012!tj&!s:&l!s:'m10Q!s:&k!s:'l10iPE!},2k00P1&0<CS0lP3%SVQ0C9OY[+07Q0=PjQ0APjP8Q09C~R[Q0D10j9PiC^Q0@%F^P5Q0AP[Q0D!s-'EYPVG9!t64p00PVP9PYP8P\Q0C#NS0mCrPW!#7I%!sB+&00GS0n/V5S0o!sG710Z5RZ!s@-QP9Q0m:0ASU%CQS0p/:RRUPTPA!s]%1VK5S0q:0@8\!su5PZH06!s=+^Q0=!#5d$S0rPQP!sm$CzPEPE!sY1?!sp/B0>8\Z!s8+IP3Q0A10j5Rj;q7P1PfP3PgPhQ0APiQ0A/RjRjPj%<7S0s%\7S0tQ!#3{0Q0JPlQ0K!~x$J,Rl%<;S0HP4CDPnQ!#3T&PoPpQ0P10q9S0u,RoRn#J%Zn%<<S0v%\<S0w!~x2P!~g&Q0W;56%<QS0x!s|$tP!~J/vPwQ0_/07S0y,RwRu%<AS0zPuQ0z%\AS0{!}F+PyPzG>P!|`~P3P4Q!|T%A;KA}S0|P~%GAS0}!|C5Q0jQ0kP7Q0k#7Rz10~;S0~+0l!|KzE!tM-10!#<1$4a#7S1010c4;q6P1PCP3%SaPIP320E5n%CmRy/:RS11!uK&8}S12Pq%G8S13%NBRv52q!uO1PnQ0v10q4S14%?mRuC^Q0P%FmRt&0dCS15Po!sJ$!s,&EYPa!}?$!sl1!u:3o!u:2000P1g00<\S16$0<S17P3&0b<S18!{@%K/09S19=ql<P1Q!#3=$kS1:Q19,Rl+0!{W-Pw%?pS1;!yb$8S1<,RwRnPnQ0H%\;S1=%[kS1>!{`/1Tz9S1?Pz10~<S1@,Rz%<VS1AP4CDfARn%KnS1B;g5S1C%F|S1D!#<I&nS1E#7RsfCRjQ1E%8nRi/06S1F,RsRZ#J%ZZQ0x%\QS1G!{~2fDRZ#4S1H#7R\/T9S1IP\%8ZS1J/0AS1K,R\%<aS1L!#;n$jS1M%KjRY;B5S1N%FZS1O!#;s4|S1P%FjS1Q!#;s;S1R%4jS1S#7S1TQ1T%8jS1U/0;S1V'RRS%<^S1WPSQ1W%\^S1XQ1R!#;R'|S1Y!t;$xQ1PQ!#;J>S1ZQ1Q$0^S1[!}f~!}f&fFRS#CS1\!{M$]!{M&^}S1^%8SS1_Q1_%G^S1`;2!}x2%4SS1!|P$bQ1_/0VS1c'RRG%<kS1dQ1bPkPAP4Q1_PQEU%?SS1eC^Q1aP7P;P5Q1bPGQ1dCX!~N7u!~Ne!s:-1!#:w$!~b3!sJ3]00!#KJ0!#KV3B000S20!s]$5!s-33!s-%21054010F!s1$41055110E10D!sE$q!sE&E!sE+4!#K{$!sB-!s4+s!s4,2104!t0&!sMC5010K10N10V!s:%!th-00!#L{$!sT,!sb2110v10?10@!t+%60!s71210471!sY$!s=3!sp0G!s4,W!s4&7!v>07!uw+7!sP%!sE+410O10=6!s=5=!sm0=5!sH3!s7II10T!sj+4010H!sH+3!t-,A6789S1f'3g017a$0PRG%46%4;31S1g]0P<&05KR[&05MS1hPQP4Q04PUCAPTPAA6;<6S04CWP3P>P5P5PV!yZ$>00!t6%U!}Y$P00X23S1iPVP91EM400DOS1j:0]JJPWCbPTPQA6A;<S1kP5EM1@Q<S1l!}v$FP5P4PT!s~?mP^P81EM9!s~%n!s~$Q0=!t#$VA6QA;S1oP4FHA1FTAS1pP3PDP5P9Q!#;=$Q0120jKBd:0cKBS019;K6S1qPq%G6S1r1EM7!t&%s-0;J,VJS1t!#;]4uQ0PPt%SmS1uEP!u$=PaP71EM8!sy%v!t}&?CbS1wPTP^A6VQAS1xP9EIQ1w/=VPmP6Q1tQ11P^DcPkP<1EM600DORO!t`&%CkRM/:RS1tA1FTaS1w1@paS1y%49S1zQ1E51G[[X7DS1{A1FT^1@k^Q0U,oGW:W8S0UPaP5GeW0P5O1b1!s+/W0W9W3P4P5O2Q!xw%PJPJPPQ0pCsPU!w1$AQ04CWQ!xV%PJPJQ1jQ06Cs!xR'Q!xM%Q1lPFQ!w}%!sM%nP_Cs!wx+Q!ws%Q!wn51qPqQ1rQ1s>0_Jy,VJRW!wN;Q!wKE!tK%vPbCs!wF$RPPTP^Q!w@%1=P!w>$PW!w=-B0_JOM,VJ!wT${Q!vRCX3[!vS%&05L!vT$U!tC$0pQ05Cs!vU5Q0!td%06PLP4D]!|x$!vW7Q0=!wH$_PLP9D]!vX;!sJ$yPLP7D]Ry!vc11#NR_!v]^Q0?#NRt!t1$bPLP8D]CARb!vb0b!vb%_Py!va'Q1t#N!sZ$MPLP6D]!vfSNS0UP?P3Q0AQ0B'|PaP8PtQ0;PTP^!#_J~!#_J2Q1o'3Q1010c9S0;'|P?!s$$3P5PpP<%CpRc!}H${#NQ08Q0a':00=XQ0:+04PTPkE`Rt!t~~!t~2A6a^VS08'3Q0PQ0^51GS1q]0P5A6ma^S1p,3t!#7q'r!#6q>lPrP;1QrRS1k20FJ4Q0Y!uS/!zM$pA6kmaS06!zz%y!zz%nPA%CnRt/:RRL20FJ91EN<S07!sf4rA6pkmS1i!#7a&kS04!{?'20FJ71ENAS05!s`/!{K&019;KVQ1UQ1U%GVS0p%CjR_!wU$h#NRb32!#X12jS1vQ1SQ1Q%SjS1s!{e@|PQQ0g20FJ81EN;S1n!u51RuPTPnA6rpkS1j!{r%urPjPVPbPyPnDcPZP^%CZ!#N=%|#N20FJ61ENQS1}!ss/A1FT|fERX/@|Q1zfGRb#4S1~!#7u'20A1FTn1@ZnQ1a!#7u&21P|!|a=Xc@P5O1Q1p#pP3p-0P5g00>TS22g00?1!uq:RuX23S23Q06;h5Q22Q0^!#9P$S24/n5b1W0S25XA=!t+%6A6nrpS26#pQ23A6|nrS27!sa&1S%4XS28!sd$9!sd+:XR?XQ?RUW5!#n@$O3ROPOg00GES2;P!s>/UPUA6j|nS2<#pRUPuX>3A6Zj|S2=!t4&28Q!vJ$S2>/n5Ru!ut$2?XA=XU=XKI!#oN&O4Q23Q!s]'Pub1X0US!sO%G@XT!sR1!v>$0!}^$1!}^oB10<P4O1b2W0W9X4[X3[!ud'g09k=&05`P1P!#lF%PHPoP8Q0uQ14!#ko$!s;/,|oQ14,|o!sA%!sP-!#l4GPk!#l2+PMQ0<CsQ1t!#kw3m!#kw+aPEPp!#ku+PcQ0>CsQ1{!#kj4Q0yQ1<PTDlQ0\Q1>5B5!#keKA6^VQS0\'!uz'lP7Q0JQ19!uz/!s;%,|lQ19,|l!sA%!sP-!uzIH!st$!w7%5Pn!v0-tP`P7D]RtPL!v24rCzRH!v4%Q0[PE!v2,Q0fP`P6D]Q0g!s]1,L|R]P4PAQ0~Q1@!v9$1B%[nS0f5B536!v<JQ06'3Q24]0P5Q1i,3H!#7z'|!#7z>BP]PTPnQ1j!#HR$nkS0!#7Z%IP@!#?1%_P`P<D]Q1h!u33jPTP|Q26!#7S&rS0>!#?l'IP@!#BM$%CXR_P`PAD]R]!#ra$<!sp1R_%8XS2@%?XS2AQ28%FXS2BPXJ0:!u5=!t0$8!#@|%`P;D]RyQ1|!ts3ZRHPTPjQ27!#79$H|1LX_/=j!sf$6!wg$1\P`PQD]R_Q1]!sg3SA1FTZ1@bZQ1zfIRH#4S1\51G[S2C[X7DA1FTj1@SjfHRc#4S2D,oGW:S2EW8PZP5Dy!#779@IP5O1!yJ'dPE!z'&4P!yw54P;10i<S0dQ1F!#u8$rS2F:0[5r!|T:Q1p'3Q0[&0PIRt!t5$0!{;&EPZ!t8&!vQ5P4PVQ1J/0QS0[Q1K!t;%j9B5Y!t7<j'3Q1EQ1S51GS2G!zF&#pQ23Q1j!#7=&G!#8?'H!tL&]Q!xz3,LXP4P^Q2@/0VS2I!s/$QS2J!tU$KZS2K%[ZS2L5B5Q2<!#Q?+%KSS2M%[S5B9R]!yMB9P!xX8P9PaQ1_/0^S2NQ1c!tB%XS2O%[X5B4R_Q2=!|9%_|!#Qb,7Pk%8cS2P/0mS2QQ2P/0aPTDlR_!z~G%CbRyP`PVD]1:yRS2R!th3bP8Pm%8bS2S/0aS2TQ2S/0^!t1$yP]A6XZjS2U!}?&yZ!}<0!{J$%CH!t2$a!t2'V!}:2y%8HR]%?HS2WQ1\%FHS2X%SHS2Y!#AM?!~F-cRMP`P^D]1:MRS2Z!u<3cRMP_%KbS2[%[bS2\5B8A6SXZR_!}R%MS1LHy/=bfJRy!t$$<!t$%yRJP`PmD]1:JRS2!x$2'LP;PnfKRJ#8S2^/0rS2_Q2^/0pPTDl=1Fc%KJS2`%[J5B;/@cQ1zfMR`#4S2a!#B3&P<Pr%8yS2b/0pS2cQ2b/0k!sg&b%KyS2d%[yS2e5B</@bfLRM#4S2f!#B]%Pc!~I>?tX@I!#L>$!|Q%:!|Q&110;10:P4O1b?W!#:,%8!#`K&;01!s@$=W0W9X6[X4[WM!#@M,0EQ0U!#ii-Q1;PwQ0_P4Q0CC~RtPtQ0DQ0GQ!#i`0Q1?PzPzP~P7Q0MC~RtQ!#~{$Q1CQ!#iL&PsPjQ1EPsPiP8Q0RC~RU#J%ZUQ0SQ!#~63Q1IP\Q1JP<Q0YC~RUQ0Z5v\Ru/{4Q1NQ!#hq-Q1RQ1T!s%$UP6Q0aC~ROQ0b3vRWPOQ0bQ0cQ1RP4J02Q1ZQ!#g\~!#rD'!#gP$Q0hQ1_Q1_Q0i!#gE3Q1eQ1aP7%SS!#r1xQ1p'!#wU%V%?r!#v'$P9!#{I$OPO%i6!$$@$6P7P7P7!$$@7%[p!xZ1T/T91{W4Q1YQ1P;B5Q1Q!xQ&zPZQ0k%Jt%ZtQ0N!t'%;P<P<P<!t'8!xd328#7S1Y/T9S1P!t/$YQ2@P;Q07C~%iVS0h!#nt$ZS0cQ2K;B5S0TQ2B!#no2PYQ1O!$']<tPuPUQ0Z!tp%QPAPAPA!tp9t!yN&M!t#$xPY!#nZ?Q1OGx!ysfh!}>$!}B%5!z%B2V!#nS%a}S1MP]%GaS0S=2]!z-32WQ1\P7Q2Y!z-eRY!z09j'3Q!#=J%26,3Y!u2&!u8@1QJRS0G!u<&k}S2gQ2^Q2^%GkS2h!|G4%?JS2i%4JS2jP7%SJ!uEeQ2<'3Q1HQ1a51G]0!tm$!tw6MRS2k!tw&p}S2l%8MS2mQ2m%GpS2n!tz6MS2oQ2fP7%SM!twQ/3_!tT&!tZ'5!tZ,fNR_/QRS2p!t]&n}S2q%8_S2rQ2r%GnS2s!t]6_S2t%4_S2uP<%S_!t`QA6cbSS2v'3Q1\Q2j51GS2w]0P9!tg-ORY!tg$x!tg&|}S2y%8YS2zQ2z%G|S2{!tg6YS2|%4YS2}P;%S!za>A6JyHS2~'3!tC&!tI'5fQRt/QRS30!tI&Z}%8tS31Q31?}Z!tA4tS32%4tS33PQ%StP5P7!tA;`MJS34'3Q2ufPRU#4S35!y@%9fRRu!tD$6!tD&X}S37%8uS38Q38%GXS39!ug6uS3:%4uS3;PVPuJ0:P5P6A6UY_!#ox,;!#Ad:>3S3<fSRW!tI$=!tI&S}S3>%8WS3?Q3?%GSS3@;29!tI3WS3A%4WS3BP^PWJ0:P4P<A6tUYS3C!#Ej$<Y!#Ej,8!tT?DfTRO!tT$E!tT&b}S3F%8OS3GQ3G%GbS3H;28!tT3OS3I%4OS3JPaPOJ0:P9P;A6utUS3K!#EU%9t!#EU&fVS3L!t5$M!t5&H}S3NQ3L#8S3OQ3O%GHS3P;26!t71Q3L#?S3QQ3L#4S3RPkQ3LJ0:S3S!uM=fURP!t;$T!t;&c}S3U%8PS3VQ3V%GcS3W;27!uJ3PS3X%4PS3YPmPP!t4$ZP8PAA6WutS3[P9EIQ3Z/=WQ3S/=OfWS3S!t7$Z!t7&y}S3\Q3S#8S3]Q3]%GyS3^;2<!uL3S#?S3_Q3S#4S3`PpQ3SJ0:A1F<P1@aPQ1zfZS3a#4S3b!#En&A1F6O1@^OfYS3c#4S3d!#EH&P!#EH>FX2?!#EH%!|,%6!|,$1!#<>$P5O1W0XC>X;d!sL9610>!sL&A=X;e!sL<<!sL&;fP5O1Q2H!#FC1600!#FC,4[X3[X]IWL!$P^+O5!#FH&Q0lP3Q1uQ0uQ0C5Oo+07Q1tQ0KQ0JQ095OlS0JQ0DQ19PkCfQ0IQ0OP5Pl!sF$D!s-'EYPm!$=`8Q0\'3Q1:Q0J+07Q0l$0<S0J!tI%!tN%P5PLPiQ0dQ0a5OsS0dQ0NQ1F%?nS1:C^Q1E%FnS0DP5Ps!sM$N!s-'EYPrG9S0N!tI9!#ZE,0l!s{$i'3Q1BQ0gP~Q0~Q0Y5OzS0~Q0bQ1@408!$8a$Q1DP4FuPz!sJ$b!s-'EY!#Z['Q0y!~[-F^HF^?FP0P:PFP4P5P7P5P9O2-0N4!#KG0010Z10hXHFX?Fp?100010^S0bP120L@@S0~PFP?Q0~$0<S1BPCP?P2P?P@PCP?20L?@S0NPI!s8$IQ00PKP@PQ!#CM&;!#7:&b10a!sH%1-0MKR:g00<<Q0F!#CJ&x00030010!yk$106S24P@PIP:Q0F20i45!wO$!sS4n1010kS0O!sS+!s%$d!sN3k!sS$S!s?&w!t<3PvP?Q0iQ1JPvH0a!}p1!uS$vP5CmS0iQ2I#tQ16Q0NP9P?Q0NP5!sG$9!sG%FQ2Q#tS0IQ2c#tR:P!s$$Q2_!s3%!tM$_!#rN4j!wO$`!s1D!#gn/9!#gn0Q2T!t@,!s$,!tA$300!xc$!s#4!tn&0IQ0I!#i[,!#t;2;10_!#i[P!tk2P?PCP4Q2T1ENVS0I+0KS2_P1P@PCQ1~#7R:Q2TQ0I#N+0I+0H20tv5S1uQ2_!|[2X00!s^'\#7S2_10]kS0u1ENaS0C!sg'!#3O'+0K!sh5S0CQ!s%'!st%%4yS0C#7S0uQ2c1ENmS3e!ss/2cQ3e!ss93eQ3e!v]$9!v]'y!#m:`J!v]1!#6x%w!#6x&910YP4!#;U'!|s$[10\g020<-045P@Q0~P@P@P5P5Cm+03bbS3e!#Nb&IQ053OS2I#J+0J!w@%5O:S0I#J-0J:S2TQ!s%,D#7!s7'Q1EN^3O!s]$RNPN!yJ>!ukU!yJ32!u7$FP5PIPFQ0I#ZRN,:4-0ZB1:5N%imS2Q$0h':Q0:+0Z+0gPTQ0IQ2Q$0Y+0X00NT!~'1!#:a/0!tG$dQ0[Q1n5O\RNQ0h!s`-!xW1600Q0h:0R\NS0[O2!#?s81X23Q1hQ1U!#X0%AQ07C~S07Q0ZQ1V408Q!#yo&P9FuQ1TQ!sB&!s/&EYS0Z!#jz'Q0Z=1Fr!$/A'0<Q2@Q2I%i^Q2J408Q2AQ28Q2BP7FuS2I!#`=<Q1|Q1JQ0hQ1K608N%?ZS1KQ1HQ1OP8FuS2JP\PNQ0hQ0[CD!#jV'Q2J/=|Q2I/=jQ1]Q1_Q1bQ2NQ1}3OS2N%iaRNQ1c!uQ$eQ1a%FSS1cP6Fu!#3a$2Q!s-'EY=1FZQ!#jZ$!sl%PN!s-'!sC$jQ!#jYBW!#yc$25!#?Q18!#?Q/!#^n$L!#^n,16Q0UPmP9PoP8Q14Q0mQ11FdPTPaQ0\!#I;,k!vb=S0EPkP8PlP7Q19Q09#NS09Q1t!sn$mQ08!#H]$mVS2E!#p\$pP7PwP6Q1<Q0R#NS0RQ1{!sU$kQ1p!xR$1w!xN'PL!$$^+<S01Pi%G<RNPsP;Q1FQ0a#NS0aCrS2N52i!#]72:Q1EQ0D%SnS2C!#f8?rP6Q0VP<Q0W/07S2QQ0M#NS0MQ1kFdS0IPTPpQ06!xn$0I/=kPnP<Q2NPLPpDcP|P;PzPAQ1@Q0Y#NS0YCrQ0gQ0>1@jrQ1zQ28!$$@'0>A1FTp1@|pQ1H!$$@'NPr!$1{?4[X3[W5!x12n$05!x40o!x41Q!wh2n/V4!wf3Q!wb7n/V9!w`GPi!wT+n/V7CrS0o92iN!wS:Q!wPK2Q!sw$8!wHA0o!wH6n/V6!wF'Q!vvBJ!vv8!vp-10q5S0n!vtAK/04S0K!vwH_/09S0o!vzP10i7S0ICrS1}!v{kW/08S2I!v~$Rq!v}-1=q!v{%1}!v{410~6S1}!v|J!#3}$!v}30UP^P9!$9w$Q0m40AQ0=CA!$<q%!#4#,a!#4#>=PaP8Q10Q0;Q09!sk$?!sk$^Q1x!#3|$^AS09!wG%mP7Q0QQ0R60AoQ11!sP$aQ0\!#}G&VS0R!$Ag+{!wG&Q0_!s%$`Q0a60AwS0a72!wD4;Q0^Q0]%SpS0`!wG@kP6Q0LQ0M60AlQ1tCA!w@$!yF$!w@%aPpP<Q0aQ1{PmDcPrP;Q0VQ0XQ0Y40AQ1kQ04Q0yQ1z!#yZ$!#3Z%yA1FTm1@rmQ0k!$Ek'YPk!#3ZD!w_&3!{^&Q14Q0q60@8!vF/!{Z+Q191VK460@7!u7$!{U:Q1<1VK960@6Q1{!sM$!{PAQ1F1VK760@;S0q!{Kb2Q1VK860@<Q1k!w'&!{E40q!{E,Q1@1VK660@A!{@IJ[!#3?BQ0nH06!vb8!#3>+!sH$!vd=!#3;'o!sO$!vfG!#74'IH06!vhe!#35&2I!tP$!vkH!#7/&1}H06!#3/^2$00$05RqQ1{,LpS02!uu&CWQ1lQ1k,LrS1l!t^'!$A_,1LnLPTPrQ!$A6$Q!$A1+!#Ed&!#EK%Q!$@9@Q0g,L|S1Q!$2;&9EIQ1Q/=rQ1h,Lj/=nQ1|,LZQ20Q!$>s$!#\u;!uW$X`qXWqWS!#[80UQ0r!$G7$0=Q0?,La!#4w,Q!#4s%Q11,Lm!#4f,Q!#4a/Q0_!#49'Q!#46@Q1t,Lk!#4%3Q02/=mQ1lQ0yQ!#3B$!uC;!#3B2A6894!$-c%f!$@0&g!$-c%RqPqQ2;!|&3?!|&D?!|&K?!|&U?Rl!|%n?!|%%o!|%0o!|%$Pl!|$9?!|$^!vk%!vg%60>!#7P;Q0K60>!#7OBQ0o60>!#7NLQ0I60>;!v_d!vZ$60><!v[I!vW%60>A!vX]g0:i6S2;!$8v$_/05RL=qw7!$+g11RwLRLPLQ0sQ0t!$+_6A5z~8RLQ!$ws$!$+Y5A5si9Rw#JS1E%ZwS1CQ0vQ!$wo3!$+Y&=5\6RwQ!$wl$!$+R&S1N!$+U6;57RlQ0zPlQ0zQ0{!$m_+!$+O~!$+O7|!$+O&}!$+O;Q1bQ1_;5;Ro$0s!$we~!tJ&1!$+j%!$+`$/04;q6PI!s$$3P5!xX-zQ0jP!xT$HQ1=Q0f!xT1!$'I+;5<S1PQ1A3vRL/{4Q!$'<&gPhP\PSQ1H%Jw%ZwQ0xQ!$tB31T:9P:Q2S=5:AQ!$t$$Q2M=gS5%FbS2M!$+,2Q2OQ1c!$+-<w!vq$W7voRqPoQ1WQ1XPwP4J02%aXRw!$sO%2O!$'sAc!$'sfRo!$'gGQ1^P]Q1`!$'_>_@01]V!y8~!y80!$'r+!y%-s!#4o%!}d'Q2FPTL0WQ1NPgPhQ1TPXQ1S%Jl%Z!}4&!~/4b/T91{q4Q2O=Bw!w-$!xO4KQ2B!xO>PL!z=$A%\VS1P!xJ&Q0c!xH'K!xHA2B!xHg!xFC!#xA&V}S2ZQ2PQ2PQ0p!#~i5cS0cQ2DP7Q2TQ2P<01Q!$8Azi'3Po!$3FO!$10'm}S2K!$10&mS1c!u@4Q2iQ2jP7Q2j#7RoQ2^<01a!uAeRw!uC827'3Q29!$3T$<,3w!$3TH`RS2<!}%$2l%8`RwQ2n=2w!w\4`S2OQ2aP7Q2a#7RL@01wk!$3RfU'3Q1aQ2D!$3R=Q!$1o'r}S2DQ!$1l%rS1a!w=6tQ2uP7Q2u#7RqQ2r<01p!txQQ2v'3!$3U<1QUR!vQ%y%8US2yQ2yQ!$1^7UQ35P<Q35#7S2{Q2y<01n!$3MRyHcS1b'3Q2jQ2a51GS0{!$3M0Q!$1{'j}S1SQ31Q31%GjS1T!v>532Q33P;Q33#7S1NQ31<01!%>d=Q34!$3D4Q!$0T$Q37Q3?!s%$9!t86AQ3BPQQ3B#7S3BQ3?<01Z!$3@>Y_`S3A'3Q35Q3;!y$%9Q!$0:$Q3>Q3G!s%$@!t:6IQ3JPVQ3J#7S39Q3G;5XJ0QP5P6Q3KCWQ3<Q!$-_$Q3FQ3V!s%$H!$2N3Q3XQ3YP^Q3Y#7Q3V;5SJ0QP4P<Q3[!$2L%tPFQ3DQ!$0j$Q3UQ3O!s%$W!$1n3Q3QQ3RPaQ3R#7Q3O;5bJ0Q!$1q$OWuS3O!$1q&W!$1q'XS3R#CP!yx%3\Q3R#8RlQ3^=2l!$1d3R#?Q3R#4S3^PkQ3^#7@01lHK09S3^!$1h<Q!$0P$Q3NQ3]!s%$P!$1V3Q3_Q3`PmQ3`#7S3\Q3];5cJ0QRl!$1[$POW!#HK$lPQ3^Q3L'=Q3c/QRS3^!zM&J}S3QQ3c#8Rl%GJS3M=2l!$1S3c#?S3DQ3dPpQ3d#7S3[?5lyJ0QQ3S91F<Q3S,@aQ1zf\S3V#4S3Y!#]b&Q3L91F6Q3L,@^f[S3X#4!#]g%Q3S!$1]~!$1][:!$1]<Q2H!w{$;01!%2t%4O1b@!#Ue'EIXDIWF!#Ue/!#Ke$10i4=qs!%>v%Q2C!s;%~9Rs,RzRi-0E5!%AE%Q12P~Q13=2~v!wQ1PiQ0v10~4Q0jC^!$/e$Q15Pz!s?$!s,&EYPn!%>aXQ1i'3Aqzs<!#H//CP3%SZS1iPIP3!#Gi&6Rs!u%%<!ya&<}Q2@Q2@?2N!u+3sQ0xQ2@/07Q2AC^!#wx$Q15Q1Y!sB%!s-&EYPZ!u0Z!#<L,!w$&1s!t}%J=5\7!t{&1|!t{&6}Q1J!s%$r;2!t}6zQ1J/08Q1KC^!#y:$Q15P\!sA$!s,&EYPj!t{IQ26'3Q1iQ0l!tj$!tn$P5!tm$2S=5:;!tm&2R!#NE&2SQ2SQ0}!tk71WQ2S/0<PbCfQ1~Q2MQ15P:!s@$!s,&EYPS!tj5Rs!tl9='3Q2>!#@#$U,3s!#C^$;5A-0E4!xx,Q2!#P4$1^Q2bQ2bQ1`!tm4Q0uQ2b;5VRsQ1dQ2b/0Q%?yS2]C^Q0C%FyS!t}$Q0uP!sH$!s-&EYPHG9!to$!xF2v'3Q2w!tk%!#KA$2ZP]Q0p=2]!tK32_?5]QRN%<mS0pP]PAH0O!#KW$Q2XQ15FuQ2_PNQ0p!s-'EYPcA6bSXS1!#{k-y!#X:=sQ2vP5H0r1@HS!$9Q+Q0bP1Q!$8b%!$8\2Q!$8W4a!$8W7Q24Q0OQ!$72@SQ2m!$725Q0i10wmRs!$7'3Q0FQ2y/0rS0F#tRNQ38/0|Rz#tRiP!s$$Q3?/0j!s6%!$7-~Q2z/0pRi#tR~P!s$2!$73A!sL%!$0e@!$71i20KiBRN!$6H%2}#7R~20Iiv!$5D$PN!$6t<NQ31/0nRN00I!sU&20KNB!sX5RNP!s$%!s`%3;#7RN20Iz!s],z!s]7zPz!$6L~!$6L/0!$6L<Q3e1RLsS3e#J-0JL1R~iRi!s2$~RsP!s$$Q2{Q2{Q0F'R!$5k$sPs!$5k~!$5k0%ZiR@!$5i+@%<jR@!$5h2&0Y@-0Xi!$5dI2f#7RBQ2m;5aS0:%<rRs!$5k@:>0RBsS0F!$5k?!#Qn$Q1M!#Qi$Q0S!#6Z42^=5o^Rz%<pS0SQ2^PVH0O!#Q}$%FJS2jQ15FuPoPzQ0S!s,&EYRzPyA6HcbS1M!#FL%zc!#n$'!#Pk&gPwQ2h=2w!tD33e%<nRzPwPa!t<$OQ2a%F`S3e!t<$S2<!#nX=!$\N$Q2KQ2mQ2mQ1c!uM50:PsQ2mP^!t,$oQ2f%FMS1c!t,&KPB!sI%0FCDPJQ1b!$6u$K/=yQ2</=J!#Q4%Q2l!#Q/$Q2n!v[6r=5qkS2n%<|S!sP$Pm!t?$tQ2u%F_Rv!v[%~PiP@!s+%EY=1FM1@YMQ1zQ33!$ov'qQ2nQ2l!s-'!sN$J1@_JQ35!$Q8&M!#FY<Q1\!#pj$2v!$xO&w!$xO'n!#E6%0!#E61CC!#Es$?!#Es1>!#Es-:!sc:!#jZ&!#Ev'!%zQ,O6g0;LhQ2;P1Q17P3Q!%[Y%1J/09RC=q\!%[X&Q1i1R\C!%[S/Q1YQ2A!#DD&8RCPC!#eW%2L!#eW/2T/T9!$Ak&P/0<S2P'RS2LQ!%[L$Q2[=gb5%Fc!#e`%:PHQ1~Q2S/06RC,R:R\#J%Z\!#el7Q0u/T9Q0u!#?h&ARi!#es%%KH=gH5Q!#ep4%KcS2MQ2X!%Ze<2bQ2_!#??$;S2_Q1WQ!s+%1XQ2b!%d[&!#`V%M!#`V<=gc5Q2X!#`W~!#Z%&k!#C+'!}%%!%Z&4Q2m=5BVR]Q1dPB!%Yo%2mPQEUQ2oC^Q2f!%Yl$PBP]!%Yk~!%YkWQ26'3&0b;Q17$0<!zt%!zy%!#G{$Aq:CQ!%cK'b007\!zn-2TQ0cQ2LQ!z8$Q1PQ2\!%c10o9Po!#6k$QR\Q0p!z\%d=gy5Q2j!z\%Q0uPMQ0C%JiS0C%ZiS2jQ1L%\aS2d!#mH3L9PLA5Lw^RwQ0S!zS%M=gM5Q3eG>S3e!#gw2`!#mH?C!w^&!s'$%\kS2^PC!zJ2`!zJ?J!#mEj!zJCx!#9S%Q2z!s%$h!zJ6z=5~mRCPzP~Pn!zI%zPaEUQ2|C^Q2}!zI&~PCPz!zH~!zHBR:!zJ9!#MS,17Q2U,3:!#MV%qV!#SL-!zL&y007iS2P!zO,PoQ2iP\P\Q0p%\mQ2e!zL1q9!#:Z$aR\=vqsS2r/{4%a`S2e%K`S0p;B5Pv!zT%PLPYQ2a%JwS2a%ZwS2iQ0S%\pS2!%#{32{/T9!#C#%2y;5kRwQ2l!zZ%Y=gY5%FUG>S2y!#622_Ro%FYS2U!z_=iAv~CzS2>PCPz%\nS2=Pi!#u$%_S2|!zc%Po!#o^AU!za~!za'!$oO$Q2qQ38Q38Q!$sn5Q38=5NrRi%<ZR:PNPZP^P4Q38PpEUQ3:C^Q3;!zd&NPiP:!zd~!zdB!#S6-!z2&Q2YQ2_!#=J00uQ2]Q0CQ2jQ1LQ2d%[H!#uo$3e!y^$BP_Q2f%J]%Z]Q1dQ2^!#5&3~9Q2>/{4Q2|?Bo!wt$!#un20p%kv!y:;oQ2rP\Ps%\rS2rPo!y5$Q2e!y2%Q0p!y3@Pv!y2~!#k|0Q2D!#kw$Q!#o461NQ31;5pRvP@Q1NPjPVP4Q31PkEUQ32C^Q33!%o%&NPvP@!y3~!y32Q1\'3Q2PQ!$l33!xx+PL!#IG$Q2iQ0SQ2T%[M!xw%2y!sF$~PtQ2}%JC%ZCPzQ2=!xv4N9AvNi:RN/{4%atRz%KtRC;B5%FuR~!#BQ4URL%FtRo!#3D<]Q1N?vv@RBPvP@%\jP]!#3B%UR]!y5%PL!y4Ao!y4~!y4+!#o\$1S!#o\%!#r&7!#oO$|R@%<SRvQ39PSPmP4Q3GPnEUQ3IC^Q3J!y7&39P@Pv!y7yRv!y99b'3Q0{!$q/&2~,3v!xg$qQ2tP\P\PsQ2r%[`!$/s0N/T91{B4AB]L5Po!#AJ%2{PuQ35!$/c%2l%\|!yE2Q3B/T9Q3B!s%$?;5n%<X!#9j$u=gu5%FW!yH3PC%k~!yA;n!#6o$%\ZPn!y:$!y5&C!y5==Bz5P~!%4G~!yD9Z!#uz'!#r/$!#uz6!#qz$XR1%<HRhQ3\PHPrP4Q3]PZEUQ3_C^Q3`P7PVP5Q3\P1Ph!yDeRh!yF7A6_`MRE'3Q2}!#RZ$R1!y<$3A,3h!$$JFQ!#sl$Q3UPlQ3W=2l!uf4[?5lbRh%<JR{Q3[PJP|P4PlPSEUQ3DC^Q3dP7PaP5Q3[PhP{!uceQ3C'3Q3;Q3J!$$^>3a/QR!#w$'a#8R{Q3P=2{!u94b#7Rh?5{cRl%<MR~PhPMPjP4P{PbEUQ3aCfQ3bP7PmP5PhPlP~!u;QQ3O!$$y>Q3V!tx+QQ3V#8R~Q3M!&5X53Y#7Rl?5~yRh%<_R{PlP_PXP4P~PHEUQ3VCfQ3YP<PpP5Pl!w5UQ3L?6PO'3Q3`Q3d!v}%!%5b-]R{!tz&A;KM}%8{RhA}hM!&+X3{Rl#7R~?5hJRz%<YRCP~PYPSP4PhPyEUP{CfPlP;PrP5P~PzPC!tx=Q3cQ3RQ3S36!%5z5_R2!ta,_}%82RCA}C_!ta42Rz!ta%C`Rr%<tRlP~PtPcP4PCPMEUP2CfPzPQP|!ta$rPlCX!$%}6!ta%XQ3aQ3c36'3Q3Yf^Rl#4!vN&f`Rr!$#D&A;KY}%8rR~A}~Y!tb4rR|#7RQ?5~_Rz%<uRCPQPuPH!xA$`EUPrCfP|PVPjK09P5PQ!vH&6Q3V96l{CWQ3<faRC!t>-U}%8CRzA}zU!%6#24CRQ#7Rj?5zYRV%<WR|PjPWPyP9PzP_EUPCCfPQP^PZK09P4PjPVP|CXP<A62l{!$&z%{!#p@08fcR{#4!u@$V%8{Rj=5VtRZ%<PRQ40RRz!#de:0X>3fbRy!u3-t}%8y!vK$t!%6^24yRH!}`%~UR0%<ORnPhPOPJP8P~PYEUPyCfPHPaPXK09P9PhP0PnCXRnP;A6r2l!#dh%n2!$+6'dRn!tJ-W}%8nRlA}lW6!tJ3nR;#7R0?5luQ3L#<P0Q3LP`P6PlPtEUPnCfP;PkPbK09Rb!ue=%C{!t>+u}PjA}ju!$+C1PZPQPVPPPMP7PjPU!|;&|PmPSK09RS1{8zPAA6Cr2!$+K$SC1=byfeRb!uD-O}%8bR}A}}O<!uD3bRK#7Rx?5}WRWQ3S#<RRPxQ3SP_P<P}PuEUPbCfPKPpPcK09P<ffRc#4#7Rp%8c=5pOQ3R#<CX=1F{1@a{Q1zfh!{h$!#e6$6PxPWPR!sG$y1@^yfg!$+c'P{!$+b~!$+bZ3!$X<$?hE5Q221n15b1!%Vr3!$+v&VW0WI!s]$1M!$Xs%b!%r`&{!#g/%!sa'1!$we0IW0Q!#gI'!$,Y1!$xI&?!sb:=!#g/5W5!&cI-P5O7g0;MTRIQ0UQ0!#hu%08!tl&1q!tl&R1WNRE!$SV4PEXa!t,$5!%r=,g0;N@!sx$P1W9!s]+<!s]0!tg%<!s]2kQ03!$a'%EQ2:WBXX[!u:,<I!u58OWQ2HXBE!sO2!sM/6P1XBE!sD+!tC0PDQ25!sb/R6W5!sb-5g0;Q1P!s;6a!s;6RNR6Q25!t<,^6WP!sJ2S<P1!tx,O!$gh-o!y6&x!y6'@Q0P51!%fn&!u8,!sX%3!y0$B010S21!xt$5!s-331!&;]+1!&>u5S!sE0!&>u,1!&<\,!s41C!s404!t02!sM;51!&>u2!s^,0000!sT1!sb5A!&>M-6!s73!&>u+A!&>u~!&>u~!&>uG!#45%Z>W[X7DXY>X_DWGW\o"). Qed.

(* [comment removed for export] *)
Section WithSegs.
Variable segs : ltac2:(zQ "20!hn8!un0@1$0$1").

Definition zf_coversB : ltac2:(zQ "50!se!hge!lc!u0!irb>2bc$4>2rb$0>2rk$1>1n$3>2kb$0>2kk$1>3len$0$2") := ltac2:(zQ "h10!se!ige!u0!hge!lc!i4!rb!hiv5!luc!m3!tu9!hji1!irb!pga!jm4!tra!qoa\2bc$c\2rb$0\2rk$3\1n$2\2kb$0\2kk$3\3len$0@2$8M0\3len$0$4^1\2l0$3M7\1x$7$4@6$b^7^6@1$f^5^4^3@2$e^1@2$h0+2+k0\5delta$3$9$1$1$1\2n0$2$1\2op$5\1a$0\1b$0$1\2op$5\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2sx$4\2lo$2\2n0$2\1e$0$1\2sx$4\1k$2\1i$3\2n0$2$1@7$d^7^6^5@1$a^4^3^2^1").

Definition kentry_overlayB : ltac2:(zQ "60!lc!u0!hge!se!hr8!irb>2bc$5>2rb$3>2rk$2>1n$1>1K$4$0") := ltac2:(zQ "98!mq2!se!hge!ige!lc!hpj9!u0!hr8!irb&\2kk$2@7$5^9^8^7^6^2^1^3&\2kb$1~0&M0\1a$0$4^2~1&\3len$1~2&\1a$0~3&\2kk$2@7$5^a^9^8^7^2^1^4&\2kb$1~5&M0\1a$0$4^3~6\2bc$8\2rb$1\2rk$2\1n$6\1K$7M7\1K$7$4^1\1a$0\1w$6\1v$1$3~4\1a$0\3len$1\1k$6~7\2lo$2\2hi$2$3\1e$1\1m$2$3\1e$1\2lo$2\2hi$2$3\1a$0\2n0$1$3\2a1$0\2n1$1\2a2$0\2n2$1$3\1a$0\3len$1\1c$2~7~4").

Definition kwr_offimageB : ltac2:(zQ "40!se!lc!hge!irb>2bc$3>2kb$0>2kk$2>3len$0$1") := ltac2:(zQ "f0!se!hge!ige!lc!u0!hu2!jse!u6!i4!rb!hpk8!irb!kj6!jm4!qoa\2bc$b\2kb$0\2kk$1\3len$0M7\1x@1$7@2$5$1$1$3@2$c^4^3\1p@2$5$1$1M5\1p@2$5$1$1$3^1\3blo$1\3bhi$1M0\3len$0$3^4\2l0$1@3$a?4segs@2$6^3^6@2$6@2$6^2^6@2$d^1@2$e+2+k0\1n$4$2\2op$8\1a$0\1b$0$2\2op$8\1a$0\1b$0$2\2op$9\1a$0\1b$0$2\2op$9\1a$0\1b$0$2\2sx$3\2lo$4\1n$4\1e$0$2\2sx$3\1k$4\1i$1\1n$4$2$2").
Definition kentry_readableB : ltac2:(zQ "60!lc!u0!hge!se!hr8!irb>2bc$5>2rb$3>2rk$2>1n$1>1K$4$0") := ltac2:(zQ "h01!se!mq2!hge!hpl5!lc!ige!u0!hr8!hiv5!tra!jp8!m3!hji1!hpm9!hpj9!irb&\1a$1\2n0$0@5$3^7^6^5^4^3\2bc$f\2rb$0\2rk$2\1n$6\1K$7M7\1K$7$4^1\1a$1\1w$6\1v$0M1\1a$1$4^3\2kb$0\2kk$2M8\1x$8$4@6$c^9^8@1$9^7^2^1@1$9^4\5delta$2$b$5$5$5~0\1a$1\2n0$0\1k$6@5$3^8^7^6^5^4\2lo$2\2hi$2@5$3^7^6^5^4^3\1e$0\1m$2@5$3^7^6^5^4^3\1e$0\2lo$2\2hi$2@5$3^8^7^6^5^4\1a$1\3len$0M1\1a$1$4^2\2kb$0\2kk$2@2$a@7$e^9^8^7^6^2^1^3@4$d^9^2^1^3\2a1$1\2n1$0\2a2$1\2n2$0@5$3^9^8^7^6^5\1a$1\2n0$0\1c$2@5$3^8^7^6^5^4~0").

Definition kn_readableB : ltac2:(zQ "70!lc!hn8!u0!hge!se!hr8!irb>2bc$6>2kn@1$1$5>2rb$4>2rk$3>1n$2$0") := ltac2:(zQ "b0!hr8!hn8!u0!luc!m3!hge!se!hpnb!hpoc!irb!hpq2\2bc$9\2kn@1$1$0\2rb$6\2rk$5\1n$2@2$3@3$a$0@4$8^5^3^2^1^4@6$7?4segs$4^4^3^2^1").

Definition kn_overlayB : ltac2:(zQ "70!lc!hn8!u0!hge!se!hr8!irb>2bc$6>2kn@1$1$5>2rb$4>2rk$3>1n$2$0") := ltac2:(zQ "b0!hr8!ige!hn8!u0!luc!hge!se!hpnb!hpl5!irb!hpq2\2bc$9\2kn@1$2$0\2rb$6\2rk$5\1n$3@2$4@3$a$0@4$8^5^3^2^1^4@6$7?4segs$1^4^3^2^1").

Definition x_dischargeableB : ltac2:(zQ "80!lc!hu2!ut6!u0!u6!mq2!tt5!irb>2bc$7>2ss$2>3ss'$2>2rb@1$4@2$1@2$1$5$3$0>2sc$6$0") := ltac2:(zQ "i01!se!ige!u0!lc!mq2!jp8!hu2!hge!i4!rb!mr2!ts4!u6!mqa!uv9!tt5!jt5!hpqe!ut6!hr1!js0!hn8!spb!hprc!hr8!hps7!vj9!hhm5!irb!hpt4!hpud!hpv5&\2a1$4\2n1$0\2a2$4\2n2$0$1\2bc$hc\2ss$h2\3ss'$h2\2rb@1$c@2$6@2$6$4$2$3\2sc$f=2kn@1$h5$h8@1$ha^4Mf\2sc$f$3^2\5taken$3\1c$h6\1a$0\1b$0$1\1a$4\1n$0M0\1n$0$3^1\1z$7@2$5@2$5@2$h4+1^1@2$h4^1+8@6$h1?4segs@1$h0^9^4@1$a^3@1$d^3@1$hf^1\2n0$2$1\2op$8\2a0$0\1b$0$1\2op$8\2a0$0\1b$0$1\2op$9\2a0$0\1b$0$1\2op$9\2a0$0\1b$0$1\2sx$3\2lo$2\2n0$2\1e$0$1\2sx$3\1k$2\1i$7\2n0$2$1~0~0\1a$4\1n$2@2$5@2$5@2$bN1^1@2$b^1N8@6$h9?4segs@1$h0^8^3@1$a^2@1$d^2^1\1a$4\1n$2\2sx$3\1e$0M0\1e$0$3^1\1z$7$1\1j$2@2$5@2$5@2$5@2$5@2$5@2$5Mc\2rb@1$c@2$6@2$6$4$2$3$3^8\1p@2$6@2$6$4$2$3M6\1p@2$6@2$6$4$2$3$3^1\2p0@2$6$4$2\3sx'$3M6\2p0@2$6$4$2$3^2\2a'$4\2n'$2@2$5@2$5@2$hb^2^a@2$h3^1^9@2$he^3^8$1@2$h3^1@1$e^a@2$hd^1@1$e^9@2$h7@1$e^a@1$a^5@2$bN1^4@2$b^4N8@6$h1?4segs@1$h0^b^6@1$a^5@1$d^5^4\2op$8\2a0$0\1b$0$1\2op$8\2a0$0\1b$0$1\2op$9\2a0$0\1b$0$1\2op$9\2a0$0\1b$0$1\3sx0$3\2lo$2\2n0$2\2e0$0$1\3sx0$3\1k$2\1i$7\2n0$2$1\1a$0\1b$0$1").

Definition x_filterB : ltac2:(zQ "40!hn8!tt5!ut6!irb>2bc$3>2ss$2>3ss'$2>3scs@1$0$1@1$0$1") := ltac2:(zQ "f0!tt5!hn8!hu2!ut6!lc!u0!ng8!kvd!u6!hpvf!uv9!mq2!hqgf!irb!hjm3\2bc$d\2ss$3\3ss'$3\3scs@1$1$0M1\3scs@1$1$0@1$1$0^1@1$7$0\1s$0\1l@1$1$0=2rb@1$8@2$2@2$2$b$5$4@2$9@1$a^5^3@3$e$0\2sc$0@1$6@5$c^8^7^6^2^1^4").

Definition sym_stepXB : ltac2:(zQ "60!u0!vn5!usc!vnc!ut6!irb>2bc$5>1K$0>1i$1>2ss$4>3scr$2$3") := ltac2:(zQ "h00!vnc!lc!vr0!uv9!usc!ut6!hn8!u0!vn5!vr8!hqi5!tt5!hqie!irb!hlp2!ts4\2bc$d\1K$7\1i$8\2ss$5\3scr$4M0\1x$0$0@5$e^5?4segs^3^2^1\3ss'$5\3scs@1$6$b\4scr'$4M1\0$1$0@2$f@1$3^5@1$3^3@3$9@3$a^7^6^3@4$c^8^5^3^2^1$2$2").


Lemma zf_coversB_eqf : ltac2:(zQ "a0!se!hge!lc!hn8!u0!jf!hr8!hqjc!hpj9!lm2>2fk@1$3$6@3$5>2rb$0>2rk$1>1n$4>2kb$0>2kk$1>3len$0$2@1$8@1$9^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##4&p'0h01bi001bh12b1h22b2h32fkh42k1h52k2h62kbh72kkh83leni013lenh91nh:2n1h;2n2h<2rkh=1xi021xh>2x0h?2x1h@2x2hA2x3hB2x4i031ai045deltai051ei061ii071ki082l0i092loi0:2n0i0;2opi0<2sxp;1p;2p;3p;4p;5p;6p;7g00eTj1OTg02cgj10Tg0;Sij1Aj2Nj3Cj4?j5<j6:j7JTg0;U<j1=j2Ej3@j4>j5;j6Mj7KTg03kkj1Lj74Tg01mbj19Tg01D[j12Tg01E@j17!s/$^j2DTg01jZj2BTg05Slj65Tg05b:j16!se$Ej23Tg008]j38Tg0097j2FTg03jZj1GTg045mj1HTg003Vj6ITg002Tj51Tg017a#Og00`TR0g00b@R1g00aaR2g00;\R3^80R4^71R5^60R6]9R7]<f0R8#0#A%=8P1P7f1R7#0/N81E78P2P6f2R6#0?C78A@678P0P5f3R5#0P6P7P8C?P5!s0&>P1P4f4R4#0!s:'D<P4!s2+;P0P3f5R9#0!s<,E:P9!s4-MP3^;0^51^20^:0^41^10R:f6R;#LP0P3P7g05U:R<P3f7R=P;%9!sf$g01VB#2R>#7%2>#2!s$&7'D,B8R>E5g00<<R?g00>4R@P@P@n011020004101040!s#$P@!s$/!sI$10008101!s'%:3010;103100!s1D4010<10910:105!s4&710610:RAP8P;P9%64RB!uw%O6'3P=P;P9P!s8&F4,3A583X0:!ut$8P<P3!s\$9!vS%>E5P?P!uF~!uFL!u,$4%6!x9&F4'3,F3%0;R@#G%H;EIP@!xZ/FJ!sX%!s6+K583eXB0D1XA1D1X@0D1X?2D1X>1D1X=0D1W3o"). Qed.
#[local] Hint Rewrite zf_coversB_eqf : bceq.
Lemma kentry_overlayB_eqf : ltac2:(zQ "a0!hr8!lc!hn8!u0!jf!hge!se!hqk8!hpl5!lm2>2fk@1$2$0@3$4>2rb$6>2rk$5>1n$3>1K$0$1@1$8@1$9^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##4]p'0h01nh12rkh21Ki001Kh31bh42fkh52kbi012kbh62kki022kkh73leni033lenh82rbh91xh:2x0h;2x1h<2x2i041ai052a1i062a2i071ci081ei092hii0:1ki0;2loi0<1mi0=2n0i0>2n1i0?2n2i0@1vi0A1wp;1p;2p;3p;4p;7p;6p;5g00eTj1CTg02cgj10Tg0;VLj19j2Bj3:j45j5=Tg0;Wdj14j2;j38j46j5>Tg0;U<j17j71Tg008]j33Tg0097j2ATg0;Sij1@Tg0;Y9j1?Tg003Vj6<Tg002Tj52Tg017aR0#Cg00`TR1g00b@R2g00aaR3g00;\R4^20R5]0R6]1f0R7#0#9%47P2P6f1R6#0/B71;67P3P5f2R5#0?:67A8567P0P4f3R8#0P5P6P7C5P8!s0&6P4^71^62^51^03^12^81R9f4R:#!s^$P6g00>4R;g01U4R<P4P6P:f8R=f7R>f6R?P6P7P5O6n01104000120101102R@P<P4P5f5RAf9RBP=P>!sT$8!sT8CP;!s$+CP@!sH$0000:3010410A10@2!s1%3!s9&310:2010;1092010810<3!s-%!s9'410=4010510>10610?!sb,7!su'!u`%P;!t~$6P!tx%!uP&F1!uP>:P!uL-!sP8!uL~!uLC534X39!uR$7!uR+!uP%A!uR>A!uR%!u|0!uR9?!uR-?PA!uR~!uR4,A4%0:RA#@%?:E<PA!{9'D=P:!s2+>534eX<0D2X;3D2X:2D2X91D2W4o"). Qed.
#[local] Hint Rewrite kentry_overlayB_eqf : bceq.
Lemma kwr_offimageB_eqf : ltac2:(zQ "90!se!lc!hn8!jf!hge!hr8!hql9!hpm9!lm2>2fk@1$2$5@3$3>2kb$0>2kk$4>3len$0$1@1$7@1$8^1@2$6?4segs^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##2'p'0h01ei001eh12fkh22kkh33leni013lenh41oh51xi021xh62x0h72x1i031ai041bi053bhii063bloi071ii081ki092l0i0:2loi0;1ni0<2opi0=1pi0>2sxp;1p;2p;3p;4p;6p;5g00eTj1ITg02cgj12Tg0;ZPj1=j2Hj3>j4DTg0;[fj29j3?j4<j5ETg01:AR0j2;Tg00hSR1j1:Tg028nj18j24Tg01FXj20Tg01D[j11Tg01E@j17!s/$^j2GTg01jZj2FTg0;]9j35Tg008]j36Tg0097j2@Tg027^j1ATg02i6j1BTg003Vj6CTg002Tj53Tg017a#Ig00`TR2g00b@R3g00;\R4^32R5]2f0R6#2#=p,4segsR7/96P3P5f1R5#2/H6A?756P2P4f2R8#2?>56P7P8P5P6C<1;33R9#:^02R:f3R;#8P1P9P4P6P;O1P0P3P3!s4$2P4f4R<f6R=,08105=g01VB#1R=#7%1=#1!s$&7'G,F6R='0557g00>4R>P!s$-n011010008101091010;3010<103104!s1D4010>10:10;100!s4&810710;n200110=000120106105R?P>n101102000210!sF$!u\%14<;P!sF8564X4:!sL';8!v$1P;f5R0!u~%0/0=557P!u[~!u[E!u97,@4%2;R>#A%B;ECP>!xc&DP7P;!s2%DE564eX72D3X63D3X52D3W1o"). Qed.
#[local] Hint Rewrite kwr_offimageB_eqf : bceq.
Lemma kentry_readableB_eqf : ltac2:(zQ "a0!hr8!lc!hn8!u0!jf!hge!se!hqm8!hpoc!lm2>2fk@1$2$0@3$4>2rb$6>2rk$5>1n$3>1K$0$1@1$8@1$9^1@2$7?4segs^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##<[p'0h01bh11nh22rbh32rkh41Ki001Kh52fkh62kbi012kbh72kki022kkh83leni033lenh91xi041xh:2x0h;2x1h<2x2i051ai062a1i072a2i081ci095deltai0:1ei0;2hii0<1ki0=2loi0>1mi0?2n0i0@2n1i0A2n2i0B1vi0C1wp;1p;2p;3p;4p;5p;6p;7g00eTj1PTg02cgj10Tg0;^Jj1@j2Oj3Fj4>j5KTg0;_cj2<j3Mj4?j5=j6LTg0;U<j1;j7:Tg01mbj16Tg05Slj68Tg0;VLj57j1GTg0;ZPj4Nj1CTg00Yhj21Tg0;Wdj53j1ETg0;[fj59j2ATg008]j32Tg0097j2BTg0;a9j1DTg003Vj65Tg0;bSj1HTg0;Sij1ITg0;Y9j1JTg002Tj54Tg017aR0#Pg00`TR1g00b@R2g00aaR3g00;\R4^40R5]1R6]3R7f0R8#0#@p,4segsR9/<8P2P6f1R6#0/O8AM968P3P5f2R5#0?F68P9P5P6P8C?P0P4f3R:#0!s8&>P9P:!s2%D=P4^81^72^61R;^13^32^21R<f4R=#;P0P4P6g01U4R>P4P5g05U:R?P4f9R@f8RAf7RB#6P6P8%6:RCE8g00<<RDg00>4REPEPEn011040004101090!s#$!s;$5000120101102RF%0Bf6RGf5RHP=P:D7RI%0APBPGPHP=D7RJPIPIPJP>P4P6P=P!sB%6P8P5O6%0@RK!s3%CNRL'1!t15PK!sY&HD7PJPI!sH$0000:3010510C10B2!s1%?!s9&?10<2010=10;2010:10>3!s-%!s9'51034010610@10710A!sb,8!su'!vi%PF!uE'P:D3RIP!uU,3!uU2@!uU/F:RKP9P@!s4%D9!uT8!sX'HD3R@!uV~!uV8RM524X0<P7^21R7%E=!uh+5!uh'O4R<P:!uh'O4RNP<P<PN!uh%11KL!uL6!xU'HO4PNP<!uJ~!uJ4=24MX07P;1A9!uE,IP!zF3!z@%3,1K!w\8!wP~!u+=!}r%8!tr$5P?P4PAPB%6!yf%CE8PDP!}TO!x1'P5D3REPI!sc$I!ux&!{''!zi&P9PA!zg@JPI!tG&!v1~!v1/,B4%0=RE#C%D=E5%GE%H=E5%IE%J=E5PE!#5g'KP9!u]%P6P8EL524eX<0D4X;3D4X:2D4X91D4W5o"). Qed.
#[local] Hint Rewrite kentry_readableB_eqf : bceq.
Lemma kn_readableB_eqf : ltac2:(zQ "a0!hn8!hr8!lc!u0!jf!hge!se!hpqe!hqna!lm2>2fk@1$0$1@3$4>2kn@1$0$1>2rb$6>2rk$5>1n$3$2@1$8@1$9^1@2$7?4segs^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##,8h01nh12rbh22rkh31Kh41bh52fkh61xh72x0h82x1h92x2p;1p;2p;3p;4p;5p;6g00eTj1FTg02cgj10Tg0;coj1<j2Ej3=j4:j5@Tg0;eDj27j3Dj4;j59j6ATg0;_cj28j56Tg0;fVj32Tg0;g2j64Tg01mEj23Tg008]j35Tg0097j2CTg0;^Jj1BTg0;hGj1>Tg003Vj6?Tg002Tj51Tg017aR0#FR1P1g00`TR2g00b@R3g00aaR4g00;\R5]0R6]2R7]1f0R8#0#<p,4segsR9/78P2P7f1R7#0/E8AD978P3P6f2R6#0?=78P9P6P7P8C;P4P5f3R:#0!s8&:P9P:!s2%D9P5^30^04^23^12R;f4R<,89P8!sI%O3=20<P9g00<<R=P<!s=%E4R>'3P9f5!s6%D6=20</3>555X4;P9P<!t/&6=20:P9P=!tA'E4'3,C5%0<R=#B%><E?!sC,D@!sa$!sQ'A555eX94D1X83D1X72D1X61D1W5o"). Qed.
#[local] Hint Rewrite kn_readableB_eqf : bceq.
Lemma kn_overlayB_eqf : ltac2:(zQ "a0!hn8!hr8!lc!u0!jf!hge!se!hps7!hqob!lm2>2fk@1$0$1@3$4>2kn@1$0$1>2rb$6>2rk$5>1n$3$2@1$8@1$9^1@2$7?4segs^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##,3h01nh12rbh22rkh31Kh41bh52fkh61xh72x0h82x1h92x2p;1p;2p;3p;4p;5p;6g00eTj1FTg02cgj10Tg0;idj1<j2Ej3=j4:j5@Tg0;k8j27j3Dj4;j59j6ATg0;Wdj18j46Tg0;fVj32Tg0;g2j64Tg01mEj23Tg008]j35Tg0097j2CTg0;VLj1BTg0;bSj1>Tg003Vj6?Tg002Tj51Tg017aR0#FR1P1g00`TR2g00b@R3g00aaR4g00;\R5]0R6]2R7]1f0R8#0#<p,4segsR9/78P2P7f1R7#0/E8AD978P3P6f2R6#0?=78P9P6P7P8C;P4P5f3R:#0!s8&:P9P:!s2%D9P5^30^04^23^12R;f4R<#8P8!sH%O3=20<P9g00>4R=P<!s=%E4R>'3f5!s4%C6=20</3>555X4;P<!t6&6=20:P9P=!t<'E4'3,C5%0<R=#B%><E?!sC,D@P9!t-'P8EA555eX94D1X83D1X72D1X61D1W5o"). Qed.
#[local] Hint Rewrite kn_overlayB_eqf : bceq.

Lemma x_dischargeableB_eq : ltac2:(zQ "d0!lc!hu2!ut6!u0!u6!jf!im3!vj9!mq2!tt5!hqpb!hqgf!lm2>2ss$2>3ss'$2>2rb@1$4@2$1@2$1$8$3$0>2sc$9@3$5$0@5$b@1$c@1$6@1$7^4^4^3^2^1@5$a?4segs^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##>lp'0h01lh12rbi002rbh22sci012sch32ssh43ss'i021ai032a'i042a0i052a1i062a2i071bi081ci091ei0:2e0i0;1ii0<1ji0=1ki0>2loi0?1ni0@2n'i0A2n0i0B2n1i0C2n2i0D2opi0E1pi0F2p0i0G2sxi0H3sx'i0I3sx0i0J5takeni0K1zp;2p;1p;6p;3p;5g01:AR0j2ATg00hSR1j1NTg00eTj1GTg07FHj14Tg01Vgj12Tg01E@j1BTg01T9j2@Tg01D[j19Tg00Yhj20Tg043Tj1:Tg044aj17Tg05_6j1CTg0;eDj65Tg00g4j11Tg01nBj26Tg0;k8j6<Tg08;_j2MTg00]nj2;!s/$Wj2LTg07T5j18Tg0;lIj2>!s/$ij2?Tg008]j3=Tg0097j2FTg02cgj1ETg04@Wj1HTg04Aej1ITg003Vj6DTg0;n8j5JTg0;oQj5KTf2R2f1R3'0f0R4'0p=3g07Y=R5g01U4R6g00aaR7'AR8g00;\R9'AR:#Ng06?kR;g017a#GR<f3R=#4#2R>P;P9P3g00>4R?g00`TR@P9P4g01VBRA#B/@4%9A#9#9#B,@4'0RAp,4segsRBP=f7RC#4RD%:2RE%72RF%C4RGE5'0P?!s$/n0110?00081010K1010A3010D104107!s1D4010G10>10A109!s4&=10;10AP?P?g00h4#1RH/64%1H#1!s$,RI,64'0RJPBP2f6RK#4RL%:3RM%73RNP4E<'0P!ul$P?P1P:P9PCP0P8P9!s:$0P6P7P9P3f9R7,M3f8R6,;41L2C33n200110F00012010310@!s:&E!s:'F10HR0P?n101100000210!sF$%87R8,;4'0%86RO,>4f4RP#:RQ,?83316H=RH16=IRI33R8PBf5RR%47R7PQ%7PRPP=!w13!w/$9!w/0<!w/SI!w/':!s4&!w/+!t+$100!sN%J10810210720!s-$?4010510B10610C!s41!sJ/210?!x1$9!s<&7!zG%P?!wO&B%2DPDPEPFPGE5,!xS%!ye~!ye2PB%2LRDPLPMP!y8$,0J!y9+B%27P7PQP!wE$,08!wF~!wF~!wF15=9X0<!wL$4!wL,PDPL!wK~!wKD4RRR#2PR!wM7!}`%KP!|h81;4O%8C,>4331?OQ;3HPB%46R6#2P6!x&'73I!x&~!x&~!x&1,F9%E>R?#H%I>EDP?P=P2P3P4DJPB!s2+K5=9eW2W1X45W3o"). Qed.
Lemma x_filterB_eq : ltac2:(zQ "90!hn8!tt5!ut6!jf!im3!vj9!hqqd!hqie!lm2>2ss$2>3ss'$2>3scs@1$0$1@3$3@1$0$1@4$7@1$8@1$4@1$5^3^3^2^1@4$6?4segs^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##-kp'0h02sch11bh21li001lh34resth43scsi013scsh52ssh63ss'h71xi021sp;1p;2p;5p;3p;4p;6g00eTR0j1BTg00f4j1ATg07FHj16Tg01Vgj14Tg02cgj19Tg07T5j18Tg0<0gj27Tg0;n8j5;Tg04QLj10Tg06ERj31Tg0;oQj52Tg008]j33Tg0097j25!t:$Tj3:Tg0<2;j4@Tg003Vj6<Tg071`j5=Tg0<3Wj4>Tg0<4ij4?Tg07Y=R1g06?kR2#BR3P0P2!s&$3f0R4%A2R5f6R6#6#4#9P6f5R7%86f3R8'7R9P4D;#0X02f2R:512n10110100020020102100!su%P4P5p,4segsR0P6P7P9P4D2!sd$=12:!sa8533P41535P3P0f7R5P6%85f1R99:2:R7'7R;P4D2R<#0R=X02R>A:294R?512R@P0f8RAP5%8AA:28:'7R8!tC/79334X23153@%65!uY$5P6P;P4D;R@!sM$R7=12?P2P7P>g00;\R>P<%04P0PAP5P8P9D2#053>X1>15>=P@!si'C@E<X72P?D=E<X33X02P9P4O!vD&0!ua&1!ua%%6:!tN$:P9P4C>P0!s0&?533eW4X61W5o"). Qed.
Lemma cap_rd_know : ltac2:(zQ "80!vj9!hn8!u0!jf!vn5!hqi5!hr8!ut6>1K$2>1i$4>2ss$7@3$3@1$1$6@1$0@3$5^3^2^1@1$0^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##20p'0h01Ki001Kh11bi011bh21ih31oi021oh42rdi032rdh52ssi041ni051xp;1p;3p;2p;6g00eTj1HTg01D[j1GTg01gjj1ATg07ZOj1?Tg0;KAj1FTg0<68j1CTg07hSj3BTg07i6j3@Tg07]@j12Tg07^Mj25Tg0<7Dj24Tg07\5j18!sS$cj1>Tg07T5j1=Tg00O[j1:Tg07jnj37Tg07J:j19Tg07FHj10Tg00g4j11Tg07l;j16Tg08G\j6;Tg008]j33Tg0097j2<Tg00hSR0j1DTg0<8Sj3ETg00aaR1g08J=g07Y=R2P1g017a#HR3P1P2f0R4f1R5P0g01VB#G#A#?R6#FR7P2f3R8#CR9g00;\R:P2g01TVg00?M5B69@64R6P8P:P2%28R;/54f2R<'4P8%88%>4R=%=8R>#:57;%98%08R;%1>%68E;n010!s#$20000!s41P<n101105000210103!sH$1!sH'10104#0%0533P<%04R>,<3P9%D7P0P!s&%2P4P:P2P6f5R0!tq%0R9/54%18'4P0%80%=0R?#:979=%90%00%1?%60!tjAf4R?!tl5#0%0?533P4P6P:!s$$2P4f7R6!tI%6R9/5<%10'4P6%86%><%=6R0#:579%96%06R9%10%66!tMA#0=339P4f6R6#0,<3%26/55%1?'4!tG-8R2%82%22%>8%=2R8#:37%92%02R:%18%62!t63!t$$:P41<39R9P9!w7$1!sD'b1!s63X47P4O11<3;!v-%2!v-'100b3X01P4O!s\%4!w}&1104AE<54!t:$>eW5W2W0o"). Qed.
Lemma sym_stepXB_eq : ltac2:(zQ "b0!u0!jf!vn5!im3!vj9!usc!vnc!ut6!hqr8!hqs4!lm2>1K$0>1i$2>2ss$7>3scr$5@3$1$6@5$9@1$a@1$3@1$4^2^4^3^2^1@5$8?4segs^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##23p'0h01si001sh11Kh21ih31lh43scri013scrh54scr'i02!s-$h63scsi033scsh72ssi042ssh83ss'i05!s,%61xp;4p;1p;2p;3p;6p;5g0;J2j4<Tg07T5j11Tg01nBj23Tg0<8Sj34Tg07FHj18Tg01Vgj17Tg02cgj15Tg0<3Wj49Tg08E@j30Tg0<4ij46Tg008]j32Tg00eTj1=Tg0097j2:Tg0<9`j3BTg003Vj6;Tg08B=j5ATg0<;5j4@Tg0<<Jj5?Tg0<=]j5>Tg00aag08J=g07Y=R0g07WmR1g08JiR2p,4segsR3f2R4f1R5f0R6C<R7P2P2P6g00;\R8P2f5R9#1%14R:'3R;f7R<f6R=;44R>%89#7#5P9P4P5C9;06g08L9R?n010!s#$20000P?n0110600023010510310200!t9$3f3R@!sg$<P8P2P;P3!sw&6=0>6P!ssK522X02P!u6%!u:$P8P2%1=/3:R7f8R>?4<4R<%8=!u'$=!u'+P!t~P!s}$P7P3!sh&6=0<!ttPP6g06?k#=R<P<P3P>!sm%R=P8P2f9R7#1%1@'3R9f;f:R;;4@RA?065!t348P2P9P3P7P@P4C6=0A!sJ4522X3!vw$%1>/3:A4;74?0=!u$4,:2%8>!v8$!t_%9AB>45E;X51W6X80P4P5P6O31:2!uS%0!uS'4!uS$100b0%85#7#5R?P3!sV%DA!s0'C@E;P?P@!s>&?P3!s2+>522eW4W7W2W1o"). Qed.
Lemma sym_stepX_know : ltac2:(zQ "c0!hn8!jf!vj9!usc!ut6!u0!vn5!vr8!hr8!tt5!vnc!hqr8>1K$5>1i$6>2ss$4>3scr$3>3ss'$4>3scs@1$0$9>4scr'$3>0@3$1$a@5$b?4segs^7^6^5^4@3$7^3^2^1@3$1@1$0$8@1$2^4@1$2^6").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##<Kp'0h01Hh12H0h21Eh31eh43ss'i003ss'h51Ki011Kh62_Hh73_H0h81bi021bh91ih:1li031lh;2rbh<1si041sh=2sch>3scri053scrh?4scr'i06!s-$h@4scr1hA3scsi073scshB4scs1hC2ssi082sshD3ss1i091ni0:2rdi0;1xp;1p;5p;3p;4p;2p;6p;8g00eTR0j1>Tg0<=]j5\Tg08E@j31Tg0;J2j47Tg0097j2WTg07T5j16Tg01nBj29Tg0<8Sj33Tg0<4ij45Tg07FHj12Tg008]j30Tg00l0j68Tg00f4j1[Tg0<0gj2XTg01:Aj2;Tg00hSR1j1VTg0;oQj5UTg04QLj1TTg06ERj3OTg01D[j1NTg01gjj1LTg07ZOj1GTg0;KAj1FTg0<68j1E!s8$dj2DTg07hSj3HTg07i6j3ITg07]@j1CTg07^Mj2JTg0<7Dj2KTg07\5j1B!sS$cj1ATg00O[j1MTg07jnj3@Tg07J:j1PTg00g4j1QTg07l;j1?Tg08G\j6RTg0<>mj8STg0<@Cj3ZTg003Vj6Y!vm$Qj6:!s/$mj2=Tg08JiR2f1R3f0R430p=4P2g08L9R5f2R6g00?MR7P3P4E:p=<g00aaR8g08J=g07Y=R9g07WmR:g06?kR;#>R<p,4segsR=f6R>f5R?f4R@f3RAD\A1634RB'4P=P>P?P@C7P21W24P=f7RCP>P?C7/44P2P=f9RDf8REPC!s9'2P3g00;\RFP2f<RG#6%66'9f>RHf=RI;36P=PGP6P3C5;14P5n010!s#$20000!s6$10;00023010010710600A1C>?RJ'4g017a#>RK%2Ef:RL#230RM]0]2P3P=PHPIPGC7/4BPFP2%6H%6A'9f@RBf?RN;3A!sJ$AP6C5;13!tM3f;RO=1GL'4%6N%6@'9PF!s$$2P4fCRPfBRQ;3>P=fARR!v$$5;1@RS!sn3A1NHIRT'4%2B%2Q50KRU]0P4A3QR?P=PB!vv$5;1AA1HIGRA'4P2P:!s&$4P4P?!u|$4!u|'8!u|$500X32PSPTP4E8A0:@IP2P<!s&$4P3P0P;P<PC%[;fER0#6/XDg01U4/;8/;F#VP=fGRIPGP3P4DU#TX=;=O;Lb;n101107!u3%20104103!tP=fDR;?3PCP=PQPCP>C5RS;1?A1BNHP3E8A0<SNP2P9!s&$4P6P8P9fFR8PDP1g01VB#N#L#GR1#FP9%E8PFP9g01TVRSP71D1Sd5H19I14POPFP9%CORF/J4fHR1'KPO%BO%A4%6ORS#M5@F%PO%2O%QS%?OER!wO1!yt2L!ua%!yu$1010:!sH$1!sK$20010109!uo=A30;ER;P=PPPEPCC5;1>A1RBNP6E8A09;RA380D=09QP9A3I8LP=P8POPLC5=0<PA0:LP%26%21R;50K[[X49P=P0PLPD!sI$QA0:DQPK%2GA0K4;X:KP=P1PIP8PGPOPLPDGSfIRD?31G#2AZD1GEYW7W6PPP4E:W0P4O1b1!s+/W0A025AP2p-0P4g00>TRAg00?1!u`=RP?<T4PA1=U4b1W!vC%2!vC$100P3O1b8W0W2X@:XB<XD9P6P3P4O3P=PE!y&$7=025A1>?@9025A<PJ!su$M!su$W2!tI-1!tI-P4P6O2b2b<W0X?:WAX49W>WCW9W5o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sym_stepXBI : ltac2:(zQ "70!u0!vn5!usc!vnc!ut6!irb!hkk4>2bc$5>2kx$6>1K$0>1i$1>2ss$4>3scr$2$3") := ltac2:(zQ "h10!vnc!lc!vr0!uv9!usc!ut6!hn8!u0!vn5!vr8!hqi5!tt5!hqie!irb!hkk4!hqt3!ts4\2bc$d\2kx$e\1K$7\1i$8\2ss$5\3scr$4M0\1x$0$0@6$f^6^5?4segs^3^2^1\3ss'$5\3scs@1$6$b\4scr'$4M1\0$1$0@2$h0@1$3^5@1$3^3@3$9@3$a^7^6^3@4$c^9^5^3^2^1$2$2").
Lemma sym_stepXBI_eq : ltac2:(zQ "c0!vj9!u0!jf!vn5!im3!usc!vnc!ut6!hqr8!hqu1!hlmc!lm2>1K$1>1i$3>2ss$7>3scr$5@3$2$6@6$9@1$b@1$4@1$0^2@1$a@1$0^2^4^3^2^1@5$8?4segs^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##,Yp'0h01Kh11ih21sh33scrh42ssi004scr'i013scsi023ss'i031xp;1p;5p;2p;3p;4p;6g07FHj12Tg01Vgj10Tg02cgj13Tg08B=j5<Tg07T5j14Tg01nBj29Tg0<8Sj38Tg0<3Wj45Tg08E@j36Tg0<=]j57Tg008]j31Tg0<AWj4;Tg076Fj1:Tg08@jj6@Tg0<Bmj5?Tg003Vj6>Tg0<DCj6=Tg00aag08J=g07Y=g07Wmg08JiR0f1R1#2R2#0#3R3p,4segsR4f2R5P1f0R6D<R7P0P0P6g00;\R8P0f5R9#4%45R:'9f7f6R;;85%29#0#3P9P5P1C5;66g08L9R<n010!s#$20000P<n01103000230102101!sF$P4f4R=f3R>P5P1D7510X20P!s4$P6C;!tS$7P8P0%4=/9:A8;95%2=!tC$=!tC+P!t>M!t&'D7R<510eP3%:2R2P4!s=%E@P3!s2'D?E>P3P2!sY'E==10<eW3W4W1W0o"). Qed.
Fixpoint sym_execTXBI_go (bc : bctx) (kx : kix) (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepXBI bc kx K i ss scr_nil with
          | SOk ss' [] _ => sym_execTXBI_go bc kx t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.
Definition sym_execTXBI : ltac2:(zQ "80!u0!ut6!lc!hn8!hge!hqv1!irb!hkk4>2bc$6>2kx$7>1t$5>1K$0>4fuel$0>5first$2>5stops@1$3$4>2ss$1$1") := ltac2:(zQ "a0!u0!hqv8!lc!hn8!hge!hqv1!ut6!hqve!irb!hkk4\2bc$8\2kx$9\1t$5\1K$0\4fuel$0\5first$2\5stops@1$3$4\2ss$6@9$7^8^7^6^5^4^3^2@1$1^1@1$1^1").
Lemma sym_execTXBI_go_eq : ltac2:(zQ "d0!ut6!u0!vj9!lc!hn8!jf!hge!im3!hqv1!hrh2!hqve!hlmc!lm2>1t$8>1K$1>4fuel$1>5first$3>5stops@1$4$6>2ss$0>2ck$0@3$5$0@9$a@1$c@1$7@1$2^2@1$b@1$2^2^7^6^5^4^3^2^1@8$9?4segs^7^6^5^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##ECp'0h01Eh12ckh25firsth31si001sh42ssi012ssh55stopsh64fuelh73scsi023scsh82IHh91Kh:1bi031bh;1fh<1ii041ih=1li051lh>1oi061oh?4scr'h@3ss'i073ss'hA1ti083scri091xp;1p;9p;8p;2p;3p;6p;4p;5g00eTR0j1=Tg07FHj13Tg076Fj11Tg0<EWl9>Tg0<Foj86Tg0097j28Tg04QLj1FTg07\5j1<Tg00N^j1DTg0;fVj3BTg00Yhj2ATg0<HCj10Tg0<IQj2@Tg0<DCj6?Tg00hSR1j1PTg08E@j3:Tg00f4j1OTg0<Jcj8M!tE$Qj6L!sA$Tj3KTg008]j3;Tg0<L:j4GTg003Vj6HTg00g4j1E!s/$Sj4ITg01Vgj1JTg02cgj1CTg0<=]j5NTf0R2#J#Cp=2g07Y=R3f1R4;;2p=5f7R5f6R6f5R7f4R8f3R9g00>4R:f2R;P4P2M9>p=9P9P!s4$g0<MQR<DNp=4g08JiR=?;42p=7g0<N_g00aaR>g00;\R?g00b@R@#=RA%34RB#2RC%1BRBP5P6P8!sz'M9>p,4segsRD!s@1G6'5^13^43]5]2REX6>PDP6P7g00h4!sL,,83X13X43X5AX2?%F9%<4#D=B@;'AP?!s$$3P2P?P3%0!uB$n010!s#$20000R@P1g08J=RFP3f:RG%<9'@RHP=P3%38RI#2%1IPGP2P8P<E?P0g06?kRJP3P4%35RK#2%1Kf>RKf=RLf;RMf8RNP;!t@%;ROP;P6!tB2PG9P?P3f9RQ#0PQPN!sF2Rn1011!s3$20020100105!sx%8RSP8P9!sX2Tn0110900023010710210800P@!sq%!s@$1010400!sa1!v>&@P1PFP3P!uo$PD!ug%C4P0P!u`$PDPKPLPMP:PNP;PPG6P!ts:!tX]'5!wn%POP;P4!sB1,83%<;,@Q%PF!tx$!t|%2!wm%7RP#2%1PPMP2P7P<E?RP!u0'%3NRH#2%1Hf?RHPKf<RUPQ!wf%!t8$5!vi2V!wc%%0GPGPQ!sC2W!w`>7RXP7P8!sX2Y!v-;T!v-5!uL/PD!uD%C4R1!wL-HPKPUP:!u8$VG6P!t_:!tDO!w>$=P1!tD$2!vV,QRT#2%1Tf@RTPHPLPG!vT-!zq3Y!vT'MPMPG!vTN6P6P7!wI3!u4;!v6%UP4P6C4R6!v6-!tp%:!tr$Y!v6=!t$;'5X3!uy$18=21762P=!{Y$9PNC4/7!wX%!{t+%3URU#2%1UfCRUfBR6PTPL!v<-M!uG2O!v<'KPKPL!sC21!ty9R!u{?!}O/UP6PTP:!tO$OG6P!svR'5]0P4%=JRRg07Wm!sx$NPLC4A:;42'7!t9$DfER1PGPHC4A:82;!s=&!v'$TRO#2%1OfGROfFRVfDRWfARYP7!v/$XP7PH!uj2X!v/'6P6!zk$!sC/Z!u79!uh,OPVPWP:PYP7PXG6R0P!sY9!uQ$;PDPWPQPKC4%OJRQ=:94'7g017a#=RZPI%22%12!s{&!sy%9/50X=ZP6P:PTP8!u=$SP8PK!tx1O4%3HP!v5$P<P8!}K$2GMELW0PDfHPLP6C4AKJ42=:57'!v,$%0UPU!#8`2,83W0X7RX3JP4P2O2!uE%5!ux22O1W0W?W7X@3!#;G$O3PD!xg$5C4g08L95;=!t4%NPN!#512!t4$!xt$0!xt'1!yl+2O1b0b3P!#6C'CGEHX<FP2O1183!#7d%600021110400b>!sr$3!t,&1b:PCPBPNP5%E7R7!#=z,PDPNP5P7!#=s-e!#=M-X8EX;>P2CIX6>W9WAo"). Qed.
Lemma sym_execTXBI_eq : ltac2:(zQ "e0!hn8!u0!jf!hr8!ut6!lc!hge!im3!hqv1!vj9!hri2!hrif!hlmc!lm2>3kn0@1$0$3>1t$8>1K$1>4fuel$1>5first$5>5stops@1$0$6>2ss$4>0@3$2@1$0$3@1$9^1^7@3$2$4@8$b@1$d@1$7^8@1$c^8^7^6^5^4^3^2@7$a?4segs^7^6^5^4^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"; "WithSegs"] "##/Kp'0h01Hh13kn0h21Kh35firsth44fuelh51lh67s_know0h76s_log0h87s_next0h95s_pc0h:7s_regs0h;!s0$sv0h<2ssh=5stopsh>1ti001si016!sv%i025!sv$i036!sv%i044s_pci056!sv%i06!s0$svp;1p;3p;8p;7p;6p;2p;9g00eTj13Tg07FHj10Tg008]j31Tg01Vgj14Tg02cgj19Tg076Fj17Tg0<Ojj86Tg0<Q?j75Tg0<RPj12Tg00hSj1=Tg08G\j6<Tg0097j2;Tg0<EWl9:Tg0<Foj8?Tg0<SZj7>!sJ$Qj68Tg017a#3R0g0<N_g00aaR1g00;\g00b@R2#3g07Y=R3f0R4#0R5f6R6510P0f1R7#0R8%44#9R9%74R:f7R;P6f5R<f4R=f3R>f2R?G6p,4segsR@P;P6P<P=P>P?F5513X10P3%24#0=105P7g00`T#3g08Hn#3g01U4#=!sX'P7P4E<#0,;0W;X81X60W7W:X92!sH/O6n01100000160104105102101103106%27!t<$8P0%2?R2#0P9P:f8R:!tl'%2>R9P9M9:P@P!s<+P9P9G?513X50!u>-2P2F>%0?P4E8b0%48#9%78!u],P7G6P@!s6/!uo$eP;P4E8W0W<W=W3X41W2W>W1o"). Qed.

End WithSegs.

(* [comment removed for export] *)
Definition kcutB (bc : bctx) (mk : saddr -> expr -> kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  (* [comment removed for export] *)
  let low :=
    if (if lin_ge0B bc [(kb, kk)] [(wb, wk)] then false   (* [comment removed for export] *)
        else if lin_ge0B bc [(wb, wk)] [(kb, kk)] then lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
  let high :=
    if (if lin_ge0B bc [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]            (* [comment removed for export] *)
        then if lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(kb, kk)]                    (* [comment removed for export] *)
             then lin_ge0B bc [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]  (* [comment removed for export] *)
             else false
        else false)
    then let we := mkAlu ALU_ADD ws wn in
         let '(hb, ho) := split_lit we in
         let ha := if (lin_ge0B bc [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0B bc [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
                   then SA hb ho else SA we 0%Z in
         [mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.

Definition kzero_cutB : ltac2:(zQ "50!se!hge!hn8!hr8!irb>2bc$4>2wb$0>2wk$1>2wn$0>2kb$0>2kk$1>3len$0@1$2$3") := ltac2:(zQ "50!se!hge!hrk0!hrp6!irb\2bc$4\2wb$0\2wk$1\2wn$0\2kb$0\2kk$1\3len$0@8$3^7$2^6^5^4^3^2^1").

Definition kfill_cutB : ltac2:(zQ "50!se!hge!hn8!hr8!irb>2bc$4>1c$1>2wb$0>2wk$1>2wn$0>2kb$0>2kk$1>3len$0@1$2$3") := ltac2:(zQ "60!se!hge!hrq0!mq2!hrp6!irb\2bc$5\1c$1\2wb$0\2wk$1\2wn$0\2kb$0\2kk$1\3len$0@8$4^8\1a$3\1n$0@3$2^2^1^9^6^5^4^3^2^1").

Definition kunk_cutB : ltac2:(zQ "50!se!hge!hn8!hr8!irb>2bc$4>2wb$0>2wk$1>2wn$0>2kb$0>2kk$1>3len$0@1$2$3") := ltac2:(zQ "50!se!hge!hrq8!hrp6!irb\2bc$4\2wb$0\2wk$1\2wn$0\2kb$0\2kk$1\3len$0@8$3^7$2^6^5^4^3^2^1").

Definition prune_zfB : ltac2:(zQ "b1!hn8!lc!hu2!se!hr8!hrqf!hge!tt5!u0!mq2!irb&@2$2@2$2@1$0$4@1$0$7@1$0$1>2bc$a>2mk>0$9>0$3$4>2wb$3>1k$6>1w$8>1K$4>2kb$3>2kk$6>3len$3>5apart>0$5$1>5hints@1$0$1>8diffbase>0$5~0~0") := ltac2:(zQ "h8h2!hn8!hr8!tt5!lc!hu2!jjd!kvd!se!ho7!tu9!hrp6!jse!js0!tra!u0!hge!hrr6!hrqf!i4!rb!t5!hrrb!mq2!irb&@2$4@2$4@1$0$1@1$0$2@1$0$3&\0$3~0&@4$5@1$0$1@1$0$2@3$8$1^a@1$6$1@1$6$2&@4$5@2$4@1$0$1@1$0$2@1$0$3~2^5&@8$a^f^e^d^c@1$9^b^9^8^7&@4$5@1$0$1@1$0$2~4@1$6$2&@4$5@2$4@1$0$1@1$0$2@1$0$3~5^5&M3~1@2$c@2$b^c@1$d^b^8~3~6&\1b$7~7&\1a$7~8&\2op$h2~9&\2op$h3~9&@4$5@1$0$1@1$0$2@3$8$1^b@1$6$1@1$6$2&@4$5@2$4@1$0$1@1$0$2@1$0$3~c^6&@8$a^h0^f^e^d@1$9^c^a^9^8&@4$5@1$0$1@1$0$2~e@1$6$2&@4$5@2$4@1$0$1@1$0$2@1$0$3~f^6&M3~1@2$c@2$b^d@1$d^c^9~d~h0\2bc$h7\2mk>0$h6>0$7$1\2wb$7\1k$f\1w$e\1K$1\2kb$7\2kk$f\3len$7\5apart>0$h1$3\5hints@1$0$3\8diffbase>0$h1~0M3~1@2$h4^6^aM7\3len$7~0^4\2l0$f@4$5@2$4@1$0$1@1$0$2@1$0$3@4$5@1$0$1@1$0$2@6$h5^c^7^6^1^a^9@1$6$2^3\1n$eM3~1@2$c@2$b^a@1$d^9^6@4$5@2$4@1$0$1@1$0$2@1$0$3@4$5@1$0$1@1$0$2@3$8$1^8@1$6$1@1$6$2^3@4$5@2$4@1$0$1@1$0$2@1$0$3@4$5@1$0$1@1$0$2@8$a^d^c^b^a@1$9^9^7^6^5@1$6$2^3~a~a~b~b\2sx$3\2lo$e\1n$e\1e$7~h1\2sx$3\2k0$e\1i$f\1n$e~h1M3~1@1^3$h0@4$5@2$4@1$0$1@1$0$2@1$0$3@4$5@1$0$1@1$0$2@3$8$1^7@1$6$1@1$6$2^2M0\1x@1$0$1~0@8$a^c^b^a^9@1$9^8^6^5^4@1^1$h0\2k0$1\1l@1$0$1@4$5@2$4@1$0$1@1$0$2@1$0$3@4$5@1$0$1@1$0$2@3$8$1^2^1@1$6$2^4").

Definition prune1pB : ltac2:(zQ "a0!hn8!lc!hu2!hr8!u0!se!mq2!tt5!nj2!irb>2bc$9>2sp$8>2wa$6>1w$4>2wv$5>1K$3>5hints@1$0$1@2$2@2$2@1$0$3@1$0$7@1$0$1") := ltac2:(zQ "idi4!hn8!hr8!tt5!lc!hu2!kvd!jjd!se!mq2!ho7!hge!mrb!lu5!uh6!u0!mr2!jse!js0!js7!tra!qoa!tu9!hrqf!qn7!i4!rb!t5!hrs3!jp8!luc!hhr8!hrt1!mqa!hr1!hrt8!uud!hrq0!hrq8!hrk0!hrtf!hru8!nj2!irb!jp1!jm4&@2$4@2$4@1$0$1@1$0$2@1$0$3&@4$6@1$0$1@1$0$2@3$9$1^6@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~1^5&@4$6@1$0$1@1$0$2@1$5$1@1$5$2&\1a$8~0&\0$3~0&@4$6@1$0$1@1$0$2@3$9$1^9@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~6^8&@8$h7^e^d@1$f^c^7@1$h5^b^3^2^4&\0$h6~8&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^9&@4$6@1$0$1@1$0$2@3$9$1^c@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~b^b&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^b&M3~5@2$h1@2$h0^a@1$h3^e^4~c~d&\1b$7~e&\1a$7~f&\2op$h8~h0&\2op$h9~h0&@4$6@1$0$1@1$0$2@3$9$1^d@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~h3^c&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^c&M3~5@2$h1@2$h0^b@1$h3^f^5~h4~h5&@2^5@2$d@1$bZ^4@1$b@2$c^3^4&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^7&M3~5@2$h2@2$c^3^4@2$h4+2+k0~h7~h8&\1p$he~h9&@2^6@2$d@1$bZ^5@1$b@2$c^4^5&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^8&M3~5@2$h2@2$c^4^5@2$h4+2+k0~hb~hc&\1b$7~hd&\1a$7~he&\2op$h8~hf&\2op$h9~hf&@2^7@2$d@1$bZ^6@1$b@2$c^5^6&M3~5@2$h2@2$c^5^6@2$h4+2+k0~i2~a\2bc$ia\2sp$i9\2wa$8\1w$e\2wv$7\1K$1\5hints@1$0$3=1k$a@1$i0^5=8diffbase>2ka$8>2kl$7~0\2ka$8\2kl$7=5apart$3@8$h7^a^9@1$f^8^3@1$h5^7@1$f^2@1$i0^2^1M3\5apart$3~0^1~2M0\5hints@1$0$3~0^5@4$6@2$4@1$0$1@1$0$2@1$0$3~3@1$5$3\1b$3\2hs@1$0$3M3\1b$3~0^2@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^8@1$5$1@3$9$2@4$i7^b@1$h5^a^5^4@1$5$2^1@4$6@2$4@1$0$1@1$0$2@1$0$3~3^1M1\1K$1~0^4\1a$8\2w'$e\1v$7M8~4^3\2kb$7\2kk$aM3~5@2$ha^2@1$f^cM3~5@2$hd@2$h1@2$h0^1@1$h3^4^7@2$h1@2$h0^7@1$h3^b^1~7@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@6$i8^2^1^4^3^7^b@1$5$2^8M3~5@8$h7^e^d@1$f^c^7@1$h5^b^2^1@1$h5^4~7M3~5@2$hc@2$hc@2$i1^bN1@2$i1^4N1@2$ha^a^3~7@2^6@2$d^2^1@1$h5^4\1a$8\3len$7M8~4^2\2kb$7\2kk$a@c$hb^d$i6@1$f^b^6^a^8^2^1^3~9^7\0$h6@2^6@2$d^3^2^4\1a$8\3len$7\2bk$eM8~4^3\2kb$7\2kk$aM3~5@2$ha^2@1$f^cM7\3len$7~0^4\2l0$a=1l$a@2$ic^1@2$h4+2+k0M3~5@2$hd@2$h1@2$h0^3^1^9@2$h1@2$h0^9@1$h3^d^3@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^b@1$5$1@1$5$2^a@4$6@2$4@1$0$1@1$0$2@1$0$3~3^a\1n$eM3~5@2$h1@2$h0^8@1$h3^c^2@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^a@1$5$1@1$5$2^9~a~h1~h1~h2~h2\2sx$3\2lo$e\1n$e\1e$7~h6\2sx$3\2k0$e\1i$a\1n$e~h6@2^6@2$d^2^1^4\2lo$a\2hi$aM7\1x$7~0@1$f^9\1z$aMa\1z$a~0^1=2r1@1$0$1M3\0$3@1$0$1@2$h2^3@2$i2^5^2@3$9$1@2$hf^3@2$i2^5^2@1$5$1@1$5$1=3lo2$a@2$ib^4@2$h0^6@1$h3^a=2r2@1$0$1M3\0$3@1$0$1@2$h2^1^4@3$9$1@2$hf^1^4@1$5$1@1$5$1@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$i3$1^3^1@1$5$2^9~ha~ha\1n$eM3~5@2$h2@2$c^2^3@2$h4+2+k0@2^4@2$d@1$bZ^3@1$b@2$c^2^3@4$6@2$4@1$0$1@1$0$2@1$0$3~3^6~i0~i0~i1~i1\2sx$3\3lo0$e\1n$e\1e$7~i3\2sx$3\2k0$e\1i$a\1n$e~i3\1e$7\1m$a~2\1e$7\2lo$a\2hi$a@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^7@1$5$1@1$5$2^6\1a$8\1n$7~2\2a1$8\2n1$7\2a2$8\2n2$7@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^8@1$5$1@1$5$2^7\1a$8\3len$7\1c$aM8~4^3\2kb$7\2kk$a@c$hb^e\1a$8\1n$7@3$i4^2^1^5@1$f^c^7^b^9^2^1^4\0$h6@8$h7^f^e@1$f^d^8@1$h5^c^3^2^5^8\0$h6@2^7@2$d^3^2^5\1a$8\3len$7M8~4^2\2kb$7\2kk$a@c$hb^d$i5@1$f^b^6^a^8^2^1^3~9^7\0$h6@2^6@2$d^3^2^4").

Definition ranges_apart_pcB (bc : bctx) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sidesB bc (sp_D sp) b2 k2 m2 then true
      else lin_apartB bc b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhiB bc n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hiB bc b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hiB bc b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_xB bc (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0B bc [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0B bc [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

Definition prune1pcB : ltac2:(zQ "c0!hn8!hu2!lc!hge!hr8!u0!u6!se!mq2!tt5!nj2!irb>2bc$b>2sp$a>2wa$8>1w$5>2wv$7>1K$4>5hints@1$0$2>3br2@1$6@2$1$3$3@2$1@2$1@1$0$4@1$0$9@1$0$2") := ltac2:(zQ "hce!hn8!hr8!lc!tt5!hu2!jjd!kvd!mq2!se!hge!mr2!ho7!tu9!hrv4!t5!uh6!hsg1!u0!jp8!mqa!hr1!u6!hrtf!nj2!hsh7!hsi6!hsj4!irb&@2$4@2$4@1$0$1@1$0$3@1$0$2&@4$5@1$0$1@1$0$3@1$6$1@1$6$3&\1a$7~0&\0$2~0&@4$5@1$0$1@1$0$3@3$b$1^a@1$6$1@1$6$3&@4$5@2$4@1$0$1@1$0$3@1$0$2~4^9&@9$h0^e^d@1$a^c^6@1$c^b^7^2^1^3&@4$5@1$0$1@1$0$3@3$b$1^9@1$6$1@1$6$3&@4$5@2$4@1$0$1@1$0$3@1$0$2~7^8&\1x@1$0$1~0&@4$5@1$0$1@1$0$3@3$b$1^2^1@1$6$3&@4$5@2$4@1$0$1@1$0$3@1$0$2~a^a&\1l@1$0$1~b&\2k0$1~c\2bc$hb\2sp$h7\2wa$7\1w$h1\2wv$8\1K$1\5hints@1$0$2\3br2@1$h5@2$4$9$9=1k$9@1$h3^6=8diffbase>2ka$7>2kl$8~0\2ka$7\2kl$8=5apart$2@9$h0^b^a@1$a^9^3@1$c^8^4@1$a^2@1$h3^2^1M2\5apart$2~0^1@4$5@2$4@1$0$1@1$0$3@1$0$2@4$5@1$0$1@1$0$3@3$b$1^7@1$6$1@1$6$3^6M0\5hints@1$0$2~0^6@4$5@2$4@1$0$1@1$0$3@1$0$2~1@1$6$2\1b$2\2hs@1$0$2M2\1b$2~0^2@4$5@2$4@1$0$1@1$0$3@1$0$2@4$5@1$0$1@1$0$3@3$b$1^9@1$6$1@3$b$3@4$h6^c@1$c^b^5^4@1$6$3^1@4$5@2$4@1$0$1@1$0$3@1$0$2~1^1M1\1K$1~0^5\1a$7\2w'$h1\1v$8M7~2^3\2kb$8\2kk$9M2~3@2$e^2@1$a^d@7$d^f^e^d^c^b^a^9M2~3@9$h0^f^e@1$a^d^7@1$c^c^8^2^1@1$c^4~5M2~3@2$h2@2$h2@2$h4^cN1@2$h4^4N1@2$e^b^3~5@2^6@2$f^2^1@1$c^4\1a$7\3len$8M7~2^2\2kb$8\2kk$9M2~3@2$e^2@1$a^c@7$d^e^d^c^b^a^9^8M2~3~6~8M0~9@7$ha^e@1$a^c^6@1$c^b^2^1^3@2^5@2$f^2^1^3~d\1a$7\3len$8\2bk$h1M7~2^3\2kb$8\2kk$9M2~3@2$e^2@1$a^d@7$d^f^e^d^c^b^a^9@2^6@2$f^2^1^4\2lo$9\2hi$9@7$d^c^b^a^9^8^7^6\1e$8\1m$9@7$d^c^b^a^9^8^7^6\1e$8\2lo$9\2hi$9@7$d^d^c^b^a^9^8^7\1a$7\1n$8@7$d^c^b^a^9^8^7^6\2a1$7\2n1$8\2a2$7\2n2$8@7$d^e^d^c^b^a^9^8\1a$7\3len$8\1c$9M7~2^3\2kb$8\2kk$9M2~3@2$e^2@1$a^d@7$d^f^e^d^c^b^a^9M2~3@9$h0^f^e@1$a^d^7@1$c^c^8^2^1^4~5M0~9@8$h8^f^3@1$a^d^7@1$c^c^2^1^4@2^6@2$f^2^1^4\2k0$1\1l@1$0$1@4$5@2$4@1$0$1@1$0$3@1$0$2~a^b\1a$7\3len$8M7~2^2\2kb$8\2kk$9M2~3@2$e^2@1$a^c@7$d^e^d^c^b^a^9^8M2~3~6~8M0~9@7$h9^e@1$a^c^6@1$c^b^2^1^3@2^5@2$f^2^1^3~d").

Fixpoint prunepcB (bc : bctx) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  (cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(br2, cache') :=
        match kbase K with
        | Some kb => match br_lookup cache kb with
                     | Some r => (r, cache)
                     | None => let r := base_rangeB bc kb in (r, (kb, r) :: cache)
                     end
        | None => (None, cache)
        end in
      let '(kept, scs1, hs1) := prune1pcB bc sp wa w wv K hints br2 in
      let '(r, scs2, hs2) := prunepcB bc sp wa w wv rest hs1 cache' in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.


Lemma kcutB_eqf : ltac2:(zQ "90!se!hr8!hn8!hge!mq2!jf!hsk3!hrp6!lm2>2fk@1$2$1@3$5>2mk>0$4>0$0$1>2wb$0>2wk$3>2wn$0>2kb$0>2kk$3>3len$0@1$2$1@1$7@1$8^1\2mk>0$4>0$0$1@2$6^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_95"] "##;Yp'0h01bh12fkh22kbh32kkh43lenh52mkh63negh73posh82wbh92wkh:2wnh;1xi001xh<2x0h=2x1h>2x2h?2x3h@2x4hA2x5i012hbi022hop;1p;2p;3p;4p;5p;6p;7p;8g00eTj1WTg02cgj14Tg0<U5j1Ij2Vj3Lj4Hj5Dj6Aj7Uj8QTg0<VCj2Cj3Jj4Ej5Bj6@j7Tj8RTg03Yfj1Sj31Tg01:AR0j2KTg00f4j1<!s/$Tj30Tg05ehj28Tg00MQj13Tg04MSj39Tg01E@j1FTg01F;j2GTg0:eDj1=Tg00Yhj2;Tg0044j3:Tg008]j3>Tg0097j2MTg03XUj1NTg03bdj1OTg003Vj6PTg002Tj56Tg01SYj4?Tg00`TR1g00b@R2f1R3f0R4C?p=5P1P2P4g01TVR5C?p=7g00=H?934p=2g017aR6#WR7g01U4R8P6\1[R9P7^41R:^32R;^21R<^:1R=^92R>^81%44#I1C43R?X59P1P>%43/V4P?P2P=f2R=#4?L34AJ3=4P1P<f3R<#4P=P3P4CHP=P<!s0$EP1P;f4R;#4P<!sD%DDP<P;!s2&BP2P:f5R:#4P;!sH'EAP;P:!s4+@P1P7f6R?#4P:!sL,FUP:P?!s6-Tg03T[R>g00;\R@^6>]7R>f7RA#SP@P7P@P@P41K12RB15<=RC%<BRD30RE15?:RF=0BDRGO2g00>4RH!sV%PGPEO2P4%73=0BD90BCRCPGO2PHn010!s#$20000!s41PA18<=g00?iRI%3:,2?RJ%3=,2<39O2%<6RK506RLPK!s_2!tx+PC%7;!tB&FRFO2!s=&F!t_&35g020<g01VB#F'G'5!u7$MPC!tk5!s640!yM$712J;#=RJf9RNP@P8P=1534!sn$Of8RP/5A%7?=0BD50BRQO2P=PQPOO2';1834RR%3A,2P/2?RS/85RT!t51%3;,2:RU/2<RV=9ISRSO2=06Kn2001!sP%120101102!v$35:6!v''A1PEGPH!s1&GEA1PCG!wGB!vx<A1PCF!s/&FEA1PMC!vMKPJP!vE$f:RJ?1OQA1JQO';PRP!uo2P!u^Q5>7X0>!to'15=3R>!wK$S15:;RT!s2$J51A!uz'AJS%74!y3&>R>=1AJ!v-B?18=3%33,2=99IU!tn%!vB;%7<!t'&TRT91A>!tE&TSA1AM>!vNK%=VPPP@P815A?%7:!y_'B91NOA1NB!v[$%3?,2A/2:RR/85!yX3<,2;/2==9IR!vrP,M7%4AR6#N%OAEPP6P?!#3E-GQP?PA!s80R5>7eXA1D6X@2D6X?1D6X>1D6X=2D6X<1D6X;9D6W1o"). Qed.
End FPX_95.

#[export] Hint Rewrite kcutB_eqf : bceq.
Section FPX_96. Context {fx : XPropExec.FPState}.

Lemma kzero_cutB_eqf : ltac2:(zQ "80!se!hn8!hge!hr8!jf!hska!hsl6!lm2>2fk@1$1$3@3$4>2wb$0>2wk$2>2wn$0>2kb$0>2kk$2>3len$0@1$1$3@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_96"] "##,{h02mkh12fkh22kbh32kkh41lh53lenh62wbh72wkh82wnh91xh:2x0h;2x1h<2x2h=2x3h>2x4p;1p;2p;3p;4p;5p;6p;8p;7g00eTj1GTg02cgj10Tg0<WNj1;j2Fj3<j45j57j69j7BTg0<Xaj14j2=j3:j46j58j6Ej7CTg0<VCj2Dj83Tg008]j32Tg0097j2>Tg0<U5j1?Tg0<Z1j1@Tg003Vj6ATg002Tj51Tg017aR0#GR1g00`TR2g00b@R3P1^52R4^33R5^22R6^82R7]7R8f0R9#0#;%49P3P7f1R7#0/F91=79P2P6f2R6#0?<79A:6!s9$5f3R5#0P6P7P9C5P5!s0&6P3P4f4R4#0!s:'D7P4!s2+8P2P1f5R:#0!s<,E9P:!s4-Eg01U4P0\2[R0P8^62]0R8f7R;,D9X00P9g01>OR0f6R<!s`,O7P0P;P!s8-G3521X48P0!s</P9G3,>1%0<R0#?%@<EAP0!sE/FB!sU1FC521eX>2D1X=3D1X<2D1X;2D1X:3D1X92D1W1o"). Qed.
End FPX_96.

#[export] Hint Rewrite kzero_cutB_eqf : bceq.
Section FPX_97. Context {fx : XPropExec.FPState}.

Lemma kfill_cutB_eqf : ltac2:(zQ "80!hge!se!hn8!hr8!jf!hsm4!hsn0!lm2>2fk@1$2$3@3$4>1c$0>2wb$1>2wk$0>2wn$1>2kb$1>2kk$0>3len$1@1$2$3@1$6@1$7^1\1c$0@2$5^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_97"] "##/1h01ah12mkh21nh31ch42fkh52kbh62kkh71lh83lenh92wbh:2wkh;2wnh<1xh=2x0h>2x1h?2x2h@2x3hA2x4hB2x5p;1p;2p;3p;4p;5p;6p;7p;8g00eTj1ITg02cgj10Tg0<[Cj1<j2Hj3>j4;j56j68j7Gj8CTg0<\Vj25j3=j4:j57j69j7Fj8DTg0<VCj2Ej82Tg01OEj33Tg008]j34Tg0097j2?Tg0<U5j1@Tg0<Z1j1ATg003Vj6BTg002Tj51Tg017aR0#IR1g00b@R2g00`TR3P1^83R4^62R5^53R6^;3R7^:2R8]9R9f0R:#0#<f1R;,5:R<X32P3P8%0;/H:P<P2P7f2R7#0?>;:A=;7:P3P6f3R6#0P7P;P:C;P7P6!s0$:P3P5f4R5#0P6!sD%D6P6P5!s2&7P2P4f5R4#0P5!sH'E8P5P4!s4+9P3P1f6R<#0P4!sL,FGP4P<!s6-Fg01U4R8P0\3[R0P9]1R9f8R=,E:X10P:f993;:X23X08R0P<!st,O7P0P=!s8/G2541X79A3;:=!sY%f7R8!tO/G2,?1%08R=#@%A8EB!sh1P:GCP<P!sY1D541eXB3D1XA2D1X@3D1X?3D1X>2D1X=3D1X<2D1W4o"). Qed.
End FPX_97.

#[export] Hint Rewrite kfill_cutB_eqf : bceq.
Section FPX_98. Context {fx : XPropExec.FPState}.

Lemma kunk_cutB_eqf : ltac2:(zQ "80!se!hn8!hge!hr8!jf!hsne!hso9!lm2>2fk@1$1$3@3$4>2wb$0>2wk$2>2wn$0>2kb$0>2kk$2>3len$0@1$1$3@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_98"] "##,{h02mkh12fkh22kbh32kkh41lh53lenh62wbh72wkh82wnh91xh:2x0h;2x1h<2x2h=2x3h>2x4p;1p;2p;3p;4p;5p;6p;8p;7g00eTj1GTg02cgj10Tg0<]fj1;j2Fj3<j45j57j69j7BTg0<_8j14j2=j3:j46j58j6Ej7CTg0<VCj2Dj83Tg008]j32Tg0097j2>Tg0<U5j1?Tg0<Z1j1@Tg003Vj6ATg002Tj51Tg017aR0#GR1g00`TR2g00b@R3P1^52R4^33R5^22R6^82R7]7R8f0R9#0#;%49P3P7f1R7#0/F91=79P2P6f2R6#0?<79A:6!s9$5f3R5#0P6P7P9C5P5!s0&6P3P4f4R4#0!s:'D7P4!s2+8P2P1f5R:#0!s<,E9P:!s4-Eg01U4P0\2[R0P8^62]0R8f7R;,D9X00P9g01PTR0f6R<!s`,O7P0P;P!s8-G3521X48P0!s</P9G3,>1%0<R0#?%@<EAP0!sE/FB!sU1FC521eX>2D1X=3D1X<2D1X;2D1X:3D1X92D1W1o"). Qed.
End FPX_98.

#[export] Hint Rewrite kunk_cutB_eqf : bceq.
Section FPX_99. Context {fx : XPropExec.FPState}.

Lemma prune_zfB_eqf : ltac2:(zQ "e1!hn8!hr8!se!lc!hu2!hrqf!hge!mq2!tt5!u0!jf!hsp6!lm2!hsq1&@2$4@2$4@1$0$1@1$0$8@1$0$3>2fk@1$0$1@3$a>2mk>0$7>0$2$1>2wb$2>1k$6>1w$9>1K$1>2kb$2>2kk$6>3len$2>5apart>0$5$3>5hints@1$0$3>8diffbase>0$5~0~0@1$d@1$c^1\2mk>0$7>0$2$1@2$b^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_99"] "##Cwp'0h02mkh12kbh22kkh33leni003lenh42wbh51Kh65aparth78diffbaseh82fkh95hintsh:1kh;1li011lh<1wh=2wkh>2wnh?1xi021xh@2x0hA2x1hB2x2hC2x3hD2x4hE2x5hF2x6hG2x7hH2x8hI2x9i031ai041bi051ei061ii072k0i082l0i092loi0:1ni0;2opi0<2sxp;1p;2p;3p;4p;5p;6p;7p;8p;9p;:p;;p;<g00eTR0j1:Tg01:Aj2?Tg02cgj11Tg0<`Gj1Cj2Qj3Mj4Ej5Bj6@j7Vj8Pl9Nl:Kl;Hl<YTg0<aYj2\j3Ij4Dj5Aj6[j7Uj8Ol9Ll:Jl;Gl<XTg0<VCj2Fj85Tg00XYj2;Tg0<bhj6<Tg00f4j1=Tg01mbj17Tg01FXj26Tg01T9j28Tg05b:j14Tg01SYj49Tg008]j3>Tg0097j2RTg0<U5j1STg0<Z1j1TTg003Vj6ZTg002Tj52!t:$Tj3WTf6R1f5R2f4R3f3R4f2R5f1R6C9f0R7C9p=0g017aR8?W67p=3%:8R9g01U4g00`TR:P8[[R;g00b@R<g00aaR=g05<6R>g00;\R?[R@%:?RAg06?kRB#:RC,?9RD/?ARE\>R>PE]7RF]9RG]6RH^3:RI^2<RJ^1:RK^58RL]<RM]:RN^4:%17#C1\76ROX0;P:PN%16/Q7POP<PM%15?M67AI657P=PL%14P5P6P7CEP5P4!s0$DP8PK%13P!sA&DBP4P3!s2&AP:PJ%12P!sE+E@P3P2!s4+[P<PI%11P!sI-FVP2P1!s6-UP:PHf7RH#1P!sP0GPP1PH!s80OP@PGf8RG#1PH!sT1M9NPHPG!s;3LPAPFf9RF#1PG!sZ4:KPGPF!s=5JP>PEf:RI#1PF!s^6;HPFPI!s?7GP9^3:^2<^1:^>:^=<^4:^0;RJf<RK,F7X0;P?PE1;1IRLP:PEP3PDPAP9PCPK!sv$7PIPFE<%=BRBP4F0RMP?PE%7F,6I/81RO!sV'%=8RN,3GP!sM%P!sn+6PKf;RQPI%4FRR!ts%O7!sM%n010!s#$20000!t$%Q,6K/8GRS!sh'13INPBP2F0RT!s|+4f>RUf=RVPK%4QRW!v8%!s~$2!s~3RXP!s$%!t-$K,6V/8FRX!t-,QNPBP1F0RY!t-+3f?RZPUPV%4KR[PIPFPG!t+$1!t+4\P\n01!s9%8101!s'%:3010;103104!s1D4010<10910:105!s4&710610:P?PEP4g05=]R\O1R]!u-,HNPBP5F0R^P0P8PEP7PQPIPF%4GR_!x{%O7P6P\O1R`!s],67PBC9RaP3C9Rbn1011!uA$20020!tF$1!uY1!s4-1!wm%P!yD'!x}$POP!x^,KPV!tT$!xY&G5!xY;PSP!x>,UPZPVPKP!x7&!s\$!x75WP!s$%?PEPXP!wt,Zf@PUPVP!wo&!sd$!wo5[P[!wo~!wo%]P!wR'QPK!t\$!wO&G5R_P`P!w5U5>EX;J!}]%2F!w=$4!uo+Q!t'$7PFPGE<!x{%!{L%G,6F/82P^!sQ+_!sE%!}%7I,6Q/8H!y8,FNPBP3F0!sc+VPUPKPQ%4!#3n%!w$$3!w$4KP!s$%WPW!w0~!w0%5P\O1!u%,1NPBP6F0!wD&IPQPFPG%4!#7Z%G5P7!sW+aP4C9!wOT,RE%1QRa#S%TQEZPa!z'%!#6u3<Y!tL'!sA5X5>EeXI>D2XHAD2XG@D2XF:D2XE<D2XD:D2XC8D2XB=D2XA<D2X@:D2X?;D2W8o"). Qed.
End FPX_99.

#[export] Hint Rewrite prune_zfB_eqf : bceq.
Section FPX_100. Context {fx : XPropExec.FPState}.

Lemma prune1pB_eqf : ltac2:(zQ "d0!hn8!hr8!lc!hu2!u0!jf!se!hsqe!mq2!tt5!nj2!lm2!hsr8>2fk@1$0$1@3$5>2sp$a>2wa$8>1w$4>2wv$6>1K$1>5hints@1$0$2@2$3@2$3@1$0$1@1$0$9@1$0$2@1$c@1$b^1@1$7^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_100"] "##zwp'0h01Ki001Kh15hintsi0!s/&h22mkh31wh41ai021ah55aparti03!s/%h61bi041bh72b1h82b2h98diffbaseh:2fkh;1kh<2k1h=2k2h>2kbi052kbh?2kki062kkh@3leni073lenhA1ni081nhB2n1i092n1hC2n2i0:2n2hD1pi0;1phE2sphF2wahG2wbhH2wvhI1xi0<1xhJ2x0hK2x1hL2x2hM2x3hN2x4i0=2a1i0>2a2i0?2bki0@1ci0A1ei0B2hii0C2hsi0D1ii0E2k0i0F2l0i0G2loi0H3lo0i0I1mi0J2opi0K2sxi0L1vi0M2w'i0N1zp%0p;1p;2p;3p;4p;5p;6p;<p;8p;7g00eTR0j1HTg01:Aj2STg02cgj1:Tg0<d4j1Yj2hj3]j4Zj5Wj6mj7eTg0<eEj1nj2`j3\j4Xj5Uj6lj7_Tg04iNj1kj81Tg043Tj16Tg00XYj2DTg044aj13Tg01T9j27Tg01mEj2CTg00f4j1ITg0<fSj6NTg05b:j19Tg00g4j1[Tg00]nj2GTg00Yhj2BTg05ehj28Tg01SYj44Tg0<`Gl<Fj1cTg01D[j1ATg01E@j1M!s/$^j2VTg01jZj2TTg01FXj2LTg01kXj2KTg01G5j2<Tg01@mj2ETg01hOj2RTg0044j3Q!s\$;j2>Tg00MQj1=Tg01OEj3jTg0<aYl<?j2gTg008]j3JTg0097j2fTg0<gcj1bTg003Vj6OTg04h6j1aTg0<i9j1dTg002Tj5@!v;$bj1i!v;$Tj3PTg0:oEj4^Tf1R1f0R2#i'Lp=;g017aR3?P12p=5f6R4f5R5f4R6f3R7f2R8P1C4P2C4p=0g06?kR9P6P7P8P1C^;P2p=2%H3R:g04fhR;g01U4R<g00aaR=g00`TR>g00;\R?#HR@%H9RA,S:RB/S@RC]1RD^03RE]HRF]3RG]F%:2#Y%n2P<PG%:1/h21`12P=PF%:8?]12A\812P>PE%:!tU$P2CZP!s0'XP3PD%:!tp&P2DWP!s2,UP@PC%:5!s9,EmP!s4/lg00b@RDP?^C>^=D^8>^B>]<^7>^E;S00%k4Q00P3PCP8P<!s+$?PCf:RE#6RF,D1RGP?PC1;27S01%3ERH'7f9RI,;HS02/72'CPBP@P:PAf7RJ%I3RK'5S03%I9R9P4F0RL!sG'P1P2!ti$HPIENP!sD$n010!s#$20000S04P?PCP5f;RMPFPH%9IRNP1P2%97ROO7PLP?PCg00h4#[RP,GI1G7PS05'Bf8RQ/D8'BS06!sM%P5P!sk$PN1812RR#6RS%3RRRP!sp%0!sK$4!tm+KP9C4RT%I?C4RU!sC$1!sC'15IKRVf<RW%9MRX1878RY%95S07P9D2P2F0!sQ$TP2C4RZn01104!uM'n1011!u_$2002010410CS08!sL$3!sL+!v%0!s4>1!s^$!s0$21105106!x&$1%:MS09g01>OR[%6IR\%3IR]PQP4!wB$8g05<6R^!v7,!y>$7O7US0:P5!vS381R_#6R`%3_R_P7!vS0!v>2PVPWPX1867RaP5!v1+!v#I;!v#1V^RbM<F!u\-0!u\-!z`$PGP>PCP7!x|%1VB#ARc#M%Ac#A!s$&M'VRc,T2,L1S0<%3MRd'71;dE/71Re!zu,15QKRfP9PJF0Rg!x3&JC4Rh!wI1!tE$ePgP!s>6f=Re#3/;WS0=/77!t%,EKRiP9PIF0S0>!t&&IC4S0?!sk1RjP!s$%?PCf>#3/;e/76!sn,MKP9PE!yz+EC4!sf5!vN$700081010F101083010J102104!s1D4010K10G10810A!s4&E10D108S0@!y31PSPR!y$GPY!x|TA!{}<1!s4$!{a3>PC%6JS0BPDPCP2!tN+?P:%3QRj/K1Rk,<81E8k/5KPK!x-4:1;jJ,R8Rk/<11Ek1!sM65Q3P9P6F0S0CP?PC1>87Rk/<cS0D!uo$6PEP\P]%9QRlg01TV#=Rm/87Rn#6S0E%3nS0F%=kS0GO!y8-4KS0HP9P5F0Rk!vj&5!vj4fPM%9ERn18m5Ro1>65Rp#=Rq!vyRI!vy1!yd&5C4S0J!yg2rPr!sS$N0003001010;!s'$!us%18Rr!us$K!tx$7PI%6QRsPj%9JRt18m8Ru#6S0L%3uS0M%=rS0N!un/5K!vm%Rr!uk&6!uk3Q03PEPN18m6Ru1>76Rv#=Rw!uiRO!ui86C4Rx!}~51<vcS0P!{Q1%6uRv%3uRyPw!#5YFm4S0Q1>54#=S0R!t}RS!t}84C4Rz!wg2{P!s$%!u,$pcRp!td&W%6MRcPdPn%6oR{%3oR|PqO7Pg!u/&J!u/4iPe%9WR}18mJS0T1>4J#=S0U!u2RV!u22!#6#1RmPm!sH$<00081110N!#4RZH!#4R6!yr,6KP9P7F0RmPrPmPk!#9-$%:WAj126XA>X4<R~!xL$IPJ!#?}%4PWP!vU$P8P1P6O7V^P4!vr'!s@&`P_P6!viCP}PaP4!vZRW!#;I2!#;G<1Q09g01PTR}P\P!#=t,Q0:P5P!#<%8!s8$0000:31!vi$M10L20!s1$7!s9&710?2110G10B2010A10I3!s-%!s9'21084010=10910>10:3!sj&10@!su'!#D}2PGQ!#C^%W!|b'!u#$OG1!#C/$Q!#C8'W!#9V/!sG$Q!#A^nS0!tf%1P[PM!v\1!tJ-8P1P7G1V^Rb!#AK%!sB,`P_P7!tf%!#@E4iM<?!#@E@Q!#<7%!u_1!sw&!#;@QS0AP>PCQ!#;@&Q!#:8$Q!#:/%M!#:/$PlQ0EQ0FQ0GG1PkQ!#8S2Q!#8I3GPG!#8I<Q!#8@%EPIPsPjPtQ0LQ0MQ0NG1PrQ!#6n3!#6d5Q!#6`%!uz,vPyPw!uz%!#5W2z!tk5!s$$?PCP!#5I$e!}U+{P|PqG1PgQ!#4:Ch!s8$!#4:{RhP!#4&/P~PW!#3v1e!#3v0!z,$G!#3x%e!#3x0!uI%!#3%3Rg!z,=1P}!{G4bP5P!z`9!~|~!~|4Rd5JCW6P3\>\<RcP?\^PC\^PC]9^1@]5^@>^?D^>>^03^3=^;D^G>]2Re1g2JX2c!#3d$Q!~#+6P[!u^7O;!u]5Q0AP!w_35P!#8W2GP4Pg!se7!t?+}!t?K!vv~!vv4=JCdXDe!v=$1!#3y+1D1\Re!},%1/7]1;]Q!#Te$k!#TF3]PQEN!#Eb$!}l5!#3V+!#7c'k!t/$GQPQ05'B1DJ8'B!s;%!sS-!#7o&!#F[?PnPYQ!#SQ,!#;{F!#SDrP[PEPsPjPJP5!xG&!u<,!#8a+[P6!uX2!#8a&!uXC!#RwR!~N4O!#9UBe!#Rt+Q0</7HQ02!#RM&L!#6I2!sX&!s>8%3W/;M!#R%,PVP9PQ!#Q7'Q!#Q73eP!s$%!tI$=/76Q0>Q!#RE3ePe!#Q]~!z96!w_GY!w_`!#QWH4!#QT6JRD/K1RY!#QT$Y!#QT;D4,R8RY/<11EY!#QT<7F0!#>?-!#=9,!#>?+!#N,BPoPq!v'^!#>-2Rx!s8$!#?3AIPQQ0BPD%94!#?5-m!tz&7!tz5HPIPlPuPw!tz_!{2%7!{23!#@2-!yc,!#@2&!ycBQ0QQ!#O\Q!#BnBnP!s$%!#A%+!#Ap+!#A%&!#QLAQ0TQ!#O6Q!#BfAz!s8$!#O3~!#O3%7KP9P8F0RKPmPKPr!#B/'!#@m07!#I616G1V^!#I476!vME!#O#S!#N|4!#Bw>!#9]2[P6PO!#Bw~!#?#G,fC%:4RO#c%b4EO%aO%d4EOPO!#mi-FeP4!s60_5JCeXN@D@XM3D@XL>D@XK=D@XJ<D@XI;D@W:o"). Qed.
End FPX_100.

#[export] Hint Rewrite prune1pB_eqf : bceq.
Section FPX_101. Context {fx : XPropExec.FPState}.

Lemma ranges_apart_pcB_eqf : ltac2:(zQ "c0!hge!se!lc!hn8!u6!hu2!jf!hr8!hss4!nj2!lm2!hst6>2fk@1$3$7@3$6>2sp$9>2b1$1>2k1$0>2n1$1>3br2@1$4@2$5$0$0>2b2$1>2k2$0>2n2$1$2@1$b@1$a^1@1$8^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_101"] "#$j&p'0h01bi001bh11Dh22b1h32b2h42k1h52k2h62n1i012n1h72n2i022n2h81oh93br2i033br2h:1ei041eh;2fkh<2h1i052h1h=3hi1i063hi1h>1ki071kh?3lo1i083lo1h@1ni091nhA3neghB3poshC1xi0:1xhD2x0hE2x1hF2x2hG2x3hH2x4hI2x5hJ2x6i0;1ai0<2e1i0=2e2i0>2h2i0?3hi2i0@1ii0A2loi0B3lo2i0C2opi0D1pi0E2p0i0F2sxi0G2z1i0H2z2p%0p;1p;2p;3p;4p;5p;6p;7p;8p;9g00eTj1NTg01:AR0j2JTg00hSR1j1MTg02cgj11Tg0<jUj1yj2`j3Wj4Sj5Qj6wj7tj8al9ZTg0<knj1uj2\j3Uj4Rj5xj6vj7oj8_l9pTg03DGj1^j7LTg04jcj1CTg01FXj20Tg03M<j1ITg04l0j1KTg04[Aj5Vj1eTg04m;j1?Tg03Oaj2Hj1]Tg04I]j77j1gTg01T9j2GTg04nGj1>Tg04]bj5Fj1bTg03EWj2=Tg04QLj1ETg00f4j1T!s/$Tj34Tg03XUj38j1iTg04\Sj5Pj1nTg03Pnj2@j1sTg04Jmj72j1qTg04_6j5Dj1kTg03Yfj33j1rTg0097j2dTg04oSj1cTg003Vj6ATg050kj1f!tU$jj1hTg03bdj1jTg03f`j1lTg03C4j1mTg04?@j1[Tg002Tj5;Tg01mEj2YTg01SYj4OTg008]j3XTf5R2f4R3'Gf3R4f2R5'0f1R6'0f0R7'G'Yp=:1056/07p=B1067,G5p=9g00`TR8g00b@R9P6P7COp=5P8P9P6g01TVCO=4579434p=6g00;\R:?X67p=<g017a#Ng04fhS001J99R;#MR<P:^78R=^59R>^38S01]9R?^68R@^49RA^28%17#y%u7Q00P8PA%16/`71\67P9P@%15?W67AU567P8P?%14P5!tk$SP!s0'RP<Q01%13!s8'DQP!s2,xP8P>%12!s9,EwP!s4/vP9P=f6R=#1!s>/FtP=!s60oP8P:f7R>#1!s@1GaP>!s82_P:^79^59!uj$2^69^49^28R?f8R@#^P8P:P2!s+$5P:P:P1P;P:f:RA#CRBP0P9P9P:P7!s>&9RC!s:,f>RD,04RE%I>S03'0106AP7PA%I=S04103DRFE:n200110E00012010B10?g00>4RGn101103000210!sI$!sS&D!sS'8106P!sN&:!sN'D00RHg00<<RIP:P:f;RJ#1RK%KAS05P2P3%I7RLDVRMPIP5PCP@%I6S06!v9$LO6n010!s#$20000!s41!u|,P!uv4PC!s809P:f@RN#?RO!s4&BRP#1RQ/HAP:P:AB2N6f<RR,04P5PRP710=NE:S07PI!t6&9P:fCRS#1RTfARUPNf?RV!x3$6F7f=RW,03S08,G7S09!v$4<00PI!sl%PTPWPRPJ!xi$7F7A97>US0:!sZ4=!uh3!s41S0;!sY4>00!s:45!ws+!xH0P!xC^!v3&K%>AS0<!{-%DFS0=!s?%1=C2#ES0>PG!s5$J89RX1523RY%TXRZ34R[PX15C@R\PXP>PZD6R]58KPIA4X\Z!s<$YPXP4!s@$Y58K!v#?!v53?!y>;%CRRK!yA4J!yA3%?PR^!x`&DR_#1R`/HR!y>&P6PEP5PD!y9$PE:S0@!y90ERE#1RaPSPPPU!y5'A973VS0A!y,@aPVPDPW!y,/SS0B!y,UC!y,~!y,F%1WRb%>RS0D!#5<$DFS0E!y0'J>#ES0F!y0&5>=Rc=4XZRdPX15JARePXPC!xe$f58b!y#$eZ!s<$cPXP2!s@$c58b!y#MR!sR2RgP!s$%!y--WRh!y-4R!y-5SRi!s1%1HaW!y#&S6104VP5PV!y%$SE:S0G!y%0FRa#1RjP_!y'$!y%-NS0H!y%@jPN!y'$!y%-_S0I!y%UJ!y%~!y%HDRj%>WS0KP@P>P=DFS0L!y%'R@#ES0M!y%'@>Rk!y%$lPX15RJRmPXPA!xg$n58j!y%$mZ!s<$kPXP=!s@$k58j!y%N!sR2RoPon011!s4$81010H101093010C10;100!s1D4010F10A109104!s4&710@109!z%/CRo!z%4@!z%5VRp!s1&1U/HC!z'&V6104JP5PJ!z'$VE:S0N!z'/PQ!yI&!y}-RS0O!y}@QPRPJPA!y}/NS0P!y}UQ!y}~!y}HARQ%>CS0R!#B8$DFS0S!y}'@3#ES0T!y}'34Rq!y}$r=8QkPIPXPqPXP5!ye$q98Ql!#9jNU!#9j<JRQ!x_4A!x_5URs!#3b&TJ!x]&U6104WS0VP5PW!x`$UE:S0W!x`0`PPPUPN!x`'1G7FS0X!x_@`PDPWPR!x_/PS0Y!x_SR`!x^~!x^HRRF%>JS0Z!ut$3DFS0[!x^'A=#ER!x]+=2Rt!x]$uPX15ACRvPXP@!x[$w58FPIA4XvZ!s<$tPXP3!s@$t58F!xtO\!v>2FP!s$%gPgn011!sC$81110G!#3ep!#J:2H!y7&JQ!#H4$PLDPPIPJPCP@Q!#H+&FLS0]!uFA^!#H2PP!#H+%1@PARgP:P:Q!#Gg0PS!zh$!#G]&2Q!#GPAS!#GP/2Q!#GKT!z_~!z_@S0_!wJ,!#GH&D!s9%Q!#G?&A3J[]PIA3J\Y!wOA`!}=@F!wm-!#F^EP^!wm'_RRx!t`%!#FC/PE!#F=/2Q!#F8AE!#F8/2Q!#F3T!wm~!wmBa!uo&WQ!#F,'!wm+F!wm'WdfPIA3Wec!wmA!#El?RyP!s$%!ws,!#EKEP!#EH&@EWRE!tf%!#E5/Pa!#E//2Q!#E&Aa!#E&/2Q!#D}T!ws~!wsBc!uo&DQ!#Dw'!ws+M!ws'DlnPIA3Dmk!wsAd!ws@aPa!#D@~!xs-!#D=EPp!xs'UCRa!uf%!#C}0P!#C}/2Q!#CxAP!#Cx/2Q!#CsT!xs~!xsBe!uo&AQ!#Cm'!xs+T!xs'ArkPIA3Alq!xsAf!sEA!#P3,P!#CLEP!#CI&@SJRz!ta%!#C30_!#C3/2Q!#C/A_!#C//2Q!#C&T!wn~!wn@R{!un&RQ!#B|'!wm&P!wl+RuwPIA3Rvt!}B@|!sD@}P!s$%yPy!#BC~R~'<X0?%M9S0h^:8R?%s@!#BX;MPIQ!#B<@RM!#B;XPCPAO1Q!#a3~!#HJBQ!#_I<!#?fNPJPRO1Q!#]F~!u@CP!#[b2bP!s$%!#=:WPRPWO1Q!#Yd~!uGD!#X$2j!s8$!#:f~!#:fUP@PCO1Q!#V-~!{&E!#Ta;!#88NPAPJO1P!#Rg~!u?D\!xa5!s$$b!{D$!#5g{/<~X8?g03T[R?P:^A?]BR?%r!#5k0!#5<Zg!#58~!#V\GQ!#o5&!#Nn'P5P[P]O2PIP5P\PYO2!#UsL!#6/gx!#6'~!v3JE!#M41P3PdPf!v3$3PePc!v3]ReP!s$%!#6{XE!#6w~!v;JL!#KT1P2PlPn!v;$2PmPk!v;^mPm!#7o~!#7oYa!#7k~!w;JS!#It1P6PrPk!w;$6PlPq!}]h!#8bNz!#8^~!v2I[!#H90P4PuPw!v1$4PvPt!zF^tP!s$%ePe!#9T~/<~X0?Q0h^<9^=9^?9^@8^>9^08R?%q!#9[i!#c&6A!#c&-O6!#c&BA!#c&-O6!#c&~!#;,|Q!#b@2Rg!#:Oh!#b<6R!#b<-O6!#b<BR!#b<-O6!#b<~!#;y|Q!#aR2Rx!s62^P!s$%!#;CY!#aP6W!#aP-O6!#aPBW!#aP-O6!#aP~!#<m|Q!#`f2RS!s62_P_!#<7~!#<7Z!#`d6C!#`d-O6!#`dBC!#`d-O6!#`d~!#=a|Q!#_z2Ra!#='i!#_u5J!#_u-O6!#_uBJ!#_u-O6!#_u~!#>V}!#_51RR!s62P!s#&^P^!#=x~!#PN&1U4/J8#NR?Q02]1R^%n!#_><5!#zp'O4!#_IC!ui%_PIPg!s?7aPIP!#7+2xP!s$%!sG$cPIP!#3D2S!s8$!#3D~:Q0ePIP!{\7{PIP!wt3RP!s$%x!uB$!wt~~X0^Q01^1?R?%k!wi0Q!#~h$Q!#{;'5!#{;'!wm%`!wmE!#w/&3!#w/'!sa%!#vR@!#;|,Q!#r}'2!#r}'!si%!#rH@!vW'!x@~Q!#ns'6!#ns'!ti%f!v7CP!#jf&4!#jf'O4!}{5!uJ2|P!s$%!}y~!y'+?!xr$3!s+$6!#;DJQ0VQ!$PX%CP7PCQ04Q08!$PR8!#5NdPA%KC!w=$!$//$AP@P>Q06!s9%FL!vj?Q0gP!#my2!yA~!$8D&@!v\4>!$8B4D!#su&N@P!$8@$D6104AP5PAP710=DE:!#;6/U!#Gr%!#t,%A973J!#;8?UPJPAPC!#t/&A97>V!#;:~!xjvC%>@!u6$6!#t/&1=>4#E!$8$&45RG=4XZ=3CcPIPXPGPXP6PZD693Cd!#V9[!$7b&}P}!}9~9,d:%1@R:#b%c@EA%e:%f@EA%g:%h@EA%i:%j@EA%]:%l@EA%m:%[@EA!yf$!$\0/M9Z!#62$!s;1p'<eXJ8D;XI9D;XH8D;XG<D;XF8D;XE9D;XD8D;WCD;W;o"). Qed.
End FPX_101.

#[export] Hint Rewrite ranges_apart_pcB_eqf : bceq.
Section FPX_102. Context {fx : XPropExec.FPState}.

Lemma prune1pcB_eqf : ltac2:(zQ "f0!hn8!hu2!hr8!lc!hge!u0!u6!jf!se!hsub!mq2!tt5!nj2!lm2!hsv6>2fk@1$0$2@3$7>2sp$c>2wa$a>1w$5>2wv$8>1K$2>5hints@1$0$3>3br2@1$6@2$1$4$4@2$1@2$1@1$0$2@1$0$b@1$0$3@1$e@1$d^1@1$9^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_102"] "##p;p'0h01li001lh11Ki011Kh23br2h31ci021ch45hintsi03!s/%h52sph61wh72wah82wvh91bi041bh:2b1h;2b2h<2fkh=2k1h>2k2h?2kbi052kbh@2kki062kkhA3leni073lenhB2n1i082n1hC2n2i092n2hD1phE2wbhF2wkhG2wnhH1xi0:1xhI2x0hJ2x1hK2x2hL2x3hM2x4hN2x5i0;1ai0<2a1i0=2a2i0>5aparti0?2bki0@1ei0A2hii0B2hsi0C2k0i0D2loi0E1mi0F1ni0G1vi0H2w'p%0p;1p;2p;3p;4p;5p;6p;7p;9p;8g00eTR0j1ETg01:Aj2DTg00hSj1TTg02cgj10Tg0<mDj1nj2Vj3Rj4Mj5Kj6lj7Yj8gTg0<nVj1Zj2Sj3Oj4Lj5mj6fj7Xj8hTg0<Xaj1Wj7GTg043Tj1ATg00XYj2<Tg0<d4j7@j1^Tg044aj1?Tg05b:j15Tg0<jUl9:j1[Tg00f4j1CTg00g4j1NTg00]nj2BTg00Yhj2>Tg05ehj2FTg01SYj42Tg0:oEj46Tg0<[Cj8Pj1bTg0<]fj7Qj1`Tg0<eEj7;j1iTg0<knl91j1eTg0<\Vj8Jj2kTg0<_8j7Ij1jTg008]j39Tg0097j2]Tg0<oej1\Tg003Vj6=Tg0=1Bj1_Tg0=2Wj1aTg0=3mj1cTg0<WNj1dTg0=5Dj1UTg002Tj54!uW$Tj3HTg017aR1f1R2f0R33Hp=7f6R4f5R5f4R6f3R7f2R8P2C2P3C2p=3g06?kR9?H23p=8%E1R:g04fhR;g01U4R<g00aaR=g00`TR>g00;\R?#ER@g00b@RA/DA#TRB%E9RC,D:RD/D@RE]2RF]4RG^11RH]8RI]6RJ]7%03#n%Z3P<PJ%02/V31S23P=PI%08?R23AO823P>PH%07P8P2P3CMP!s0'LP1PG%06!s7'DKP!s2,mP@PF%05!s9,ElP!s4/fPBPE%04!s;/FYP!s61XP:^A>^@A^?>^G>^FA^E>RFf7RG#WP1PEP7P<PEP8P?PEf;RH#ARI,<2RJf=RK#0RLf<RMPHf:RNf9ROf8RPPGF@RQP?PEPLPMPI%?HRR%5NRSP4P2P3%57RTM9:PDP@P:PC%C1RU,7PS00%C9R9PGF3RVP?PEg00h4#NRW,BN1B7WRX'>1<O8'>RYPV!t0,PRPSP41F23RZ#AR[%?ZRZP!t2$VP0!sN$G!t<'PUP9C2R\%C?C2R]!sC$2!sC'17NUR^PK%5MR_1F78R`%55S01C6/89P3F3!sP$\P3C2R\n0110400020000n101103!s5%2010410BRa!sK$>!sK+010!s#$!s46S02!s701!sa$;000121105106Rb!wT$2P?PE%ANRc,<2Rd%0MRePHPNPOPPPGP4F@Rf!uO$ePHPc%?NRg%5ORhP5P2P3P8M9:Ri!uj,GUP9P4F3RjP0!xb$6PcPgPh!sS%O6!sq,!s<$5P[PZ!sk$Pj!v|&4P!vg4OURkPM%5HRlP`P6!v_,!vUHm!vU1Rn!t#,23!x/$oPPC2Rp!se%:!se,C1!w+@!vs6S03!{J,PJPQ!yo3!uf$7!yd1!uf2P^PKP_P`P5!u_R_!u_2^!u24!t|'0!xq&q%0!xW+P5P6F@RrPr%0!xn-P5F@RsPrPf!uOB2P3!uO$Rt!uQ$1!sE$8!sE&!sC$GPP^!u[$oPOC2RL!w6f!{%,PdP!zf%iP!z9'e!z9/FQPnP!xQgRe!s:$1000:3110;10H10G2!s1%730!s-%10?2010D10A2010@10E3!s-%!s9';10F4010<10810=109!su&7102!su'!#662PJPKPM!}W,F;Ru!s>$K!wQ2TM91!#5-%!#56&K!zE2!sI&!#3]M!wUP!tt-P4F;Rv!s>$M!~Z-!#3G%1Rw!wz+M!wz0GRx!s[4!#37%1PjP!~83y!xOh!w30u!vX87!vX%!}#3z!}#CP!||1;R{P{P!|{1;R|P{Pv!tSB!|{&1!|y+8PK!|y0JRKPzP!|qt!x2%!wu;IRwP!wJi!|q~!|q4Ry59EX0FPF^3ARz1k3PX3A!}/&b!#3h?x!#3ZIR}!ugCR~PqPrPrP!#6i:!#6T+5!#6T0O7P^!xWi!#5/~!w<4=9EyX0zPF%jG!w2+!u{MK!ukJRt!umCQ03!un~!un:FPE^4@^11^8>^6=^7<^5;RF%iG!#8?55!#6I-O6RQQ!#CdD!zu06!#3j-O6RfP}!#5[OQP!#?1CP8!#50-O6R^P^P7!#50-O6P^!xC4t!#=w_w!#=ii!xn~!xn9DFP?^C>^>A^;>^2B^B>^=A^:>^5;RA%e!xt7!#8S$5!#=}2O8!#=|15!#=|2!sH$!#={z!#8_$6!#=k2O8Ra!#5|,!sJ3[PZP8O8!#=Y5m!#=Yz!v537!v5$!#=X2_!{ND{P{P!#=8:!wc3!t2%!#4_&_!#<}z!w0,wPm!{w~!{w~9!#<^$8!vs-!uT'!#D_2T!#D&$?PE1BOW/>X1<P8'>!s9%!#DX3!sT&!#Pi9PkPMPlP`Q!#TD-!#N&F!|\w%AORT,<2RXP|!tu$HPNPT%?ORW%5PRAP6!#GW+y!#Qz+4UP9P5F3RU!xs&HPTPWPA!#Gi&!sq,!s<$6!#Gg+U!v5&5!v53Q00PHPS!#SrT!|\2S!#OT%GC2Ro!~5q!y47!#Hh'!x^D!#SaR!uN2\!#3+C!#;R,P7F;RPPPP{PPP|!{GF!u9+!{x%!#H1-7GJP\!#5xl!z5$P!z,'yP!yX9IPSPo!#3[~!#3[u,]E%0GRo#[%\GE=%^o%_GE=%`o%aGE=%bo%cGE=%do%UGE=Po!#cR0Gg!x+,!s8&h59EeXNBD4XM@D4XL1D4XK>D4XJ=D4XI<D4XH;D4W<o"). Qed.
End FPX_102.

#[export] Hint Rewrite prune1pcB_eqf : bceq.
Section FPX_103. Context {fx : XPropExec.FPState}.

Lemma prunepcB_eqf : ltac2:(zQ "f0!hn8!hu2!hr8!lc!hge!se!u0!u6!jf!htg3!mq2!tt5!nj2!lm2!htgd>2fk@1$0$2@3$8>2sp$c>2wa$a>1w$6>2wv$5>2kn@1$0$2>5hints@1$0$3>5cache@1$0@2$1$5@1$7@2$1$4$4@2$1@2$1@1$0$2@1$0$b@1$0$3@1$e@1$d^1@1$9^1").
Proof.
ltac2:(KReplay.run1z (kr_t_XAxSymExec3B ()) ["FPX_103"] "##@5p'0h02knh11wh22wah32wvh41Kh55hintsh61pi001ph72sph81xi011xh92x0h:2IHh;3br2i023br2h<5cacheh=1eh>2fkh?1oh@4resti036!sC$'i043hs1i053hs2i062kbi074kepti081ri094scs1i0:4scs2p;1p;2p;3p;4p;5p;6p;7p;8g00eTj19Tg01:AR0j26Tg00hSR1j1MTg02cgj11Tg0=6[j1Yj2Nj3Kj4Fj5Cj65j7Bj8WTg0=7lj1Uj2Lj3Gj4Dj5Xj67j7?j88Tg008]j34Tg00f4j1TTg0097j2;Tg002Tj52!sA$Tj33Tg0=9:j1>Tg0=:Fj2<Tg01SYj40Tg02=ij2Jj1RTg00nJj1HTg0<mDj8Ij1PTg0044j3=Tg02?=j2Aj1ETg0<nVj8@j1OTg0=;Vj1QTg003Vj6:Tg03iBj1STg01Qcj5VTg017aR2#9R3g04fhR4g01U4R5g00aaR6g00`TR7g00;\#9R8g00b@R9/69R9#MR:,67R;#9R<g06?kR=#9R>,63R?/68R@]<RA]5RB^03RC]3RD]1RE]2f0RF#1#Y%UFP5PEf1RE#1/NF1LEFP6PDf2RD#1?KEFAGDEFP7PCf3RC#1PDPEPFCFPC!s0&DP3PBf4RG#1!s:'DCPG!s2+XP2f6RH#1RIf5RJ!s@&FE5PHP!s4,754BX03P8PA%1!s='E%T2RKE5!sN+EPKE7P<P@PI!s:+KPFFB!sr-KPFF?f7RI!s:+KPEPFG8,;@X9<D2X88D2%1!sF,FE5P!s4/754BP8PAf8RA#1!sA'A32DE!t\$A!sT+!t\&f9RK#1!s>'A32CDRL!te$K!sS+LPFF?PBf:RL!s<+CE7P0P:!uG$1P716:<RM%>JRNP1P:PM1<DFRO!sG$FPCC0RPP:P<f<RQ#1/JFRRP7P:PFPRC0=3;DC0n1011010002101080!t+$%H9R9PEC0RR!sG2600P0P?P8P@f=RS#1PQf;RTPLPKPIPGPEGIRUP0P3P>P@PE!sR'PHPDPGO2!s@-?P8P3P>A=2JEA==GFC0PDC0n200110000012010810:R=!s<&1!s<'0105!sP37109!sN64!s:32103!vc/PMP!v\&POP!vN$1AQFRJ!vI&J!vI>!v<6RJ!uj+SPQP!v8/@!v65fAf@RVf?RWf>RXPSPLPDPGG8P!uhLRY!ujKRZ54@X6BP:^=7RB%EL!u|APEPFO1RP!u~&P!u~Q!u|+UP!tpL=4@ZX?BP@^;:^58^42^37^16^25^74RB%O!u%,!w,,D!w,1O7!t?R6B!u~1%>G!|['EF!|Y&DC!sI$1ATFRM!v/&M!v/$E!|R;P9PF!sB4!v7/!u+'APHPC!y59PVPWPX!y_$K!y/S!uzK,;@%1LR=#P%QLE:%R=%SLE:P=!#3{,5PD!s8/A32GCRGPEPFGWP!#4L+!s8%854@e!#66+W:X@3X42PFDVX03D2X37D2X16D2X25D2X74D2W>o"). Qed.
End FPX_103.

#[export] Hint Rewrite prunepcB_eqf : bceq.

(* [comment removed for export] *)
#[export] Hint Rewrite zf_coversB_eqf kentry_overlayB_eqf kentry_readableB_eqf kn_readableB_eqf kn_overlayB_eqf : bceq.
Section FPX_104. Context {fx : XPropExec.FPState}.


(* [comment removed for export] *)

End FPX_104.


Section FPX_105. Context {fx : XPropExec.FPState}.




(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX_105.


Section FPX_106. Context {fx : XPropExec.FPState}.



(* [comment removed for export] *)
Inductive pk_res := PKeep | PRepl (l : list kentry).

(* [comment removed for export] *)

(* [comment removed for export] *)
Record binfo := BI { bi_base : expr; bi_br : option (Z * Z) }.
Record ntab := NT { nt_vars : list (list (expr * positive)); nt_other : list (expr * positive); nt_next : positive; nt_info : ptree binfo }.



Record stx := STX { sx_a : saddr; sx_w : nat; sx_v : expr; sx_sp : sprep; sx_bid : positive; sx_br : option (Z * Z) }.

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)





(* [comment removed for export] *)

(* [comment removed for export] *)
Record einfo := EI { ei_bid : positive; ei_gid : positive; ei_kb : expr; ei_br : option (Z * Z); ei_k : Z; ei_m : option Z }.

(* [comment removed for export] *)
Definition gval : ltac2:(zQ "00T") := ltac2:(zQ "40!hu2!hge!u6!hhr8@2$0@2$0$3@1$2@2$0$1$1@2$0$1$1").
Definition gtab : ltac2:(zQ "00T") := ltac2:(zQ "20!himf!htm8@1$0$1").
Record gst := GST { gs_gid : ptree (ptree positive); gs_next : positive; gs_bnds : gtab }.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)

End FPX_106.


End AX2B.
(* [comment removed for export] *)
