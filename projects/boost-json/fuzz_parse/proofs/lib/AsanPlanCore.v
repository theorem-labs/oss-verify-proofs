(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AxSymExec3 AxSymExec3B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsanPlanCore () := KReplay.lz_vm "#'XKC47Corelib7Program6Basics4flip!sD,4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3lebI!s`15Logic2eq00!s]<2le!sB<6leb_leK!t|,Numbers7BinNums8positive02!sK=1Z!sD?!si,1K!u4;1I!t'?0!ul83and!sA4!vi,4bool00K!sFA1!u-G3c89OSSVerify6Proofs:boost_json:fuzz_parse3lib<AsanPlan!s~#3APC4CEILC13~~~!soa7!so#MAX!sr%C4!xC&5Lists4!s+#8flat_map!sC79fold_left!sD7:!sD$righ!sE87ex!s2#bC!u8O:AxSymExec33AX25sfact!u4'!w>+Classes9Morphisms@reflexive_proper!sS5?Relation!s6&=eq_Tran!wx%!t'?Grewrite_r!sh&_eq_dom!sZ?Ceq_!s]3!sV?Mt!tY#_co!t&#inv_impl_m!sE&!vaP;!va,B4AX2B:pt_ge!xS%!vh2!|'-8!tG$d_r!t;a4gval!t5&!xg^6!u&%!soV!t`4!sq#!uq+!~[=list00!|}a8fresh_ok!t;B6op!y##!#4:>prod!t]c4a_ss!wRfs_know!soe8!~'#s_of!xEg4mkbc!y6hmk_kix!uUe4s_pc!w5hreg!w~&K!znA1!t7bnext!t7B!zj'2K!t9^9sym_state01!wzg<!sv#execTXBI!w9e5s_log!ychcarryK!sq%!}ta5mk!}u+!#>Dawith!~ih:!w>,!w<f!vJ$!sn&!#;b=:respectful!#=mD<eq_R!#>K&!s|?J!#>q+!#=e$_r!s]GI!s],!#?Z/xy!tjISymmetric!sUE8s!sR%y!t^??eq!#A%%!tT3!#=r,7f_equal!{Ba?!xk,!#8_Z!sz49!|>%_eq!stg?!~u/!sz+!|Ka9run_block!stg=!st+!yU#!#6yI1i!tB`3acs00!t:%!#?W;3nat00I!#9E^kentry!t8+!sq^8sidecond!ssg6s!tfl5saddr!spg!#;W,!stW!#AD4bctx!sq'!zaa?!x6%_apart_bB!szg>!sz1!#92d>ranges!sw&x!|WB!{C$2!#Wz'5!#Wy#8PeanoNat3!s&#leb!#XB<of_nat!#A7^4expr!#A2'!#C[;and!tU=3su!sC>ltb!#6;a!vq1B!#77fC!sz2_eq!#Is&!#V0+ogicHFunctionalExtens!s1$ityIf!s?+_e!s@1!wUd0!yMG1!#]\?!#HO_5two64!|ng@!|n1pB!~gvp!}lsp!yxg!zt1p!ztvp!zt-!#93`prep!#7Jh:kn_unfill!xXh9!su+!stg6kimg!#83W!#DM4mk_!vU$!xFh5bc_fk!#4-3!#c8'6filter!{H_8!u#'!#88A3or!#7Ua:!uC$_!#XTj=!w0+!{T,!xuaD!#4B2!t#k>!{c,!syk!|^,M!sug7havoc1!}Rh6!sr%!sqg5kwr!}N'!#\GA2!z[bkzero_cut!}oh:k!wa#!sul9kunk!st[!#I?2!u`+!srg!u]'!sre8!uZ'!vOg>!x=,!#CH,!syb!xA+!syk=!xE+!~ukC!#Ly1!s~k8!~2%!#C,h!#3s%p!srg9kn_!su$!thh8!st'!ssg<!vR'!yEZ!#Ul2zlit!#HK&!z6a3in!#@{g4ei_m!sog5ei_k!talk!takbr!sp%!#9q<!#uK#1!#cI76!#z=$!#B/;9andb!#d8#!#S%<add!#3hap_expr_eqb!#c8i:ob!su^!#^$3p_rn!#o-g;base_!#Lv#!#;ke4sp_D!teg9in_sides!#?=hlin!#8&$!suh<hull_!tp&!sw%!$6;8or00!#KF'4Bool!s'$<orb_true_iff!sF68!sF#!{H#K!sB'9micromega=RingM!s4'5Psatz02!sOK6!sO6:Z!sL+;!|W%!v/$!s{86VarMap1t!sDB3!sD@1I!sD?0I!uCC7Formula00!t567Env!sT#5PExpr02C!sI55Tauto8B!sm&C!v2@=Z!sT$CheckerC!u0<4f!#4d#!sq?C!sq0_soundK!yO;1!s@<2!#66;sym!sB89False!#6U#!$=a<t!#61a!#<V$_b!uL#s!|ugA!~b+_of_!}&#!s|%!#?E`=!#?E#_verdic!$3>hei_bid!sq&!w#+P!w#+Pos3!s&#eq!$;&_8!#:1&!u'g7!#:-%!#=@&!}%K1K!|^<G!sJ'4!}ME3!smF8!$C@<!$Aw+0!u1D3Op203!~e<5eKind!$6^<unit!t48!se%4kind!}c4!sf31!$DZA2!~K84True01I!#Bobnfo!#xe+!#4O>!#8N/0!#8zM1!#;F75!#3}#!$H29!uS%0!#F5aEINF!{ug4bkey!#@Ggnt_buck!$?y'!vc'!#b],2In!$N'9x!$Jt3!s@,1!#tE^!#}J&!#\M%!sq_!#{b%!#u9&5!}Z+!}R&6PosDef3Pos;of_succ_nat!#bBa!#kp2!#8]+!v5g2!sqe!#sp$!sol3!sok4!sok5!sok6!sok7!sok8!y`m3!sqm!#WZ&!#RE;pow!sC=opp!}R@!#S'#!sd;7pos_sub!#{Y?3!u[g5!#6sf6kdescr!wAm6!sqm7!sqm!zen9!sqm:!x0V3Lib2Nd:and_elimF!|E&!#8s`?!#IQ$fast_kind!|NB6modulo!$6Nantab!$;{C:comparison!$an=!sL/1!sLH2!sLH3I4ELinuxProcessSemantics5Riscv5Instr5aluop00!sRHmul!sR$!yU^5ptree!#En3!$aN-Forall2!$X+b9!y,$G_go!#3rgei_g!#OT'!wE;3app!{3ne!$#N'35stdpp7tac!w\#<!$I#%_hel!$ep7;!vc&!#US#!uo`7gs_b!#U1i9NTI_empt!#HBg?scan_entries!$_;'!sza3NTI!#4Bf<!z;+!$K,j!#pz&G!u]g<!vY/!swg8nt!xGm9gs!st0!#7Q`3gst!$6Th=!#v<'!#xwj<!xD+!y=s!$-fg8kwr!$%~,!#zfa!ss&!y8V!#I42k!$%-i5k!$,Il!$#~n8cutout!$3#h7!ss&!zni!y#&!u`k9!tk&!$%ah!vV'!$%bg:kn_!sv%!$Azk!su%!#49g!vV+!wPk7kreadZ!$:2h!sr%!~He;know_looku!$J+g<!sv-!~Vh@!sw/!$I~h4lres!#:Oh8!wN$8eB!y7m8e!|jiwritable!|jj!su'!xBg4xlo!y3h8xinsid!$&@f3xlo!sle7!t_&!uSilo!$=1k<!vH'!$[G-!#Mz98list_ind!#:id!yJ%!$]b'!swa;!sw-!zEihi!yPhhi!x^ihi!#@ol!$D_$x!#4Gi!ss%!tgi!$EM#!tgk!ss%!wE&!#f2;eqb!{2boff_imag!{2l!sw-!svg6img_!#4p&!sqf!{9'!wfb!%@&#!vPi6!sr%!}fe:!$<H+!}mg?!$=?,!}tllen_eq!$rYh7!ss&!vXe7lin_ge0!#5Dg!sr&!#>Fg<!ss'!$Kaixterm!%1pg=p!~A#aligned!x=h<!sx/!ubfe!sq$!wLg7!sq%!x@h;!sr&!|`k5xlo!#UDh4!sp#!#44e!zq#b!#44k7e!$JI/!#;P;max!w_b!u-#s!$K^j6e!ux[!vm7s!vml;e!#7w2!#8sa!vT-!szk;!yX,B!trlb!#:gp5xhi!},khi1!{DDin!t4cb2!t}h3xb2!v_hdea!#|_&!spa9!#5X#!#b5k!xG$!#7Dn2!#7Dk!w?h8!xx#!{mo2!{ml!uVh<!#\[#_byt!$Zj'!swa;!sw-!svmZ!#WWF7na!#WVeA!v0/!tD#'!u=g:!#Yo%_!$l@h9!su+!v2&!stO!#8A3!st'0!#=ae!#_r&!#J<g=!tg+!}9k@find_containing!wTh?!s{2!szg6is_f!%Wr'!$QU;neg!#Wza7am!$74,!zUbm!sp#!#Pt+!thebas!#j#g6am_le!#LN&!$1?5!$aV#!t2a>!~B,!zm,!%OY`4ama!%9a'!sqa5!wb$!%:Uishadow_of!#4|h!su+!#4-d5mkSrl!u[q!#4$g4ead!#TWe9split_li!$dJh!vL$!#JVg:!sq%!#7Ok!wD&!ue%ok!#7Oh!s{2!un&!#Jg;div!t?a;!t6#coversZ!u7g;!#dx%!w+k3KH!$<5g=!vw&!%rw#!wqh<!sx/!swgD!#>82!vbk>!#5c+!sykD!{c3!t#,k!t#`!#8S%2!xbotwin!xbq!sx$!}R&!$I8;s!#=Eb:vis!u3n9!su+!stgA!v{0!ynk2kn!#3<gnx!$5sg<!$v0#vars_l!swh5a_vi!yP+!$Qi5f!$N+#!#GXc_ghos!u$h7a_eager!srg8a_a!#S~k8!{5#c!u\j2p!%>yg6a_maps!w>jtotsz!z4jy!#|bh5a_br!%tNg4a_fd!ykjtidse!{Tkvmo!x0'!#:i`!%ud#!$GSg>!#8W+!#6gjA!#AF/!s|k7!tw#!#Jd'!sra;!sr&!%z]+!}Rcdd_!#9Uh;node_shdisj!svg?!sv-!uek7reg!#NC+!srb!#}a#u!$L{g3re!#\mg8mmap!#Y$+!ssa<!ss'!wDk<!#Y_%map!#i+i!sw-!svg=stack!%:}#!$4fi<!sx/!uihe_sp0_early!svhsaf!%K00!sva:!sv,!su%!#J%;6length!u5blit!$e?0!#5fa!#UL$!sqg@!{T/!#:@l!z`/!s|k=gran!$ow$!&,Hi<!sx/!swg?!zf-!#]Ckkn_!tv%!%t$$!#]Ch!s{2!szg9!%wy#cli!#9cgA!x\0!#XKk!vk3!wl{!$kAg:kn_rezero!#VDh!su+!tkhfixed_arg!#:th!su%in!sxlA!sx0!#>]+!#oQ`<!s|-m!#oX&!#^wg1!srn3!srn!&3Cg9budge!#j6+!sta6re!#yM+!u[a4vmop!#c;h>!}e,!#f~k!$n>+!#<5k!#GW#!{+'!|wh!sx0!|wk!w_%!$'qV!$CG2sr_up!yCn!{wh=!#PG#mprotec!#OQgA!sx0!#L}j;a!xK#match!#HIh!sv,!sug<!$W,&!#o+j!xQ%!%?:gA!$S_/!}vk<!$de&!swk?!xP-!szk!#Y]$mun!&o{'!trb!sv-!{@k=!&76+!%0Gi!#iN#her!$uuh!ui$un!#n3'!#9@a!su,!#]>mt!#]>j:after_ca!%kph8!#KR$!%&Fh@!$jx-!#JOl!$t%,!~zlsummary_!&H5j@!sw/!#_Hk!%9V'!}-j;copy!$+Nm:!sv,!su%!#?e^>z!#v6#_le_to_Z!v_i!%'Y%!zKm!$Jv1!s{h!w\-_!$Kr+!%SZ<to_na!'8w=m!&qR-!#`6#!&_<#ad!&1h,!#}#$7!s+#Def3seq!w1cblob_prefi!#dIg?!v42!~Up!t&#!~Up!t{$!~U+!w,<ma!%Qha;!#8M+!#NIg3NCS!#3`gx_memis!#Y'j5eadd!#~Wg>!%5T+!#C;k!xd'mi!tqh?!sv-!#92j8!#=n#ov!#86g7!ss&!srg:x_istrnc!}8i8x_sealed!~,p!tpoD!s{3!xQlSEALED_W!ssg6nt_!$,7'!#9Q'!&qS6eqb!#56;n!#r`b!tU#g!$-fh4!%z]+C7!soN!#?},8!'Ft%!'I5gA!#oU#!%|L%!tj#!#KugE!s|4!$+{khs_ni!&hShin_w!#_&h<!#H/#!sv%!#x#h!sw/!'+6-!%l=K1K!%l=L1!#6;ae_pg!#~ml4!su#!sog5!$$V#!sp%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsanPlanCore3APC~~~~~~hc4CEILhc7CEILMAX46Stdlib6ZArith6BinInt1Zn02le89OSSVerify6Proofsaboost_jsonafuzz_parse3libcAsanPlanCore3APC8WithSegs~~~~~~od6spiece37Corelib4Init9Datatypesu24boolu24listu23natu25falseod9listZ_eqb46Stdlib5Arith8PeanoNat3Nathi23eqbod5mkindu24trueod4amapu24negbod6is_fog36Stdlib5Lists4Listhma7forallbod7is_holeod4vmop79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~hp94exprod6VFixInod4VNewod5VProtod6VUnmapod3acs37Corelib5Lists7ListDefig93nthod4a_sshp94ELithp96s_regshp96kentryhp96s_knowhp94s_pchp96s_nexthp99sym_stateu24Noneu23nilhp93SSRhp95saddrhp96sentryod5mk_ssod7with_sshp96sr_updu23appod2knod6set_kn37Corelib4Init3Natisa3addu26option3h5LinuxProcessSemantics5Riscv5Instriuc5aluopiuc5mulopu24Somehp95two64n06modulood6lit_ofod3regiuc7ALU_ADDhp95mkAluiuc7ALU_SUBiuc5M_MULhp94mkMd08positive46Stdlib6PArith6BinPos3Posjo4bof_succ_natu24unithp95ptreeod4vkeyhp96pt_getu24andbodfexpr_all_live_thp98expr_eqbn03addn03lebhp96a_basen06of_natodcexpr_vars_ltoddsaddr_vars_ltu24produ23fstu23sndod3afdu24pairod7vmop_anod8vmop_allhp98sidecondod8fresh_okhp95carryhp95s_loghp9asym_execTXhp98facts_of79OSSVerify6Proofsaboost_jsonafuzz_parse3libbAxSymExec3B4AX2B~~~~~~kq94bctxkq96carryKkq93kixkq96mk_kixkq94mkbckq9csym_execTXBI37Corelib4Init5Logicli72eqod9run_blockoddrun_block_refod5cs_gchp99saddr_eqbn03eqbhp9eranges_apart_xn03subhi23lebn03ltbkq9franges_apart_xBodekentry_apart_bodfkentry_apart_bBhp95sprephp9eranges_apart_pkq9franges_apart_pBodfkentry_apart_bpodh0kentry_apart_bpBu23orbod6kimg_bhp98mk_sprephma6filterkq95bc_fkkq99mk_sprepBod9kn_unfillodakn_unfillBodakn_unfillMu24consod5kwr_bhp99kfill_cuthp98kunk_cuthp99kzero_cutkq9akfill_cutBkq99kunk_cutBkq9akzero_cutBod6havoc1od7havoc1Bod7havoc1pod8havoc1pBhma8flat_mapod8kn_havocod9kn_havocBkq94gvalhp94sp_Dhp96sp_rngkq9chull_in_sidehma7existsbhp96zlit64oddhavoc_verdictkq9bbase_rangeBkq95ei_brkq94ei_kkq95ei_kbkq94ei_mkq95einfokq93inbodfhavoc_fast_kindkq94EINFkq94ntabod9havocG_gokq96pt_maphma7Forall2od9kn_havocGod9kn_havocMhp93KWrhp94kcutkq95kcutBod7kwr_cutod8kwr_cutBod7cutout1od8cutout1Bod8cutout1pod9cutout1pBod9kn_cutoutodakn_cutoutBhp93xhiig93maphp99split_lithp93xlohp94KImgod9kimg_cut1hc6img_hihc6img_lohp94lreshp9bknow_lookupkq9cknow_lookupBod6kreadZod7kreadZBod7kread8eod8kread8eBod9kwritableodakwritableBodbkwritable_xodckwritable_xBod7kzero_xod8kzero_xBod7kfill_xod8kfill_xBodboff_image_xodcoff_image_xBhp9abase_rangekq94xhiBkq94xloBod6flat_xod7flat_xBhp97lin_ge0kq98lin_ge0Bod7len_eqbod8len_eqbBod4esubhp96ealignkq97ealignBodcpage_alignedoddpage_alignedBhp96erangehp93linhp96lin_ofhp99lin_rangeod3NCSodccaller_savedodakn_vars_ltod8sr_freshn03divn03mul04Nposod2pc35stdpp9bitvectorbdefinitionsqq62bv3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsqs9afetch_wordqs98is_ecallqq67Z_to_bvhp9alin_brangehp9alin_srangen03maxkq9blin_brangeBkq97erangeBkq9blin_srangeBod4xlo1od5xlo1Bn03minod4xhi1od5xhi1Bod3xb2od4xb2Bod4xlo2od5xlo2Bod4xhi2od5xhi2Bn04log2n03powodbkread_bytesodckread_bytesBod6add_knhp95KWordhp92SAhp9ezbytes_le_to_Zod3nxthp94EVarhp96KRangehi23ltbod4bumpod4eaddod6escaleodcresidue_factod7set_regisa3subu26lengthod5esizehp97xinsidehp98xinside0kq99xinside0Bkq98xinsideBod9xinside_codaxinside_cBodffind_containingodh0find_containingBod9shadow_ofodashadow_ofBodfshadow_split_okodh0shadow_split_okBodcshadow_factsoddshadow_factsBodcshadow_twinsoddshadow_twinsBod9vis_twinsodavis_twinsBod7vis_addodbvis_add_refod5eaddzodedisj_side_factod9find_disjn03oppod6zcdivpod9gap_excl1od8gaps_cuthp9afind_rangehma9fold_leftod9gap_childod7gaps_ofod9gaps_lohiodbnode_shdisjodfnode_shdisj_refod7page_upod7reg_litod8mmap_lenodcmmap_len_refodbinside_mapsodcinside_mapsBodbe_sp0_earlyhc3KHIhcashadow_offu21Sod6coversodblit_entriesodcstack_side_xoddstack_side_xBodasafe_rangeodbsafe_rangeBodcgrant_keep_boddgrant_keep_bBod9kimg_clipodfkn_grant_filterodh0kn_grant_filterBodh0kn_grant_filterMhp95KDisjodae_pg_earlyod4SHLOod9kn_rezeroodakn_rezeroBoddfixed_in_argsodh1fixed_in_args_refodcfixed_in_armoddmmap_fixed_inodh1mmap_fixed_in_refodaENOMEM_RETod6set_pcodfmmap_fixed_freeod9mmap_nullod9KNONELAZYod7KRWLAZYod5KNONEod3KRWod9mmap_gateod6refuseod4ArmEod4ArmFod4ArmGoddnode_mprotectodh1node_mprotect_refodaamap_matchodbamap_matchBodbnode_munmapodfnode_munmap_refn04landod2AMod4KFOGodanode_unvisodenode_unvis_refodcsummary_fillodh0summary_fill_refodacopy_factsodbcopy_factsBhp95KBlobhma4findodcsummary_copyodh0summary_copy_refodbsummary_mizodfsummary_miz_refod7img_covod8img_covBodh0summary_istrncpyodh4summary_istrncpy_refig93seqod4V_S1od4V_S2od4V_S3od4e_pgod6V_ARGCod5e_sp0od6V_ENVCod6e_envpod6e_auxvod4V_L0od6e_str0od3V_Wod5e_sp8iuc8ALU_SLTUod6e_str1hp94EAluhp93EMdhc9x_envscanhcbx_envscan_khc7x_smearod8kimg_cuthc8x_pnscanhcax_pnscan_kod8kw_argv1od8e_argv1wodakentry_eqb36Stdlib4Bool4Boolhit53eqbod9mkind_eqbod6esubsthp95a_offod6asubsthp96KAlignhp95KFillhp94KUnkhp95KZerood6FdFileod6nt_getod6nt_setod7erenameod7arenameod9evars_allod5emaxvod6csmaxvodacsvars_allod6mk_bwdod6mk_fwdod9rename_cshi23maxod8evars_food9csvars_foodbnumber_fromodbcompact_mapodbnode_renameod7cover_xodbsaddr_eqb_hodckentry_eqb_hod7kflat_hodh0kimg_sub_coveredodckunk_coveredodakn_incl1_hod7loopctxod5shapeiuc4ffmtiuc5instriuc6awidthiuc5csropiuc7fcvt_tyiuc5msizehp96sr_getiuc5amoopiucbbranch_condiuc6fariopiuc6fcmpopiuc5fmaopiuc9fminmaxopiuc6fmvdiriuc6fsgnophp9acond_probehp9bitab_lookupod9entails_hod9diff_regshi26eq_dechma5nodupiuc5BC_EQhp9ddecide_branchodarespell_okod5hw_good4hullod5kfoot69OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec3~~~~~~hloa8existsbLodbhull_covershp96e_addrod6in_winhp97e_widthodh1range_apart_hullsodh5range_apart_hulls_refodbexpr_vars_todcfill_in_winsodh0fill_in_wins_refod7hull_wfoddhulls_vars_ltodh0wins_apart_hullshcastops_morehc9x_imemcpyhc9x_imemsethc8x_memcpyhcbx_memiszerohc8x_memsethp94itabodh2mk_itab_ranges_acchp96PTLeafhc6e_auxvhcae_atrandomhc6e_auxbhc6atablehc4auxwhc5e_sp0hc5V_UIDhc6V_ARGChc4V_HWhc8BRK_ASLRhc5V_BRKhc6V_ENVChc4V_L0hc4V_L1hc4V_S1hc4V_S2hc4V_S3hc3V_Whc8e_argv1whc6e_atr8hc4e_pghc5e_sp8hc6e_str0hc5eaddzhc8kw_argv1hc9ph_addr_zhc8ph_ent_zhc8ph_num_zhc6rw_lenhc5rw_lohc6e_atrbhc5K_RNDhc9atr_entryhccinit_kn_withig96repeathc4esubhc5e_stkhc8e_stklenhc3acshc8vis_costhc3ACShc5FdStdhc9MBASE_MINhc3NX0hcaSTKLEN_MAXhc7a_entryhc4amaphc6escalehc9init_regshc8init_vishc5mk_sshc4vmophch0init_acs_of_withhc7init_knhcae_pg_earlyhcbe_sp0_early3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehpgb7Segment" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)

Module APC.
Import AX2. Import AX2B.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition CEIL : Z := 0x7fff7f800000.
(* [comment removed for export] *)
Definition CEILMAX : Z := 0x7fffff800000.
Lemma CEIL_le_CEILMAX : ltac2:(zQ "30!lf!m6!o8@2$2$0$1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) [] "##'hh01mh11nh21Hp;2p;3p;1p-1R0p10000R1p4p710p9P0P!s2$2!s3/31!s4%!sS$N!sS+8!sS/8g000kj29Tg001Hj38!s/$bj23Tg002>j2;!s/$^j10Tg003Cj15!s/$aj12Tg004Fj2:Tf0R1#2#2p=<%2!s0$#2p=1%01#0p=7!s-$#0#0p=6!s2+!s$'p=4g004`R0g005>g005YR2f1R3/91g0069R438f2R5/33[R613311953=824R7[f3/35\71;31P3n200!v;$0012!s-%0X00W1P6^00^10P!sx$Y#<#1#1#1R1#0!s0$0#7#6#4#4#5%21!s931:24O3b2g007>g008G'3eo"). Qed.
(* [comment removed for export] *)
Definition KHI : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition FLOOR : Z := 0x2aaaaaaab000.
(* [comment removed for export] *)
Definition MBASE_MIN : Z := 0x154555557000.
(* [comment removed for export] *)
Definition PID_MAX : Z := 4194304.

Record atable : Type := AT {
  img_lo : Z; img_hi : Z;          (* [comment removed for export] *)
  n_res : nat;                     (* [comment removed for export] *)
  shadow_off : Z;                  (* [comment removed for export] *)
  a_entry : Z;                     (* [comment removed for export] *)
  rw_lo : Z; rw_len : Z;           (* [comment removed for export] *)
  ph_addr_z : Z; ph_ent_z : Z; ph_num_z : Z;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  x_imemset : Z; x_imemcpy : Z; x_memset : Z; x_memcpy : Z; x_memiszero : Z;
  (* [comment removed for export] *)
  x_istrncpy : Z; x_sealed : Z; x_popfree : Z;
  (* [comment removed for export] *)
  x_smear : Z;
  (* [comment removed for export] *)
  x_sniff : Z; sniff_tab : Z; sniff_cell : Z;
  (* [comment removed for export] *)
  x_envscan : Z; x_envscan_k : Z; x_pnscan : Z; x_pnscan_k : Z;
  stops_more : list Z              (* [comment removed for export] *)
}.

Section WithSegs.
Variable segs : ltac2:(zQ "20!hg1!hpk0@1$0$1").
Variable IT : ltac2:(zQ "10!hmt6$0").
Variable A : ltac2:(zQ "10!hnhd$0").
Variable nx0 : nat.     (* [comment removed for export] *)
Variable LIMIT : Z.     (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive spiece : Type := SPLit (bs : list Z) | SPBlob (k : nat).

Inductive shape : Type :=
| SNil
| SExit (code : Z)
| SEmitP (fd : Z) (ps : list spiece) (s : shape)   (* [comment removed for export] *)
| SAlt2 (a b : shape)
| SCase (e : expr) (mid : Z) (s1 s2 : shape)
| SHole (h : nat)                            (* [comment removed for export] *)
| SNext.                                     (* [comment removed for export] *)

Fixpoint listZ_eqb (x y : list Z) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => Z.eqb a b && listZ_eqb x' y' | _, _ => false end.
Definition spiece_eqb : ltac2:(zQ "20!t9!va>1x$0>1y$0$1") := ltac2:(zQ "80!t9!va!hg1!hg8!h9!hge!hh6!hjd\1x$0\1y$0M0\1x$0$1^2\1a@1$2$4M0\1y$0$1^2\1b@1$2$4@2$6^2^1\1k$3$5\1k$3M0\1y$0$1^2\2bs@1$2$4$5\2k'$3@2$7^2^1").
Fixpoint spieces_eqb (x y : list spiece) : bool :=
  match x, y with [], [] => true | a :: x', b :: y' => spiece_eqb a b && spieces_eqb x' y' | _, _ => false end.

(* [comment removed for export] *)
Fixpoint shape_eqb_h (x y : shape) : bool :=
  match x, y with
  | SNil, SNil => true
  | SExit c, SExit c' => Z.eqb c c'
  | SEmitP fd ps s, SEmitP fd' ps' s' => Z.eqb fd fd' && spieces_eqb ps ps' && shape_eqb_h s s'
  | SAlt2 a b, SAlt2 a' b' => shape_eqb_h a a' && shape_eqb_h b b'
  | SCase e m a b, SCase e' m' a' b' => expr_eqb e e' && Z.eqb m m' && shape_eqb_h a a' && shape_eqb_h b b'
  | SHole _, SHole _ => true
  | SNext, SNext => true
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mkind : Type := KRW | KRWLAZY | KNONE | KNONELAZY | KFOG | KHOLE.   (* [comment removed for export] *)

Definition mkind_eqb : ltac2:(zQ "20!hk4!va>1a$0>1b$0$1") := ltac2:(zQ "40!hge!hk4!va!hkc\1a$1\1b$1M1\1a$1$2^2M1\1b$1$2^1$3$0$0$0$0$0M1\1b$1$2^1$0$3$0$0$0$0M1\1b$1$2^1$0$0$3$0$0$0M1\1b$1$2^1$0$0$0$3$0$0M1\1b$1$2^1$0$0$0$0$3$0M1\1b$1$2^1$0$0$0$0$0$3").

(* [comment removed for export] *)
Record amap : Type := AM {
  am_base : expr;       (* [comment removed for export] *)
  am_len  : expr;       (* [comment removed for export] *)
  am_kind : mkind
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition is_tok_kind : ltac2:(zQ "20!va!hk4>1k$1$0") := ltac2:(zQ "40!hge!hk4!hkc!va\1k$1M1\1k$1$3^1$0$0$0$0$2$2").
Definition is_hole (m : amap) : bool := mkind_eqb (am_kind m) KHOLE.
Definition is_fog (m : amap) : bool := is_tok_kind (am_kind m).
Definition no_fog : ltac2:(zQ "30!va!hg1!hl3>2ms@1$1$2$0") := ltac2:(zQ "50!hl3!hg1!hla!hm1!hnd\2ms@1$1$0@3$4$0\1m$0@1$2@1$3^1^1").
Definition no_holes : ltac2:(zQ "30!va!hg1!hl3>2ms@1$1$2$0") := ltac2:(zQ "50!hl3!hg1!hla!ho8!hnd\2ms@1$1$0@3$4$0\1m$0@1$2@1$3^1^1").


(* [comment removed for export] *)
Inductive afd : Type :=
| FdStd                                   (* [comment removed for export] *)
| FdFile (k : nat) (len off : expr)       (* [comment removed for export] *)
| FdDir.                                  (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive vmop : Type :=
| VNew (k : mkind) (a n : expr)                    (* [comment removed for export] *)
| VFixIn (arm_noreserve prot_none : bool) (a n : expr)  (* [comment removed for export] *)
| VUnmap (a n : expr)                              (* [comment removed for export] *)
| VProt (a n : expr).                              (* [comment removed for export] *)
Definition vmop_map : ltac2:(zQ "20!hp2!hta>1f>0$1$1>1o$0$0") := ltac2:(zQ "80!hta!hp2!va!hu2!hub!hv2!hva!hk4\1f>0$0$0\1o$1M1\1o$1$1^1\1k$7\1a$0\1n$0@3$4^3@1^5^2@1^5^1\1x$2\1y$2\1a$0\1n$0@4$3^4^3@1^6^2@1^6^1\1a$0\1n$0@2$6@1^4^2@1^4^1\1a$0\1n$0@2$5@1^4^2@1^4^1").

Record acs : Type := ACS {
  a_ss    : sym_state;          (* [comment removed for export] *)
  a_maps  : list amap;          (* [comment removed for export] *)
  a_totsz : Z;                  (* [comment removed for export] *)
  a_ylo   : Z;                  (* [comment removed for export] *)
  a_eager : Z;                  (* [comment removed for export] *)
  a_vis   : list (expr * expr); (* [comment removed for export] *)
  a_ghost : list (expr * expr); (* [comment removed for export] *)
  a_abytes : Z;                 (* [comment removed for export] *)
  a_brk   : expr;               (* [comment removed for export] *)
  a_fd    : afd;
  a_tidset : bool;              (* [comment removed for export] *)
  a_vmops : list vmop           (* [comment removed for export] *)
}.

Definition reg : ltac2:(zQ "30!hg8!ig3!hta>2cs$1>1n$0$2") := ltac2:(zQ "70!hg8!ii0!ii7!ig3!iie!hta!ij6\2cs$3\1n$0@4$1$5^1@1$6@1$2^2@1$4Z").
Definition kn : ltac2:(zQ "30!hg1!ig3!ik0>2cs$1@1$0$2") := ltac2:(zQ "30!ii7!ig3!ika\2cs$1@1$2@1$0^1").
Definition pc : ltac2:(zQ "20!h9!ig3>2cs$1$0") := ltac2:(zQ "30!ii7!ig3!il4\2cs$1@1$2@1$0^1").
Definition nxt : ltac2:(zQ "20!hg8!ig3>2cs$1$0") := ltac2:(zQ "30!ii7!ig3!ilc\2cs$1@1$2@1$0^1").

Definition with_ss (cs : acs) (ss : sym_state) : acs :=
  ACS ss (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs).
Definition mk_ss : ltac2:(zQ "60!hg1!hg8!h9!hta!ik0!im6>1p$2>2sr@1$0$3>1k@1$0$4>2nx$1$5") := ltac2:(zQ "a0!hg1!in3!hg8!ina!h9!io0!hta!ik0!io7!ip0\1p$4\2sr@1$0$6\1k@1$0$7\2nx$2@6$5^4^3@1$3$9^2^1@1$1$8").
Definition set_reg : ltac2:(zQ "30!ig3!hg8!hta>2cs$0>1n$1>1e$2$0") := ltac2:(zQ "c0!hg8!ii7!ig3!ipa!iq2!hta!ika!ilc!il4!ij6!iqc!im6\2cs$2\1n$0\1e$5=2ss$b@1$1^3@2$4^4@4$3@1$8^1@3$a@1$9^1^3^2@1$6^1@1$7^1").
Definition set_pc : ltac2:(zQ "20!ig3!h9>2cs$0>1p$1$0") := ltac2:(zQ "90!h9!ii7!ig3!ipa!iq2!ika!ilc!ij6!im6\2cs$2\1p$0=2ss$8@1$1^2@2$4^3@4$3^2@1$7^1@1$5^1@1$6^1").
Definition set_kn : ltac2:(zQ "30!ig3!hg1!ik0>2cs$0>1k@1$1$2$0") := ltac2:(zQ "a0!hg1!ii7!ig3!ipa!iq2!ik0!ilc!il4!ij6!im6\2cs$2\1k@1$0$5=2ss$9@1$1^2@2$4^3@4$3@1$7^1@1$8^1^2@1$6^1").
Definition add_kn : ltac2:(zQ "30!ig3!hg1!ik0>2cs$0>1k@1$1$2$0") := ltac2:(zQ "60!ik0!ir6!hg1!ig3!irc!is1\2cs$3\1k@1$2$0@2$5^2@3$1$0^1@1$4^2").
Definition bump : ltac2:(zQ "20!ig3!hg8>2cs$0>1d$1$0") := ltac2:(zQ "b0!hg8!itc!ii7!ig3!ipa!iq2!ika!ilc!il4!ij6!im6\2cs$3\1d$0=2ss$a@1$2^2@2$5^3@4$4@1$8^1@1$9^1@1$6^1@2$1@1$7^1^2").
Definition set_regs : ltac2:(zQ "30!ig3!hg1!hta>2cs$0>2sr@1$1$2$0") := ltac2:(zQ "a0!hg1!ii7!ig3!ipa!iq2!hta!ika!ilc!il4!im6\2cs$2\2sr@1$0$5=2ss$9@1$1^2@2$4^3@4$3@1$8^1^2@1$6^1@1$7^1").

Definition lit_of : ltac2:(zQ "30!iu3!h9!hta>1e$2@1$0$1") := ltac2:(zQ "b0!hta!h9!in3!hg8!va!jh0!jh9!ji2!iu3!ji9!jj2\1e$0M0\1e$0@1$8$1^1\1z$1@2$7$1@2$a^1$9\1n$3@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2sx$4\2lo$3\1n$3\2e0$0@1$2$1\2sx$4\1k$3\1i$1\1n$3@1$2$1").
Definition reg_lit : ltac2:(zQ "40!hg8!iu3!h9!ig3>2cs$3>1n$0@1$1$2") := ltac2:(zQ "40!hg8!ig3!jjb!jk4\2cs$1\1n$0@1$2@2$3^2^1").

(* [comment removed for export] *)
Definition eadd : ltac2:(zQ "10!hta>1a$0>1b$0$0") := ltac2:(zQ "30!hta!jka!jl5\1a$0\1b$0@3$2$1^2^1").
Definition esub : ltac2:(zQ "10!hta>1a$0>1b$0$0") := ltac2:(zQ "30!hta!jle!jl5\1a$0\1b$0@3$2$1^2^1").
Definition escale : ltac2:(zQ "20!hta!h9>1c$1>1e$0$0") := ltac2:(zQ "50!h9!jm9!iie!hta!jn2\1c$0\1e$3@3$4$1@1$2^2^1").
Definition eaddz : ltac2:(zQ "20!hta!h9>1a$0>1z$1$0") := ltac2:(zQ "50!h9!jka!iie!hta!jl5\1a$3\1z$0@3$4$1^2@1$2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition vkey : ltac2:(zQ "20!hg8!jna>1n$0$1") := ltac2:(zQ "20!hg8!jpe\1n$0@1$1^1").
Fixpoint expr_vars_t (e : expr) (acc : ptree unit) : ptree unit :=
  match e with
  | ELit _ => acc
  | EVar n => pt_set (vkey n) tt acc
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_t x (expr_vars_t y acc)
  | EExt _ _ _ x => expr_vars_t x acc
  | EBlob _ _ _ _ => acc
  end.
Definition live_vars_t (cs : acs) : ptree unit :=
  let acc := fold_right expr_vars_t PTLeaf (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars_t (a_base a) (expr_vars_t v acc)
                                      | KZero a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KBlob a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KWr a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KFill a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KUnk a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars_t (am_base m) (expr_vars_t (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars_t l (expr_vars_t o acc) | _ => acc end in
  expr_vars_t (a_brk cs) acc.
Definition in_live_t : ltac2:(zQ "40!va!hg8!jqd!jr4>1t@1$3$2>1v$1$0") := ltac2:(zQ "90!jqd!iu3!va!hge!hg8!hkc!jrd!js4!jr4\1t@1$8$0\1v$4M1\1x@1$1$0$2@3$7$0^2@1$6^1\1u$0$5$3").
Fixpoint expr_all_live_t (t : ptree unit) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => if Nat.ltb n nx0 then true else in_live_t t n
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => if expr_all_live_t t x then expr_all_live_t t y else false
  | EExt _ _ _ x => expr_all_live_t t x
  | EBlob _ _ _ _ => true
  end.
Definition kn_gc_entry_t : ltac2:(zQ "60!va!jqd!h9!hta!ik0!jr4>3spb$3>3spk$2>1t@1$5$1>1K$4$0") := ltac2:(zQ "h3e!hta!hkc!hg8!h9!va!io7!jse!jh0!jh9!jt5!hla!ju7!jv3!jv9!ik0!jvf!jqd!jr4!kg9&@2$6@2$b^3^9@2$d@2$c^2^1^8&@1$a~0&\1n$3~1&\2sx$4\2lo$2\1n$2\1e$0$1&\2sx$4\2k0$2\1i$3\1n$2$1&M0\2n0$0$4^3~2\1n$2$1\2op$7\2a0$0\2b0$0$1\2op$7\2a0$0\2b0$0$1\2op$8\2a0$0\2b0$0$1\2op$8\2a0$0\2b0$0$1~3~4&\1k$3~5&\1b$0~6&M5\1a$5$4^2~7&\2n0$0~8&\1a$5~9&@2$6@2$b^3^a@2$d@2$c^2^1^9&@1$a~b&\1n$3~c\3spb$0\3spk$3\1t@1$h1$h0\1K$eMe\1K$e$4^1\1a$5\1w$2\1v$0M5\1a$5$4^3\1b$0\1k$3@1$a@2$6@2$b^2^9@2$d@2$c^1@1$h2^4^8~a\1a$5\2n0$0\2k0$2M5\1a$5$4^3\1b$0\1k$3M0\2n0$0$4^4~d\1n$2$1\2op$7\2a0$0\2b0$0$1\2op$7\2a0$0\2b0$0$1\2op$8\2a0$0\2b0$0$1\2op$8\2a0$0\2b0$0$1~3\2sx$4\2k1$2\1i$3\1n$2$1\2lo$3\2hi$3$1\1e$0\1m$3@2$9^4^2\1e$0\2lo$3\2hi$3@2$9^5^3\1a$5\1n$0$1\2a1$5\2n1$0\2a2$5\2n2$0@2$6@2$6@2$6@2$9^6@1$f^4@2$9^6^3@2$9^6@1$f^2@2$9^6^1\1a$5\2n0$0\1c$3M5\1a$5$4^3\1b$0\1k$3M0\2n0$0$4^4~d\1n$2$1\2op$7\2a0$0\2b0$0$1\2op$7\2a0$0\2b0$0$1\2op$8\2a0$0\2b0$0$1\2op$8\2a0$0\2b0$0$1~3~4~a").
Definition cs_gc (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars_t cs in
  set_kn cs (List.filter (kn_gc_entry_t spb spk live) (kn cs)).

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint expr_vars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar n => Nat.ltb n b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => expr_vars_lt b x && expr_vars_lt b y
  | EExt _ _ _ x => expr_vars_lt b x
  | EBlob _ _ _ _ => true
  end.
Definition saddr_vars_lt : ltac2:(zQ "30!va!hg8!io7>1b$1>1a$2$0") := ltac2:(zQ "40!hg8!kh2!jvf!io7\1b$0\1a$3@2$1^2@1$2^1").

(* [comment removed for export] *)
Fixpoint shape_vars_lt (b : nat) (s : shape) : bool :=
  match s with
  | SNil | SExit _ | SHole _ | SNext => true
  | SEmitP _ _ s' => shape_vars_lt b s'
  | SAlt2 x y => shape_vars_lt b x && shape_vars_lt b y
  | SCase e _ x y => expr_vars_lt b e && shape_vars_lt b x && shape_vars_lt b y
  end.
Definition kentry_vars_lt : ltac2:(zQ "30!va!hg8!ik0>1b$1>1K$2$0") := ltac2:(zQ "a2!kh2!hta!jse!ki1!io7!h9!hg8!ik0!va!hkc&\1n$1@2$2@2$3^4^2@2$0^4^1&\1a$4~0\1b$6\1K$7M7\1K$7$8^1\1a$4\1w$6\1v$1@2$2@2$3^5^3@2$0^5^1~1\1a$4\1n$1\1k$6@2$2@2$3^5^3@2$0^5^2\2lo$5\2hi$5$9\1e$1\1m$5@2$0^4^2\1e$1\2lo$5\2hi$5@2$0^5^3~1\2a1$4\2n1$1\2a2$4\2n2$1@2$2@2$2@2$2@2$3^6^4@2$0^6^3@2$3^6^2@2$0^6^1\1a$4\1n$1\1c$5@2$2@2$3^5^3@2$0^5^2~1").
Fixpoint sr_vars_lt (b : nat) (sr : list expr) : bool :=
  match sr with [] => true | e :: r => expr_vars_lt b e && sr_vars_lt b r end.
Fixpoint kn_vars_lt (b : nat) (k : list kentry) : bool :=
  match k with [] => true | K :: r => kentry_vars_lt b K && kn_vars_lt b r end.
Definition pairs_vars_lt : ltac2:(zQ "50!hta!va!hg1!hg8!kj1>1b$3>1l@1$2@2$4$0$0$1") := ltac2:(zQ "90!hta!kj1!kh2!jse!kj8!hg1!hg8!kje!hnd\1b$6\1l@1$5@2$1$0$0@3$8@2$1$0$0\1p@2$1$0$0@2$3@2$2^3@3$4$0$0^1@2$2^3@3$7$0$0^1^1").
Definition maps_vars_lt (b : nat) (ms : list amap) : bool :=
  forallb (fun m => expr_vars_lt b (am_base m) && expr_vars_lt b (am_len m)) ms.
Definition fd_vars_lt : ltac2:(zQ "30!va!hg8!kk4>1b$1>1f$2$0") := ltac2:(zQ "70!kk4!hg8!hkc!kh2!hta!jse!va\1b$1\1f$0M0\1f$0$6^1$2\1k$1\1l$4\1o$4@2$5@2$3^5^2@2$3^5^1$2").
(* [comment removed for export] *)
Definition vmop_an : ltac2:(zQ "30!hta!kj1!hp2>2op$2@2$1$0$0") := ltac2:(zQ "60!hta!kka!hp2!va!kj1!hk4\2op$2M2\2op$2@2$4$0$0^1\1k$5\1a$0\1n$0@4$1$0$0^2^1\darm_noreserve$3\9prot_none$3\1a$0\1n$0@4$1$0$0^2^1\1a$0\1n$0@4$1$0$0^2^1\1a$0\1n$0@4$1$0$0^2^1").
Definition vmop_all : ltac2:(zQ "30!va!hp2!hta>1P>0$2$0>2op$1$0") := ltac2:(zQ "70!hta!kl1!jse!va!kj8!kje!hp2\1P>0$0$3\2op$6@2$2@1^2@3$4$0$0@1$1^1@1^2@3$5$0$0@1$1^1").
Definition vmop_vars_lt : ltac2:(zQ "30!va!hg8!hp2>1b$1>2op$2$0") := ltac2:(zQ "40!hg8!kh2!hp2!klb\1b$0\2op$2@2$3@1$1^2^1").
(* [comment removed for export] *)
Definition fresh_ok (cs : acs) : bool :=
  let v := nxt cs in
  sr_vars_lt v (s_regs (a_ss cs)) && kn_vars_lt v (kn cs)
  && maps_vars_lt v (a_maps cs) && pairs_vars_lt v (a_vis cs) && pairs_vars_lt v (a_ghost cs)
  && expr_vars_lt v (a_brk cs) && fd_vars_lt v (a_fd cs) && forallb (vmop_vars_lt v) (a_vmops cs) && Nat.leb nx0 v.

(* [comment removed for export] *)
Definition run_block_ref : ltac2:(zQ "50!hg8!ig3!hg1!iu3!h9>1K$0>4fuel$0>5stops@1$2$4>2cs$1@1$3$1") := ltac2:(zQ "hc0!hg1!ig3!km6!kj1!va!iu3!ik0!in3!hg8!ina!ika!ilc!il4!ij6!im6!ji2!hkc!h9!ii7!kn2!ipa!iq2!io0!knd!ko6!io7!ip0!kof\1K$8\4fuel$8\5stops@1$0$h1\2cs$1M4\0$4@1$5$1@1$h3^1=2ss$e@1$h2^1=3ss'$e@7$hb?4segs?2IT^5^4$h0^3@6$h6@1$c^1@1$d^1@1$9$ha@1$a^1@1$b^1@1$7$h9M3\1x@2$3@2$3@1$0$6@1$0$2@1$0$4@1$5$1@3$h7@1$h8^1@1$a^1@1$9$4\1p@2$3@1$0$6@1$0$2\1l@1$0$4M3\1p@2$3@1$0$6@1$0$2@1$5$1^2\3kn'@1$0$6\2l0@1$0$2M0\2l0@1$0$2@1$5$1^1@2$f$1@2$h5^7@4$h4@1$c^5@1$d^5^2@1$b^5\1s$2\2l1@1$0$2@1$7$1@1$7$1").
(* [comment removed for export] *)
Definition run_block : ltac2:(zQ "50!hg8!ig3!hg1!iu3!h9>1K$0>4fuel$0>5stops@1$2$4>2cs$1@1$3$1") := ltac2:(zQ "i10!hg1!ig3!km6!kj1!va!iu3!ik0!ika!in3!hg8!ina!ilc!il4!ij6!im6!ji2!hkc!h9!ii7!kn2!ipa!iq2!io0!kpd!ko6!io7!ip0!kuc!kv4!kve!lg5!lgf!lh7\1K$9\4fuel$9\5stops@1$0$h1\2cs$1M4\0$4@1$5$1@1$h3^1=2ss$e@1$h2^1=2bc$hb@1$hf@1$h7@1$7^1=2kx$hd@1$he@1$7^2=3ss'$e@9$i0?4segs^2^1?2IT^7^6$h0^5@6$h6@1$c^3@1$d^3@1$a$ha@1$7^3@1$b^3@1$8$h9M3\1x@2$3@2$3@1$0$6@1$0$2@1$0$4@1$5$1@4$hc^3@1$h8^1@1$7^1@1$a$4\1p@2$3@1$0$6@1$0$2\1l@1$0$4M3\1p@2$3@1$0$6@1$0$2@1$5$1^2\3kn'@1$0$6\2l0@1$0$2M0\2l0@1$0$2@1$5$1^1@2$f$1@2$h5^9@4$h4@1$c^5@1$d^5^2@1$b^5\1s$2\2l1@1$0$2@1$8$1@1$8$1").
Lemma run_block_eq : ltac2:(zQ "80!hg8!ig3!hg1!iu3!ljb!h9!lk1!lkd>1K$0>4fuel$0>5stops@1$2$5>2cs$1@3$4@1$3$1@4$6^4^3^2^1@4$7^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##D`p'0h02knh11Kh21bi001bh32bch42csh52fkh64fuelh75hintsh85lemmah93logh:1pi011ph;1si021sh<5stopsi033kn'i041li052l0i062l1i071xp;1p;2p;6p;9p;4p;7p;3p;@p-1R0p1009SR1p4p710p8P0P!s2$2!s3%p100:0!s73N!s73m!se'p100;Ip4p70R0g00<Q!t%/g00=>R2!s7,p100=nR3!sv-P3!sE1>b!sf0?RR0!t;/@L!sd+R4g00A[R5!sF/B9!t[%6p100CB!sr+!s6$DKR7!s8,P7!tU,6!tU-6P4p8g00EVR4j1BTg00F6j1\Tg00GCj1W!s/$eR6j2KTg00HEj1>Tg00INj10Tg00JWR3j17Tg00KbR7j18Tg00Lkj1DTg00N6j13Tg00O=j12Tg00PFj1I!s/$fj11Tg00Qoj1MTg00RQj6ATg00S_l9ETg00U0j1@Tg00V8R8j4<Tg00WCj4;Tg00XMj2=Tg00YYj7?Tg00Zfj3LTg001Hj35j16TP2j1VTg00[nj4:Tg00\Uj1HTg00]Dj44Tg00^;j3FTg00_1j1U!s/$`j6STP1j7Jl@RTg00`Kj2CTg00a7j6QTP0l9P!s5$Tj7OTg004Fj2GTg00bhj3TTP5j6NTg00d6l9[Tg00eJj4ZTg00fXj4YTg00gjj2XTg00hLR5f0R0'Xp=9g00iVR1g004`#B%\0g005YR2P2%W5R9P2P9P0P6g00j5#BR:g00k@R;#BR<'KR=%B2R>P9f2R?#>R@#0RA#7RB#8RCp,4segsRDPC%DAp,2ITREf5RFf4RGg0069RHf3RI%3@%2@g00lMRJ#IRKPA%1@g00mX#MR@EARLM9ERM#@%0M%I2RMC<P6P:P<P9f1RNP4P;P9P0f6ROPD%>ORP#0RQ#7#8%DQPEf9RRf8RSPHf7RT%3P%2PPKPQ%1PP@EARPM9ERQ#3%2QPN%1QC;'=#9%M5RQn10110500020020102106n2001101000120103105!s:&7!s:'1104PQn!sK$!sd$100!vi'P=P>P9PDPEPFPGPHPIPLF?RL#@R2%0LRL;LM!uV'P!uT+!sV$RPSPHPTPPF?RP#3%2PPN%1PC;,=O#9P!t~MRP!u$7RU!u&000035P0g00nbRV!tO$GPIPHP?%>NRW#3%2WPK%0WRX%1W!vj$WF?RY!uY+C%@0%00P!ww-!uG,%3G%2GPN%1G!u6U!u47=59UX;V%0YRV%0W55:P9%69%V9!t_,P2PLPMC<RZP!ux8!sP'%7LR[#8R\!sW+]!sW91K=>R^P!t1,0!x%9f:PRPHPS%>TRR#3%2RPK%0R%1RP@EAF?!s;'N%1RC;,=T!v,dV^PZP]g0100R]%BJRJP^^7>RZ^0:RR]9R_]3R`P]P_%6]RaPJPR%6JP:PZ%6:RbP>P^%6>%6^RcC:RdC:ReC:RfC:RgP]P_PfPJPRPeP:PZPdP>P^Pc%H^C4!s$%9F`gP8PCP\P]^5:R\P:P]PbPaC:RC!s2$a%H]C49F\CP7PBP[P:^0:R[P:P:PbPbC:RB!s2%%H:C49F[BP3PAPL!s9$U:PLPAP0ESFJFJP2P21CJ2PLPL1C:LPMPM1C>MM@REQPUPU1C9UM9PW8!{'/PWFOP^%@YRY?LVMRL!x2-P!yw<:^!sM+L!}\:SPTPHPO%>FRL#3%2LPK%0LRK%1L!|3$@!~L$!s?$N%1LC;,=F!x]dRL,G9%7V#8PYPVPMC<ATYVMENO2PD%7X#8RY%DX!uu/M9E!~5$!s;01G:XM9[EN!u]+Y%@V%0V!}|9PD%7K#8%DK!uo,P@M9ER@#3%2@PN%1@!uXi=59Le1G9Qn01!sS$!sh$0b2PIP?PNP0CZ!s0+Y559eX45W<X61W1o"). Qed.

Definition run_block_gc : ltac2:(zQ "50!hg8!ig3!hg1!iu3!h9>1K$0>4fuel$0>5stops@1$2$4>2cs$1@1$3$1") := ltac2:(zQ "90!ig3!iu3!hg8!in3!ji2!hg1!h9!lld!lk1\1K$2\4fuel$2\5stops@1$5$6\2cs$0M1\1x@1$1$0@1$1$0@4$8^4^3^2^1\3cs'$0@2$4$0@1$7^1@1$3$0").

Local Open Scope lzb_scope.
Definition kentry_eqb : ltac2:(zQ "20!ik0!va>1x$0>1y$0$1") := ltac2:(zQ "c3!hta!hge!io7!h9!ik0!hg8!jse!va!ju7!lm5!ln2!hjd&\2a1$2\2n1$0\2a2$2\2n2$0$1&\2n'$0@2$6@2$9^4^2@2$8^3^1&\2a'$2~1\1x$4\1y$4M4\1x$4$7^2\1a$2\1w$5\1v$0M4\1y$4$7^4\2a'$2\2w'$5\2v'$0@2$6@2$6@2$9^6^3@2$b^5^2@2$8^4^1\2a0$2\1n$0$1\2a0$2\1n$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\1n$0$1~0\2a0$2\1n$0\1c$3$1\2a0$2\1n$0$1\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$0$1~2\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a0$2\2n0$0\1c$3$1\2a0$2\2n0$0$1\1a$2\1n$0\1k$5M4\1y$4$7^4\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a'$2\2n'$0\2k'$5@2$6@2$6@2$9^6^3@2$8^5^2@2$b^4^1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a0$2\2n0$0\1c$3$1\2a0$2\2n0$0$1\2lo$3\2hi$3M4\1y$4$7^3\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\3lo'$3\3hi'$3@2$6@2$a^4^2@2$a^3^1\1e$0\1m$3$1\1e$0\3lo0$3\3hi0$3$1\1a$2\1n$0$1~0\1a$2\1n$0\1c$3$1\1a$2\1n$0$1\1e$0\1m$3M4\1y$4$7^3\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\2lo$3\2hi$3$1\2e'$0\2m'$3@2$6@2$8^4^2@2$a^3^1\2e0$0\2lo$3\2hi$3$1\1a$2\1n$0$1~0\1a$2\1n$0\1c$3$1\1a$2\1n$0$1\1e$0\2lo$3\2hi$3M4\1y$4$7^4\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\3lo0$3\3hi0$3$1\2e0$0\1m$3$1\2e'$0\3lo'$3\3hi'$3@2$6@2$6@2$8^6^3@2$a^5^2@2$a^4^1\1a$2\1n$0$1~0\1a$2\1n$0\1c$3$1\1a$2\1n$0$1\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1~2~0\2a0$2\2n0$0\1c$3$1\2a0$2\2n0$0$1\2a1$2\2n1$0\2a2$2\2n2$0M4\1y$4$7^5\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$1\3a1'$2\3n1'$0\3a2'$2\3n2'$0@2$6@2$6@2$6@2$9^8^4@2$8^7^3@2$9^6^2@2$8^5^1\1a$2\1n$0\1c$3$1\1a$2\1n$0$1\1a$2\1n$0\1c$3M4\1y$4$7^4\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a'$2\2n'$0\2c'$3@2$6@2$6@2$9^6^3@2$8^5^2@2$a^4^1\2a0$2\2n0$0$1\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a0$2\2n0$0\1c$3$1~2").
Local Close Scope lzb_scope.

Definition amap_eqb (x y : amap) : bool :=
  expr_eqb (am_base x) (am_base y) && expr_eqb (am_len x) (am_len y) && mkind_eqb (am_kind x) (am_kind y).

Fixpoint list_eqb {T : Type} (eqb : T -> T -> bool) (x y : list T) : bool :=
  match x, y with
  | [], [] => true
  | a :: x', b :: y' => eqb a b && list_eqb eqb x' y'
  | _, _ => false
  end.

Definition pair_eqb : ltac2:(zQ "30!hta!kj1!va>1x@2$1$0$0>1y@2$1$0$0$2") := ltac2:(zQ "60!hta!kj8!kj1!kje!ju7!jse\1x@2$2$0$0\1y@2$2$0$0@2$5@2$4@3$1$0$0^2@3$1$0$0^1@2$4@3$3$0$0^2@3$3$0$0^1").

Definition afd_eqb : ltac2:(zQ "20!kk4!va>1x$0>1y$0$1") := ltac2:(zQ "90!kk4!hta!hge!va!hg8!jse!hkc!ju7!hjd\1x$0\1y$0M0\1x$0$3^2M0\1y$0$3^1$6\1k$4\3len$1\3off$1$2$2\1k$4\1l$1\1o$1M0\1y$0$3^4$2\2k'$4\2l'$1\2o'$1@2$5@2$5@2$8^6^3@2$7^5^2@2$7^4^1$2M0\1y$0$3^1$2\1k$4\3len$1\3off$1$2$6").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition kentry_apart_b : ltac2:(zQ "50!hta!ik0!va!hg1!h9>5allkn@1$3$1>2ub$0>2uk$4>2un$0>1K$1$2") := ltac2:(zQ "h16!io7!hta!h9!va!ln8!jse!ik0!hkc!iie!hg8!jv9!loa!hg1!ji9!lp0!lp7!kg9&\1b$1\1k$2@7$4^9^8^7^6^2^1^3&M0\1a$0$3^2~0&\1l$1~1&\1a$0~2&\1b$1\1k$2@7$4^a^9^8^7^2^1^4&M0\1a$0$3^3~4\5allkn@1$c$6\2ub$1\2uk$2\2un$1\1K$6M6\1K$6$3^1\1a$0\1w$9\1v$1M0\1a$0$3^3\1b$1\1k$2@2$5@2$e^4N8@7$4^a^9^8^7^2^1@1$8@1$h0^4~3\1a$0\1l$1\2k0$9~5\2lo$2\2hi$2@2$5@2$5@2$5@2$aZ^2@2$a^2^1@2$f@2$b^1^2$d@7$4^7^6^5^4@1$8Z^2@1$8@2$b^1^2\1e$1\1m$2$7\1e$1\2lo$2\2hi$2$7\1a$0\1n$1~1\2a1$0\2n1$1\2a2$0\2n2$1$7\1a$0\1l$1\1c$2~5~3").

Local Open Scope lzb_scope.
Definition kentry_apart_bB : ltac2:(zQ "50!hta!va!h9!ik0!kuc>2bc$4>2ub$0>2uk$2>2un$0>1K$3$1") := ltac2:(zQ "h16!io7!hta!h9!va!lpd!jse!hkc!iie!ik0!hg8!jv9!loa!ji9!kuc!lp0!lp7!kg9&\1b$1\1k$2@7$4^9^8^7^6^2^1^3&M0\1a$0$3^2~0&\1l$1~1&\1a$0~2&\1b$1\1k$2@7$4^a^9^8^7^2^1^4&M0\1a$0$3^3~4\2bc$d\2ub$1\2uk$2\2un$1\1K$8M8\1K$8$3^1\1a$0\1w$9\1v$1M0\1a$0$3^3\1b$1\1k$2@2$5@2$e^4N8@7$4^a^9^8^7^2^1@1$7@1$h0^4~3\1a$0\1l$1\2k0$9~5\2lo$2\2hi$2@2$5@2$5@2$5@2$aZ^2@2$a^2^1@2$f@2$b^1^2$c@7$4^7^6^5^4@1$7Z^2@1$7@2$b^1^2\1e$1\1m$2$6\1e$1\2lo$2\2hi$2$6\1a$0\1n$1~1\2a1$0\2n1$1\2a2$0\2n2$1$6\1a$0\1l$1\1c$2~5~3").
Local Close Scope lzb_scope.

Lemma kentry_apart_bB_eqf : ltac2:(zQ "90!hta!ik0!va!hg1!ljb!h9!lr0!ls1!lgf>2fk@1$3$1@3$4>2ub$0>2uk$5>2un$0>1K$1$2@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##89p'0h01Ki001Kh11bi011bh22b1h32b2h42fkh52k1h62k2h72n1i022n1h82n2i032n2h92ukh:2unh;1xh<2x0h=2x1h>2x2i041ai052a1i062a2i071ci081ei092hii0:1ki0;2k0i0<1li0=2loi0>1mi0?1ni0@1vi0A1wp;1p;2p;3p;4p;7p;6p;5g00EVj1KTg00Kbj13Tg011;j1>j2Jj3?j4<j5ETg012Oj19j2Hj3=j4;j5FTg013bj18j70Tg0153j11!s/$Rj2:Tg0162j1I!s/$Rj15Tg017[j22Tg000kj27Tg0189j2G!s/$Vj2@Tg001Hj36Tg004Fj2ATg0193j1BTg01:Gj1CTg00A[j6DTg01;_j54Tg00j5R0#Kg01<aR1g004`R2g005YR3^00R4^:1R5]9f0R6#3#>%96P2P5f1R5#3/J61H56P1P4f2R4#3??56A=456P0P3f3R7#3P4P5P6C<P7!s0&;P3^81^62^31^71^52^21R8f4R9#8P0P3P5g00mXR:P3P4g01=j#1!s$1,:7R;f5R<f9R=f8R>f7R?P5P6%I7#5R@O6'2n0110400012010110:P:P3P5P9P>P?f6RAP5P6P4O6!sP5RB!sR$4P<P=P>P!t%$P7!sP8Cg01>IRD/751756'21G65REg01>g'@'2RFP4PAP<P9%5DRDP5%5EREO6'2g0069RGPGPBPGPCPB!t+$0000:3010410A10@2!s1%<!s9&<10;2010=1092010810>3!s-%!s9'410?40105102106103!sb,7!su'!w-%!u\%f:RB!u^-@F0,2;!v]<!sO%!v[&F0!v17!v[&!s{/7!sP8B!sp$<P9PDP5PEF0,2FPG!v+$GPBPC!v0~!v04563X1!z>%6!u7&!ua/!v4B!sO%<!v4>;!s{6!v49!v2'7!v43;PGP?P;!v4~!v44,A3%39R;#B%C9EDP;!}}'DE!tp$!s2%F563eX>0D4X=1D4X<2D4X;1D4W4o"). Qed.
#[local] Hint Rewrite kentry_apart_bB_eqf : bceq.


(* [comment removed for export] *)
Definition kentry_apart_bp : ltac2:(zQ "60!hta!ik0!va!hg1!h9!lt3>5allkn@1$3$1>2sp$5>2ub$0>2uk$4>2un$0>1K$1$2") := ltac2:(zQ "h28!io7!hta!h9!va!ltc!jse!ik0!hkc!iie!hg8!jv9!loa!hg1!lt3!ji9!lp0!lp7!kg9&\1k$2@8$4^a^9^8^7^6^2^1^3&\1b$1~0&M0\1a$0$3^2~1&\1l$1~2&\1a$0~3&\1k$2@8$4^b^a^9^8^7^2^1^4&\1b$1~5&M0\1a$0$3^3~6\5allkn@1$c$6\2sp$d\2ub$1\2uk$2\2un$1\1K$6M6\1K$6$3^1\1a$0\1w$9\1v$1M0\1a$0$3^3\1b$1\1k$2@2$5@2$f^4N8@8$4^b^a^9^8^7^2^1@1$8@1$h1^4~4\1a$0\1l$1\2k0$9~7\2lo$2\2hi$2@2$5@2$5@2$5@2$aZ^2@2$a^2^1@2$h0@2$b^1^2$e@8$4^8^7^6^5^4@1$8Z^2@1$8@2$b^1^2\1e$1\1m$2$7\1e$1\2lo$2\2hi$2$7\1a$0\1n$1~2\2a1$0\2n1$1\2a2$0\2n2$1$7\1a$0\1l$1\1c$2~7~4").

Local Open Scope lzb_scope.
Definition kentry_apart_bpB : ltac2:(zQ "60!hta!va!h9!ik0!lt3!kuc>2bc$5>2sp$4>2ub$0>2uk$2>2un$0>1K$3$1") := ltac2:(zQ "h28!io7!hta!h9!va!lue!jse!hkc!iie!ik0!hg8!jv9!loa!lt3!ji9!kuc!lp0!lp7!kg9&\1k$2@8$4^a^9^8^7^6^2^1^3&\1b$1~0&M0\1a$0$3^2~1&\1l$1~2&\1a$0~3&\1k$2@8$4^b^a^9^8^7^2^1^4&\1b$1~5&M0\1a$0$3^3~6\2bc$e\2sp$c\2ub$1\2uk$2\2un$1\1K$8M8\1K$8$3^1\1a$0\1w$9\1v$1M0\1a$0$3^3\1b$1\1k$2@2$5@2$f^4N8@8$4^b^a^9^8^7^2^1@1$7@1$h1^4~4\1a$0\1l$1\2k0$9~7\2lo$2\2hi$2@2$5@2$5@2$5@2$aZ^2@2$a^2^1@2$h0@2$b^1^2$d@8$4^8^7^6^5^4@1$7Z^2@1$7@2$b^1^2\1e$1\1m$2$6\1e$1\2lo$2\2hi$2$6\1a$0\1n$1~2\2a1$0\2n1$1\2a2$0\2n2$1$6\1a$0\1l$1\1c$2~7~4").
Local Close Scope lzb_scope.

Lemma kentry_apart_bpB_eqf : ltac2:(zQ "a0!hta!ik0!va!hg1!ljb!h9!mg1!mh3!lt3!lgf>2fk@1$3$1@3$4>2sp$8>2ub$0>2uk$5>2un$0>1K$1$2@1$7@1$9^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##9Ep'0h01Ki001Kh11bi011bh22b1h32b2h42fkh52k1h62k2h72n1i022n1h82n2i032n2h92sph:2ubh;2ukh<2unh=1xh>2x0h?2x1h@2x2hA2x3i041ai052a1i062a2i071ci081ei092hii0:1ki0;2k0i0<1li0=2loi0>1mi0?1ni0@1vi0A1wp;1p;2p;3p;4p;5p;8p;6g00EVj1MTg00Kbj13Tg01?oj1?j2Lj3Bj4=j5:j6HTg01ADj1;j2Cj3>j4<j58j6ITg01BXj19j80Tg0153j12!s/$Rj2KTg0162j1J!s/$Rj15Tg017[j21Tg000kj26Tg0189j2A!s/$Vj2@Tg001Hj37Tg004Fj2DTg01Cij1ETg01E=j1FTg00A[j6GTg01;_j54Tg00j5R0#Mg01FUR1g01<aR2g004`R3g005YR4^00R5^<2R6];R7]:f0R8#3#?%;8P2P7f1R7#3/L81C78P3P6f2R6#3?B78A>678P2P5f3R5#3P6P7P8C=P5!s0&<P0P4f4R9#3!s:'D:P9!s2+8P4^82^63^32^72^53^22^91R:f5R;#9P0P4P7g00mXR<P4P6g01=j#2!s$1,K5R=P;f:R>f9R?f8R@f7RAP7P8%J5#5RBO7'1n0110400012010110:P<P4P7P9P?P@PAf6RCP7P8P6O7!sR5RD!sT$6P;P>!sV%!sR$5!sR8Eg01>IRF/671678'11A87RGg01>g'@'1RHP6PAPCP;P9%5FRFP7%5GRGO7'1g0069RIPIPDPIPEPD!t-$0000:3010410A10@2!s1%<!s9&<10;2010=1092010810>3!s-%!s9'410?40105102106103!sb,7!su'!w6%!u`%f;RD!ub0BG0,1=!ve<!sQ'!vc&G0!v77!vc&!t#15!sR8D!st&;P9PFP7PGG0,1HPI!v4$IPDPE!v8~!v84574X1:!v>$8!u;&!ug1!v<B!sQ';!v<>=!t#8!v<9!v:,5!v<3=PIP@P=!v<~!v<4,D4%3;R=#E%F;EGP=!~B,EH!tt&!s4%I574eXA0D4X@2D4X?3D4X>2D4X=1D4W4o"). Qed.
#[local] Hint Rewrite kentry_apart_bpB_eqf : bceq.



Definition kimg_b : ltac2:(zQ "20!va!ik0>1K$1$0") := ltac2:(zQ "80!hta!hge!io7!h9!ik0!hg8!va!hkc\1K$4M4\1K$4$6^1\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\2lo$3\2hi$3$7\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$1\2a1$2\2n1$0\2a2$2\2n2$0$1\1a$2\1n$0\1c$3$1\1a$2\1n$0$1").

(* [comment removed for export] *)
Definition kn_unfill : ltac2:(zQ "40!hg1!hta!ik0!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "a0!ik0!hta!hg1!mi7!h9!mg1!mid!mj6!lt3!mk2\1k@1$2$0\2ub$1\2uk$4\2un$1=2sp$8@4$7^4^3^2^1@3$9$0\1K$0@2$3@1$6^1@6$5^6^2^5^4^3^1^5").

Local Open Scope lzb_scope.
Definition kn_unfillB : ltac2:(zQ "50!hta!hg1!h9!ik0!kuc>2bc$4>2ub$0>2uk$2>2un$0@1$1$3") := ltac2:(zQ "c0!va!hta!ik0!hkc!h9!mh3!mid!lt3!mkc!kuc!ml5!mk2\2bc$9\2ub$1\2uk$4\2un$1=2sp$7@4$a^4^3^2^1@3$b$2\1K$2M0\0$0$0@1$6^1$3@6$5^6^2^5^4^3^1@1$8^5").
Local Close Scope lzb_scope.

Lemma kn_unfillB_eqf : ltac2:(zQ "80!hg1!hta!ik0!ljb!h9!mm2!mme!lgf>2fk@1$0$2@3$3>2ub$1>2uk$4>2un$1@1$0$2@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##/Hh01Kh12ukh22unh31bh42b1h52fkh62k1h71lh82n1h91sh:2sph;2ubh<1xh=2x0h>2x1p;1p;2p;3p;4p;6p;5g00EVj1KTg00Kbj10Tg01G_j1>j2Jj3?j4ETg01Hnj1:j2Ij3=j4FTg01ADj1<j63Tg01J<j1;Tg01KGj49j1ATg01LUj16Tg01M_j31Tg01N:j48j1HTg01OEj27Tg001Hj32Tg004Fj2G!sA$bj1@Tg00A[j64Tg01Q1j1BTg01?oj1CTg01RCj1DTg01;_j55Tg00j5R0#KR1g01<aR2g004`R3P1^22R4]1f0R5#0#>%:5P3P4f1R4#0/J51I45P2P1f2R6#0??45A=645g01FUR7g005YR8^00^22^13^;2]:R9f3R:#<P8P8%;5R;g0069R<P4f5R=#0f4R>P:P6C9P!s-$P5O5n010!s#$20000X00%0>#6R?510P=P=!sO%C8!sW'E3R@,7;X00=10>RA521X39P7^82^63^42R7%H:P8P8P;P<P=P4!s`%O3!sh,!tA4=10?=21AX97P1P!sd,@!sP75!sP$71P>!sx&4C8!s-%P5E3!tj+:,G1%0:R0#6%@:E4%A0%B:E4%C0%D:E4P0!sY%CE!sc'CF521eX>2D5X=3D5X<2D5W5o"). Qed.
#[local] Hint Rewrite kn_unfillB_eqf : bceq.

Definition kn_unfillM : ltac2:(zQ "40!hg1!hta!ik0!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "40!hg1!mme!ik0!lgf\1k@1$0$2@1$1@1$3^1").
Lemma kn_unfillM_eq : ltac2:(zQ "70!hg1!hta!ik0!ljb!h9!mm2!mnb@3$3>1k@1$0$2>2ub$1>2uk$4>2un$1@1$0$2$6$5").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01kh12ubh22ukh32unp;1p;3p;5g00EVj15Tg01S\j14Tg01ToR0j10Tg01HnR1j11Tg001Hj33Tg01;_j52Tg00j5#5R2g01<aR3g004`P2^33]2]1R3P0P1f0R1#4%01%11533eX02D2o"). Qed.



(* [comment removed for export] *)
Definition kwr_b : ltac2:(zQ "20!va!ik0>1K$1$0") := ltac2:(zQ "80!hta!hge!io7!h9!ik0!hg8!va!hkc\1K$4M4\1K$4$6^1\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$7\2a1$2\2n1$0\2a2$2\2n2$0$1\1a$2\1n$0\1c$3$1\1a$2\1n$0$1").
Definition havoc1 : ltac2:(zQ "40!ik0!hg1!hta!h9>1k@1$1$0>2ub$2>2uk$3>2un$2>1K$0@1$1$0") := ltac2:(zQ "f0!ik0!hta!io7!h9!ina!hg1!va!hg8!mo8!mi7!lr0!mof!mp7!mq4!mr0\1k@1$5$0\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$5$0@2$9@1$b^1@5$a^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$5$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$e^9^8^7^6^2^1^3\1a$2\1n$1\2k0$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\1n$1@1$4$0\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$5$0^3\2kb$1\2kk$3@8$c^3^a^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$d^9^8^7^6^2^1^3").

Local Open Scope lzb_scope.
Definition havoc1B : ltac2:(zQ "50!hta!ik0!hg1!h9!kuc>2bc$4>2ub$0>2uk$3>2un$0>1K$1@1$2$1") := ltac2:(zQ "h00!ik0!hta!io7!h9!ina!va!hg1!hg8!mo8!hkc!ls1!mof!kuc!mrd!msb!mt8\2bc$c\2ub$1\2uk$3\2un$1\1K$0M5\0$5@1$6$0M5\0$5$5@1$b^1$9@5$a^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$6$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$6$0^2\2kb$1\2kk$3@7$f^9^8^7^6^2^1^3\1a$2\1n$1\1k$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\1n$1@1$4$0\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$6$0^3\2kb$1\2kk$3@8$d^a^3^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$6$0^2\2kb$1\2kk$3@7$e^9^8^7^6^2^1^3").
Local Close Scope lzb_scope.

Lemma havoc1B_eqf : ltac2:(zQ "80!ik0!hg1!hta!ljb!h9!mu6!muf!lgf>2fk@1$1$0@3$3>2ub$2>2uk$4>2un$2>1K$0@1$1$0@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##@|p'0h01lh11Ki001Kh21ci011ch32ukh42unh51bh62fkh72kbi022kbh82kki032kkh93leni043lenh:2ubh;2wbh<2wkh=2wnh>1xh?2x0h@2x1hA2x2i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;7p;8p;5p;6g00EVj1VTg00Kbj10Tg01V>j1Bj2Uj3Cj4@j5QTg01WJj1>j2Oj3Aj4?j5RTg012Oj1=j58Tg01XUj19Tg00PFj1;Tg01Y_j3:Tg01Z?j7Tj1HTg01[Nj8Sj1JTg01\]j7Nj1LTg01OEj26Tg01]kj77j1FTg01_7j84j2ETg01`Cj75j1DTg001Hj31Tg004Fj2GTg01aNj1ITg00A[j62Tg01baj1KTg01d4j1MTg011;j1<Tg01eFj1PTg01;_j53Tg00j5R0#VR1g01<aR2g004`R3P1^10R4^42R5]3f0R6#0#B%>6P3P5f1R5#0/U61O56P2P4f2R4#0?C56AA456P0P1f3R7#0P4P5P6C@P7!s0&?g005YR8^10^42^33^:2R9f4R:#=P8P1P8P8%95R;g0069R<P6P:!sc%O4n010!s#$20000%;0R=9:05R>P0P1P5P=g00mXR?P1P5f9R@#0RAf8RBf7RCf6RDP5P6P4FTn01105000120102103REP=!s$-?P1P4f:RF!u7$@PBPC!sb$7GS!sb6G!sV$5PA!sN$!t4'N!sP5!s8$0000:3010510B10A2!s1%4!s9&>10:2010<1092010810=3!s-%!s9'510>4010610?10710@!sb&41!t:%510!vJ2P8P1f5RA!vj'D8RH,6;P!vX+!u9&@!u907!u95!vE5P4PF!vA04!vA6F!t-85!sP6I!vCJ;!vCuRJ511X59P1^92^83^72^=2^<3^;2R9%D:!z^'P;P<PH!sc2H!vk-!yd1!y6':!us/O6!y`7!y8~!usB=11JX09P9^23R<1E6AX23!ug$!uO=!xn%A!|11O!yL7I!uO~!uOH<P9%F:!uF4G!uF0F!tv~!wGL8P1%9!#5K'P6D8'6A:06=!u'$6!}a+!yb%A!}aR!}7/!}a8!t+85!#4z[!}]v,G1%0:RA#H%I:E2%JA%K:E2%LA%M:E2%<A%P:E2PA!v`+Q!vl-R511eXA0D3X@2D3X?3D3X>2D3W6o"). Qed.
#[local] Hint Rewrite havoc1B_eqf : bceq.


Definition havoc1p : ltac2:(zQ "50!ik0!hg1!hta!h9!lt3>1k@1$1$0>2sp$4>2ub$2>2uk$3>2un$2>1K$0@1$1$0") := ltac2:(zQ "h00!ik0!hta!io7!h9!ina!hg1!va!hg8!mo8!mi7!mg1!mof!mp7!mq4!mr0!lt3\1k@1$5$0\2sp$f\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$5$0@2$9@1$b^1@6$a^6^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$5$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$e^a^8^7^6^2^1^3\1a$2\1n$1\2k0$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\1n$1@1$4$0\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$5$0^3\2kb$1\2kk$3@8$c^3^b^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$d^a^8^7^6^2^1^3").

Local Open Scope lzb_scope.
Definition havoc1pB : ltac2:(zQ "60!hta!ik0!hg1!h9!lt3!kuc>2bc$5>2sp$4>2ub$0>2uk$3>2un$0>1K$1@1$2$1") := ltac2:(zQ "h10!ik0!hta!io7!h9!ina!va!hg1!hg8!mo8!hkc!mh3!mof!lt3!kuc!mrd!msb!mt8\2bc$d\2sp$c\2ub$1\2uk$3\2un$1\1K$0M5\0$5@1$6$0M5\0$5$5@1$b^1$9@6$a^6^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$6$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$6$0^2\2kb$1\2kk$3@7$h0^a^8^7^6^2^1^3\1a$2\1n$1\1k$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\1n$1@1$4$0\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$6$0^3\2kb$1\2kk$3@8$e^b^3^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$6$0^2\2kb$1\2kk$3@7$f^a^8^7^6^2^1^3").
Local Close Scope lzb_scope.

Lemma havoc1pB_eqf : ltac2:(zQ "90!ik0!hg1!hta!ljb!h9!mv9!ng3!lt3!lgf>2fk@1$1$0@3$3>2sp$7>2ub$2>2uk$4>2un$2>1K$0@1$1$0@1$6@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##Aqp'0h01lh11Ki001Kh21ci011ch32ubh42ukh52unh61bh72fkh82kbi022kbh92kki032kkh:3leni043lenh;2sph<2wbh=2wkh>2wnh?1xh@2x0hA2x1hB2x2hC2x3i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;5p;7p;8p;6g00EVj1XTg00Kbj10Tg01f^j1Bj2Wj3Cj4@j5=j6RTg01gkj1>j2Uj3Aj4?j5<j6STg01ADj1;j67Tg01XUj1:Tg00PFj1VTg01Y_j39Tg01Z?j7Tj1ITg01[Nj8Kj1LTg01\]j7Dj1NTg01OEj24Tg01]kj75j1GTg01_7j86j2FTg01`Cj78j1ETg001Hj32Tg004Fj2HTg01aNj1JTg00A[j63Tg01baj1MTg01d4j1OTg01?oj1PTg01RCj1QTg01;_j51Tg00j5R0#XR1g01FUR2g01<aR3g004`R4P1^10R5^53R6]4R7]3f0R8#0#B%>8P3P7f1R7#0/W81U78P4P6f2R6#0?C78AA678P3P5f3R5#0P6P7P8C@P5!s0&?P0P1f4R9#0!s:'D=P9!s2+<g005YR:^10^53^44^33^;2R;f5R<#;P:P1P:P:%:7R=g0069R>P8P<!sh'O5n010!s#$20000%V0R?9907R@P0P1P7P?g00mXRAP1P7f:RB#0RCf8RDf7REf6RFP7P8P6FTn01105000120102103RGP?!s$-AP1P6f;RH#0P6f9RIPDPE!sd$5GK!sd6J!sX$7PC!sN$!t6'D!sP5!s8$0000:3010510B10A2!s1%4!s9&>10:2010<1092010810=3!s-%!s9'510>4010610?10710@!sb&41!t:%5104!vL1!v|$F!vl,E7RC,4=P!vZ+!u9&B!u905!u95!vG5P6PHP!vA/6!vA6H!t-88!sP6K!vCJ;!vCuRL521X6;P1^:3^94^83^>3^=4^<3R;%E<!zb'P=P>PC!sc2C!vk-!yf1!y6'9!us/O!vE7J!y8~!usB=21LX0;P;^24R>1F8FX24!ug$!uO=!xn%<P6!xn/O7!yL6K!uO~!uOH>P;%G<!uF4J!uF0H!tv~!wGL:P1%:!#5O,P8E7'4A908?!u,$8!}c+I!yd$<!}cR!}9/!}c8!t+88!#4|[!}_v,H1%0<RF#I%J<E3%LF%M<E3%NF%O<E3%PF%Q<E3PF!vb-R!vp0S521eXC0D1XB3D1XA4D1X@3D1X?2D1W7o"). Qed.
#[local] Hint Rewrite havoc1pB_eqf : bceq.


Definition kn_havoc : ltac2:(zQ "40!hg1!hta!ik0!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "80!ik0!hta!hg1!h9!mv9!mj6!lt3!nge\1k@1$2$0\2ub$1\2uk$3\2un$1=2sp$6@4$5^4^3^2^1@4$7$0$0@5$4^5^1^4^3^2^5").

Definition kn_havocB : ltac2:(zQ "50!hta!hg1!h9!ik0!kuc>2bc$4>2ub$0>2uk$2>2un$0@1$1$3") := ltac2:(zQ "90!hta!ik0!h9!ng3!lt3!mkc!kuc!ml5!nge\2bc$6\2ub$0\2uk$2\2un$0=2sp$4@4$7^4^3^2^1@4$8$1$1@5$3^5^1^4^3^2@1$5^5").

Lemma kn_havocB_eqf : ltac2:(zQ "80!hg1!hta!ik0!ljb!h9!nha!ni5!lgf>2fk@1$0$2@3$3>2ub$1>2uk$4>2un$1@1$0$2@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##,xh01lh12ukh22unh31Kh42b1h52fkh62k1h72n1h81sh92sph:2ubh;1xh<2x0h=2x1p;1p;2p;3p;4p;5p;6g00EVj1JTg00Kbj11Tg01i7j1<j2Ij3=j4CTg01jEj18j2Fj3;j4DTg01gkj1:j55Tg01KGj49j1?Tg01LUj16Tg01N:j47j1HTg001Hj32Tg004Fj2ETg01Obj1>Tg00A[j63Tg01Q1j1@Tg01f^j1ATg01kRj1BTg01;_j54Tg009Sj4GTg00j5R0P0f1R1f0R2CGp=0%J0R3g01<aR4g004`R5P3^24R6]1%12#<%82P5P6%11/I21F12P4P3f2R6#1?=12A;612g01FUR7P3^30^24^15^:4]9R0f3R8#:P2f4R9#1R:P8P6P1C9!s-%O4%6:R:'0P9P!s9&C7!s-%D5R;/09R<523X00P7^74^65^44R7%H8P9P2!sj&3!sW'/0:=23<X87P3P810;2!s5$03P8!sI%P2C7!s-%D5/08,E3%18R<#6%>8E3%?<%@8E3%A<%B8E3P<!sZ&C!sd+D523eX=4D4X<5D4X;4D4W5o"). Qed.
#[local] Hint Rewrite kn_havocB_eqf : bceq.

(* [comment removed for export] *)
Definition havoc_verdict : ltac2:(zQ "40!h9!va!lt3!nj1>2sp$2>2uk$0>2m1$0>1g$3$1") := ltac2:(zQ "h21!h9!kj1!va!iu3!hta!jna!jv3!hge!jv9!mi7!hkc!io7!nj9!nk1!lt3!nj1!nkb!nlb&@2$1@2$1$5$4@1$3@2$1$0$0\2sp$e\2uk$0\2m1$0\1g$fM1\1g@2$1~0@2$1$0$0$2^1\1p~0\2p0@2$1$0$0M1\1p~0$2^2\2p1@2$1$5$4\3obr@1$3@2$1$0$0M1\2p1@2$1$5$4$2^2\1b$5\2kb$4M1\2p0@2$1$0$0$2^5\3glo$0\3ghi$0M2\0$2$2M3\1x@1$3@2$1$0$0$2@1$d^c\1p@2$1$0$0M1\1p@2$1$0$0$2^1\3lo1$0\3hi1$0M3\3obr@1$3@2$1$0$0$2^8\2p0@2$1$0$0M1\2p0@2$1$0$0$2^1\3lo2$0\3hi2$0@2$9@2$8@2$6@2$6^4^h1^h0@2$6^2^8@2$8@2$6^1^7@2$6^5^h1$7$7$a@3$h1@2$1$b$4@4$h0^3^5^2^1@1$c^c").
(* [comment removed for export] *)
Definition havoc_fast_kind : ltac2:(zQ "20!va!ik0>1K$1$0") := ltac2:(zQ "d5!hta!hge!hg8!h9!va!jh0!jh9!io7!hkc!ik0!jv9!jse!lp0&\2sx$4\2lo$2\2n0$2\1e$0$1&\2sx$4\1k$2\1i$3\2n0$2$1&M0\1n$0$4^1\1z$3$8\2n0$2$1\2op$5\2a0$0\1b$0$1\2op$5\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1~0~1&\1n$0~2&\1a$7~3\1K$9M9\1K$9$4^1\1a$7\1w$2\1v$0@2$c^2N8~4\1a$7\1n$0\1k$2M0\1n$0$4^2\1z$3$8\2n0$2$1\2op$5\2a0$0\1b$0$1\2op$5\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1~0\2sx$4\2k0$2\1i$3\2n0$2$1\2lo$3\2hi$3@2$b@2$aZ^2@2$a^2^1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$7\1n$0$1\2a1$7\2n1$0\2a2$7\2n2$0$1\1a$7\1n$0\1c$3M0\1n$0$4^2\1z$3$8\2n0$2$1\2op$5\2a0$0\1b$0$1\2op$5\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1~0~1~4").
Fixpoint havocG_go (bc : bctx) (sp : sprep) (ub : expr) (uk : Z) (un : expr) (vt : ptree (gval * bool))
         (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           match pt_get vt (ei_gid ei) with
           | Some (g, true) => if (inb g ei && havoc_fast_kind K)%bool then [K] else havoc1pB bc sp ub uk un K
           | _ => havoc1pB bc sp ub uk un K
           end
       | None => havoc1pB bc sp ub uk un K
       end) ++ havocG_go bc sp ub uk un vt rest irest
  | _, _ => []
  end.
Definition kn_havocG (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  match un with
  | ELit z1 =>
      let sp := mk_sprepB bc ub uk un in
      let '(r, gs) := scan_entries bc (bc_fk bc) nt_empty gst_empty in
      let '(infos, _) := r in
      havocG_go bc sp ub uk un (pt_map (fun g => (g, havoc_verdict sp uk (zlit64 z1) g)) (gs_bnds gs)) (bc_fk bc) infos
  | _ => kn_havocB bc ub uk un
  end.

Lemma ranges_apart_pB_hull : ltac2:(zQ "h60!h9!ljb!va!hkc!hta!iu3!iie!nm6!ji2!kj1!nn0!lt3!no0!kuc!nof!np8!nq0!nq9!nr1!nj1!nra!lue>2bc$d>2sp$b>2ub$4>2uk$0>2z1$0>1g$h3>2ei$h2>2kb$4>2kk$0>1m$0>2z2$0>0@3$1$2@4$a^a^8@1$7^7^6$3>0@3$1$2@2$h4^7^6$3>0@3$1@1$5$0@1$h1^7@2$8$0^4>0@3$1$4@1$h0^8^7>0@3$1$0@1$f^9^7>0@3$1@1$5@2$9$0$0@1$e^a@2$c^h0^9>0@3$1$0^8@1$7^7@3$1$2@8$h5^h2^h1^h0^f@1$6^e^b^a@1$6^8$3").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "#$-]p'0h04Hnumh11Hh21mi001mh32Hih42Hvh51pi011ph63Ebrh72eih82kbh92kkh:1oi021oh;2z2h<2H0h=4__x1h>4__x2h?4__x3h@4__x4hA4__x5hB4__x6hC1nhD3H1khE2H3hF2H4hG1bi031bhH1zi041zhI2H2hJ7__arithhK4__ffhL8__varmaphM5__withN2b0hO2b1hP2b2hQ1ei051ehR3kbghS3obri063obrhT3EkbhU3EkkhV2EmhW2HShX2HmhY2_HhZ2bch[1gh\3ghih]3gloh^3hi1i073hi1h_3hi2i083hi2h`3lo1i093lo1ha3lo2i0:3lo2hb2sphc2ubhd2ukhe2z1i0;2p0i0<1xp%0p&0p;2p;1p;3p;4p;6p;5p;7p;=p;8g00GeR0j2XTg00GCR1j1nTg01lcj12Tg01mlj2STg01o4j1cTg00gjj2UTg001Hj34Tg020=j1WTg021Gj1:Tg022Pj18Tg016Rj1HTg023Zj4FTg000kj26Tg024:j6E!s/$Vj3TTg005>R2j2RTg0259j20!t3$bj25Tg002>j2r!sA$Vj3qTg026hj3oTg0287j1KTg029@j2ZTg02:Pj1BTg02;Wj5?Tg02<ej7CTg004Fj2mTg02>4j4iTg00:mj3hTg01OEj2LTg02?ES00j2Y!s2$_k20>Tg02@?k30=Tg0153j1f!s9$[j2]Tg02ADj3d!s/$mk20<Tg00PFk10;Tg01Y_k30:Tg00EVk10!vR$BYj2\Tg02C7j4^!s/$Uk102Tg02D3k101!s0$Qk10!u~$3aj1b!u~$^j1[Tg02E<j2MTg00Qoj1a!s8$_j2}Tg02FAj2|!s/$mj3{Tg02GLj4zTg02H>j3y!s/$Xj3xTg02I2j4_!s/$Nj2l!s/$mj2wTg02JIj1~Tg00A[j6kj7eTg02K[l=vTg02M1j4uTg01Cij8tTg02NCk103Tg02ONj2s!s/$mk205Tg02Q8k20!xh$RDk407!s0$ok708Tg02SSk309Tg02T6j8p!x}$YR3f3R4f2R5f1R6f0R7Cug0069R834p=AA4378p=11Z679445p=@f7R9f6R:f5R;f4R<%H4P5P6P7Gt=438p=>P:P;P<P!s=$CFP7CFp=gP9!s=%g02TZR=g01<aR>P4P5CF!sM,Gg004`R?P?P6!s8%O&037,s6p=9%W7-056p=;%87-066p==1056/67p=31667!tO%7!s;$07p=D1067,65p=J1056,64/L7p=I16<4!s`&'Lp>0?1656!sA$j1056%27'0p=<P?P6g02U?P7H07p=P!s5%fR@g02VERAPAg02VeS01P7g02WEK08p=QB09?67p=NP4P@PAPAQ01!vB&pp=VP3g02WeR@!su$XEP8P7EEp=`g0100g01FUg00B9P01X=>RB1X??RC#nRD'XREPCg02XaRFf:RGf8RH%29P;CA1S:;#1%n?RI%c:1U?434RJ%W9=4>:RK%:H=4?:RLPDf9RM#8RNf@ROPHC@%2:94?9RPfBRQfARRPOf?RSf>RTPGPM%H9RUG>[!s#%^;?^2?^9?^8>]7P7P0PBPDPTf<RVf;RW#2PEPCP:P;CFCA!s2$9P:CF/S;#1PDPNfDRXPHC@fFRYfERZPXfCR[PQPGPMPUG>\P[\L\K\J!t:1^7F^5C!t>$=P>PQPO%2S!t,$BPD!ys%Fg!t?&BPDPHP9P:Fg!tE,HR\!tE$JR]fIR^P\fGR_PY!tEH^:D!tH$?P?PYPX%2[!t6+M!t8$;GG!tJ-G!s<$:GG!tL,LR`!tL$NRafMRbP`fKRcP]!tLEP7P^P_%2Y!t++VPWPG1O:!tB0f=RUPVPW1O9!tF0ORNPHC@PI%cWP1P?P3P7P3!s$119ZU1;XUP@n010!s#$200001=[!s:4%:URd,6S!s>3ReA3d7T!s=3P@n10110<00021!sA%#1X:IP;1U?HP<EE!t\5[W1;QW!t\5R!s:4%:WRI,6!tt4A3IHV!s;3#1!t51XV1;[!sL41=Q!s:4%:VRI,6!uT4RfA3IMURI;T7%1f%1I'RP2%1e10dG/7TfTRdfSRefRRIfQRffPRgPUPV%HGG>!wN119_S1;Y!vv41=Z!s:4%:S,6R!uU5%:O/0U/7R!s{,^R1;\!sQ41=_!s:4Rh%:R,6[Ri;T6%1h%1i'RP2!sq,]Q1;^Q!sq5\Q!tX7Q,7XfYR\fXRifWRhfVRjfURkPQPR%HS!uu/19`X1;cX!t%5]X!t%7Z,7_!s^%aY1;bY!u@4Z1=`YRl!u>$Z%1l!u>'19N_1;a_!s{51=b_#1f^Rbf]Rlf\RZf[RmfZRnP_PY%HX!t~'19f^1;g^!si7g]#119ecR]1;IcRI!tN$]!y'&19d`#11;e`#1fcRIfbR]faRXf`RYf_R_P`Pc%H^G>P719ja#11;jN#1P217671556S02[S0315671756R^[S041545\^1r67S05P6n20!td'1!te$000X2?XC?S06Q03^2?^C?R^P7Pe%:fRcPWO315ecQ06P^P7%:e/0gRePdPQ!s?$d%WdRe=qm<A4>me%8kRe=omGA4DmeP>%WjA4>b7XQ>P6PkPaEEA4>lkP?%:h15n7XH?P;!s?%15\!s>$i107j/5nXH?P<PjPNEE10jk/5\P>PifoRjfmRaflRe#2Rc!#5K']P7PY1OZmR`GGCAfqRofpRpPjfnRqPaPnP\%HhG>S07]4XR>PqPefkRr!#:,%BPDPXPiP_1OmnGGCAPD%8nRsPpPq%2a!sJ+IPnP71OlZ!t3$rRtPoPpPjPqPmPn%HiG>]4XSDPjPaP!tk/\PsP!tg$P?Pi!{=$1PCP3%KoRi!#9-%3P7!s;%fuR`/ZbS08!s@-3P3ftRs#2S099D4`Rc?J6YRuP8107YRv10<`Rw73:!z61!x`$10;!x`%10:108!#6r3;!sN+1!sN'9107!sN4100P8!u3$t%BoRxPmPnP7D?P8PtPpPj%2qRy!s;%FC!tV2!{t2XH?PD%8m!v%,P!u~4P4!uv1PuP8A3v_w!uY~!uY-P!uV%\!uV,P!uS%\!uSD:D!xM'p!uK3%8bS0:!s<,fsR\#2S0;9D4sP6PI10<s937]CI!uO?6!uOW31m37!w4;%8_!zI0cfdRc,06RyP7PIPwI0?!t_s=437!{p,\!t`5X!vF-wRwfvRx#2S0<5D4ffRv,06S0=feRu,07S0>?J<w3j!ttz3P6P8g00mX/X>S0?PbPiPXPYCi%BsS0@3h!#?47!uS&`!uS5I!~<2yRz,04fxR{#2;3y!~7$cRy10<z73I!{Z~100S0A!{]&x%B`P_PbPlD?S0BP8PxPsP\%2t!s<%!{bC]4]0P6!um't!um5Y!s9,A<4x`106uS0CAJy<x!x'uS0D#1A4388%KsP!}M%!{g%7!ti5cS0E!z0-zRy=<4zS0FP6fiR|fhR}10<yS0G537!}Vu!yH/P6!tm5uS0H!yJ2{R~=<4yS0IQ0='6!yJ$v10<~S0=73u!yK~!#6#+{%BwPXPYP_D?P8P{PxP`Q09!s9%!yE3S09!yH40!wR+!ui2Q!uf/Q0IP6fjRuQ0=937|!wFa!w2&!t+'!zo'8vS0=!w&2|S0I=<4~S0HfgR~7J!w,%~Q0I,0<S0I73v!w/n!vs%y%BzPIP]PX!vs$yP{PwQ0<!s9%!}:D0!v`,!uD-Q0HP6PrQ0I937u!v^M#1%8~!|J;p+01@R~f~S0I5<:P6Pq107aR]?J9~!t2OPDP6p+01ARIP|C@!{q-5!wW1p+01BR{=<HIS0H?J6e!wV$e10M{Rv73r!wSY!{4,IPuP|P}!{4&~Q0If}#2!s;%!{65I!wD46!{87%2~S0=9D9IP6Pj10HI937q!v?9#1PD1UC!v,$CR|Pr!v,&!ss'5P3P310M|%2{106a33P810G|93]e!usF8!vd'DR]%B|PePrPu!ud$]P{PIQ0=!s9%!y}D!u_$!yl%pA37jvCI!u1$O56,UCp+01FRvPqC@P3A<G]|P4Pq105q10W]73aCIS0HP8P21L67#1%15%16Ra'YR|[%17,Ya1L56#1[Ra1L45#1\|20>67P7!#L67P3XO3Pa^P3^O!zW&ERa=<W]R]?J<jS0=104j10VaR|73qS0<10<\Rq,6]R]A34t|R|<0=5%1]%1|'YQ00%2aS009DVv10;sRV'710Uv,7qp+01GRq=<UvRU10:o'7AD;op10TqRT'7'YP710:`,7U!#MR%p+01IRUp+01HRa5<SRS10HwR|P6O315S|p+01JR|=<OU10Ms'7RSADHs\10R|'7RHP2Q03Q04Q021745[Q05!v$:!#O8%5Q04!#O8$S04!tO%KR2=<R|10G`g02YmR|g01=jRR#fR]#f,]?1]?]1]?R5d?5d?g02ZY+0<&0;|40:S02&04|S03P?P?1\?<P51\?:C^P6!s6$;P4&02?C^C^S0J&01?S0K&00?R|g006YRR#bR]#[,M?Rt%[RRu#b,M?Rr'P,Q|%aARAP|1M?RRR1M?uRe'N1M?]R]'NRI%[u,M?Ru/Nt!sU$PA1NurRu,PI,Q|S0LCVCVQ01,}|S01P7P51m38RI1|75#1dg01>IRr={?6CzS0MbKbLbMX=?X>?X??X@?XA?XB?15;<1065R{/0410<:'5AD54<10;:'5R4[[^=?^>?^??^@?^A?^B?P7PyPxPW%22p+01LRWPQPgP5O8bJO3b<3yb1b<W1P7O117VT!y&&109xR^10OURO!xu%^OQ!w~$P7ADM`s10Q2Q0!xg%JQ0KP|1Ne]/Pt!uu$P|1NRt/Pu!s4$Q!uw+Q!uS?{;106:10<;'5P!uC;zPWP[P`PxPGPN!u=,9xSH!u?,!z:-211000!s'$b0O3b1C_Q0H9438P3!#6W%!#:x&U%Ba!#S;$D?P8PUPqPvQ00!s9%!#MpCG3PIQ0=Q0<'LP7EEb1W6W0X_?Xa?P6P7O2!#<C/1104104X5CP7O1A43@8RjPD%aCP~P}C@P3p-0P7g02[ER}g02[bn01103!tA'XQ3R~/`6P}Q0I#1/l7!t@%!#96$2!uq%!t<$P6PbO2b:W0X^?X`!t\E1`~7P}Q09!s}&X0j!s|65O1b:W4W0Q0D=43@Q0?PlQ0:PYP_Ci%B\3h#1P`Q0@!#KW&PlPZP7PDPiQ08PkC_P9P:P?%2m15r7g01>g,w7'RX2?%~mPZPdEkM=v!sj'lPZD?#1!w~+!#I@%x!#B{4E!#=-0Q0FQ0C'6P8Q0>Q0G73c!#EV~!#=H'7P8PwP`PsQ0;PYP_Pb!y\FQ0A!#e2'7P8P8!sJ3P7PIPI!x{1bNQ0BP7EkbWW4W0!sC-1!#3v$O2b0bN1ZonPfEE%2hPgEEQ07eW4PYP<P7F!s0%5PdFebFbEbDbIbDbFb1bEb1WDWY!yM-!#7}&!s/&b3WIW3!sF@E!sFBF!sFAb3XVPW6XULXTKXXJW3W4X;?X2?X9?X8>X7FX\?X]!{BAXSDXR>XG=!sL91105X5B!sC<2X5E!sC<1W[Xe?Xd?Xc>WbWZo"). Qed.

Lemma havoc_fast_keep : ltac2:(zQ "h60!ik0!ljb!va!hkc!hg1!h9!nr1!lgf!ji2!mo8!ina!ng3!ns1!nn0!iie!hta!lt3!nm6!nt3!nj1!nra!ntb>2fk@1$4$0>2sp$h0>2ub$f>2uk$5>2z1$5>1g$h3>2ei$6>1t$h5>1K$0>0@3$1$2@4$d^8^6@1$h1^5^4$3>0@3$1$2@2$h4^5^4$3>0@3$1$2@1$c^3$3>0@4$h2@1$7^c^5^4@2$8$6^6@3$1@1$4$0@6$b@1$7^d^c^b^a@1$e^9^5@3$9$0^5@1$a$0").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "#$B-p'0h02HDh12Hkh21Hh31bi001bh41ei011eh51ni021nh64len1h74len2h82opi032oph91ki041kh:1mi051mh;1ai061ah<3leni073lenh=2E1h>2E2h?2E3h@2HihA3HlthB2sxi082sxhC2loi092lohD2HmhE2b1i0:2b1hF2b2hG2e'hH1ii0;1ihI2k0i0<2k0hJ1oi0=1ohK1vi0>1vhL1wi0?1whM1zi0@1zhN3HbrhO2HvhP1Ki0A1KhQ2_HhR2a1i0B2a1hS2a2i0C2a2hT2bkhU1ci0D1chV2eihW2fchX2fkhY1gi0E1ghZ2hii0F2hih[3hi'h\3lo'h]2m'h^2n1i0G2n1h_2n2i0H2n2h`5nd_i1ha2sphb1thc2ubhd2ukhe2z1i0I2a0i0J6a_basei0K5a_offi0L2kbi0M2kki0N2n0i0O3obri0P1pi0Q2p0i0R2p1i0S1si0T1xi0U2x'i0V1yi0W2y'p%0p&0p;1p;4p;2p;3p;6p;8p;Bp;7g00EVk10STg01lcj1?Tg02M1k40KTg01mlk20RTg00Kbj12Tg00gjj2<Tg02\>k40ITg00GeR0j2Q!s1$CR1j1pTg020=j19Tg01o4j1`Tg02NCj1vTg023Zj43Tg02]Gk100Tg02^Pj2~Tg02_^j3|Tg022Pj1MTg029@j2STg001Hj30Tg016Rj11Tg01f^j6sTg00PFk10HTg01Y_j3eTg02ONk20F!s0$mk20CTg02Q8k20>Tg021Gj17Tg000kj2VTg0259k209Tg02`5R2j2oTg004Fj2u!s:$Ok405Tg00Qok10!u4$4:j6gTg02INj2xTg01XUk102Tg01?oj6PTg01OEj2fTg02?Ek201!s0$_k20Q!s|$ij3_Tg02b4j2nTg02c>k10NTg003Cj1m!ud$2j1OTg00a7j6cTg01Cij85Tg017[j2@!tP$2j4ZTg00A[j6d!so$glBlTg0153j1E!s/$Rk20JTg02e@j2YTg02fKk10GTg02gTk30ETg02h]k30DTg02ifk30BTg02jok30ATg02l8k40!tA$mAk40=Tg02nJj3XTg02oUj2qTg0189j2BTg002^j1RTg030`k20;!sB$Vj2UTg031=j1i!s/$Zk20?Tg032;j2y!s/$\k108Tg033:j2kTg034Ej1aTg035Pj3hTg036[j2LTg037fj4jTg0391j3TTg03:<j2WTg02HXk307Tg01Z?k706Tg01[Nk80LTg01\]k70MTg03;Gk604Tg03<Lk10OTg03=`k20PTg005YR3f0R4g0069R530p=4&0O4=035p=8g01<aR6g004`R7f1R8%74C3p=wf6R9f5R:#af4R;f3R<f2R=P8P4C3'<30p=IP6P7%9!sX'K1<74p=:P:P;P<P!sQ$EP!t6%>!s9$!sU$=P8C3P4C3,<:p=^%a8=0=4p==g01>gR>,U4p=N20P4>p=]!s^'P!s]+p=t!t+%1<7!sl$;p=}P:P7P;1<<!tD%cp=GA0784p=;!sd$!u+$p=D!s`/p={!t+1!sw':p=J%?4,<7p=\!u@'!t8&[A0684p=F!s[%P4CZp=HP3P5!ui+dp=r!ux'!su$=094p=Cf7R>P9!v</G5!v<%z!s9%g02XER?!sk$gp=AA0385/x4p=6!u}5!tu$b1<8490<=p>0<1<=8=0<4p>0:g00j5R@$0SRAg01FUg00B9g02XaRBg03>@P>P:%?;RCP<H0K#420R;<#4%8=f;RD#2P;P<1<B:H0I1Q67RB%p7RE'QRF#pRGP;PFPBPE%99RH/w9%`9FIS00g02TZRI,Q6RJP6PIPH%v9C3&00H,~:3|1Q77RK#pRL%M9f<RM#2RN/SH30PNPDf:RNf9RHf8RO#1P;Es&0H@RP9e@;50AQ00P6PI%9>RQ%v>!s}$Q,~95|J%MOf>RJ#2%9O'S50L%`HPEP1P7!s&$3P4P01QI6RQ/QLPKP3f=RKP0PQPLP3P8P0PIP6!s0&7!sW$;P3!s$1fDRI#v-0F<%9I-0C=g02WeRQn010!s#$20000%MI-0>;P!s=37IRR,V8!s>3209RO/V4!s>3n200110Q00012010910F!s:&R!s:'010L!s:&P!s:'R10O!s:&E!s:'P10QRRPQn10110T00021010500#4PGPN!x8%1KMMP8FI%:4RS90E<X:7,o7]0]@P4%4RPGPD!sP'KK%:8RRFIP7%:<=0ESX:7P=%:=,uEH05W0W@X:7P4O1A03Q5RTPGPH!sd'DD&037RUFIP3PQP3p-0S01P4g02[ERVg02[bS02n011!v/,X43P?P5P8EgPVA0EUS!tn%/x4b2W0W@!uT%=!uT'@00P9P<O2bJ%`N!tq&,o7P2P7%`D!s7&fAR2#2f@S03f?R?PJ%1KPHEsAe@HP50AP4%`K=0ESPE%`JPGPK!u;'??P4FIXJEP>PRP4EgPGPM!sC'JJPRFIP3&02KfERR#2S04PIfCRSfBRW%12S05PKEP'fS06P5g005>1f84#4%4=%48RX+01RY[%44-01X1f=8#4[RX1f<=#4\Y20Q84P4!xX$!yL%1!vD$000XF3XE3PX^F3^E3P4&02JS07fFRX#2PRPIPS%1WPJEPS08Q07#4Q08#4P@%84PGP8!u:'WW%::FIfIRY#2fHRZfGR[PX%1RP=E>]0]1PJg00mXR\P\g00iVR]A_=84#8A_<=!sn&PZ%7Z%:DE^R^5=GfOR_#2S09fNR`fMRafLRbfKRc#1S0:A_;<!t&&^K6]LP41n<=Rd?_84#81n;<Re?_!t%+c%7cS0;%:JE^Rf5=GPGP1PFP7P4P0!sH$7P4!~]$7P4P4P3!~6$3g03?KRg!s5$gP]P7P>g01>IRh&0N4#mRi!z8$2!z8%10102g03@1Rjg03@WRkg03A=Rl!sL$V0003!sL%W!s'$P5P5!~'$!|x%3!w[%%O>Rm#N!s?&:!{;'Pm%]m!~W2!{,4!~A3P10=!uB'P!u=/;PhP!u25PjPkP!t{R;Ri!t{6i%]i!t{@P00X4G!wd&:P;%O<#?Rm#:Dt!#8|&bS0</wbP?D}S0=P4EG1;m?!x#80P6!x%$8!{N&!uy-110@!v57S0>P9!tc>1D9:Rm%?iC{!t_'aS0?%7aRiQ03EJRnP8EG1;:iPGP6!tc$6!tc+6!tc+6P8P8!tcM@PO!tc@>9S0A%O:#\D[!tf'`Ri%7`S0BP2EJS0CP=Ec1F>i%9_Ri,FOfPRo#7S0D,;O%OO#?/;IfYRp#2RqfXRrfWRsfVRtfURu#1S0EPMPD%ON#1G5,@4#4X33%2rRvPsPtPufTRwfSRxfRRyPDPNPR%OHRzP_P`PIP6PD%9yS0FP=CZ%7yR{=HN8P6Q0F%Mx1Sq450LX36PYPDP=Ed%?z?HR4MBlP!t-&%1wPDPN%1zG5,@5#4eg01=j#E!s$1-0JHP>CrW?W>W=P4O1b2!s+/%2yS0GfQRzPoP_%1`S0H1n:;Rv?_<=E>eW0W1XK6XL]X97X36P8P4O!#9A$S!w[$110J10KW;!#B`$O3P\1Y84#81Y!#3_'X%7X%:HE^R|5=G%2aS0IPbPcfJR}%1YS0J1Y!#4W'56P41n=8S0K/Y!sn$d!sn'Y%7Y%:ME^R~5=GP6P6P3P4P5PQ!s$/!}h+8!~O$1010N3010310I100!s1D4010810910N101!s4&410;10N#4S0LP!}I'mP6PEP8%\4PU!s$/!tP$7!tP02!t/&6!t:,!s1=!tP,2!tP32S0MQ0=FC%2xPyPzPo%1_P>P9P=Gz]0]1P=A0355S0N!tu'Q0A%\8S0OPnFC!#7yH!#5]'9!#5DUN9!#5@39%]9!#7=g<!t^W<!t^4<%]<!#6xES0P!#3Y&O>S0Q%?=S0R#:S0SC3Q0CP4EGQ0R/;2!vu,Q0>PH!st:T!st'HOS0U%\<S0VC3!yc&i%7_RiPWEJS0W!#64$O!#64/Q0@PD!#5N?NHS0X%:CS0Y!#5O+oS0ZQ0DPSEJS0[P=EcQ0Z,FN%9zRC,FD1;D{%?>S0\/;XfZRi#2PpPr!#3m$PwPJPKP[POPzPoPXP6PJ%9wS0]!#4h$wS0^=HK8P6Q0]%Muf[S0_#2R2/S!#4q&cPJ!#4q$OS0`?H[4MBl!#4=:W0W1XM7P4O1!z|-PU!zx&!s7&QPUD[S0aP1PFQ01!{1'!s1%1P7!s/%VQ02!vL00!#I~,!y|1V!vt8Rn!xQ$DAPV%2uS0bPwPxPy%1zS0cPHPO&0G<S0dG5/64b2W0X1TX5]P4O1g03AcRm!u%'1DDNS0ePU!xY&C%7zS0fPIEJS0gFCR!uS+PMPDPUEbS0hPn!uf'FP{PREJS0iP4DAS0jPVPq!wh%Q0EPKPMB0E:;<S0k!tZ076X66W8!#7?&Q!s_8D!s_$l!s_&X0C!s`+X8m!sa'g03BOR{!sh9B!sh$m!sh6!tJCA!s`$E!tJ8{!sa'!v7&KPM!v7%j!{?'xRC/wxPXD}S0n50GRX!vd+JPK!sS%o!vd,]Q0^P[EJS0]!ve%pPVP2PiPpPr%1sRqP?PJ!#VM&H0@S0q!vl0<6X5]XC]XB3!#Vm&O4Q!sl/P!si2=S0p!uR+X!y4%XH7XI!sj1n01101000811!#8|r!t0$2S0r%2oS0sP_P`Pa%1bS0t1Ye!#=w'<6!#=t@X;\!sA%P\AX!#KY$X<=8==G^Q09P`PaPbQ0:AX!#K6+9]^56P4AXd!sU%e!sU$f!#=K~!#=K3<!#=K&!#3S,Q0MQ0CFCQ!~-'Q0cPOP>!#<-$S0c]1P<Q!#<+-QQ0OQ0WFCPGQ!#8_&Q0UQ!#8S$[!#8S'S!#8S0N!#7Q=Q0XQ0VC3Q0gP8EGQ0f,;H!#8:2M!sg@eQ0YD[Q0i!#7x$F,FD1FMCQ0^,;MQ0\/;Zf\S0\#2Q0_!z^&sPt!z`$YPOPxPyPZP6P?%9tS0^!#7u$tS0F=HJ8P6Q0^%Msf]#2S0i!#7s+aP?P=EdQ0`?HY!#7pIS0NQ0aQ0W50G!vt,UPUD[Pn!v_$!#6a$sR!#9i%%1xS0[PNPHQ!#6\7S0dQ0hQ!~S%!w\$jPnQ!~5%RX!}F0JPKQ!#5l6!#52,S0kP!s[6!#5hAS0l!s\7m!#4z@S0m!s\7E!s\CEPGQ0o!#5O&u%7u%:ZDtH0<R{!vq'!xH$UEb!#5H+^Q0FPYEJ!v6$CPVQ0iQ0\!x}$%1pRpQ03P?Q!#5=FS0qP!sg1P!sd'!#58+{!#58;S0p!#5;~!t3$2Q0GPzPoP_Q0HAXv!#L++T]!#56G!w3&1q84#81q!#L''R%7R%:OE^RR5=G1B=<g006Y#RR]#m%R]#R!s$&m+0;R]'UP31u341B<;/U]=034P31B:9RT!s5'!ww&%1hR{/D>RpP3PEP81B9>#?Ri#:S03PU!#Ev0!t[&}%7}%:KE^RCFC1VhO1VO>'@1B>ORq#NS0_'@%2zRrPoP_P`%1aR2P{PO%1qG5'@#4RX]0]AP81B;:/U]Rm!#5s+1D{9S0\%?TC{P~H0:!#JJQ7P7PN%iDP7P7%iMR0PD20?84RT#mS0i1y84S0F!#I197P7P0PD1y48S0^&08TRT!sQ9!#IV-1010U!s'$!#J6T1BNDR0!#Z550%]0!#Ksg7P7P>%iO!v/%HRgPO!|P$!uz?!sJ$^P!ur~0000Q0_!um4q%]q!#\|LpQ03C3PC!#\`$iKPGQ!#LM&!z-$\qDtPf!#:{$;,;O!#:{2{!t'?{PH1BOH#\EbQ0=!#;#$<,F{Q0?!s+$B,;D1BDM#?/;W1BKJRO#N,@4!#Kz&Q0[P{PJ%1OG5RO'@#4X331@54/@O!#ZG%tR!sP$P!#SK%P{PKPS1BMKROPaPbPWP6P{Q0ZP=CZQ0D!#LR&Z%Mz1Ss450LX46P[P{!#LJ%?HS4MBl1@55!tR%Px%1yP{PK!tT$'@#4e1UO]P>Cr1VhK1VKM'@PD!#Z9<W0WAA03mQ!#;z+\PUP~!#Lx+Pp!#<2$P!#Kl%1xX!#l&$A!#lY,100P4P=O2bAb3%2bRXPcP}PY%1ZRn1q!#5}+Z7XC7!#5w$1k84#81k=8==GRPG1k<=#!#N,,!#Mq8X4GR1P|!tZ%Q!#[$$P}Q0J1k;<EP!#9Z%W1X]7XG!#71%Ah=84#8PGAh!#iY'1K[[%:NFIPGAh;!tH&^!s}'!#ED,h:!s~1[7X\!t%$!#\x+L!u?$L!u?$|!tb0L!#\_/Q0K/L!sQ$d8==G~PG1Le!tH%!v{&P!#6Q%P21Lv!tE05!#9S:0!#Gc2!#{@&j#8!#zn'j!t=%!#zd&Cj!tC9!#Jt&Cj!tI/_6XS\X^6XR!#|E'O4P\AT!vt$AT!#Hr6T!#Hr+U7!us$AT!#Hr$T!#Hr'Q0LQ!#G0'Q0dQ0kQ0lQ0mQ0EQ0qQ!#=f~!#=f7T!#=f,W7!#=fNP\1W!xs$W!xs6W!xs4W!sQ$!xs%Q0rQ!#MJ&Q0t1W!#MGU!sA$4000:31!up$?10>2!s1%2!s9&210421!v'$F!#io%53!s-%!s9'61024010B10G10C10H!sb,D!su'PDP8O2407O3b2CZQ069035P3P5P3PAP4Ae@?PR5P@PAP?PPP\PAP8%2cRcPYPZ%1[R[P8P4P=K06!u-$6!{,'L10MP!s#/\PAP=PXP=P}PYPn!s]$<L0L!s]6!t4$P!t1$P!t-+M!sO5!s8$A!vH$0!vH,!s1%7!s9&!vH$0!vHS!sj&10D!su'!#;-0=0A5X33Ae@JP,uAQ07Q08'fP4Egb2Q04PIPSPWQ05PKEsAe@KP50Aeb0WDX:!#60%!#y//!#<Z%bDWNWQW0P4J04W`W1W@WOXP@WbWVWYXe7Xd7Xc6WaWXo"). Qed.

Lemma havocG_go_eq : ltac2:(zQ "h80!ik0!nj1!hg1!lgf!va!iu3!h9!iie!nr1!kka!kj1!ljb!ng3!nu3!nn0!hta!jr4!lt3!nm6!nt3!ntb!nuf!nv9!nge>2fk@1$2$0>2sp$h1>2ub$f>2uk$6>2z1$6>4bnds@1$h0$1>1t$h4>2kn@1$2$0>5infos@1$2@1$5$8>0@5$h6$0@1$5$8@2$h3@1$3^9^3^2^1@3$b@1$2$0@8$d@1$3^a^9^8^7@1$7^6@4$h5$1@2$a$1$4\1g$1@4$9$1$4^1@4$e^a^8@1$h2^7^1^5^3^2@4$h7$0$0@5$c@1$3^a^9^8^7@1$7^6^3").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##Fnp'0h01gi001gh12Hch22HKh32Hvh42HFh51bi011bh65infosh72knh81oi021oh92Hih:2Hkh;2IHh<1Kh=4bndsh>2eii032eih?2fkh@5iresthA1lhB2oii042oihC4!s<$D2sphE1thF2ubhG2ukhH2z1i051ai061ei071pi081xp;1p;2p;5p;8p;3p;4p;6p;=p;9g00EVj1MTg03C;j1_Tg00GCR0j1CTg00Kbj12Tg02\>j2Ej4BTg03DEj5LTg016Rj1:!sX$eR1j2W!sC$cj8?Tg01f^j5>j6ATg001Hj30Tg00PFj1XTg004Fj26Tg03F1j1KTg00CBj3=Tg01mlj25Tg03G<j3Ij2Hj1UTg00gjj2DTg00Qoj1GTg03<Lj1@Tg017[j2FTg024Vj3STg005>R2j2R!sm$Yl=QTg02I2j4PTg00@Lj5TTg00A[j6JTg03Hmj8OTg01Y_j3NTg03IJl9^Tg01lcj1]Tg02M1j4\Tg023Zj4[Tg00DKj4YTg009Sj4ZTf3R3f2R4f1R5#]f0R6C\p=3g00B9R7g005YR8P5P6C[p=9P7P4!s3$Yp=<g00j5R9P9!s8$Zp=;%@6,F5p=7AN956p=4f5R:#2f4R;P3P4%:5P6EAp=1P:P!s81Vg00699086p=8%M9R<g01FUg01<ag004`R=%_7g03>@g02XaR>#CR?#MR@P9P?f8RA#2/E!tj$DL!s9$9RB#2RC/E3f;RD#2REf:RFPBPAf7RG#:RH1W78RIPDPBPAP6C3,96X07f6RJ3<P5P6G?PEP!sX$PHD>/;550<X6@X7<PCPAPGPJ%::D>%X9RC';,6<f=RH#2PGP3P4CB!tT$>RE#2/EAP4P5DLf?RK#2RLPEPHf<RM%:DRNPKPHPM!tO,=<IFP3P4G?P!sO$PMPND>/;350<P<f@RN!si$KPEPH%:MROD>RP/;;RQP0P>P<PJP0PIP<fBRRPNPK!t$0H%K6RS5=IP1P7P8P<P6!s+,1553RT/7D14DCfERUfDRVfCRWPRfARXPDE1RYn010!s#$20000PYn011!s9$!s6$n2001107000120100101%2RRZPX!tZ$EPAEVR[n101108000210!sU$%2XR\!sI%%:HR]PGEAR^!sN%4!sN'300=I96P!sO&P]D>/;:9I9^50<XA<P<P<!u{&:!u{%PX!sO$!uy/M==IS!uu87TF14FCPVPWPR!u#$FE1R]!uh2]!uhEP^!uW5P!wy&POPJEAR_!uQ5R`,H91H9_PQPQP<P<\<Ra%U9RbPbP`P_Pa\</6b!uW$\PDPGP6CB!ue&5!ue&W!u,$!ue%R\X07Rb=<IERa!uk>M14MCfFRTPU!uq&ME1RS!um2S!umF!vU'KPBE1!uy6[!x>60<[]2P:PZPMPA1D>6CB%CIRMP0P7PM%K5RZ9=7ER[1DI\%GIR\!t#2500!us&6!{;::/7H14HCfGRSP!u\'HE1R_!uZ2_!uZF]!uN5=0<]X8MP[%C7!u,$!t]%!u7$P6PU!v6$6C3RM,96,DIP!u97!u19J/7E14ECfHR1P!u3'EE1R\!u12\!u1FY!u18YP6PMP81686RMPT!v;$5C3=086P8P1!tB$3!s6+<P5!ti%;A/7NRY14NCfJR\fIR0P!tq%NE1R[!tm2[!tm1!xd$3P5PS!uG$4C3R[#8153G/7KP8PMA08Y6P815JFRY%@RRM'F!tP,14WCfMR_fLR`fKRcP\P0PWE1Rd!tE1=0<d]1P515:B/7XRX#8ASYM6%8Y%8M'RP215GD#8%@W#814VCfNRWP_P`PcP\PVE150<P615BH#8%@T#8P<fQRBfPRVfORGPWP_PSE114SCPBPVP!s8%DPKPcPSPAP5P6PEM=QCPW:W9P5P6O2!w`$!tr%1!ts$000b1W1g02WeRA908X!tN&0P1PRE1,6<W1!v]1P6O1b1b5W3A08[AP!w@'UPK!sV%3!sV63b5X07P6O116<!{+&2!xy$1!t^$b8A=IaZP7PIPbPEPZDTEJW2X>>P6O1PLPFPJ%G>CB16<^W2!sg2600P4O1GO16<QGO!#5D,N!s-$!#7$-DRIP;P3G?P6EJ!sP-I14J;RJAN?:3G?1;PJ50<eW;W4W2X@@XC<XB?X<9!#?j$M9^W4W6X7<WEW=XH=WGWFWDW?o"). Qed.

Lemma kn_havocG_eq : ltac2:(zQ "80!hg1!hta!ik0!lgf!ljb!h9!ni5!og4>2fk@1$0$2>2ub$1>2uk$5>2un$1@3$4@1$0$2@4$7@1$3^4^3^2^1@4$6@1$3^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##B]p'0h01gi001gh11pi011ph21ki021kh32ESh42opi032oph53un1h63un2h71ni041nh82sxi052sxh92uni062unh:1Hh;2HFh<2_Hh=3_H0h>1ai071ah?2fkh@2gsi082gshA1ii091ihB5infosi0:!s/%hC2loi0;2lohD2t1hE2ubhF2ukhG2z1i0<!s+$=1bi0>1ei0?1li0@1ri0A1xi0B1zp;1p;2p;4p;8p;3p;9p;5p;:g00EVj1FTg00GCj1G!s/$eR0j2BTg00Kbj10Tg01LUj12Tg01KGj43Tg01lcj1:Tg02M1j48Tg03Ijj1ATg03Dcj89Tg01i7j41Tg001Hj34Tg004Fj26Tg016Rj15Tg023Zj4DTg03K6j1TTg03LDl9STg03MXj2ETg02^Pj2<Tg02_^j3;Tg02\>j2>!t:$Ej5?Tg005>R1j2CTg03N`l:PTg02fKj1OTg02gTj3MTg02h]j3LTg02ifj3KTg02joj3JTg02l8j4ITg02mAj4NTg03P1j4HTg03Q?j4QTg00DKj4RTf1R2f0R3g03RPR4g03S]R5CQp=@g00B9R6g005YR7P2P3CDp=7P6f2R8!s5$Rp==g00j5R9#FR:g01<aR;g004`R<P;P;P:P3P0g02Xa#GR=#FR>g03>@R?'BR@g03TkRAP:f5RB#0RC%2C'@RDP0P>P?P:P2f9RE#0RFPFf8RGf7RHPBC3PGPHPB1B67RIf:RJ#0PEPGf6RKC3PG%:BP3C8,73X06%A8RL3=%2FP2G9n200110@00012010:104!s:&A!s:'@108PCf4RMf3RNP2C1%0HPKPBPNC1ROP!s$$%0GROPHPKPMC1RPPPn0110600081010<101043010310710=!s1D4010510;10410>!s4&2109104%0MPNP8P3C154:P3PD1B@ARD16D3%0KRP%2P'@=4D3P0P@PA%2O,@O!s6,P:P2!vq-=RO#0RPPPf<RQf;RR%5GRSC3PQPRPSf>RT#0POPQ%5EC3PQ%:E!vm,==IL%2P!vjPFPGPH%5M!u4$]3!tZ'%0QRL%2L'@!tr$!yt$54!xj,8f?R0#0RLPLPTPO%5JRUC3PTPOPUf@RU#0RVP0PT%5RC3PT%:R!xd/NR05=I%2LRW!t{;PP!uh%!tf&^0AP31@LW!t]$>P?P8P2CD!te'U%2VRDP4P5!wR$2%TVP3M9S1EV8g00iVR5#GRWg02TZ,B;RL1<429;L3R41<B89;L2[]1]2P9P=1>V8PDPND?'C'CP1fARD#0RV/EN1<K!sR$\4^1L^2W!sU&N%2VPMD?'CfBRV#0RSPSPDPU%5OROC3PDPUPOfC!xF$VPD%5TC3PD%:T!x%00%2SPBG9!sb%PO!yf&1EPB1<E!tF4fDRP#0RB/>K%2BPHD?'CP11<J!sP5ER1!sP%H%2BPGD?fF!~0$KPKP1PP%5DRDC3P1PPPDfGRO#0PBP1%5VC3P1%:V!x%/H!x#$KPEG9!sd%PD!tw'<Q!tI5HR=#0R9/>J%29PRD?fIR9%09RWP=PO%5PRLC3R4P=POPP%AJRPPR%2WRDPQP3M:PPWP!sC%LfJ#0P9P=%51C3P=%:1!v\0PPDPQG9P!s~$PL!tb$eW;W=P2P3O2!yy$0!s#$12!s-%0W:W<!sD6!s/&b>W3X@AXD?XB>!sM-1!sP$12110?104X1@!sC91100P3O1b3b1XG<P3O1PCPMPN%O3C1,6:X75P3O1g03AcRM!}?%AM82!sD&6;X5;W4P8!t,$3!sF&L!sF1X4M!sG'g03BO!sn+K!snBJ!sn<%0RRRPJPE!|X%P3CI!sO%9;X75XC5X87!sA'O4P!sQ1N!uP'XA<X2!sQ1n0110>00081110B!#7'qNR!tR'H!t\+!xr$X9;WFWEW?o"). Qed.

Definition kn_havocM : ltac2:(zQ "40!hg1!hta!ik0!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "40!hg1!og4!ik0!lgf\1k@1$0$2@1$1@1$3^1").
Lemma kn_havocM_eq : ltac2:(zQ "70!hg1!hta!ik0!ljb!h9!nha!oh0@3$3>1k@1$0$2>2ub$1>2uk$4>2un$1@1$0$2$6$5").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01lh11kh22ubh32ukh42unh51xh62x0h72x1p;1p;2p;3p;4p;6p;5g00EVj1BTg00Kbj11Tg03P1j19j2Aj3;j4?Tg01jER0j14j2<j38j43Tg01i7j47j1:Tg001Hj32Tg004Fj26Tg03V5j1@Tg00A[j65Tg03WGj4=Tg01;_j50Tg03XXR1j1>Tg00j5#BR2g01<aR3g004`R4P2^43R5]3R6]2R7P1P0P3P6f0R6#1#9%46R0P4P5f1R5#1/A61<56P3P2f2R1#1?;56A8156P2f3R8#1R9P1P5P6C7f4P8P1P5C3R:9226X02P7%48P6P8P1P5O3=22:X07P8P1P5P6C3,62%:9%@8E5P9P1P5P6C?P8P1P5P6C=E5X73D0X64D0X53D0%>6=270eX12D0o"). Qed.



(* [comment removed for export] *)
Definition kwr_cut : ltac2:(zQ "40!hta!hg1!h9!ik0>1k@1$1$3>2ub$0>2uk$2>2un$0>2kb$0>2kk$2>3len$0@1$1$3") := ltac2:(zQ "60!hta!h9!hg1!ohc!oi3!ik0\1k@1$2$5\2ub$0\2uk$1\2un$0\2kb$0\2kk$1\3len$0@8$4$3^7^6^5^4^3^2^1").

Definition kwr_cutB : ltac2:(zQ "50!hta!h9!hg1!ik0!kuc>2bc$4>2ub$0>2uk$1>2un$0>2kb$0>2kk$1>3len$0@1$2$3") := ltac2:(zQ "50!hta!h9!ohc!kuc!oib\2bc$3\2ub$0\2uk$1\2un$0\2kb$0\2kk$1\3len$0@8$4^7$2^6^5^4^3^2^1").

Lemma kwr_cutB_eqf : ltac2:(zQ "80!hta!hg1!h9!ik0!ljb!oj4!oje!lgf>2fk@1$1$3@3$4>2ub$0>2uk$2>2un$0>2kb$0>2kk$2>3len$0@1$1$3@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##-1h02mkh12fkh22kbh32kkh41lh53lenh62ukh72unh82wbh92wkh:2wnh;1xh<2x0h=2x1h>2x2h?2x3h@2x4p;1p;2p;3p;4p;5p;6p;8p;7g00EVj1GTg00Kbj10Tg03Yfj1;j2Fj3<j45j57j69j7BTg03[3j14j2=j3:j46j58j6Ej7CTg03\?j2Dj83Tg001Hj32Tg004Fj2>Tg03]Fj1?Tg03^Pj1@Tg00A[j6ATg01;_j51Tg00j5R0#GR1g01<aR2g004`R3P1^52R4^33R5^22R6^72R7]6f0R8#0#;%48P3P7f1R7#0/F81=78P2P6f2R9#0?<78A:9!s9$5f3R5#0P9P7P8C5P5!s0&6P3P4f4R4#0!s:'D7P4!s2+8P2P1f5R:#0!s<,E9P:!s4-Eg00mXP0\2[R0P6^:2^93^82]0R6f7R;,D8X00P8g036[R0f6R<!sf,O7P0P;P!s8-G3521X46P0!s</P8G3,>1%0<R0#?%@<EAP0!sE/FB!sU1FC521eX@2D1X?3D1X>2D1X=2D1X<3D1X;2D1W1o"). Qed.
#[local] Hint Rewrite kwr_cutB_eqf : bceq.


Definition cutout1 : ltac2:(zQ "40!ik0!hg1!hta!h9>1k@1$1$0>2ub$2>2uk$3>2un$2>1K$0@1$1$0") := ltac2:(zQ "e0!ik0!hta!io7!h9!hg1!ina!va!hg8!mo8!lr0!oj4!mp7!mq4!mr0\1k@1$4$0\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$4$0@5$9^5^4^3^2^1@3$8$0^1@1$5$0M0\1K$0@1$4$0^1\1a$2\1w$7\1v$1@1$5$0\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$d^9^8^7^6^2^1^3\1a$2\1n$1\2k0$7@1$5$0\2lo$3\2hi$3@1$5$0\1e$1\1m$3@1$5$0\1e$1\2lo$3\2hi$3@1$5$0\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$a^9^8^7^6^2^1^3\2a1$2\2n1$1\2a2$2\2n2$1@1$5$0\1a$2\3len$1\1c$3M2\1a$2@1$4$0^3\2kb$1\2kk$3@8$b^3^a^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$c^9^8^7^6^2^1^3").

Definition cutout1B : ltac2:(zQ "50!hta!ik0!hg1!h9!kuc>2bc$4>2ub$0>2uk$3>2un$0>1K$1@1$2$1") := ltac2:(zQ "f0!ik0!hta!io7!h9!ina!hg1!va!hg8!mo8!ls1!oje!kuc!mrd!msb!mt8\2bc$b\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$5$0@5$9^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$5$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$e^9^8^7^6^2^1^3\1a$2\1n$1\1k$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$a^9^8^7^6^2^1^3\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$5$0^3\2kb$1\2kk$3@8$c^a^3^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$d^9^8^7^6^2^1^3").

Lemma cutout1B_eqf : ltac2:(zQ "80!ik0!hg1!hta!ljb!h9!ok9!ol3!lgf>2fk@1$1$0@3$3>2ub$2>2uk$4>2un$2>1K$0@1$1$0@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##C^p'0h01lh12ukh22unh31Ki001Kh41ci011ch52ubh61bh72fkh82kbi022kbh92kki032kkh:3leni043lenh;2wbh<2wkh=2wnh>1xh?2x0h@2x1hA2x2i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;5p;7p;8p;6g00EVj1YTg00Kbj10Tg03_^j1Aj2Xj3Bj4?j5TTg03`kj1=j2Kj3@j4>j5WTg03[3j1<j76Tg011;j5;j1PTg00PFj1:Tg01Y_j39Tg01Z?j7Vj1HTg01[Nj8Uj1LTg01\]j7Jj1NTg012Oj57j1CTg01]kj74j1FTg01_7j88j2ETg01`Cj75j1DTg001Hj31Tg004Fj2GTg01aNj1ITg00A[j62Tg01baj1MTg01d4j1OTg01eFj1QTg03Yfj1RTg03b7j1STg01;_j53Tg00j5R0#YR1g01<aR2g004`R3P1^30R4^22R5]1f0R6#0#A%=6P3P5f1R5#0/X61K56P2P4f2R4#0?B56A@456P0P1f3R7#0P4P5P6C?P7!s0&>P1^:2^93^82R8^22^13^52R9f4R:#<g005YR;P1f5R<#0P:!s_%D;%:0R=9905R>P0P1P5P=g00mXR?P1P5f9R@#0RAf8RBf7RCf6RDP5P6P4FVn01105000120102103REP=!s$&!sd$P:PBPCP!sX&O6!sX6F!sR&4f:RG!uM$@!sZ$5P6P7GU!sX6H!t&&A!t&/FJ!sP6A!s:$0000:3010510B10A2!s1%4!s9&>10:2010<1092010810=3!s-%!s9'51044010610?10710@!sb&41!t<%5104n0!t9%020000P;P1P<!w++7RIP!v}+!u6&@!u604!u65!vj2!sV1!vj7J!vj'P4PG!vf08!sT6G!s~85!sP6K!vfJ;!vfuRL511X09P;^30!{;-%C:!w%$6!w%'O4!w#-!zE,JP=PHP!xw~!u7C=11LX69P8^=2^<3^;2R8%D!u3%I!u%>F!u%~!u%G08P8^43RH1E6<X43!u#B!z5%<!}u1O7!{;6K!uO~!uOHHP8%F!wG5F!uF0G!tv~!wGL;P1!{E'P6D7A906=!t~$6!~s+!}q%<!#3KK!sV16!sV8!#3I&!~w/!#3I7!sz8!#3G5!#3E~!vhA,G1%0:R<#H%I:E2%L<%M:E2%N<%O:E2%P<%Q:E2%R<%S:E2P<!w4+T!w@-W511eXA0D3X@2D3X?3D3X>2D3W7o"). Qed.
#[local] Hint Rewrite cutout1B_eqf : bceq.


Definition cutout1p : ltac2:(zQ "50!ik0!hg1!hta!h9!lt3>1k@1$1$0>2sp$4>2ub$2>2uk$3>2un$2>1K$0@1$1$0") := ltac2:(zQ "f0!ik0!hta!io7!h9!hg1!ina!va!hg8!mo8!mg1!oj4!mp7!mq4!mr0!lt3\1k@1$4$0\2sp$e\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$4$0@6$9^6^5^4^3^2^1@3$8$0^1@1$5$0M0\1K$0@1$4$0^1\1a$2\1w$7\1v$1@1$5$0\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$d^a^8^7^6^2^1^3\1a$2\1n$1\2k0$7@1$5$0\2lo$3\2hi$3@1$5$0\1e$1\1m$3@1$5$0\1e$1\2lo$3\2hi$3@1$5$0\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$a^a^8^7^6^2^1^3\2a1$2\2n1$1\2a2$2\2n2$1@1$5$0\1a$2\3len$1\1c$3M2\1a$2@1$4$0^3\2kb$1\2kk$3@8$b^3^b^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$4$0^2\2kb$1\2kk$3@7$c^a^8^7^6^2^1^3").

Definition cutout1pB : ltac2:(zQ "60!hta!ik0!hg1!h9!lt3!kuc>2bc$5>2sp$4>2ub$0>2uk$3>2un$0>1K$1@1$2$1") := ltac2:(zQ "h00!ik0!hta!io7!h9!ina!hg1!va!hg8!mo8!mh3!oje!lt3!kuc!mrd!msb!mt8\2bc$c\2sp$b\2ub$1\2uk$3\2un$1\1K$0M6\0$6@1$5$0@6$9^6^5^4^3^2^1@3$8$0^1@1$4$0M0\1K$0@1$5$0^1\1a$2\1w$7\1v$1@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$f^a^8^7^6^2^1^3\1a$2\1n$1\1k$7@1$4$0\2lo$3\2hi$3@1$4$0\1e$1\1m$3@1$4$0\1e$1\2lo$3\2hi$3@1$4$0\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$a^a^8^7^6^2^1^3\2a1$2\2n1$1\2a2$2\2n2$1@1$4$0\1a$2\3len$1\1c$3M2\1a$2@1$5$0^3\2kb$1\2kk$3@8$d^b^3^9^8^7^2^1^4\1a$2\3len$1M2\1a$2@1$5$0^2\2kb$1\2kk$3@7$e^a^8^7^6^2^1^3").

Lemma cutout1pB_eqf : ltac2:(zQ "90!ik0!hg1!hta!ljb!h9!ole!om9!lt3!lgf>2fk@1$1$0@3$3>2sp$7>2ub$2>2uk$4>2un$2>1K$0@1$1$0@1$6@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##DUp'0h01lh12ubh22ukh32unh41Ki001Kh51ci011ch61bh72fkh82kbi022kbh92kki032kkh:3leni043lenh;2sph<2wbh=2wkh>2wnh?1xh@2x0hA2x1hB2x2hC2x3i051ai062a1i072a2i081ei092hii0:1ki0;2k0i0<2loi0=1mi0>1ni0?2n1i0@2n2i0A1vi0B1wp;1p;2p;3p;4p;5p;6p;7p;8g00EVj1[Tg00Kbj10Tg03cHj1Aj2Zj3Bj4?j5<j6WTg03dVj1=j2Mj3@j4>j5;j6VTg03[3j1:j75Tg01?oj6Yj1RTg00PFj1UTg01Y_j39Tg01Z?j7Lj1JTg01[Nj8Dj1NTg01\]j7Cj1PTg01ADj66j1ETg01]kj78j1HTg01_7j84j2GTg01`Cj77j1FTg001Hj31Tg004Fj2ITg01aNj1KTg00A[j63Tg01baj1OTg01d4j1QTg01RCj1STg03Yfj1TTg03b7j1XTg01;_j52Tg00j5R0#[R1g01FUR2g01<aR3g004`R4P1^40R5^33R6]2R7]1f0R8#0#A%=8P3P7f1R7#0/Z81M78P4P6f2R6#0?B78A@678P3P5f3R5#0P6P7P8C?P5!s0&>P0P1f4R9#0!s:'D<P9!s2+;P1^:3^94^83R:^33^24^13R;f5R<#:g005YR=P1f6R>#0P!sa+EY%U0R?9907R@P0P1P7P?g00mXRAP1P7f:RB#0RCf8RDf7REP>P7P8P6FLn01105000120102103RFP?!s$&!sb$P9PDP!sX+O6!sX6G!sR&6f;RH#0P6f9RI!s\$7P8P5GD!sZ6J!t+&C!t+/FC!sP6!s:%0000:3010510B10A2!s1%4!s9&>10:2010<1092010810=3!s-%!s9'51044010610?10710@!sb&41!t<%5104n0!t9%020000P=P1P>!w--6RKP!w#+!u8&B!u808!u85!vn2!sV15!uh6L!vn'P6PHP!vh/4!sT6H!s~87!sP6M!vhJ;!vhuRN511X0;P=^40!{?+^;2R;%E<!w-$8!w-,O5!w+-!zN,LP?PJP!x~~!u<C=11NX6;P:^>3^=4^<3R:%F!u5%K!u%>G!u%~!u%G0:P:^54RJ1G8>X54!u#B!z:%<P6!z:/O!yh6PM!uO~!uOHJP:%H!wG5G!uF0H!tv~!wGL=P1!{G,P8E6A908?!u$$8!~z+I!}x$<!#3RK!sV15!sV8!#3P&!~~/!#3P7!sz8!xd6!#3L~!vjA,I1%0<R>#J%K<E3%N>%O<E3%P>%Q<E3%R>%S<E3%T>%X<E3P>!w6-W!wD0V511eXC0D2XB3D2XA4D2X@3D2X?2D2W7o"). Qed.
#[local] Hint Rewrite cutout1pB_eqf : bceq.


Definition kn_cutout : ltac2:(zQ "40!hg1!hta!ik0!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "80!ik0!hta!hg1!h9!ole!mj6!lt3!nge\1k@1$2$0\2ub$1\2uk$3\2un$1=2sp$6@4$5^4^3^2^1@4$7$0$0@5$4^5^1^4^3^2^5").

Definition kn_cutoutB : ltac2:(zQ "50!hta!hg1!h9!ik0!kuc>2bc$4>2ub$0>2uk$2>2un$0@1$1$3") := ltac2:(zQ "90!hta!ik0!h9!om9!lt3!mkc!kuc!ml5!nge\2bc$6\2ub$0\2uk$2\2un$0=2sp$4@4$7^4^3^2^1@4$8$1$1@5$3^5^1^4^3^2@1$5^5").

Lemma kn_cutoutB_eqf : ltac2:(zQ "80!hg1!hta!ik0!ljb!h9!on5!oo1!lgf>2fk@1$0$2@3$3>2ub$1>2uk$4>2un$1@1$0$2@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##,xh01lh12ukh22unh31Kh42b1h52fkh62k1h72n1h81sh92sph:2ubh;1xh<2x0h=2x1p;1p;2p;3p;4p;5p;6g00EVj1JTg00Kbj11Tg03ecj1<j2Ij3=j4CTg03g2j18j2Fj3;j4DTg03dVj1:j55Tg01KGj49j1?Tg01LUj16Tg01N:j47j1HTg001Hj32Tg004Fj2ETg01Obj1>Tg00A[j63Tg01Q1j1@Tg03cHj1ATg03h@j1BTg01;_j54Tg009Sj4GTg00j5R0P0f1R1f0R2CGp=0%J0R3g01<aR4g004`R5P3^24R6]1%12#<%82P5P6%11/I21F12P4P3f2R6#1?=12A;612g01FUR7P3^30^24^15^:4]9R0f3R8#:P2f4R9#1R:P8P6P1C9!s-%O4%6:R:'0P9P!s9&C7!s-%D5R;/09R<523X00P7^74^65^44R7%H8P9P2!sj&3!sW'/0:=23<X87P3P810;2!s5$03P8!sI%P2C7!s-%D5/08,E3%18R<#6%>8E3%?<%@8E3%A<%B8E3P<!sZ&C!sd+D523eX=4D4X<5D4X;4D4W5o"). Qed.
#[local] Hint Rewrite kn_cutoutB_eqf : bceq.




(* [comment removed for export] *)
Definition kn_keep : ltac2:(zQ "40!hg1!hta!ik0!kj1>1k@1$0$2>2ws@1$0@2$3$1$1@1$0$2") := ltac2:(zQ "h96!h9!hta!kj1!iu3!io7!va!hg1!hkc!ik0!kj8!ooe!kje!jv3!lp7!jse!hg8!mk2!ji2!kka!op5!ju7!opc!oq9!nlb!kg9&\1b$1\1o$0@3^6^2^1@2$a^9^3&M4\1a$4$5^2~0&\1n$1~1&\1a$4~2&\1b$1\1o$0@3^7^2^1@2$a^a^4&M4\1a$4$5^3~4\1k@1$6$8\2ws@1$6@2$2$1$1=3wss@1$6@2$2@2$2$1$0@1$3$0@4$h3@2$2$1$1@2$2@2$2$1$0@1$3$0\1w@2$2$1$1@4$h2@2$2$1$0@1$3$0@1$h5@3$9$1$1^1@2$h6^3@3$b$1$1^1^1=4test>1b$1>1o$0>1n@1$3$0$5\1b$1\1o$0\1n@1$3$0=4mine@1$6@2$2@2$2$1$0@1$3$0@3$h0@2$2@2$2$1$0@1$3$0\1w@2$2@2$2$1$0@1$3$0@2$h4@3$9$1$0@3$9@2$2$1$0@1$3$0^1^4^4M6\4mine@1$6@2$2@2$2$1$0@1$3$0$5^1$7\1p@2$2@2$2$1$0@1$3$0\1l@1$6@2$2@2$2$1$0@1$3$0@3$h7@2$2@2$2$1$0@1$3$0\1w@2$2@2$2$1$0@1$3$0=2wk$0@3$b$1$0@3$9@2$2$1$0@1$3$0^1M3\1x@1$3$0$5@3$b@2$2$1$0@1$3$0^2\2wl$0@2$e@2$e@2$dZ^1@2$d^2M3\1n@1$3$0$0^7\1n$0@2$c^9^1@2$c^2+1@2$d^8@2$c^2^1$7^3@3$h0$8\1K$8M8\1K$8$5^1\1a$4\1w$f\1v$1M4\1a$4$5^3\1b$1\1o$0@3^7^2^1@2$h1$0@1$h8^4~3\1a$4\1n$1\2k0$f~5\2lo$0\2hi$0$7\1e$1\1m$0$7\1e$1\2lo$0\2hi$0$7\1a$4\1n$1$7\2a1$4\2n1$1\2a2$4\2n2$1$7\1a$4\1n$1\1c$0~5~3^4").

(* [comment removed for export] *)
Definition kimg_cut1 : ltac2:(zQ "30!h9!ik0!hg1>1a$0>1n$0>1K$1@1$2$1") := ltac2:(zQ "f1!ik0!ina!mo8!hta!h9!io7!va!hg1!jv3!hg8!or0!jv9!lp7!ir6!mi7&\2a0$5\2n0$3@3$2$0^3@1$1$0\1a$4\1n$4\1K$0M0\1K$0@1$7$0^1\2a0$5\1w$9\1v$3@3$2$0^4@1$1$0~0\2a0$5\2n0$3\1k$9@3$2$0^4@1$1$0\2lo$4\2hi$4M6\0$6@1$7$0@2$e@2$b^1^5@2$b@2$8^5^4^2@3$2$0^3@1$1$0@3$d$0M6\0$6@1$7$0@2$c^2^5@3$2$0@2$a^2^5@1$1$0@1$1$0M6\0$6@1$7$0@2$c@2$8^5^4^1@3$2$0@2$a@2$8^5^4^1@1$1$0@1$1$0\1e$3\1m$4@3$2$0^3@1$1$0\1e$3\2lo$4\2hi$4@3$2$0^4@1$1$0~0\2a1$5\2n1$3\2a2$5\2n2$3@3$2$0^5@1$1$0\2a0$5\2n0$3\1c$4@3$2$0^4@1$1$0~0").
Definition kimg_cut : ltac2:(zQ "30!hg1!h9!ik0>1k@1$0$2>1a$1>1n$1@1$0$2") := ltac2:(zQ "50!ik0!h9!hg1!or8!nge\1k@1$2$0\1a$1\1n$1@4$4$0$0@2$3^2^1^3").

(* [comment removed for export] *)
Definition kimg_clip : ltac2:(zQ "20!hg1!ik0>1k@1$0$1@1$0$1") := ltac2:(zQ "d0!hta!hkc!io7!h9!ik0!jv9!jse!hg8!va!hg1!os4!osd!mk2\1k@1$9$4@3$c$4\1K$4M4\1K$4$8^1\1a$2\1w$7\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\2k0$7$1\2lo$3\2hi$3@2$6@2$6@2$5@1$b?1A^2@2$5^2^1@2$5^1@1$a?1A\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$1\2a1$2\2n1$0\2a2$2\2n2$0$1\1a$2\1n$0\1c$3$1\1a$2\1n$0$1^1").

(* [comment removed for export] *)
Definition kreadZ : ltac2:(zQ "60!h9!hg1!hg8!iu3!hta!ik0>1k@1$1$5>1b$4>3off$0>1n$2@1$3$0") := ltac2:(zQ "h20!h9!hta!in3!hg1!hg8!km6!va!iu3!ina!jh0!jh9!ot6!ji2!hge!ik0!ote!ji9!jj2\1k@1$3$e\1b$1\3off$0\1n$4Mb\1x$b@1$7$0@8$f?4segs^4^3^2^1$d@1$8$6@1$8$5\1v$1\3scs@1$3$5\5hints@1$3$6M1\1v$1@1$7$0^3\1z$0M3\3scs@1$3$5@1$7$0^3@2$c$0@2$h1^1$h0\1s$5\1l@1$3$5@1$2$0\2n0$4@1$2$0\2op$9\1a$1\2b0$1@1$2$0\2op$9\1a$1\2b0$1@1$2$0\2op$a\1a$1\2b0$1@1$2$0\2op$a\1a$1\2b0$1@1$2$0\2sx$6\2lo$4\2n0$4\1e$1@1$2$0\2sx$6\2k0$4\1i$0\2n0$4@1$2$0\3scs@1$3$5\5hints@1$3$6@1$2$0@1$2$0").

Definition kreadZB : ltac2:(zQ "50!h9!hg8!iu3!hta!kuc>2bc$4>1b$3>3off$0>1n$1@1$2$0") := ltac2:(zQ "h20!h9!hta!in3!hg1!hg8!km6!va!iu3!ina!jh0!jh9!ot6!ji2!hge!ji9!kuc!oud!jj2\2bc$f\1b$1\3off$0\1n$4Mb\1x$b@1$7$0@8$h0?4segs^4^3^2^1$d@1$8$6@1$8$5\1v$1\3scs@1$3$5\5hints@1$3$6M1\1v$1@1$7$0^3\1z$0M3\3scs@1$3$5@1$7$0^3@2$c$0@2$h1^1$e\1s$5\1l@1$3$5@1$2$0\2n0$4@1$2$0\2op$9\1a$1\2b0$1@1$2$0\2op$9\1a$1\2b0$1@1$2$0\2op$a\1a$1\2b0$1@1$2$0\2op$a\1a$1\2b0$1@1$2$0\2sx$6\2lo$4\2n0$4\1e$1@1$2$0\2sx$6\1k$4\1i$0\2n0$4@1$2$0\3scs@1$3$5\5hints@1$3$6@1$2$0@1$2$0").

Lemma kreadZB_eqf : ltac2:(zQ "a0!h9!hg1!hg8!iu3!ljb!ovd!pg6!hta!ik0!lgf>2fk@1$1$8@3$4>1b$7>3off$0>1n$2@1$3$0@1$6@1$9^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##2Wp'0h01nh13acch22fkh35hintsi00!s/%h41li011lh53offh62rbh72rkh82sxi022sxh91xi031xh:2x0h;2x1i041ai052b0i061ei071ii081ki092k0i0:2loi0;2n0i0<2opi0=1si0>3scsi0?1vi0@1zp;1p;2p;3p;8p;6p;4p;5g00EVR0j12Tg00GCj1FTg00Kbj10Tg03iRj16j2Cj3;j4@Tg03j^j1Ej2<j3:j4ATg03kij27j85Tg00PFj13Tg03=`j28Tg00gjj29Tg00Qoj1DTg001Hj34Tg004Fj2BTg03m7j2=Tg03nHj2>Tg00A[j6?Tg01;_j51Tg00j5#2g01<aR1g004`R2g00iVR3%F2R4]0R5]5f0R6#0#6%E6P2P5f1R5#0/C61<56P3P4f2R7#0?;56A:756g005YR8%28g00k@R9#2g03o]R:]1]3]8^03^72^61R;p,4segsR<f3R='7P:P4P6P=P7P5g02WeR>%38R8%39R?O6P1P4P7P0P9P4P7g01>g,86,92%D2R9n10110>0002002010=101R0P9!s$/n0110?00081010@1010;3010<104105!s1D4010210:10;106!s4&810710;!t-+300033010?10>1!t[%>10000!uW$<f4!uY%P>P8P?G5!uN-!ty~!s4$9!ty%!v5%!t{B544X4;!u%%!u#&6!u%+!sgG,B4%0=R9,=<1>=<E?P9!sl%C@!sv'CA544eX;3D1X:2D1X91D1W2o"). Qed.
#[local] Hint Rewrite kreadZB_eqf : bceq.


(* [comment removed for export] *)
Definition kread8e : ltac2:(zQ "50!hta!hg1!iu3!h9!ik0>1k@1$1$4>1b$0>3off$3@1$2$0") := ltac2:(zQ "d0!hg1!hta!km6!in3!va!ina!iu3!ot6!ji2!hge!h9!ik0!ote\1k@1$0$b\1b$1\3off$aM7\1x$7@1$6$1@8$c?4segs^3^2^1N8$9@1$5$4@1$5$2\1v$1\3scs@1$0$2\5hints@1$0$4M0\3scs@1$0$2@1$6$1^2@2$8$1^3\1s$2\1l@1$0$2@1$3$1\3scs@1$0$2\5hints@1$0$4@1$3$1@1$3$1").

Definition kread8eB : ltac2:(zQ "40!hta!iu3!h9!kuc>2bc$3>1b$0>3off$2@1$1$0") := ltac2:(zQ "d0!hta!hg1!km6!in3!va!ina!iu3!ot6!ji2!hge!h9!kuc!oud\2bc$b\1b$0\3off$aM7\1x$7@1$6$0@8$c?4segs^3^2^1N8$9@1$5$4@1$5$2\1v$0\3scs@1$1$2\5hints@1$1$4M1\3scs@1$1$2@1$6$0^2@2$8$0^3\1s$2\1l@1$1$2@1$3$0\3scs@1$1$2\5hints@1$1$4@1$3$0@1$3$0").

Lemma kread8eB_eqf : ltac2:(zQ "90!hta!hg1!iu3!ljb!h9!ph0!pha!ik0!lgf>2fk@1$1$7@3$3>1b$0>3off$4@1$2$0@1$6@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##-op'0h03acch12fkh25hintsi00!s/%h31li011lh41nh53offh62rbh72rkh82sxh91xi021xh:2x0i031si043scsi051vp;1p;2p;8p;3p;6p;5g00EVR0j11Tg00GCj1DTg00Kbj12Tg040fj17j2<j3?Tg0423j1Cj2;j3@Tg03kij2:j85Tg0153j10Tg00PFj13Tg00gjj28Tg00Qoj19Tg001Hj36Tg004Fj2BTg03m7j2ATg03nHj2=Tg00A[j6>Tg01;_j54Tg00j5#1g01<aR1g004`R2%D1R3]5f0R4#2#7%C4P2P3f1R5#2/<41;54g00iVg005YR6%16g00k@R7#1g03o]R8]0]2]8]4^72^61R9p,4segsR:f2R;':P8P3P4P;P5g01=j#0!s$1R<g02WeR=%36R6%37R>O6P0P7P3P5181;%91R7n10110400020020103101R0P7P7n011020003301051041!sI%410000!tM$:f3P;P5P<P=P6P>G5P!saG563X39!sg%!se$4!sgR,B3%2;R7,A:1=;:E>A?754A@;54563eX:2D4X91D4W1o"). Qed.
#[local] Hint Rewrite kread8eB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kwritable (allkn k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xlo allkn wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinside allkn b off (ELit n) wb wk wn)%bool then true
      else kwritable allkn rest b off n
  | _ :: rest => kwritable allkn rest b off n
  end.

Local Open Scope lzb_scope.
Fixpoint kwritableB (bc : bctx) (k : list kentry) (b : expr) (off n : Z) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%lzb
          then match xloB bc wn with Some wl => Z.leb (off + n) (wk + wl) | None => false end
          else false)
      then true
      else if (Z.leb 0 n && Z.ltb n two64 && xinsideB bc b off (ELit n) wb wk wn)%lzb then true
      else kwritableB bc rest b off n
  | _ :: rest => kwritableB bc rest b off n
  end.
Local Close Scope lzb_scope.

Lemma kwritableB_eqf : ltac2:(zQ "90!hg1!h9!ik0!va!ljb!pi5!pj1!hta!lgf>2fk@1$0$2@3$4>1k@1$0$2>1b$7>3off$1>1n$1$3@1$6@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##B{p'0h01bh11nh23offh31kh42IHh51Kh62b1h72b2h81ei001eh92fkh:2k1i012k1h;2k2h<2n1i022n1h=2n2i032n2h>1oh?4resti041ai052a1i062a2i071ci082hii092k0i0:2loi0;1mi0<2n0i0=1vi0>1wi0?2wbi0@2wki0A2wli0B2wni0C1xp;1p;2p;3p;4p;5p;7p;6p;8g00EVj1TTg00Kbj11Tg043?j1Ej2Sj3Lj4Cj55Tg044Nj1Aj2Pj3Dj4Bj50Tg00PFj1RTg004Fj2>Tg02Omj2=Tg000kj23Tg045\j2Oj1ITg0259j28Tg018Vj2;Tg016Rj1:Tg046ej7Kj1@Tg017[j22Tg0482j2<j1HTg0498j79j1FTg00GCR0j1GTg04:Bj1JTg00A[j67Tg04;Oj1MTg01Y_j3NTg04<`j8?Tg01;_j56Tg001Hj3QTg005YR1f1R2f0R33Qp=4g00j5R4#TR5P5g01<aR6g004`R7P1^17R8]2R9]0%13#E%A3P6P9%12/S31P23P7P8f2R8#1?L23AD8!s9$1f3R9#1P8P2P3CCP9!s0&BP4f8R:#1!s8'D5P:!s2+0'4^17^27^06X35f7R;%R4!sC',>1X17X27X06f9R<!sk0<!sk8P1f:R=f4R>!sC'P4P1f6R?!sU$9P8P8P9g00mXR@P1P2P1!s$,1=;2RA133?RBg02WeRCn010!s#$20000RDP0!ub$?RE#1RF/O818;?1823RG'3RHPCn10110C00021010A00P!sk3Ig0069RJ!tI/g01>IRKf5RL'3RMg01>gRN,;LRO!sf4PPFP;P?%:LRFP2P3P8FK!sK3PJP>!s81!s4410400012010?10@P>P9P8!s>$9000:3010410>10=2!s1%<!s9&<1!s\%:1082010010;3!s-%!s9'410B40105102106103!sb,7!su'P4P1P?f>RQP:P?PLP>D0R:f=P;PLP>P9D0RRP:PRPRP:P!ws012AB!wP%1<E8P!w=HP!w6$12MOPEP;P?P!vZ'9RO'2PJPEP<!s>$LD0R<!vZR<P:PR!vZ~!vZ4RE'4X01P1^=6^;7^76^<6^:7^66RM%F=!vz%!v\$!v`5IP!z:,PP>!v+/O6!vV6!v+~!v+i/4EX0M%G7^86RM%H!uuA1P1P!~#&P>P8O1!yWO!vS&O!vE~!vE~EX>M!v:$LPRf<P?!~S%D0RMPRPMPMPR!|w2=?2133L'2!|}'Q818?L/3G!}&N3K>1;>N'2PQP?PL%:>!}1'!}/$:!vVR:PRPM!vV~!vV4,>1%1=R1#I%J=E7%@1%M=E!yU&!#:,%!#:'%O3E7P1AN4L>RL!sC+=P!s2'0'4e!#:r'W4X?5X54!sc'G?X17D6X27D6X06D6X35D6W9o"). Qed.
#[local] Hint Rewrite kwritableB_eqf : bceq.


Fixpoint kwritable_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%bool
          then match xhi allkn n, xlo allkn wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinside allkn b off n wb wk wn then true
      else kwritable_x allkn rest b off n
  | _ :: rest => kwritable_x allkn rest b off n
  end.

Local Open Scope lzb_scope.
Fixpoint kwritable_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KWr (SA wb wk) wn :: rest =>
      if (if (expr_eqb b wb && Z.leb wk off)%lzb
          then match xhiB bc n, xloB bc wn with
               | Some nh, Some wl => Z.leb (off + nh) (wk + wl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideB bc b off n wb wk wn then true
      else kwritable_xB bc rest b off n
  | _ :: rest => kwritable_xB bc rest b off n
  end.
Local Close Scope lzb_scope.

Lemma kwritable_xB_eqf : ltac2:(zQ "90!hg1!hta!ik0!va!ljb!h9!pje!pkc!lgf>2fk@1$0$2@3$4>1k@1$0$2>1b$1>3off$5>1n$1$3@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##Ejp'0h01bh11nh23offh31kh41oh52IHh61Kh72b1h82b2h91ei001eh:2fkh;2k1i012k1h<2k2h=2n1i022n1h>2n2i032n2h?4resti041ai052a1i062a2i071ci082hii092k0i0:2loi0;1mi0<2n0i0=2nhi0>1vi0?1wi0@2wbi0A2wki0B2wli0C2wni0D1xp;1p;2p;3p;4p;5p;7p;6p;8g00EVj1WTg00Kbj10Tg04=Bj1Ej2Vj3Mj4Cj55Tg04>Sj1Aj2Sj3Dj4Bj51Tg00PFj1UTg004Fj2=Tg02Omj2<Tg000kj24Tg04?cj2Rj1@Tg045\j2Qj1JTg0259j27Tg046ej7Lj1?Tg017[j2;Tg04@lj2:j1HTg0482j28j1ITg0498j79j1FTg00GCR0j1GTg04:Bj1KTg00A[j63Tg04B2j1NTg04;Oj1OTg01Y_j3PTg04<`j8>Tg01;_j56Tg001Hj3TTg005YR1f1R2f0R33Tp=2g00j5R4#WR5P5g01<aR6g004`R7P1^16R8]2R9]0%03#E%A3P6P9%02/V31S23P7P8f2R8#0?M23AD823P6P1f3R9#0P8P2P3CCP9!s0&BP4f8R:#0!s8'D5P:!s2+1'2^16^27^06X35f7R;%U4!sC',=1X16X27X06f9R<!sk0<!sk8P1f:R=f4R>!sC'P4P1f6R?!sU$9P8P8P9g00mXR@P1P2P1!s$,1<;2RA143?RBg02WeRCn010!s#$20000RDP0P7P1f?RE#0RFf5RG'R!s:&@RH#0/Q917:21783RI'4RJPCn10110D00021010B00RK!s<4=00P!t;3Lg0069RM!tk$FP;P?PGP2P3P8FLPMP>!sU1!s4410400012010@10AP>P9P8!s>$9000:3010410?10>2!s1%<!s9&<1!s\%:1082010010;3!s-%!s9'410C40105102106103!sb,7!su'P4P1P?f>RFP:!u2$>D1R:f=P;PGP>P9D1RNP:PNPNP:P!wS01;AB!vt%1:EGR!s2'8H9P!vo8!vmGP!vf%E!vf09PMPEP<!s:%D1R<!wI2H!vtD<P:PN!vt~!vt4RA'2X01P1^>6^<7^86^=6^;7^76RO%F=!w<%!vv$!vz5L!u|&>!u|/O6PMP<!ydR!un~!un9/2AX0O%G7^96RO%H!u_A1P1P!}c&P>PGO1PK!y;J!xa~!uq_4OPO%I!ukM!|B&PGP9O1!|D`!v/~!v/b4!uV$Nf<P?!#54$D1ROPNPOPOPN!v611<?2143G';!#3^&F>!s0&8E917;2/4I!#3aaF!|a$>!#3a,:!|cR:PNPO!vg~!vg4,=1%0=R1#J%K=E3%@1%N=E3%?1%O=E3!|K$!#<_&!#<]%O3E3P1AP4G>RG!sC+=P!s2'1'2e!#=L'W5X?5X64!sc'G>X16D6X27D6X06D6X35D6W:o"). Qed.
#[local] Hint Rewrite kwritable_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kzero_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinside allkn b off n zb zk zn then true
      else kzero_x allkn rest b off n
  | _ :: rest => kzero_x allkn rest b off n
  end.

Local Open Scope lzb_scope.
Fixpoint kzero_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) : bool :=
  match k with
  | [] => false
  | KZero (SA zb zk) zn :: rest =>
      if (if (expr_eqb b zb && Z.leb zk off)%lzb
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if xinsideB bc b off n zb zk zn then true
      else kzero_xB bc rest b off n
  | _ :: rest => kzero_xB bc rest b off n
  end.
Local Close Scope lzb_scope.

Lemma kzero_xB_eqf : ltac2:(zQ "90!hg1!hta!ik0!va!ljb!h9!plb!pm5!lgf>2fk@1$0$2@3$4>1k@1$0$2>1b$1>3off$5>1n$1$3@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##Ejp'0h01bh11nh23offh31kh41oh52IHh61Kh72b1h82b2h91ei001eh:2fkh;2k1i012k1h<2k2h=2n1i022n1h>2n2i032n2h?4resti041ai052a1i062a2i071ci082hii092k0i0:2loi0;1mi0<2n0i0=2nhi0>1vi0?1wi0@1xi0A2zbi0B2zki0C2zli0D2znp;1p;2p;3p;4p;5p;7p;6p;8g00EVj1WTg00Kbj10Tg04C?j1Ej2Vj3Mj4Cj55Tg04DLj1Aj2Sj3Dj4Bj51Tg00PFj1UTg004Fj2=Tg02Omj2<Tg000kj24Tg04?cj2Rj1@Tg045\j2Qj1JTg0259j27Tg046ej7Lj1?Tg017[j2;Tg04@lj2:j1HTg0482j28j1ITg0498j79j1FTg00GCR0j1GTg04:Bj1KTg00A[j63Tg04B2j1NTg04;Oj1OTg01Y_j3PTg04<`j8>Tg01;_j56Tg001Hj3TTg005YR1f1R2f0R33Tp=2g00j5R4#WR5P5g01<aR6g004`R7P1^16R8]2R9]0%03#E%A3P6P9%02/V31S23P7P8f2R8#0?M23AD823P6P1f3R9#0P8P2P3CCP9!s0&BP4f8R:#0!s8'D5P:!s2+1'2^16^27^06X35f7R;%U4!sC',=1X16X27X06f9R<!sk0<!sk8P1f:R=f4R>!sC'P4P1f6R?P9g00mXR@P1P2P1!s$,1<;2RA143?RBg02WeRCn010!s#$20000RDP0P7P1f?RE#0RFf5RG'R!s:&@RH#0/Q917:21783RI'4RJPCn10110@00021010C00RK!s<4=00P!t;3Lg0069RM!tk$FP;P?PGP2P3P8FLPMP>!sU1!s4410400012010A10B!vC$8!s+$>P9P8!sH$9000:3010410?10>2!s1%D!s9&<1!sf%:1082010010;3!s-%!s9'410<40105102106103!sb,7!sG'P4P1P?f>RFP:!u<$>D1R:P!wG01;AB!vh%1:EGR!s2'8H9P!vc8!vaGP!vZ%E!vZ09PMPEP<!s:%D1R<!w=2H!vhD:f=P;PGP>P9D1RAPAP:PAP<P:PA!vt~!vt4RN'2X01P1^>6^<7^86^=6^;7^76RO%F=!w<%P!w-/L!v0&>!v0/O6PMP<!ydR:P!un~!unA/2NX0O%G7^96RO%H!u_71P1P!}c&P>PGO1PK!yGJH!uq~!uqh4OPO%I!ukC!|N&PGP9O1!|P`!v/~!v/l4!u`$A!v&11<?2143G';!#3^&F>!s0&8E917;2/4I!#3aaF!|U$>!#3a,:!|WRAf<P?!#79$D1R?P?PA!xE$AP?!vg~!vg4,=1%0=R1#J%K=E3%@1%N=E3%?1%O=E3!|U$!#<_&!#<]%O3E3P1AP4G>RG!sC+=P!s2'1'2e!#=L'W5X?5X64!sc'G>X16D6X27D6X06D6X35D6W:o"). Qed.
#[local] Hint Rewrite kzero_xB_eqf : bceq.



(* [comment removed for export] *)
Fixpoint kfill_x (allkn k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%bool
          then match xhi allkn n, xlo allkn zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinside allkn b off n zb zk zn)%bool then true
      else kfill_x allkn rest b off n c
  | _ :: rest => kfill_x allkn rest b off n c
  end.

Local Open Scope lzb_scope.
Fixpoint kfill_xB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (n : expr) (c : Z) : bool :=
  match k with
  | [] => false
  | KFill (SA zb zk) zn c' :: rest =>
      if (if (Z.eqb (c' mod 256) (c mod 256) && expr_eqb b zb && Z.leb zk off)%lzb
          then match xhiB bc n, xloB bc zn with
               | Some nh, Some zl => Z.leb (off + nh) (zk + zl)
               | _, _ => false
               end
          else false)
      then true
      else if (Z.eqb (c' mod 256) (c mod 256) && xinsideB bc b off n zb zk zn)%lzb then true
      else kfill_xB bc rest b off n c
  | _ :: rest => kfill_xB bc rest b off n c
  end.
Local Close Scope lzb_scope.

Lemma kfill_xB_eqf : ltac2:(zQ "90!hg1!h9!hta!ik0!va!ljb!pn0!pna!lgf>2fk@1$0$3@3$5>1k@1$0$3>1b$2>3off$1>1n$2>1c$1$4@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##IGp'0h01bh11ch21nh33offh41kh51oh62IHh71Kh82b1h92b2h:1ei001eh;2fkh<2k1i012k1h=2k2h>2n1i022n1h?2n2i032n2h@4resti041ai052a1i062a2i072c'i082hii092k0i0:2loi0;1mi0<2n0i0=2nhi0>1vi0?1wi0@1xi0A2zbi0B2zki0C2zli0D2znp;1p;2p;3p;4p;5p;6p;7p;9g00EVj1]Tg00Kbj10Tg04EXj1Kj2\j3Rj4Fj5Cj66Tg04Fej1Dj2Uj3Jj4Ej5Bj61Tg00PFj1VTg004Fj2@Tg002^j12Tg003Cj1TTg03=`j29Tg04H1j2>Tg02Omj2<Tg000kj27Tg04?cj2Ij1ATg045\j2Hj1PTg0259j2:Tg046ej7Gj1[Tg017[j24Tg04@lj2=j1NTg0482j2?j1OTg0498j7;j1LTg00GCR0j1MTg04:Bj1QTg00A[j68Tg04B2j1STg04;Oj1ZTg01Y_j3YTg04<`l9WTg01;_j55Tg001Hj3XTg005YR1f1R2f0R33Xp=3g00j5R4#]R5P5g01<aR6g004`R7P1^17R8^26R9]3R:]0%03#K%D3P6P:%02/\31U23P7P9f2R9#0?R23AJ923P6P8f3R8#0P9P2P3CFP8!s0&EP7P1f4R:#0!s:'DCP:!s2+BP4f:R;#0!s:,E6P;!s4-1'3^17^26^37^06X45f9R<%V4!sH,,@1X17X26X37X06f;R=!sw2=!sw=P1f<R>f5R?!sH,P4P1f7R@!s8$8P9!s+&:g00mXRAP1P9P1!s$1g006Y#2!s$2TRB,99RCf6RD/9B'>RE1<<2RFg02WeRGn010!s#$20000f8RH,73RIP!s?2RJP0!vg$BRK#0RL/I@!s7&CRM#0/H:1:;21:93RN'7ROPGn10110@00021010C00RP!s<4=00!t84Qg0069RR!uP+EPLP<PHP@P2P3P8FG!sY3PRP?!s81!s4410400012010A10BP9!s:$9000:3010410?10>2!s1%<!s9&<1!sX%:1082010010;3!s-%!s9'410<40105102106103!sb&D107!sG'P4P1P@f@P<P@PDP?P:E1RLf?PH!s4%P8E1RSPLPSP!s+$fARTP;!uh$DP?E1R;P!x`014EF/4I!wG%1=K@R!s2'?M:P!wB8!w@GP!w9%K!w30;RM,4EPRPKP=!s?&DE1R=!w6RS!w6~!w64RF'3X01P1^?6^=7^96^>6^<7^86RU%L>!wV%!w6$!w:+P!w&/QP!z</?!v//O6!vU6!v+~!v+e/3FX0U%M7^:6RU%N!uuE1P1P!~N&P?P@O1PP!yVN!vS%M!vEE!y[6!vG~!vGI5UPU%O!vAQ!}3&PDP:O1!}5`!v/~!v/^4!uR$Sf>P@!#4\$P9E1RUPSPUP!s+%L!v8119?B,>CRC1<H2'4173@'4!#4\&TD!s0&?K:1:<2/7N!#4_aT!#6$%!#4_%,4CPRP;!}IRU!vw~!vw4,@1%0>R1#P%Q>E8%A1%S>E8%[1%Z>E8!},$!#>y+!#>w'O4E8P1AY4D?RD!sG->P!s4,1'3e!#?q-W6X@5X74!sl,M9WX17D5X26D5X37D5X06D5X45D5W;o"). Qed.
#[local] Hint Rewrite kfill_xB_eqf : bceq.



(* [comment removed for export] *)
Definition off_image_x : ltac2:(zQ "50!hta!va!hg1!h9!ik0>1k@1$2$4>1b$0>3off$3>1n$0$1") := ltac2:(zQ "90!osd!iie!hta!hg1!h9!os4!ik0!ln8!loa\1k@1$3$6\1b$2\3off$4\1n$2@7$7^4^3^2^1@1$1Z@1$0?1A@1$1@2$8@1$5?1A@1$0?1A").

Definition off_image_xB : ltac2:(zQ "40!hta!va!h9!kuc>2bc$3>1b$0>3off$2>1n$0$1") := ltac2:(zQ "80!osd!iie!hta!h9!os4!kuc!lpd!loa\2bc$5\1b$2\3off$3\1n$2@7$6^4^3^2^1@1$1Z@1$0?1A@1$1@2$7@1$4?1A@1$0?1A").

Lemma off_image_xB_eqf : ltac2:(zQ "90!hta!va!hg1!ljb!h9!po5!pp3!ik0!lgf>2fk@1$2$7@3$3>1b$0>3off$4>1n$0$1@1$6@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh12b1h22b2h32fkh42k1h52k2h61nh72n1h82n2h93offh:1xh;2x0h<2x1p;1p;2p;3p;7p;6p;4p;5g00EVj1ETg00Kbj10Tg04HNj1;j2Dj3<j4?Tg04I_j15j2Bj3:j4@Tg013bj16j74Tg016Rj13Tg04Joj17Tg04L:j18Tg0189j29Tg001Hj32Tg004Fj2CTg0193j1ATg01:Gj1=Tg00A[j6>Tg01;_j51Tg00j5#Eg01<aR0g004`R1g005YR2^60R3]9f0R4#0#;%54P1P3f1R3#0/D41B34P0P2f2R5#0?<34A:534P2^80^51^20^70^41^10R6f3R7#6P4P7P5P3g01>I#3R8p,1AR9#7R:%89/9:#3R9O6f4P7P5P3P8P:P9F4522X06P7P5P3P4P8P:P9F4,C2%07R9#A%=7E>P9P5P3P4C?P7P5P3P4C@522eX<0D1X;1D1X:0D1W3o"). Qed.
#[local] Hint Rewrite off_image_xB_eqf : bceq.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition flat_x : ltac2:(zQ "50!hta!va!hg1!h9!ik0>1k@1$2$4>1b$0>3off$3>1n$0$1") := ltac2:(zQ "h00!h9!iu3!va!kj1!hge!jv3!jse!hta!jv9!hg1!pq2!ik0!ji9!ooe!oq9!lp7\1k@1$9$b\1b$7\3off$0\1n$7M1\1x@1$1@2$3$0$0$2@2$a^4^3\1p@2$3$0$0M3\1p@2$3$0$0$2^1\2lo$0\2hi$0M1\1x@1$1$0$2@2$e^7^4\2nl$0M1\1x@1$1$0$2@2$d^8^5\2nh$0@2$6@2$6@2$8Z@2$5^4^7@2$8@2$5@2$5^3^7^1$c@2$fZ^2$4$4$4").

Local Open Scope lzb_scope.
Definition flat_xB : ltac2:(zQ "40!hta!va!h9!kuc>2bc$3>1b$0>3off$2>1n$0$1") := ltac2:(zQ "e0!h9!va!iu3!hge!kj1!jv3!hta!jv9!ji9!no0!kuc!pr0!pr8!lp7\2bc$a\1b$6\3off$0\1n$6M2\1x@1$2@2$4$0$0$1@2$9^4^3\1p@2$4$0$0M4\1p@2$4$0$0$1^1\2lo$0\2hi$0M2\1x@1$2$0$1@2$c^7^4\2nl$0M2\1x@1$2$0$1@2$b^8^5\2nh$0M1\0$1$1M1\0$1$1@2$7Z@2$5^4^7@2$7@2$5@2$5^3^7^1$8$3@2$dZ^2$3$3$3$3").
Local Close Scope lzb_scope.

Lemma flat_xB_eqf : ltac2:(zQ "90!hta!va!hg1!ljb!h9!ps0!ps9!ik0!lgf>2fk@1$2$7@3$3>1b$0>3off$4>1n$0$1@1$6@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##5Cp'0h01oh11eh22fkh31nh43offh51xi001xh62x0h72x1i012hii022loi032nhi042nli051pp;1p;2p;3p;6p;4p;5g00EVj1QTg00Kbj10Tg04MEj1Bj2Pj3Gj4LTg04NQj1>j2Nj3Aj4MTg00GCR0j18Tg04@lj1?j27!s=$eR1j2=Tg029@j2<j1ETg045\j2;j1HTg0259j21Tg000kj22Tg018Vj2OTg04O\j2:j1CTg0482j29j1FTg017[j23Tg001Hj34Tg004Fj2DTg04Pij1@Tg00A[j65Tg04:Bj1ITg04?cj1JTg04B2j1KTg01;_j56Tg00j5#Qg01<aR2g004`R3g005YR4^32R5]4f0R6#0#B%>6P3P5f1R5#0/P61N56P2P4f2R7#0?G56AA756%83^12R8f3R9#?P01=33R:P4f4R;#0/<9R<P1P3P3P4P6P0P3P4f7R=#0/;;!s5%P;f5R>O1P4!s$%g01>IR?119='2R@117=/16g01>gRA'2RBg02WeRCn010!s#$200001O?5RDP!s<2REPCn101!s:%21010300!s:4400n20011050001201!s>$!sN4500P0P:P41:;9!uM319=;RF!uY&8/7>R>13@B/3D!tRsRB544X08P8%F9!t_%P!w+4P9P;O1!s2&>P!v#8!v=6!tUN=44BX08%8:!xp$%C!tZ'6P9O1!t^4FP!t<g!wF'97!ym46R1/99!wS&7=;1191,2?1171/16/2A'3!wSv,D4%09RC#E%@9E5%HC%I9E5%JC%K9E5PCP7P5P6CLP9!s0&M544eX72D6X63D6X52D6W2o"). Qed.
#[local] Hint Rewrite flat_xB_eqf : bceq.



(* [comment removed for export] *)
Definition ehi : ltac2:(zQ "50!hg1!iu3!h9!hta!ik0>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "40!hg1!hta!ik0!ooe\1k@1$0$2\1e$1@2$3^2^1").
Definition elo : ltac2:(zQ "50!hg1!iu3!h9!hta!ik0>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "40!hg1!hta!ik0!oq9\1k@1$0$2\1e$1@2$3^2^1").

(* [comment removed for export] *)
Definition len_eqb : ltac2:(zQ "40!hta!va!hg1!ik0>1k@1$2$3>1n$0>1m$0$1") := ltac2:(zQ "c2!hta!h9!kj1!mo8!ina!kka!pt3!jse!hg1!mi7!ju7!ik0&@3$3@2$2$0$1@4$5$0$1^2Z@1$4@2$2$0$1&@3$3@2$2$0$1@4$5$0$1^1Z@1$4@2$2$0$1\1k@1$8$b\1n$0\1m$0@2$9@2$a^2^1@2$7@3$6^3~0~1@3$6^3~1~0").

Local Open Scope lzb_scope.
Definition len_eqbB : ltac2:(zQ "30!hta!va!kuc>2bc$2>1n$0>1m$0$1") := ltac2:(zQ "b2!hta!h9!kj1!mo8!ina!kka!pte!jse!mi7!ju7!kuc&@3$3@2$2$0$1@4$5$0$1^2Z@1$4@2$2$0$1&@3$3@2$2$0$1@4$5$0$1^1Z@1$4@2$2$0$1\2bc$a\1n$0\1m$0@2$8@2$9^2^1@2$7@3$6^3~0~1@3$6^3~1~0").
Local Close Scope lzb_scope.

Lemma len_eqbB_eqf : ltac2:(zQ "80!hta!va!hg1!ljb!pua!pv4!ik0!lgf>2fk@1$2$6@3$3>1n$0>1m$0$1@1$5@1$7^1@1$4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh12fkh21mh33negh43posh51xh62x0p;1p;2p;3p;6p;5p;4g00EVj1GTg00Kbj12Tg04R=j1=j2Fj3@Tg04SJj1:j2Ej3ATg04TVj1>j30Tg02Omj27Tg00Gej2;Tg00PFj19Tg01Y_j31Tg017[j23Tg01OEj25Tg001Hj38Tg004Fj2DTg04U`j1CTg04Vmj1BTg00A[j6?Tg01;_j56Tg023Zj4<Tg01<aR0g004`R1f0R2g01>IC<p=4g00j5#GP0g005YR3^20%22#=%:2P0P3f1R4#2/F21E42g04X>R5P3^35]4R5f2R6#>1764R7P21;01R1%46%91R831R9%44=118R:O2P2P:P9O2'3'5f3R;?09:A0;:9'3,57583X051742%42=118R8906:A068:'3'5,D3%26R8#C%B6E?A@842AA642583eX60D6X50D6W1o"). Qed.
#[local] Hint Rewrite len_eqbB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_diff : ltac2:(zQ "30!hta!iu3!h9>1e$0>1f$0@1$1$2") := ltac2:(zQ "c0!hta!h9!in3!hg8!va!jh0!jh9!ji2!iu3!pvf!ji9!jj2\1e$0\1f$0M0\1x$0@1$8$1@2$9^2^1\1z$1@2$7$1@2$b^1$a\1n$3@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2sx$4\2lo$3\1n$3\2e0$0@1$2$1\2sx$4\1k$3\1i$1\1n$3@1$2$1").

(* [comment removed for export] *)
Definition page_aligned : ltac2:(zQ "40!va!hg1!hta!ik0>1k@1$1$3>1e$2$0") := ltac2:(zQ "c3!hta!qg6!jv9!hg8!va!h9!jh0!jh9!hg1!ik0!ln2!jj2&\1a$0\1b$0@2$2+c@2$1^5^4&\2op$6~0&\2op$7~0\1k@1$8$9\1e$0M0\1e$0$4^1\1z$5@2$a@2$b^1+hgg0Z\1n$3@2$2+c@2$1^3^2~1~1~2~2\2sx$4\2lo$3\1n$3\2e0$0@2$2+c@2$1^6^5\2sx$4\2k0$3\1i$5\1n$3@2$2+c@2$1^6^5").

Definition page_alignedB : ltac2:(zQ "30!va!hta!kuc>2bc$2>1e$1$0") := ltac2:(zQ "b3!hta!qh0!jv9!hg8!va!h9!jh0!jh9!kuc!ln2!jj2&\1a$0\1b$0@2$2+c@2$1^5^4&\2op$6~0&\2op$7~0\2bc$8\1e$0M0\1e$0$4^1\1z$5@2$9@2$a^1+hgg0Z\1n$3@2$2+c@2$1^3^2~1~1~2~2\2sx$4\2lo$3\1n$3\2e0$0@2$2+c@2$1^6^5\2sx$4\1k$3\1i$5\1n$3@2$2+c@2$1^6^5").

Lemma page_alignedB_eqf : ltac2:(zQ "80!va!hg1!ljb!qhb!qia!hta!ik0!lgf>2fk@1$1$6@3$2>1e$5$0@1$4@1$7^1@1$3^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##04p'0h01ei001eh12fkh21xh31zi011zi021ai031bi042e0i051ii061ki072k0i082loi091ni0:2opi0;2sxp;1p;2p;3p;6p;5g00EVj1DTg00Kbj16Tg04YGj1;j2>Tg04ZYj17j2?Tg04[jj1Cj22Tg003Cj15Tg03=`j2:Tg04H1j29!sA$aj18Tg000kj20Tg001Hj33Tg004Fj2BTg04]3j1ATg04^?j1@Tg00A[j6=Tg01;_j5<Tg002^j14Tf0R0#4#4p=1g00j5#Dg01<aR1g005YR2%60#;%70g004`^01R3f1R4#CP1P2P4g006YR5#1!s$-5,:0g01>I'9R6%85#1#5R5P4f2R7O1'0f3R8f4R9O1,05R:P!s$%9f5R:!s9%;P;n01100000810101101093010:102103!s1D4010;108109104!s4&6105109!u0%P61287,0512:9!tD&P;P;f6/2:!tg&!tTx7!tT%532X33!tZ$0P61274!tZ$98,05R5P!s$%!v${!tR&,B2%64R;#A%@4E=1>;01?40532eX21D<W1o"). Qed.
#[local] Hint Rewrite page_alignedB_eqf : bceq.



(* [comment removed for export] *)
Definition kn_contra : ltac2:(zQ "30!va!hg1!ik0>1k@1$1$2$0") := ltac2:(zQ "h9i0!h9!kj1!hta!hg1!va!hge!lp7!jse!iu3!kje!io7!kj8!hg8!mi7!qja!qk4!qkb!ql5!ji9!jv9!ik0!jh0!jh9!hkc!nlb&@3$h1@1$e^d@3$b$0@1$3@2$1$0$2^5@3$9$0@1$3@2$1$0$2^5&@2$7@2$7@2$h3Z^2@2$6^1$h2@2$d@2$6^1^d@2$6^c^2&\1b$0~1&\1a$0~2&M1\1p@2$1$0$0$4^1~3&\1p@2$1$0$0~4&M8\1x@1$8@2$1$0$0$4~0~5$5&\2l1@1$3@2$1$0$2~6&\2p0@2$1$0$2~7&M3\2l0@1$3@2$1$0$2$4^1$5~8&\2l0@1$3@2$1$0$2~9&\1p@2$1$0$2~a&M3\1x@1$3@2$1$0$2$4@3$9$0@1$3@2$1$0$2^1$5~b&=1l$f@1$h0^6~c&\1b$2~d&\1a$2~e&\2op$h5~f&\2op$h6~f&@3$h1@1$e^e@3$b$0@1$3@2$1$0$2^5@3$9$0@1$3@2$1$0$2^5&@2$7@2$7@2$h3Z^2@2$6^1$h2@2$d@2$6^1^e@2$6^d^2&\1b$0~h3&\1a$0~h4&M1\1p@2$1$0$0$4^1~h5&\1p@2$1$0$0~h6&M8\1x@1$8@2$1$0$0$4~h2~h7$5&\2l1@1$3@2$1$0$2~h8&\2p0@2$1$0$2~h9&M3\2l0@1$3@2$1$0$2$4^1$5~ha&\2l0@1$3@2$1$0$2~hb&\1p@2$1$0$2~hc&M3\1x@1$3@2$1$0$2$4@3$9$0@1$3@2$1$0$2^1$5~hd&=1l$f@1$h0^7~he\1k@1$3$h4@3$h8$h4\1K$h4Mh4\1K$h4$4^1\1a$a\1w$c\1v$2$5\1a$a\1n$2$5\1a$a\1n$2\2k0$c$5\2lo$0\2hi$0$5\1e$2\1m$0$5\1e$2\2lo$0\2hi$0M4\0$4$4@2$6^1^2$h7M2\1e$2$4^3\1z$0=1l$f@1$h0^4M3\1x@1$3@2$1$0$2$4@3$9$0@1$3@2$1$0$2^1$5\1p@2$1$0$2\2l0@1$3@2$1$0$2M3\2l0@1$3@2$1$0$2$4^1$5\2p0@2$1$0$2\2l1@1$3@2$1$0$2M8\1x@1$8@2$1$0$0$4@3$h1@1$e^b@3$b$0@1$3@2$1$0$2^5@3$9$0@1$3@2$1$0$2^5\1p@2$1$0$0M1\1p@2$1$0$0$4^1\1a$0\1b$0@2$7@2$7@2$h3Z^2@2$6^1$h2@2$d@2$6^1^b@2$6^a^2$5\1n$c$5~h0~h0~h1~h1\2sx$4\3lo0$c\1n$c\2e0$2~hf\2sx$4\2k0$c\1i$0\1n$c~hf\1a$a\1n$2$5\2a1$a\2n1$2\2a2$a\2n2$2$5\1a$a\1n$2\1c$0$5\1a$a\1n$2$5^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition caller_saved : ltac2:(zQ "20!hg1!hg8@1$0$1") := ltac2:(zQ "30!hg8!mo8!ina@3$1$0N1@3$1$0N5@3$1$0N6@3$1$0N7@3$1$0Na@3$1$0Nb@3$1$0Nc@3$1$0Nd@3$1$0Ne@3$1$0Nf@3$1$0Nh0@3$1$0Nh1@3$1$0Nhc@3$1$0Nhd@3$1$0Nhe@3$1$0Nhf@1$2$0").

Fixpoint sr_fresh (sr : list expr) (ixs : list nat) (nx : nat) : list expr :=
  match ixs with
  | [] => sr
  | i :: t => sr_fresh (sr_upd sr i (EVar nx)) t (S nx)
  end.

Definition NCS : nat := 16.

Definition ret_lit : ltac2:(zQ "30!iu3!h9!ig3>2cs$2@1$0$1") := ltac2:(zQ "h10!h9!hta!in3!hg8!va!jse!iu3!jh0!jh9!ji2!ig3!jk4!ji9!ln2!jv9!lp7!jj2\2cs$aM1\1x$1@1$6$0@2$b^1N1\1r$0M4\0$4@1$6$0@2$5@2$5@2$d@2$h0^1+2Z@2$f^1$c@2$eZ^1@2$9$0^1@1$2$0\1n$3@1$2$0\2op$7\1a$1\1b$1@1$2$0\2op$7\1a$1\1b$1@1$2$0\2op$8\1a$1\1b$1@1$2$0\2op$8\1a$1\1b$1@1$2$0\2sx$4\2lo$3\1n$3\1e$1@1$2$0\2sx$4\1k$3\1i$0\1n$3@1$2$0").

(* [comment removed for export] *)
Definition after_call : ltac2:(zQ "60!iu3!ig3!hg1!h9!hta!ik0>2cs$1>3ret$3>2rv@1$0$4>2k'@1$2$5@1$0$1") := ltac2:(zQ "ha0!hta!iu3!hg1!ig3!va!jse!in3!ji2!hg8!hkc!itc!h9!qm2!ii7!qm8!kh2!kn2!qn7!ipa!qo4!iq2!ik0!ilc!ij6!iqc!im6\2cs$3\3ret$b\2rv@1$1$0\2k'@1$2$h5=2ss$h9@1$d^4=2nx$8@1$h6^1=3sr1@1$2$0@3$h3@1$h7^2$e^1=3sr2@1$2$0M1\2rv@1$1$0@1$2$0^5\1e$0@3$h8^2Na^1^1M4\0$4@1$1$3@2$5@2$5@1$h0^8@2$h1^3^5M1\2rv@1$1$0$4^6\1e$0@2$f^4^1$9@2$7$3@2$h4^8@4$h2^7^1^5@2$a^3$c@1$6$3").
(* [comment removed for export] *)
Definition after_call2 : ltac2:(zQ "70!iu3!ig3!hg1!hg8!h9!hta!ik0>2cs$1>3ret$4>2rv@1$0$5>2k'@1$2$6>5extra$3@1$0$1") := ltac2:(zQ "ha0!hta!iu3!hg1!itc!ig3!va!jse!hg8!qm2!in3!ji2!hkc!h9!ii7!qm8!kh2!kn2!qn7!ipa!qo4!iq2!ik0!ilc!ij6!iqc!im6\2cs$4\3ret$c\2rv@1$1$0\2k'@1$2$h5\5extra$7=2ss$h9@1$d^5=2nx$7@1$h6^1=3sr1@1$2$0@3$h3@1$h7^2$e^1=3sr2@1$2$0M1\2rv@1$1$0@1$2$0^6\1e$0@3$h8^2Na^1^1M5\0$5@1$1$4@2$6@2$6@1$h0^9@2$h1@2$3@2$3^3$8^5^6M1\2rv@1$1$0$5^7\1e$0@2$f^4^1$b@2$a$4@2$h4^9@4$h2^8^1^6@2$3@2$3^3$8^5@1$9$4").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition page_up : ltac2:(zQ "10!h9>3len$0$0") := ltac2:(zQ "40!h9!jv3!qof!qp5\3len$0@2$3@2$2@2$1^1+vvf+hgg0+hgg0").

Definition is_ecall_at : ltac2:(zQ "20!va!ig3>2cs$1$0") := ltac2:(zQ "f0!qpb!qq1!jse!iu3!qs3!va!hge!rg0!rge!ig3!ji9!jv3!jv9!lp7!rha\2cs$9@2$2@2$2@2$cZ@1$1^1@2$d@2$b@1$1^1+4$aM3\1x@1$3@1$4@1$0#i0$5@2$7?4segs@2$e@1$0#k0@1$1^1\1w@1$4@1$0#i0@1$8^1$6").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xlo1 : ltac2:(zQ "50!hg1!iu3!h9!hta!ik0>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "h1hb!h9!iu3!kj1!ji2!ri5!hta!in3!qja!rj3!rk1!hg8!va!jh0!jh9!hg1!ik0!nm6&\3lo'$0\2z0$0@2$3$0@2$9^5^2&M2\2p0@2$2$0$0@1$1$0^1~0&\2p0@2$2$0$0~1&M2\1p@2$2$0$0@1$1$0^1\3lo'$0\1z$0@2$3$0^2&\1p@2$2$0$0~3&M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0@2$3$0^2&\1p@2$2$0$0~5&M1\1x@1$1@2$2$0$0@1$1$0@2$4^8^7~2@2$3$0^2&\1z$0~7&\2lo$0~8&M2\1p@2$2$0$0@1$1$0^1~9&\1p@2$2$0$0~a&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^5^4~4~c&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~b~d&\1b$5~e&\1a$5~f&\2op$c~h0&\2op$d~h0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^9^8~2@2$3$0^2&\1z$0~h3&\2lo$0~h4&M2\1p@2$2$0$0@1$1$0^1~h5&\1p@2$2$0$0~h6&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~4~h8&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~h7~h9\1k@1$e$f\1e$5M5\1e$5@1$1$0^1\1z$0@2$3$0@1$h0^1\1n$aM1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~2@2$3$0^2M1\1x@1$1@2$2$0$0@1$1$0@2$4^3^2~4M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~6@1$6$0~h1~h1~h2~h2\2sx$b\2lo$a\1n$a\2e0$5~ha\2sx$b\2k0$a\1i$0\1n$a~ha").

Definition xlo1B : ltac2:(zQ "40!iu3!h9!hta!kuc>2bc$3>1e$2@1$0$1") := ltac2:(zQ "h0hb!h9!iu3!kj1!ji2!rk7!hta!in3!rl6!rm1!rk1!hg8!va!jh0!jh9!nm6!kuc&\3lo'$0\2z0$0@2$3$0@2$9^5^2&M2\2p0@2$2$0$0@1$1$0^1~0&\2p0@2$2$0$0~1&M2\1p@2$2$0$0@1$1$0^1\3lo'$0\1z$0@2$3$0^2&\1p@2$2$0$0~3&M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0@2$3$0^2&\1p@2$2$0$0~5&M1\1x@1$1@2$2$0$0@1$1$0@2$4^8^7~2@2$3$0^2&\1z$0~7&\2lo$0~8&M2\1p@2$2$0$0@1$1$0^1~9&\1p@2$2$0$0~a&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^5^4~4~c&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~b~d&\1b$5~e&\1a$5~f&\2op$c~h0&\2op$d~h0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^9^8~2@2$3$0^2&\1z$0~h3&\2lo$0~h4&M2\1p@2$2$0$0@1$1$0^1~h5&\1p@2$2$0$0~h6&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~4~h8&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~h7~h9\2bc$f\1e$5M5\1e$5@1$1$0^1\1z$0@2$3$0@1$e^1\1n$aM1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~2@2$3$0^2M1\1x@1$1@2$2$0$0@1$1$0@2$4^3^2~4M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~6@1$6$0~h1~h1~h2~h2\2sx$b\2lo$a\1n$a\2e0$5~ha\2sx$b\1k$a\1i$0\1n$a~ha").

Lemma xlo1B_eqf : ltac2:(zQ "90!hg1!iu3!ljb!h9!rn0!rn7!hta!ik0!lgf>2fk@1$0$7@3$2>1e$6@1$1$3@1$5@1$8^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##Fop'0h01oh11ei001eh22fkh31xi011xi021ai031bi042e0i051ii061ki072k0i082loi093lo'i0:1ni0;2opi0<1pi0=2p0i0>2sxi0?1zi0@2z0p;1p;2p;3p;6p;5g00EVj1MTg00GCR0j19Tg00Kbj12Tg04_Oj1<j2GTg04`Yj1Lj2=!sR$eR1j2KTg04abj1Dj20Tg01lcj1@Tg00gjj28Tg04boj27j1BTg04d;j2;!s/$Xj25j1?Tg00Qoj1:Tg04ehj23j1HTg04g1j21j1JTg001Hj34Tg004Fj2CTg04h>j1ATg00A[j66Tg04iNj1ETg04jbj1>Tg04l2j1FTg01;_j5ITg00j5#Mg01<aR2g004`R3#9R4f0R5#2#<%L51K33R6#9^12R7f1R8#DP2P4P8%@5,83R9P0P6P4f3R:#2R;f2R<'7R=P1P3P3P4P5!sF&4R>f5R?O1R@!sB,1;>8,83n200110=00012010910@RA1838RBn101101000210!sJ$!sT&<!sT'810?!t3%P8P<O1RC!tK-B!sT3910?RD!sV%15;<!sR?810?R;%:3RE!tU2<00!s8G!t5%%2?RF/7>RG!v446RHf7RIO1PAP!uaQ:P>O1RJP!uA+F>P;P!tvZRFP!s$%!t~&HRF/7?RK!t~3PIf8RL!t|V@!tv-?!tvan0110000081010?1010:3010;102103!s1D4010>!tk$:104!s4&610510:!{@%P!{:&13:<!ux310H?RF!uvMRM!s^':<RN!u|+1:<!u|KRO!yn;13?>!tn5LI!tlNP!s\'?>RQ!tl,?!ybLRR!s:6SP!s$%!tt&H?!{^49/0L!tuNL!y]&F!tq,H!y]LR?!s:6TPT!y_x7!y_%RT544X07P7%J8!yl1P=P!y&&P!x~+PC!{z]!sh&GP!x:&P!x6+PJ!|x^GP!s$%!sp%KP!wI4P@!}~~!}~b=44T!wD%H!wD3CPMP!|`<PJPPP!{87RP!s$%!up'LP!yk7?P?!uL~!uL+2!|W$!#4S'<8!|m3PQ!#7GR10<8!|j,<8!zMc13>:!#4I4IH!tfU>:!tf,>:!z1^EP!s$%SPS!~X~:,C4%28RS#B%A8E6%?S%E8E6%>S%F8E61GS51=85544eX32DIW2o"). Qed.
#[local] Hint Rewrite xlo1B_eqf : bceq.


Definition xhi1 : ltac2:(zQ "50!hg1!iu3!h9!hta!ik0>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "h1hb!h9!iu3!kj1!ji2!ri5!hta!in3!qja!rj3!rnf!hg8!va!jh0!jh9!hg1!ik0!nm6&\2z0$0\3hi'$0@2$3$0@2$9^4^1&M2\2p0@2$2$0$0@1$1$0^1~0&\2p0@2$2$0$0~1&M2\1p@2$2$0$0@1$1$0^1\1z$0\3hi'$0@2$3$0^1&\1p@2$2$0$0~3&M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0@2$3$0^1&\1p@2$2$0$0~5&M1\1x@1$1@2$2$0$0@1$1$0@2$4^8^7~2@2$3$0^1&\2hi$0~7&\1z$0~8&M2\1p@2$2$0$0@1$1$0^1~9&\1p@2$2$0$0~a&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^5^4~4~c&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~b~d&\1b$5~e&\1a$5~f&\2op$c~h0&\2op$d~h0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^9^8~2@2$3$0^1&\2hi$0~h3&\1z$0~h4&M2\1p@2$2$0$0@1$1$0^1~h5&\1p@2$2$0$0~h6&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~4~h8&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~h7~h9\1k@1$e$f\1e$5M5\1e$5@1$1$0^1\1z$0@2$3$0@1$h0^1\1n$aM1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~2@2$3$0^1M1\1x@1$1@2$2$0$0@1$1$0@2$4^3^2~4M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~6@1$6$0~h1~h1~h2~h2\2sx$b\2lo$a\1n$a\2e0$5~ha\2sx$b\2k0$a\1i$0\1n$a~ha").

Definition xhi1B : ltac2:(zQ "40!iu3!h9!hta!kuc>2bc$3>1e$2@1$0$1") := ltac2:(zQ "h0hb!h9!iu3!kj1!ji2!rk7!hta!in3!rl6!rm1!rnf!hg8!va!jh0!jh9!nm6!kuc&\2z0$0\3hi'$0@2$3$0@2$9^4^1&M2\2p0@2$2$0$0@1$1$0^1~0&\2p0@2$2$0$0~1&M2\1p@2$2$0$0@1$1$0^1\1z$0\3hi'$0@2$3$0^1&\1p@2$2$0$0~3&M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0@2$3$0^1&\1p@2$2$0$0~5&M1\1x@1$1@2$2$0$0@1$1$0@2$4^8^7~2@2$3$0^1&\2hi$0~7&\1z$0~8&M2\1p@2$2$0$0@1$1$0^1~9&\1p@2$2$0$0~a&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^5^4~4~c&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~b~d&\1b$5~e&\1a$5~f&\2op$c~h0&\2op$d~h0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^9^8~2@2$3$0^1&\2hi$0~h3&\1z$0~h4&M2\1p@2$2$0$0@1$1$0^1~h5&\1p@2$2$0$0~h6&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~6@1$6$0&M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~4~h8&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~h7~h9\2bc$f\1e$5M5\1e$5@1$1$0^1\1z$0@2$3$0@1$e^1\1n$aM1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0M1\1x@1$1@2$2$0$0@1$1$0@2$4^6^5~2@2$3$0^1M1\1x@1$1@2$2$0$0@1$1$0@2$4^3^2~4M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~6@1$6$0~h1~h1~h2~h2\2sx$b\2lo$a\1n$a\2e0$5~ha\2sx$b\1k$a\1i$0\1n$a~ha").

Lemma xhi1B_eqf : ltac2:(zQ "90!hg1!iu3!ljb!h9!ro5!roc!hta!ik0!lgf>2fk@1$0$7@3$2>1e$6@1$1$3@1$5@1$8^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##Fup'0h01oh11ei001eh22fkh31xi011xi021ai031bi042e0i052hii063hi'i071ii081ki092k0i0:2loi0;1ni0<2opi0=1pi0>2p0i0?2sxi0@1zi0A2z0p;1p;2p;3p;6p;5g00EVj1MTg00GCR0j19Tg00Kbj12Tg04mFj1<j2GTg04nPj1Lj2=!sR$eR1j2KTg04abj1Dj20Tg01lcj1@Tg00gjj28Tg04boj27j1BTg04oYj2;Tg04dXj25j1?Tg00Qoj1:Tg04ehj23j1HTg04g1j21j1JTg001Hj34Tg004Fj2CTg04h>j1ATg00A[j66Tg04iNj1ETg04jbj1>Tg04l2j1FTg01;_j5ITg00j5#Mg01<aR2g004`R3#9R4f0R5#2#<%L51K33R6#9^12R7f1R8#DP2P4P8%@5,83R9P0P6P4f3R:#2R;f2R<'7R=P1P3P3P4P5!sF&4R>f5R?O1R@!sB,1;:5,83n200110>00012010A106RA1835RBn101101000210!sJ$!sT&=!sT'@10!t3&P8P<O1RC!tK-B!sT66RD!sV%15;<!sRB5R;%:3RE!tU2=00!s8G!t5%%2?RF/7>RG!v446RHf7RIO1PAP!uaQ:P>O1RJP!uA+F>P;P!tvZRFP!s$%!t~&HRF/7?RK!t~3PIf8RL!t|V@!tv-?!tvan0110000081!t2%10;3010<102103!s1D4010?10:10;104!s4&810710;!{@%P!{:&13:<!ux310H?RF!uvMRM!s^':<RN!u|+1:<!u|KRO!yn;13?>!tn5LI!tlNP!s\'?>RQ!tl,?!ybLRR!s:6SP!s$%!tt&H?!{^49/0L!tuNL!y]&F!tq,H!y]LR?!s:6TPT!y_x9!y_%RT544X07P7%J8!yl1P=P!y&&P!x~+PC!{z]!sh&GP!x:&P!x6+PJ!|x^GP!s$%!sp%KP!wI4P@!}~~!}~b=44T!wD%H!wD3CPMP!|`<PJPPP!{87RP!s$%!up'LP!yk7?P?!uL~!uL+2!|W$!#4S'<8!|m3PQ!#7GR10<8!|j,<8!zMc13>:!#4I4IH!tfU>:!tf,>:!z1^EP!s$%SPS!~X~;,C4%28RS#B%A8E6%?S%E8E6%>S%F8E61GS51=85544eX32DIW2o"). Qed.
#[local] Hint Rewrite xhi1B_eqf : bceq.



(* [comment removed for export] *)
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := m mod two64 in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', s + (2 ^ j - 1))
      else (e, 0)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', s1 + s2)
  | _ => (e, 0)
  end.

Definition xb2 (k : list kentry) (e : expr) : option (Z * Z) :=
  let plain := match xlo1 k e, xhi1 k e with Some lo, Some hi => Some (lo, hi) | _, _ => None end in
  let '(e', s) := deand e in
  if Z.eqb s 0 then plain else
  match xlo1 k e', xhi1 k e' with
  | Some lo', Some hi' =>
      if Z.leb s lo' then
        match plain with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some (lo' - s, hi')
        end
      else plain
  | _, _ => plain
  end.

Definition xb2B (bc : bctx) (e : expr) : option (Z * Z) :=
  let plain := match xlo1B bc e, xhi1B bc e with Some lo, Some hi => Some (lo, hi) | _, _ => None end in
  let '(e', s) := deand e in
  if Z.eqb s 0 then plain else
  match xlo1B bc e', xhi1B bc e' with
  | Some lo', Some hi' =>
      if Z.leb s lo' then
        match plain with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some (lo' - s, hi')
        end
      else plain
  | _, _ => plain
  end.

Lemma xb2B_eqf : ltac2:(zQ "a0!h9!hg1!iu3!kj1!ljb!rp4!rpa!hta!ik0!lgf>2fk@1$1$8@3$4>1e$7@1$2@2$3$0$0@1$6@1$9^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##;7p'0h01oh11eh22fkh31xi001xi012e'i022hii033hi'i042loi053lo'i061pi075plaini081sp;1p;2p;3p;6p;5p;4g00EVj1NTg00GeR0j2M!s1$CR1j19Tg00Kbj12Tg0506j1Lj2GTg051?j1Dj2<Tg04nPj1@j20Tg052Gj18Tg04H1j2=Tg04_Oj23j1?Tg00gjj26Tg00Qoj1;Tg000kj2KTg0189j2:Tg04d;j2HTg04oYj2CTg04`Yj21j1ATg001Hj35Tg004Fj2BTg053Qj1>Tg00A[j67Tg04mFj1ETg054_j1FTg01;_j5ITg023Zj4J!se$`R2P2f1R3f0R4CJp=4g00j5#Ng01<aR51M22R6#9R7%24#L%D4%92^15R8%@3P0P5P2P7%83R9g005YR:P7g01>I,=4R;P1P2P7f4R<#2R=f3R>'3!s:%P>P<O1R?1434,66R@%;6RAn10110000021010200P!s:3400RB!sj%13=!st+f2R=O1P:P71K=3RCP1P6P7!tN&6RD#2f5RE!tL+EPDO1P@P!t@KFP0P2!s`$41:<E,H31C4>'4,66n2001106000120104102RG1:3=/4!uQ$H!sv%7!sv'600PFn0!t0%020000!td%%2E/3<!tp&<PEO1RF!trM!s82300PB!s:2500!tF1!u2&0!u2$1!sS$8!xB'P9P:P7P!x2&11<>!s0&0E<!td9RB!vZ8I!sh+3!sh+=RJ!t+$!wn011DE!wx&7/0D!t3:K!t38LPGP!w/7L!w/711E!w,&10DE!t6:E!t68D!w,6I!w,WRL557X08P8%A3!w:9P=P>O1PB!{j?P=P3O1!s2&!vr6PFP!vO9K!vO:K!vO7P?PE!z2~8=57LX!z9,%84!z:1>=!wu'<>!}lNA!sf+!z8+<=!vB0D!u|:D!u|2I!u`6A!u`W,B7%23RA#?%>3E7%EA%F3E71GA41<34557eX35DIW2o"). Qed.
#[local] Hint Rewrite xb2B_eqf : bceq.


Definition xlo2 : ltac2:(zQ "50!hg1!iu3!h9!hta!ik0>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "90!h9!iu3!kj1!in3!ji2!hg1!rp4!hta!ik0\1k@1$5$8\1e$7M1\1x@1$1@2$2$0$0@1$1$0@2$6^2^1\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0@2$4$0^2@1$3$0").

Definition xlo2B : ltac2:(zQ "40!iu3!h9!hta!kuc>2bc$3>1e$2@1$0$1") := ltac2:(zQ "80!h9!iu3!kj1!in3!ji2!rpa!hta!kuc\2bc$7\1e$6M1\1x@1$1@2$2$0$0@1$1$0@2$5^2^1\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0@2$4$0^2@1$3$0").

Lemma xlo2B_eqf : ltac2:(zQ "90!hg1!iu3!ljb!h9!rq1!rq8!hta!ik0!lgf>2fk@1$0$7@3$2>1e$6@1$1$3@1$5@1$8^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##'{p'0h01eh12fkh21oh31xi001xi012loi021pi031zp;1p;2p;3p;6p;5g00EVj1ATg00GCR0j13Tg00Kbj12Tg055mj14j2;Tg0577j1@j2<!sR$eR1j2:Tg051?j17j20Tg00gjj25Tg00Qoj16Tg001Hj31Tg004Fj28Tg0506j19Tg058@j1?Tg00A[j6>Tg01;_j5=Tg00j5#Ag01<aR2g004`R3#3R4f0R5#2#4%@51:33R6#3^02R7f1R8#7P0P6P4P5P8O1P1P3P3P4P51538n2001102000120101103R1%63R3n!s4$0000210!sI$!sm%f2/08P1P!sG6514X2!t<&1085!sL9,84%28R3#9%?8E>1;351<85514eX32D=W1o"). Qed.
#[local] Hint Rewrite xlo2B_eqf : bceq.


Definition xhi2 : ltac2:(zQ "50!hg1!iu3!h9!hta!ik0>1k@1$0$4>1e$3@1$1$2") := ltac2:(zQ "90!h9!iu3!kj1!in3!ji2!hg1!rp4!hta!ik0\1k@1$5$8\1e$7M1\1x@1$1@2$2$0$0@1$1$0@2$6^2^1\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0@2$4$0^1@1$3$0").

Definition xhi2B : ltac2:(zQ "40!iu3!h9!hta!kuc>2bc$3>1e$2@1$0$1") := ltac2:(zQ "80!h9!iu3!kj1!in3!ji2!rpa!hta!kuc\2bc$7\1e$6M1\1x@1$1@2$2$0$0@1$1$0@2$5^2^1\1p@2$2$0$0M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0@2$4$0^1@1$3$0").

Lemma xhi2B_eqf : ltac2:(zQ "90!hg1!iu3!ljb!h9!rr0!rr7!hta!ik0!lgf>2fk@1$0$7@3$2>1e$6@1$1$3@1$5@1$8^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##'{p'0h01eh12fkh21oh31xi001xi012hii021pi031zp;1p;2p;3p;6p;5g00EVj1ATg00GCR0j13Tg00Kbj12Tg059Mj14j2;Tg05:Wj1@j2<!sR$eR1j2:Tg051?j17j20Tg00gjj25Tg00Qoj16Tg001Hj31Tg004Fj28Tg0506j19Tg058@j1?Tg00A[j6>Tg01;_j5=Tg00j5#Ag01<aR2g004`R3#3R4f0R5#2#4%@51:33R6#3^02R7f1R8#7P0P6P4P5P8O1P1P3P3P4P51535n2001102000120103101R1%63R3n101100000210!sI$!sm%f2/08P1P!sG6514X2!t<&1085!sL9,84%28R3#9%?8E>1;351<85514eX32D=W1o"). Qed.
#[local] Hint Rewrite xhi2B_eqf : bceq.



(* [comment removed for export] *)
Definition fact_ok : ltac2:(zQ "30!ik0!va!hg1>1k@1$2$0>1K$0$1") := ltac2:(zQ "h30!h9!hta!io7!hge!va!iu3!ik0!jse!jv9!hg8!rrf!hg1!rr0!rq1!qg6!ln8!ln2!lp7!rs6\1k@1$b$6\1K$6M6\1K$6$4^1\1a$2\1w$9\1v$1$3\1a$2\1n$1$3\1a$2\1n$1\2k0$9$3\2lo$0\2hi$0$3\1e$1\1m$0@2$7@2$7@2$h1Z^1@2$h0^1@2$h2+2@1$a^1@2$8@1$a^1@2$e^4^2\1e$1\2lo$0\2hi$0M5\1x@1$5$0$4@2$d^5^3\1l$0M5\1x@1$5$0$4@2$c^6^4\1h$0@2$7@2$8^4^2@2$8^1^3$3$3\1a$2\1n$1$3\2a1$2\2n1$1\2a2$2\2n2$1M2\2a1$2$4^4\2b1$1\2k1$0M2\2a2$2$4^4\2b2$1\2k2$0@7$f^a^4^3^7^2^1^5\1a$2\1n$1\1c$0$3\1a$2\1n$1$3").

(* [comment removed for export] *)
Fixpoint kread_bytes (fuel : nat) (k : list kentry) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZ k b off 1, kread_bytes f k b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Fixpoint kread_bytesB (bc : bctx) (fuel : nat) (b : expr) (off : Z) : option (list Z) :=
  match fuel with
  | O => Some []
  | S f => match kreadZB bc b off 1, kread_bytesB bc f b (off + 1) with
           | Some z, Some rest => Some (z :: rest)
           | _, _ => None
           end
  end.

Lemma kread_bytesB_eqf' : ltac2:(zQ "a0!hg1!h9!hg8!iu3!ljb!rsc!rta!hta!ik0!lgf>2fk@1$0$8>4fuel$2@3$4>1b$7>3off$1@1$3@1$0$1@2$6@1$9^2^1@2$5^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##0jp'0h01bh14fuelh21oh33offh41xi001xh52x0h62IHh71fh82fkh91ni014resti021zp;1p;2p;3p;4p;5p;6g00EVj1>Tg00GCR0j1;Tg00Kbj10Tg05;`j24j39j4ATg05=1j26j38j42Tg001Hj35Tg004Fj27Tg01;_j51Tg0153j13Tg03iRj4?j1CTg003Cj1HTg0259j2=Tg01Y_j3GTg00gjj2FTg00Qoj1ETg03j^j4:j1DTg05>Aj1BTg00A[j6<Tg05?Qj4@Tg00j5#>g00iVR1g01<aR2g004`R3%>3R4#;R5]3R6]0R7f2R8#0R9f0R:'416:835R;X11P2P6f1R<#0g01=jR='416=<P3P5A99=:A8=8:P=f3R9P<P:C2,75X53D1X42D!sd$%09%3<R6'41669P3P5f4R6#0%38R>;9:A8>6:P7f5R>,69P0!sH$6R?#0P8P<%3=R=C?P0P4P5P<P9g006Y#HR@,=8RAO2AG3<:,F4RB%E4RCn10110000021010100P!s:3200!t4%P?P8P<P=C:!t,&>f7P9PAC2PBP!sp6RA!sr7RD555X27%;3^91^33^02R7%D>!t3&:!t3%O3P!se8=55DX27!sS&>P<P:!t`-6P?P81=<@!tb;!sy7,75%0>RC#C%B>E<14C9P8E<PC%39!wm&AP9!t:%C2555e!wx,X6;X71P:C@W1W8o"). Qed.
Lemma kread_bytesB_eqf : ltac2:(zQ "a0!hg1!hg8!h9!iu3!ljb!rsc!rta!hta!ik0!lgf>2fk@1$0$8@3$4>4fuel$1>1b$7>3off$2@1$3@1$0$2@1$6@1$9^1\4fuel$1@2$5^1^2").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h04fuelh11bh22fkh33offp;1p;2p;5g00EVj10Tg00GCj16Tg00Kbj12Tg05;`j11Tg05=1j25Tg05@2j24Tg01;_j53Tg00j5#0g00iVR0g01<ag004`R1%01#6]3]1f0R1#2#1f1R2,51X001421X00D3W2o"). Qed.
#[local] Hint Rewrite kread_bytesB_eqf' kread_bytesB_eqf : bceq.


Definition node_join : ltac2:(zQ "50!ig3!hg8!iu3!h9!hta>2cs$0>1b$4>3off$3>1n$1@1$2$0") := ltac2:(zQ "h70!ig3!iu3!h9!in3!jse!va!hg1!irc!iie!ik0!lp0!ji2!mo8!hg8!ina!ru9!ps0!rsc!rv2!rvb!hta!sg1!kg9\2cs$0\1b$h4\3off$2\1n$dM5\0$5@1$1$0@2$4@2$4@2$aN1^1@2$a^1N8@4$h0@1$7^4^3^2@1$8@1$h6^1M1\1x@1$1@1$6$2@1$1$0@4$h1^1@1$7^4^3^2\2bs@1$6$2@2$b$0@2$f^5@3$c$9@3$h2@2$h3^4^3^2@1$8@1$h5^1@1$e$9@1$3$0@1$3$0").

Fixpoint drop_ixs (ixs : list nat) (i : nat) (k : list kentry) : list kentry :=
  match k with
  | [] => []
  | K :: r => if existsb (Nat.eqb i) ixs then drop_ixs ixs (S i) r else K :: drop_ixs ixs (S i) r
  end.

(* [comment removed for export] *)
Definition residue_fact (k : list kentry) (e ne : expr) : list kentry :=
  let '(e', s) := deand e in
  if Z.ltb 0 s then
    match xlo1 k e', xhi1 k e' with
    | Some lo', Some _ => if Z.leb s lo' then [KRange (esub e' ne) 0 s] else []
    | _, _ => []
    end
  else [].

Definition node_fresh : ltac2:(zQ "50!iu3!ig3!hg8!h9!hta>2cs$1>1r$2>4logc$3>4base@1$0$4@1$0$1") := ltac2:(zQ "i40!iu3!ig3!jse!hta!h9!ik0!in3!hg1!sh3!jv9!va!mo8!hg8!pvf!kh2!sh9!si1!sib!qof!ji2!ru9!sj2!sj9!sk0!kn2!irc!jk4!sk9!sl8!rr0!rq1!iie!qg6!jv3!rs6!loa\2cs$1\1r$c\4logc$4\4base@1$0$3=1k@1$7$5@1$h9^4=1c$4@2$i2+2^3=1b$3M0\4base@1$0$3$3^3\1b$3^1@1$hfZ=1e$3@2$d@2$ha^7^6^1Ma\0$a@1$0$1@2$2@2$2@2$2@2$2@2$2@2$2@2$2@2$h1N0^7@2$h1^7Ni0@2$9Z^6@2$9^6+i8@2$9^6@2$i0^4^1@2$e@1$8^8^2@2$e@1$8^8^1@1$h8^8M0\1x@1$0$4@1$0$1@2$he^4^1\2lo$4M0\1x@1$0$4@1$0$1@2$hd^5^2\2hi$4=1v$c@1$8^a=2ne$3@2$h7^6@1$f^1=4kres@1$7$5@3$hb^8^5^1=2kf@1$7$5@3$b$5@3$h0@1$f^3@2$h2@2$i3@2$i1^5^8+1^8@2$h2^4^8@3$b$5@3$h0@2$d^6^2ZZ^1@2$h3$1@2$h5@3$hc@2$h4^e^1^d@2$h6^8^3N1@1$6$1@1$6$1@1$6$1").

(* [comment removed for export] *)
Definition node_droprange (cs : acs) (b n : expr) : acs :=
  let '(bb, bk) := split_lit b in set_kn cs (kn_havocM (kn cs) bb bk n).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_bump : ltac2:(zQ "30!ig3!hg8!iu3>2cs$0>1m$1@1$2$0") := ltac2:(zQ "a0!ig3!va!sh3!in3!ji2!hg8!iu3!sm2!sj2!lp0\2cs$0\1m$5M1\0$1@1$6$0@2$9@1$2^2^1@2$4$0@2$8^2@2$7^1@1$2^2@1$3$0").

(* [comment removed for export] *)
Definition node_havoc : ltac2:(zQ "40!ig3!hg1!hg8!iu3>2cs$0>2rs@1$1$2@1$3$0") := ltac2:(zQ "h60!hg8!ig3!jse!va!ilc!sib!in3!ji2!sm9!hg1!iu3!itc!ii7!kn2!ipa!qo4!iq2!ika!il4!ij6!im6!hnd\2cs$1\2rs@1$9$0M3\0$3@1$a$1@2$2@1$d^2@3$h5$0\1r$0@2$2@2$5N0^1@2$5^1Ni0^1=2ss$h4@1$c^2@2$7$1@2$h0^3@4$e@1$h2^1@3$f@1$h3^1^2@1$4^1@1$h1^1@2$b@1$4^1@2$8$0^2@1$6$1").

(* [comment removed for export] *)
Fixpoint esize (e : expr) : nat :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => S (esize a + esize b)
  | EExt _ _ _ a => S (esize a)
  | _ => 1%nat
  end.
Definition bigb : ltac2:(zQ "30!va!hg8!hta>1K$1>1e$2$0") := ltac2:(zQ "40!hg8!sn2!hta!sib\1K$0\1e$2@2$3^2@1$1^1").
Fixpoint kn_bigsubst (K : nat) (k : list kentry) (nx : nat) : list kentry * nat :=
  match k with
  | [] => ([], 0%nat)
  | KWord a w v :: r =>
      if bigb K v then let '(r', c) := kn_bigsubst K r (S nx) in (KWord a w (EVar nx) :: r', S c)
      else let '(r', c) := kn_bigsubst K r nx in (KWord a w v :: r', c)
  | x :: r => let '(r', c) := kn_bigsubst K r nx in (x :: r', c)
  end.
Definition node_havocbig (cs : acs) (K : nat) : option acs :=
  let rs := List.filter (fun r => bigb K (reg cs r)) (seq 1 31) in
  match node_havoc cs rs with
  | Some cs1 =>
      if fresh_ok cs1 then
        let nx1 := nxt cs1 in
        let '(k', c) := kn_bigsubst K (kn cs1) nx1 in
        Some (with_ss cs1 (mk_ss (pc cs1) (s_regs (a_ss cs1)) k' (nx1 + c)))
      else None
  | None => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xinside_c : ltac2:(zQ "50!hta!h9!va!hg1!ik0>1k@1$3$4>1b$0>3off$1>1n$0>2cb$0>2ck$1>2cn$0$2") := ltac2:(zQ "80!hta!va!h9!hg1!hkc!ik0!sna!so5\1k@1$3$5\1b$0\3off$2\1n$0\2cb$0\2ck$2\2cn$0M1\0$1$1@7$6^7^6^5^4^3^2^1$4@7$7^7^6^5^4^3^2^1").
Definition xinside_cB : ltac2:(zQ "40!hta!h9!va!kuc>2bc$3>1b$0>3off$1>1n$0>2cb$0>2ck$1>2cn$0$2") := ltac2:(zQ "70!hta!va!h9!hkc!kuc!sp1!spe\2bc$4\1b$0\3off$2\1n$0\2cb$0\2ck$2\2cn$0M1\0$1$1@7$6^7^6^5^4^3^2^1$3@7$5^7^6^5^4^3^2^1").
Lemma xinside_cB_eqf : ltac2:(zQ "90!hta!h9!va!hg1!ljb!sqa!sr6!ik0!lgf>2fk@1$3$7@3$4>1b$0>3off$1>1n$0>2cb$0>2ck$1>2cn$0$2@1$6@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##0:h01bh12b1h22b2h32cbh42ckh52cnh62fkh72k1h82k2h91nh:2n1h;2n2h<3offh=1xh>2x0h?2x1h@2x2hA2x3hB2x4p;1p;2p;3p;4p;5p;6p;7g00EVj1LTg00Kbj10Tg05AHj1=j2Kj3>j4;j57j69j7FTg05BWj16j2?j3<j4:j58j6Jj7GTg0498j1Ij74Tg05Cej7Hj1BTg05E3j73j1@Tg001Hj32Tg004Fj2ATg05F>j1CTg00A[j65Tg046ej1DTg04;Oj1ETg01;_j51Tg00j5#Lg01<aR0g004`R1g005YR2^50R3^41R4^30R5^90R6]<f0R7#0#=%67P1P6f1R6#0/K71?67P0P5f2R5#0?>67A<5!s9$4f3R4#0P5P6P7C;P4!s0&:P1P3f4R3#0!s:'D7P3!s2+8P0P2f5R8#0!s<,E9P8!s4-JP2^;0^81^20^:0^71^10R9f6R:#IP2P2P7P:!sX,O6R;g0069R<f7R=#0!sC/FHn010!s#$20000!se$=!sH04R>P<!s:23!s\1R=522X09P9%@:!si$>P<P;!sK1=22=X09!sE$!sr-P7F4P<!s82!t-2,A2%0:R<#B%C:E5%D<%E:E5P<!s[0F!sk2G522eXB0D1XA1D1X@0D1X?0D1X>1D1X=0D1W6o"). Qed.
#[local] Hint Rewrite xinside_cB_eqf : bceq.

(* [comment removed for export] *)
Definition find_containing (k : list kentry) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside_c k b off n (am_base m) 0 (am_len m)) ms.

Local Open Scope lzb_scope.
Definition find_containingB (bc : bctx) (ms : list amap) (kinds : list mkind) (b : expr) (off : Z) (n : expr) : option amap :=
  List.find (fun m => negb (is_fog m) && existsb (mkind_eqb (am_kind m)) kinds && xinside_cB bc b off n (am_base m) 0 (am_len m)) ms.
Local Close Scope lzb_scope.

Lemma find_containingB_eqf : ltac2:(zQ "b0!hg1!hl3!hta!iu3!ljb!h9!ss3!st5!hk4!ik0!lgf>2fk@1$0$9@3$4>2ms@1$0$1>5kinds@1$0$8>1b$2>3off$5>1n$2@1$3$1@1$7@1$a^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##/]h01bh11mh21nh33offh42cbh52ckh62cnh72fkh85kindsh91xh:2x0h;2x1h<2x2h=2x3p;1p;2p;3p;4p;5p;7p;6g00EVj14Tg00GCj1OTg00Kbj10Tg05GPj1;j2Dj3>j4<j58j6ITg05Hej1Nj2?j3=j4:j59j6JTg05BWj1Mj75Tg05J9j1LTg05KDj1K!s/$bj1CTg05Lnj1BTg00:mj36Tg05N<j1@Tg05OHj1ATg05PSj33Tg017[j22Tg001Hj37Tg004Fj2ETg05AHj1F!sS$lj1GTg00A[j6HTg01;_j51Tg00j5#4g05R?R0#4R1g05SJR2#4R3g01<aR4g004`R5%O0R6^24R7]3R8]0R9]8f0R:#0#;%N:P3P9f1R9#0/D:1?9:P4P8f2R8#0?>9:A=89:P5P7f3R7#0P8P9P:C<P7!s0&:P4P6f4R;#0!s:'D8P;!s2+9g005YR<^64^55^44^24^35^04R=f5R>#MP<!s$%%L:#KR<%C:#BR?=62>R@g02WeRAn010!s#$20000P9!t-%%@:RBg01>IRC%A:RDO6P!sQ2X10=30>12<@f7!td&BPCPDF5'2!sC&576X0=A62?;,2<f6!u1&!sM2;,E6%0>R0#F%G>EHP0!u[,EIP>!s4-J576eX=4D1X<5D1X;4D1X:3D1X91D1W7o"). Qed.
#[local] Hint Rewrite find_containingB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_of (k : list kentry) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrl k b 3) (ELit (shadow_off A))) in (sb, sk, mkSrl k n 3).

Definition shadow_ofB (bc : bctx) (b n : expr) : expr * Z * expr :=
  let '(sb, sk) := split_lit (eadd (mkSrlB bc b 3) (ELit (shadow_off A))) in (sb, sk, mkSrlB bc n 3).

Lemma shadow_ofB_eqf : ltac2:(zQ "90!hta!kj1!hg1!ljb!h9!su9!sv5!ik0!lgf>2fk@1$2$7@3$3>1b$0>1n$0@2$1@2$1$0$4$0@1$6@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##,Tp'0h01ah11eh22fkh31nh41sh51xi001xh62x0i012sbi022skp;1p;2p;4p;3p;6p;5g00EVj1GTg00GeR0j27Tg00Kbj13Tg05TVj1:j2Ej3BTg05Uej1Fj2?j3=Tg05W3j1>j31Tg003aj1<!s/$Cj1;Tg05X;j19Tg016Rj18Tg05YJj22Tg05ZSj14Tg023Zj40Tg001Hj36Tg004Fj2DTg05[_j1CTg05\jj1@Tg00A[j6ATg01;_j55Tg00j5#Gg01<aR1g004`R2,71R3/71R4^31f0R5#3#:%F5P1P4f1R6#3/E51?65P1^42^01R7f2R8#>P0P1P2P4P5P8g006Y#<#;R9O2p,1A#9#8R:'2#4P3P1!sO$6P5C0R;P8f3R<P9O2C0n2001100000120101102!s}'A1<89/2:!sh&;f5?1<9!sZ9564X17!s`,86!s`04?18!s`:,D4%38R9#C%@8EAAB965A=865564eX61D5X51D5W2o"). Qed.
#[local] Hint Rewrite shadow_ofB_eqf : bceq.



(* [comment removed for export] *)
Definition lit_coversZ (m : amap) (lo hi : Z) : bool :=
  match am_base m, am_len m with
  | ELit a, ELit l => (negb (is_fog m) && mkind_eqb (am_kind m) KRWLAZY
                       && Z.leb 0 a && Z.leb 0 l && Z.ltb (a + l) two64 && Z.leb a lo && Z.leb hi (a + l))%bool
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition shadow_split_ok (k : list kentry) (ms : list amap) (b n sb : expr) (sk : Z) (sn : expr) : bool :=
  let '(bb, bk) := split_lit b in
  let shlo := shadow_off A - 4096 in
  (Z.ltb 0 shlo && Z.ltb shlo KHI && Z.eqb (KHI mod 8) 0 && Z.eqb (shlo mod 8) 0 && flat_x k bb bk n && flat_x k sb sk sn
   && ranges_apart_x k bb bk n (ELit shlo) 0 (ELit (KHI - shlo))
   && match xhi k b, xhi k n with Some hb, Some hn => Z.leb (hb + hn) (2 ^ 47) | _, _ => false end
   && existsb (fun m => lit_coversZ m (shadow_off A) (shadow_off A + shlo / 8)) ms
   && existsb (fun m => lit_coversZ m (shadow_off A + KHI / 8) (shadow_off A + 2 ^ 47 / 8)) ms)%bool.

Local Open Scope lzb_scope.
Definition shadow_split_okB (bc : bctx) (ms : list amap) (b n sb : expr) (sk : Z) (sn : expr) : bool :=
  let '(bb, bk) := split_lit b in
  let shlo := shadow_off A - 4096 in
  (Z.ltb 0 shlo && Z.ltb shlo KHI && Z.eqb (KHI mod 8) 0 && Z.eqb (shlo mod 8) 0 && flat_xB bc bb bk n && flat_xB bc sb sk sn
   && ranges_apart_xB bc bb bk n (ELit shlo) 0 (ELit (KHI - shlo))
   && match xhiB bc b, xhiB bc n with Some hb, Some hn => Z.leb (hb + hn) (2 ^ 47) | _, _ => false end
   && existsb (fun m => lit_coversZ m (shadow_off A) (shadow_off A + shlo / 8)) ms
   && existsb (fun m => lit_coversZ m (shadow_off A + KHI / 8) (shadow_off A + 2 ^ 47 / 8)) ms)%lzb.
Local Close Scope lzb_scope.

Lemma shadow_split_okB_eqf : ltac2:(zQ "a0!hta!hg1!va!ljb!h9!hl3!tg2!th4!ik0!lgf>2fk@1$1$8@3$3>2ms@1$1$5>1b$0>1n$0>2sb$0>2sk$4>2sn$0$2@1$7@1$9^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##>lp'0h01bh11mh21nh32b1h42b2h51eh62fkh72k1h82k2h92n1h:2n2h;1oh<3offh=2sbh>2skh?2snh@1xi001xhA2x0hB2x1hC2x2hD2x3hE2x4i012bbi022bki032hbi042hnp;1p;2p;3p;4p;5p;6p;7g00EVj1HTg00Kbj10Tg05^9j1Sj2ej3Tj4Qj5Kj6Ij7^Tg05_Nj1Lj2Wj3Rj4Oj5Jj6dj7UTg04NQj1`j45Tg05ZSj1GTg05X;j1VTg002^j1;Tg003Cj16Tg0189j2D!s/$Vj2CTg03=`j2BTg04H1j2ATg016Rj1ETg0193j7Pj1XTg04?cj2@j1ZTg0259j29!s}$aj18Tg030`j2NTg000kj2MTg05`bj2=Tg05a?j3?Tg00:mj34Tg017[j2<Tg013bj7Fj1cTg04@lj2:j1aTg001Hj37Tg00GCR0j1bTg004Fj2_Tg04B2j1YTg00A[j6>Tg01:Gj1[Tg04MEj1\Tg05bOj1]Tg01;_j52Tf0R1#;#;p=3f2R2f1R3'</<1p=1g00j5#Hg05R?R4#HR5g01<aR6g004`R7g005YR8^?6R9]>R:^=6R;^26R<]0%01#S%L1P6P<%03/e11W31P6P;%02?T31AR2!s6$:f3R:#0P2P3P1CQP:!s0&OP7P9f4R9#0!s:'DKP9!s2+JP6P8f5R;#0!s<,EIP;!s4-dP8^26^<7^06R<f6R=#`g00GeR>P6P7P8%G;R?P8!s$Eg01>IR@p,1A#VRAg006Y#;RB#3RC#;#3!s$&6'DRD'CREg05c_RF,CDRGg02WeRHn010!s#$20000%6CRC,BF/A@RIP!sC21BDC/A@RJ!s?3RK!uP%P=O3!sB3P2!ur%!s@5f9RL#0RM!s`%%EDRNP@1DFD#EROFP!so40P7P8f7RP,@M!s3&:RM#0/@P1931%6B%8B#8!s$$6'NRB'MRQPHn101!sn%21010400!s:4300RR!ud4=DC,9A9?1AX14RDf8RS544RT!sO5FC,9A1=BC,9A5?1X14RA=44SRB!sR3n20!tH'121!tT$2P!xd&P?1<EG?1IJRJPL!v4%C5RIPL!v`%C5RG31!s@'PNP@POFFRE!v&%1:LP!s0'MPP!uoL31?1TB!tf7RM578X0<P8^:6^87^46^96^77^36R<%c=!u/,!z`<KP!y\4PG!yU4G!yU'!uK%O6!sZ4!wd4P!wM4P!w3H=78MX0<%b7^56R<%a!u<?GPE!zD9P2PPO1!s2&:!s2$!w7L!u@p;<!u5'%G9PS!vd$;C5PS!#3u$C551J!s='!yH'!y<'S=!yP+=!yFOA44DPA44AP31!tg7,_8%0=RA#Z%Y=E>%XA%[=E>%\A%]=E>PA!#5c-F^P=!s60U578eXE6D2XD7D2XC6D2XB6D2XA6D2X@5D2W6o"). Qed.
#[local] Hint Rewrite shadow_split_okB_eqf : bceq.

(* [comment removed for export] *)
Definition shadow_facts (k : list kentry) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in
  if match find_containing k ms [KRWLAZY] sb sk sn with Some _ => true | None => shadow_split_ok k ms b n sb sk sn end
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Definition shadow_factsB (bc : bctx) (ms : list amap) (b n : expr) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in
  if match find_containingB bc ms [KRWLAZY] sb sk sn with Some _ => true | None => shadow_split_okB bc ms b n sb sk sn end
  then [KWr (SA sb sk) sn; KZero (SA sb sk) sn] else [].

Lemma shadow_factsB_eqf : ltac2:(zQ "80!hg1!hta!ik0!ljb!hl3!ti8!tj7!lgf>2fk@1$0$2@3$3>2ms@1$0$4>1b$1>1n$1@1$0$2@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##6]p'0h01bh11nh22msh32fkh45kindsh51oh63offh71pi001ph82sbi012sbh92ski022skh:2sni032snh;1xi041xh<2x0h=2x1i051ap;1p;2p;3p;6p;7p;4p;5g00EVj14Tg00Kbj10Tg05dgj1@j2Rj3Aj4MTg05f9j1<j2Ij3?j4NTg05_Nj1>j77Tg00GeR0j2:Tg05TVj3;j1=Tg00PFj16Tg01Y_j35Tg05GPj6Qj1FTg02b4j2PTg036[j2OTg02e@j2HTg05Uej38j1BTg05Hej69j1DTg001Hj31!t?$CR1j1CTg004Fj2ETg05gJj1GTg00A[j62Tg05hcj1JTg05^9j1KTg05j6j1LTg01;_j53Tg00j5R2#4R3g05R?R4#4R5g01<aR6P3^16R7]0f0R8#0#@%<8P6P7f1R7#0/R81I78P6P3f2R9#0?A78A?978g004`R:g005YR;^:6]9^86^16^06^25R<f3R=#>P01:6:R>!sh$4R?#0?;97P0P6P:P3P7P;P3P1P4P;f8R@#0f7RAg05SJRBg05kO%6B35RCP7P8P9EQRDg0069REP?PAf6RFf5RG!sC%O6n101104000210105001P78RH/O91HH9%62RH552552R2PHn010!s#$20000n2001!s7%120!so$2!s:&4!s:'0103P0P!uB$A8?97RI!u?7P@PAP!u$'9PE!s6$FP!tu&F7R@!tw5P!t_\RJ513X0<1:>!wD&R<%B=!tv'P8P9P7O2!tw8DPEP!t[p=13JX7<%4B%C4^16^6:^06]4^25RB%D!td,!vW9?!vW,O5!tjx5B!x/,=78!tT8APF!x,0!x'%?!x,'!tbo,E3%0=RH#F%G=E2%=H%J=E2%KH%L=E2PHP9P7P8CMP=!s0&N513eX=6D3X<6D3X;5D3W3o"). Qed.
#[local] Hint Rewrite shadow_factsB_eqf : bceq.



(* [comment removed for export] *)
Definition shadow_twins (k : list kentry) (sb : expr) (sk : Z) (sn : expr) (vis : list (expr * expr)) : list kentry :=
  if flat_x k sb sk sn then
    flat_map (fun p => let '(pb, pk, pn) := shadow_of k (fst p) (snd p) in
                       if flat_x k pb pk pn then [KDisj (SA sb sk) sn (SA pb pk) pn] else []) vis
  else [].

Definition shadow_twinsB (bc : bctx) (sb : expr) (sk : Z) (sn : expr) (vis : list (expr * expr)) : list kentry :=
  if flat_xB bc sb sk sn then
    flat_map (fun p => let '(pb, pk, pn) := shadow_ofB bc (fst p) (snd p) in
                       if flat_xB bc pb pk pn then [KDisj (SA sb sk) sn (SA pb pk) pn] else []) vis
  else [].

Lemma shadow_twinsB_eqf : ltac2:(zQ "90!hta!hg1!ik0!kj1!ljb!h9!tk7!tl6!lgf>2fk@1$1$2@3$4>2sb$0>2sk$5>2sn$0>3vis@1$1@2$3$0$0@1$1$2@1$7@1$8^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##4ip'0h01ph11bh21nh32fkh43offh52skh62snh73vish81xi001xh92x0h:2x1h;2x2i012p0i022pbi032pki042pnp;1p;2p;3p;4p;6p;5g00EVj1<Tg00GeR0j26Tg00Kbj10Tg05l[j1?j2Mj3Cj4@j5JTg05mmj1Pj2Dj3Aj4>j5KTg05Uej1=j3:Tg04MEj47j1FTg000Nj3OTg05o>j3NTg02b4j25Tg037fj4;Tg00PFj1LTg01Y_j39Tg009Sj41Tg04NQj42j1BTg001Hj34Tg004Fj2ETg05bOj1GTg00A[j68Tg05TVj1HTg05hcj1ITg01;_j53Tg00j5R1#<R2g01<aR3g004`R41633R5#<R6P2]7R7^63R8]5f0R9#0#?%P9P4P8f1R8#0/M91D89P3P7f2R7#0?C89AA789P6P2f3R:#0P7P8P9C@P:!s0&>1634R;/63^23^13R<f4R=#=g005YR>P2f5R?#0P=P:P7C7P5P1P0P;P3P2P8AO339R@AN339RAO2P0P3P4P2P8P>P2f:RB#0P8P9P7C7f9RCf8RD'5f7RE1589RFP7C;%L1RG591RHPGn010!s#$20000n20011!s9$120102103!s:&0!s:'1104X05P8C1!se3P>P2P?!u/&2!u//f6RI?:@ARJ!u#1PB!t{&2P!t[sRB542X0<P>^23^44!w0$%B=!tE$9!ts%O3!v|0!tk3?!tk%O3!tkt=42BX1<!t4$!tX$P8!vO1A:?@A!t]2C!vJ'15DEPIP!x;$=91G!tk_9!tk5,E2%0=RG#F%G=E8%HG%I=E8PG!{%'DJ!u''P9DK542eX;6D3X:3D3X94D3X83D3W3o"). Qed.
#[local] Hint Rewrite shadow_twinsB_eqf : bceq.

Definition vis_twins (k : list kentry) (b n : expr) (vis : list (expr * expr)) : list kentry :=
  let '(sb, sk, sn) := shadow_of k b n in shadow_twins k sb sk sn vis.
Definition vis_twinsB (bc : bctx) (b n : expr) (vis : list (expr * expr)) : list kentry :=
  let '(sb, sk, sn) := shadow_ofB bc b n in shadow_twinsB bc sb sk sn vis.
Lemma vis_twinsB_eqf : ltac2:(zQ "80!hta!hg1!ik0!kj1!ljb!tm6!tn2!lgf>2fk@1$1$2@3$4>1b$0>1n$0>3vis@1$1@2$3$0$0@1$1$2@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##/Pp'0h01nh11bh22fkh31lh41pi001ph52sbi012sbh62ski022skh72sni032snh83vish91xi041xh:2x0h;2x1p;1p;2p;3p;5p;6p;4g00EVj17Tg00GeR0j22Tg00Kbj10Tg05o[j19j2Dj3=j4ATg060jj1Gj2>j3;j4<Tg05mmj1:j55Tg05TVj38j1CTg05Uej34j1FTg001Hj33Tg004Fj2ETg05hcj1BTg00A[j66Tg05l[j1?Tg0628j1@Tg01;_j51Tg00j5#7R1g01<aR21222#7R3P1]8R4^02f0R5#0#9%G5P2P4f1R6#0/D51>65P3P1f2R7#0?=65A;765g004`R8P4^72]6^52R4f3R9#:P01228R:P2P1f4R;#0?897P0P2P8P1P6P;P6P5P7f5R<O4n2001100000120101102!s:&4!s:'0103P0P!sx$A4;!ss/f8!ss%P<D5!sq7R<!ss7R=531X3412:2^02^12R4%F9!t2'P5P9P7O2P!sc8=31=X44!t_,976!t_-7!t_&;!t_9!sx7,E1%09R;#C%B9E6%?;%@9E6P;P!ss$CAP9!s0&<531eX;3D1X:2D1X92D1W2o"). Qed.
#[local] Hint Rewrite vis_twinsB_eqf : bceq.

(* [comment removed for export] *)
Definition vis_cost : ltac2:(zQ "10!h9>3nhi$0$0") := ltac2:(zQ "30!jv3!h9!qof\3nhi$1@2$0@2$0^1@2$2^1+8+kgg0").

(* [comment removed for export] *)
Definition vis_add_ref (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k0 b n in
  match xhi k0 n with
  | Some nhi =>
  if (Z.leb 3 (ealign k0 b) && Z.leb 3 (ealign k0 n) && flat_x k0 bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p)
                           && ranges_apart_x k0 bb bk n pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_x k0 pb pk (snd p) && ranges_apart_x k0 sb sk sn pb pk (snd p)) (a_ghost cs)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_facts k0 (a_maps cs) b n ++ vis_twins k0 b n (a_vis cs) ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs))
  else None
  | None => None
  end.
(* [comment removed for export] *)
Definition vis_add (cs : acs) (b n : expr) (k : list kentry) : option (acs) :=
  let k0 := kn cs in let bc := mkbc k0 in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc n with
  | Some nhi =>
  if (Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n
      && expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p)
                           && ranges_apart_xB bc bb bk n pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_vis cs)
      (* [comment removed for export] *)
      && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                           flat_xB bc pb pk (snd p) && ranges_apart_xB bc sb sk sn pb pk (snd p)) (a_ghost cs)
      && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
  then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (shadow_factsB bc (a_maps cs) b n ++ vis_twinsB bc b n (a_vis cs) ++ k) (nxt cs))
                (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                ((b, n) :: a_vis cs) (a_ghost cs) (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs))
  else None
  | None => None
  end.

Lemma vis_add_eq : ltac2:(zQ "80!ig3!hta!hg1!iu3!ljb!tnf!to9!ik0>2cs$0>1b$1>1n$1>1k@1$2$7@3$4@1$3$0@4$5^4^3^2^1@4$6^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##U_p'0h01pi001ph11bh21nh31eh41lh52b1h62b2h72csh81kh92k1h:2k2h;2msh<2n1h=2n2h>1oh?3offh@3vishA1zi012bbi022bki033nhii042pbi052pki062sbi072ski082sni091xp&0p;1p;2p;3p;4p;7p;<p;6g00EVj1ETg063Nj17Tg04[jj1mj2ATg00GCR0j1JTg05ZSj1F!s:$eR1j2DTg00Kbj16Tg05TVj3_j1nTg04?cj2Qj1qTg003aj1d!s/$Cj1cTg000kj24Tg017[j20Tg04MEj4Cj1vTg064Uj1^Tg065]j2B!sV$Nk302Tg05o>k301Tg0193j7>j1sTg066nj1VTg0688j33!s/$Tj1RTg069`j1STg06:lj1WTg0259j2:Tg06<9j1fTg06=Fj1PTg00HEj1NTg00O=j1KTg06>Mj1ITg05dgj4Lj1j!tS$[j4Mj1kTg00WCj49Tg06?Xj1HTg06@dj1GTg023Zj4TTg01Y_j3UTg06Anj1bTg06C8j1aTg06DAj1`Tg06ENj1]Tg06FZl<<Tg00Qok103Tg05Uej3[j1xTg04@lj2\j1uTg04NQj4?k100Tg013bj7@j1~Tg05f9j4Yj1zTg060jj4Oj1yTg001Hj35Tg004Fj2tTg04B2j1oTg00A[j68Tg05hcj1lTg06Gdj1pTg06I7j1rTg01:Gj1iTg05bOj1wTg04]3j1hj2XTg04^?j1gTg06JMj4{Tg06KYj4|Tg03G<j3}Tg00gjj2eTf2R2f1R3'0f0R4'0p=1f4R5f3R6'0/02/03/04p==g00j5R7?}34p=2g00hLR8/e4p=;A3234,06p=Zg01<aR9%E7R7g004`R:^39R;%76R<#m%J8R=P1P9P:P=%F6R>P11D9:R?P9P=f6R@#7RA#6f5RB;_5RC!sR'P3P0P:P=f:RD#7RE#6RFf8RG'QRHg005YRIP=g006Y#d#cRJf7RKPDO1'4PKf9RLO1,4J'0f;RM#7RN#6ROP@PBPLCC%^MRP/BDRQ311BPLRR1D99RS!tI&IB02994#FRTf>#7RU#6RVP3P4B01992RWCCRXPVPLPGf<RYP3P4PWF>RZPVPBP5P@!s8+V31n2001109000120104105X0S%VMR[33!t@'PT10XV!sR;RMRX53S%SMR\%WMR]':%f4R^':p,5LIMITR_'4R`D=%PMRa%NM#KRbPO%IMRcPDPLCLPOPDPLP[CM/2GRO'2PPC9Pc%HMRd%GMReP\P9P9!sS$T=US[RfPX1:]^R]%bMRg%aMRh%`MRi%]MRjM<<#;Rk&038Rln010!s#$20000Pln1!u<'21110300!uO&0!uO$1106107!uc01100108!s:31102!x~+>P1P!yK$A[AB5RA!y?31\EGPIP=1AND,4J1ANL!xp$RmPN!xh&?'0?1QRRnP!xZ+PTPU!wv%C?RoPUPLPGP!xB'@PU!x@0@RU!x@<P[CZ!x=/oU!sO:=3SX;1`RUPaPbPNP!wh%YRpPN!wj&O/2G!wh'PdPeP\PfPXP]PgPhPiP!wD%P!w>2RN!w@sRq35XA;PI^29^?:^19R;&00<!wX5P!}l4PHPIP=PK!w?%O3=1mQPR!w;-D!vq%O3RR?1ZV!vJ=[!vs/R!sO>XP`D=PkP!zN~1102=5=qX1;PI^=9^::^69^<9^9:^59R;%~!v<O!zE1D!z9/O6PD!z9/O6RY51o!z:KY!z:A!vDC0!vDkg05R?#EP7^29^19];R;%z!vAO!|3%K!|3%O3/2O!{}R!xmx4;%ESP7]@!uM%R7%y!uKW!~L$O3/2G,2p!uN`!wwj471D?9!uK+x!uK72PBP5O2!uQ6N!w2x07%J:^39R7%u!t^7!#8V3P@PGO1!t\z>7!#@Z+2R7!tT'%7BRq?[56!t[3%7LRN/\K!#:7$EL,4J1AEG,4J'0PEP@PBPGC?%^DRA/BLR>311BAGRH!~+,f=#7Rj!#:A'iPjPLPGPM!#:A'j!#:A1h!#?[=DRg53!#3{,10ih!sS;RDRh53S%SDRi%WDR]':/:^/4_R_D=%PDRX%ND#KRfPE%IDR\PLPGCYPE!tm$gCO/2K'2PAC9P\%HDRE%GDRePiP9P9!sQ$T=USgRdPh!#?M&DR^%aDRc%`DRP%]DRD!~0~!xF,Rp,t=%6<R[#q%o<E8%n[%l<E8%k[%p<E8%j[%r<E8%s[%i<E8%v[%w<E8%h[%g<E8!xb+!x},6q?_!x{66N/Q!xy%XF!xy$XF!xy&F!xy&C;1>P!xl-%6j!xk+CRH!xk2>!xk2>RW!xk<=3Sg!xg/HW!sO=hP_D=PXPfPFP!xF%LPF!xF&M!xF-PEPePiPdPhP]P^PcPPP!wz~!}B1peP6P2P3P4C{!s0+|55=eW8X29W1X78o"). Qed.


(* [comment removed for export] *)
Fixpoint find_disj (k : list kentry) (b1 b2 : expr) : option (expr * Z * expr * expr * Z * expr) :=
  match k with
  | [] => None
  | KDisj (SA c1 o1) n1 (SA c2 o2) n2 :: r =>
      if (expr_eqb c1 b1 && expr_eqb c2 b2)%bool then Some (c1, o1, n1, c2, o2, n2)
      else if (expr_eqb c1 b2 && expr_eqb c2 b1)%bool then Some (c2, o2, n2, c1, o1, n1)
      else find_disj r b1 b2
  | _ :: r => find_disj r b1 b2
  end.
(* [comment removed for export] *)
Definition disj_side_fact : ltac2:(zQ "50!hta!h9!ik0!hg1!iu3>1k@1$3$2>2cA$0>2oA$1>2nA$0>2cB$0>2oB$1@1$4$2") := ltac2:(zQ "h10!h9!ik0!iu3!kj1!in3!hta!va!tp7!jv3!jv9!ji2!jse!hg1!pvf!rq1!si1!pq2\1k@1$c$1\2cA$5\2oA$0\2nA$5\2cB$5\2oB$0M2\1x@1$2$0@1$2$1@2$e^6^3\1n$0M2\1x@1$2@2$3$0$0@1$2$1@2$h0^7^3\1p@2$3$0$0M3\1p@2$3$0$0@1$2$1^1\1z$0\3bhi$0M6\0$6@1$2$1@2$b@2$9Z^4@2$9^4@2$8^1^5@2$a$1@3$f@2$d@2$7^6^5@2$7^9^8^4@2$8^1^5@1$4$1@1$4$1@1$4$1").
Definition node_casedisj : ltac2:(zQ "40!ig3!hta!iu3!kj1>2cs$0>2b1$1>2b2$1@1$2@2$3$0$0") := ltac2:(zQ "h22!kj1!hta!ig3!h9!iu3!ik0!in3!va!mo8!ina!ru9!tpf!ps0!ji2!hg1!kka!tr0!irc&@2$0@2$0@2$0@2$0$1$3$1$1$3&@2$0~0$1\2cs$2\2b1$1\2b2$1=1k@1$e$5@1$h1^3M4\1x@1$4~1@1$4@2$0$2$2@3$h0^1^3^2\1p~1M0\1p~1@1$4@2$0$2$2^1\2p0~0\2n2$1M0\2p0~0@1$4@2$0$2$2^2\2p1@2$0@2$0@2$0$1$3$1$1\2o2$3M0\2p1@2$0@2$0@2$0$1$3$1$1@1$4@2$0$2$2^2\2p2@2$0@2$0$1$3$1\2c2$1M0\2p2@2$0@2$0$1$3$1@1$4@2$0$2$2^2\2p3@2$0$1$3\2n1$1M0\2p3@2$0$1$3@1$4@2$0$2$2^2\2c1$1\2o1$3M7\1x$7@1$4@2$0$2$2@4$c^c^2^1^3M7\1x$7@1$4@2$0$2$2@4$c^c^5^7^9M4\1x@1$4$5@1$4@2$0$2$2@6$b^c^2^1^3^5^7\2K1$5M4\1x@1$4$5@1$4@2$0$2$2@6$b^d^6^8^a^3^2\2K2$5@2$d@2$0$2$2@4$f$2$2@2$a^h1@3$8$5^2@1$9$5@2$a^h1@3$8$5^1@1$9$5@1$6@2$0$2$2@1$6@2$0$2$2@1$6@2$0$2$2@1$6@2$0$2$2@1$6@2$0$2$2").

(* [comment removed for export] *)
Fixpoint gaps_cut (gs : list (Z * Z)) (xlo xhi : Z) : list (Z * Z) :=
  match gs with
  | [] => []
  | (a, b) :: r =>
      (if Z.ltb xhi a || Z.ltb b xlo then [(a, b)]
       else (if Z.ltb a xlo then [(a, xlo - 1)] else []) ++ (if Z.ltb xhi b then [(xhi + 1, b)] else []))
      ++ gaps_cut r xlo xhi
  end.
(* [comment removed for export] *)
Definition zcdivp : ltac2:(zQ "10!h9>1a$0>1b$0$0") := ltac2:(zQ "30!h9!trc!qof\1a$0\1b$0@1$1@2$2@1$1^2^1").
(* [comment removed for export] *)
Definition gap_excl1 : ltac2:(zQ "50!h9!hg1!ik0!kj1!hta>1k@1$1$2>1b$4>2sc$0>1K$2@1$1@2$3$0$0") := ltac2:(zQ "h97!h9!hta!kj1!ina!hg8!io7!hg1!va!jh0!jh9!ik0!jv3!jse!iu3!nm6!jv9!loa!ir6!mo8!kka!ts2!ju7!oq9!qof!ln2&\2lo$0\2hi$0@1$3@2$2$0$0&\2op$8\1a$1\2b0$1@1$3@2$2$0$0&\2op$9\1a$1\2b0$1@1$3@2$2$0$0&\2lo$4\1n$4\1e$1@1$3@2$2$0$0&\2sx$7~3&\2k0$4\1i$0\1n$4@1$3@2$2$0$0&\2sx$7~5\1k@1$6$a\1b$1\2sc$0\1K$aMa\1K$a@1$6@2$2$0$0^1\1a$5\1w$4\1v$1@1$3@2$2$0$0\1a$5\1n$1@1$3@2$2$0$0\1a$5\1n$1\2k0$4@1$3@2$2$0$0~0\1e$1\1m$0@1$3@2$2$0$0\1e$1~0\1a$5\1n$1@1$3@2$2$0$0\2a1$5\2n1$1\2a2$5\2n2$1M5\2a1$5@1$6@2$2$0$0^4\2b1$1\2o1$0M5\2a2$5@1$6@2$2$0$0^4\2b2$1\2o2$0=3one>2cb$1>2co$0>2cn$1>2pb$1>2po$0>2pn$1@1$6@2$2$0$0\2cb$1\2co$0\2cn$1\2pb$1\2po$0\2pn$1M7\0$7@1$6@2$2$0$0@2$c@2$h5^6^h1@2$h8^5ZM1\2pb$1@1$6@2$2$0$0^3\1L$0M1\2pn$1@1$6@2$2$0$0^2\1M$0Md\1x@1$d$0@1$6@2$2$0$0@2$h6^h4^6\3nlo$0=1P$0@2$b@1$e^3^5=2Mz$0@1$e^3M7\0$7@1$6@2$2$0$0@2$c@2$fZ^3@2$fZ^1@3$h2@2$2$0$0@4$h3$0$0@2$b@2$h7@2$h0^2^3^h5+1@2$h0@2$h4@2$b^2^1^h5+1@1$3@2$2$0$0@1$3@2$2$0$0@1$3@2$2$0$0\1n$4@1$3@2$2$0$0~1~1~2~2~4~6\1n$4@1$3@2$2$0$0~1~1~2~2~4~6@1$3@2$2$0$0@3$h1@2$2$0$0@6^1^5^4^8^3^2^6@6^1^3^2^6^5^4^8\1a$5\1n$1\1c$0@1$3@2$2$0$0\1a$5\1n$1@1$3@2$2$0$0").
(* [comment removed for export] *)
Definition gaps_of : ltac2:(zQ "60!h9!hg1!hg8!iu3!kj1!ig3>2cs$5>1v$2>2sc$0@1$3@1$1@2$4$0$0") := ltac2:(zQ "hf0!h9!kj1!hg1!iu3!va!in3!lp7!jse!hla!sh9!ik0!ji9!ji2!mo8!kj8!hg8!ina!kka!kje!ig3!sk0!tsb!tt7!irc!hta!kpd!tu2!nge!tv0!jv9!qp5\2cs$h3\1v$f\2sc$0=1k@1$2$a@1$h7^3=1b$h8@2$h4^2@1$9^3M4\0$4@1$3@1$2@2$1$0$0@1$8@2$7@2$6Z^3@2$6^3$b@1$5@1$2@2$1$0$0M3\1x@1$3@2$1$0$0@1$3@1$2@2$1$0$0@2$ha@1$h9^2@1$9^4\1p@2$1$0$0M1\1p@2$1$0$0@1$3@1$2@2$1$0$0^1\2lo$0\2hi$0M4\0$4@1$3@1$2@2$1$0$0@1$8@2$7@2$hdZ^2@2$6@2$he^6^1$b@1$5@1$2@2$1$0$0=4excl@1$2@2$1$0$0@4$hb$a@2$1$0$0@3$h5^5^4^6^5@2$c@1$2@2$1$0$0@5$hc@1$2@2$1$0$0@2$1$0$0\2gs@1$2@2$1$0$0\1x@2$1$0$0@3$h6^2@3$e$0$0^1@3$h2$0$0^1^1@3$d@2$1$0$0@4$h1$0$0^3^2@1$h0@2$1$0$0@1$5@1$2@2$1$0$0").
Definition gap_child : ltac2:(zQ "40!h9!ig3!hg8!kj1>2cs$1>1v$2>1g@2$3$0$0$1") := ltac2:(zQ "c0!h9!mo8!kj8!hg8!kj1!kje!ig3!irc!is1!sh9!si1!ik0\2cs$6\1v$3\1g@2$4$0$0@2$8^3@3$1$b@3$a@1$9^2@3$2$0$0^1@3$5$0$0^1@1$7^3").
Definition node_casegaps : ltac2:(zQ "50!ig3!hg1!hg8!iu3!h9>2cs$0>1v$2>2sc$4@1$3@1$1$0") := ltac2:(zQ "b0!h9!hg1!ig3!iu3!kj1!in3!ji2!hg8!op5!tvd!ug9\2cs$2\1v$7\2sc$0M3\1x@1$3@1$1@2$4$0$0@1$3@1$1$2@3$a^3^2^1\4gaps@1$1@2$4$0$0@2$6@1$1$2@4$8@2$4$0$0$2@2$9^4^3^1@1$5@1$1$2").

(* [comment removed for export] *)
Definition gaps_lohi : ltac2:(zQ "40!h9!kj1!hg1!iu3>4gaps@1$2@2$1$0$0@1$3@2$1$0$0") := ltac2:(zQ "c0!h9!kj1!hg1!kj8!kje!tv0!in3!ji2!iu3!kka!rk1!rnf\4gaps@1$2@2$1$0$0M2\4gaps@1$2@2$1$0$0@1$8@2$1$0$0^1@1$6@2$1$0$0\1g@2$1$0$0\2gs@1$2@2$1$0$0@2$7@2$1$0$0@4$9$0$0@5$5$0@2$1$0$0\1a$0\1x@2$1$0$0@2$b^2@3$3$0$0^1^1@3$3$0$0^2@5$5$0@2$1$0$0\1a$0\1x@2$1$0$0@2$a^2@3$4$0$0^1^1@3$4$0$0^2").
Definition node_rangegaps : ltac2:(zQ "40!ig3!hg8!iu3!h9>2cs$0>1v$1>2sc$3@1$2$0") := ltac2:(zQ "b0!h9!iu3!ig3!kj1!in3!hg1!ji2!hg8!tvd!uh3!ug9\2cs$2\1v$7\2sc$0M1\1x@1$1@1$5@2$3$0$0@1$1$2@3$a^3^2^1\4gaps@1$5@2$3$0$0M1\1x@1$1@2$3$0$0@1$1$2@1$9^1\1g@2$3$0$0@2$6$2@3$8^5^4^1@1$4$2@1$4$2").

(* [comment removed for export] *)
Definition node_shdisj_ref (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_of k b1 n1 in let '(sb2, sk2, sn2) := shadow_of k b2 n2 in
  if (Z.leb 3 (ealign k b1) && Z.leb 3 (ealign k n1) && Z.leb 3 (ealign k b2) && Z.leb 3 (ealign k n2)
      && flat_x k c1 o1 n1 && flat_x k c2 o2 n2 && flat_x k sb1 sk1 sn1 && flat_x k sb2 sk2 sn2
      && match xhi k b1, xhi k n1, xhi k b2, xhi k n2 with
         | Some h1, Some m1, Some h2, Some m2 => Z.leb (h1 + m1) (2 ^ 47) && Z.leb (h2 + m2) (2 ^ 47)
         | _, _, _, _ => false end
      && ranges_apart_x k c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.
(* [comment removed for export] *)
Definition node_shdisj (cs : acs) (b1 n1 b2 n2 : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(c1, o1) := split_lit b1 in let '(c2, o2) := split_lit b2 in
  let '(sb1, sk1, sn1) := shadow_ofB bc b1 n1 in let '(sb2, sk2, sn2) := shadow_ofB bc b2 n2 in
  if (Z.leb 3 (ealignB bc b1) && Z.leb 3 (ealignB bc n1) && Z.leb 3 (ealignB bc b2) && Z.leb 3 (ealignB bc n2)
      && flat_xB bc c1 o1 n1 && flat_xB bc c2 o2 n2 && flat_xB bc sb1 sk1 sn1 && flat_xB bc sb2 sk2 sn2
      && match xhiB bc b1, xhiB bc n1, xhiB bc b2, xhiB bc n2 with
         | Some h1, Some m1, Some h2, Some m2 => Z.leb (h1 + m1) (2 ^ 47) && Z.leb (h2 + m2) (2 ^ 47)
         | _, _, _, _ => false end
      && ranges_apart_xB bc c1 o1 n1 c2 o2 n2)%bool
  then Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
  else None.

Lemma node_shdisj_eq : ltac2:(zQ "60!hta!ig3!iu3!ljb!uhf!uid>2cs$1>2b1$0>2n1$0>2b2$0>2n2$0@3$3@1$2$1@5$4^5^4^3^2^1@5$5^5^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##R2p'0h01bh12b1h22b2h31eh41nh52n1h62n2h72csh82k1h92k2h:1oh;3offh<1pi001ph=1zi012c1i022c2i032h1i042h2i052m1i062m2i072o1i082o2i093sb1i0:3sb2i0;3sk1i0<3sk2i0=3sn1i0>3sn2i0?1xp;1p;2p;3p;4p;7p;6p;5g063Nj12Tg04[jj1dj2CTg00GCR0j1HTg05ZSj1E!s:$eR1j2LTg00Kbj11Tg05TVj3@j1bTg003aj1<!s/$Cj1BTg000kj23Tg04MEj48j1\Tg04?cj25j1STg0259j2JTg002^j1]Tg030`j2YTg0193j7Kj1`Tg02b4j2ITg037fj4VTg00PFj1UTg01Y_j3TTg06Lij2GTg00gjj2FTg00Qoj1PTg05Uej3?j1QTg04NQj46j1OTg04@lj24j1MTg013bj7Dj1NTg001Hj39Tg017[j20Tg004Fj2RTg04B2j1cTg00A[j6=Tg05hcj1aTg01:Gj1_Tg05bOj1ZTg04]3j1[j2ATg04^?j1XTg06N4j5^Tg06ODj5WTf2R2f1R3f0R4'3'0p=;f4R5f3R6'0/02/03/04p=71C34,32p=:102!s:%>g00hLR7g01<aR8g004`R9^38R:%25R;#d%H7R<P1P8P9P<%E5R=!s3'P=P11L89R>P8P<f9R?#2R@#1f8RAf7RB3@RC!sR+3P1P!sN%=RD#2RE#1f:RF;@?RG!sK,g005YRHP<g006YRI#<#BRJf<RKf@RLO1RM'3PKf?RNO17;JPKf>ROO1,3JPKPD!s/$fARP#2RQ#1RRf;RSPFPNC8PRP?PAPDC8D7PRf5RTP5f6RU!s@$3P4P2C8P0P9PH15RL!s0%fB#2RV#1RW/5!s9'C#2RX#1RY!s9,D#2RZ#1/5L1J62%]IRI#B%<I#<!s$$B'YRI'31J34;;IRIg02WeR[n10110?00021010600P!s:34!s:65!s:6300R\PRP!ua$!u]%FKR]D7g00j5R^1IT5PU1I34P2CV%U^3TR^,GP,F7RP%P7R_n010!s#$20000n2001!s7%12010:10<!s:&?!s:'010>!sN3910;!sN6=!s:32108!s:01!uF$7!yn/!s0-!yL$A?@ABR@!ye5A?EF?RE!s?-HP<A:JQL1CQN7;JA:JQOA:JQD3>R`PQ!vE%C6PQ!y$&6PQPTP5PU!s0$!xz%6D7Ra!x~&4Q!xX&14V!s0+X!s0+ZLPIP!x=r!tt'!x;&DRZ3>PPP!wn~!wnH0!wn%Rb39X=:PH^48^;9^08R:%O;!x,?P!~g6PG!w{1PK!uk%O3PK!uo%O35>`PK!wd%!s=$!wd$O3P\P]D7!v0~!v0R=9<bX0:PH^68^99^28^58^89^18R:%N!v9d10a\R\!v?'!v;&6'0!ux~!}rR!ux&1L>8^48!y%%Q!unA5PAPBO2!ut6APFP?!s@0!uz$\Z!uf~!x`W<:%H!#;r%M!ubA!#4g5P!#4b1!#3V$PM!s-&DPLO1!s2&O!s2-N!s2$!#3xs=>a!v|~!v|X::!#?\+6R!s3+P:!v`'%2ARb??BU!v{5%2KRP???A!w&1%2LRZ=:JN1CZO!#8j$ZDA:JZKPZ!|j$OC6PZ!|n$KC6D7PZ!#8h'Z!#8h&!#8F'N!s0'Q!s0+V!s0+XN!wju!tr'!tn%FDD71GL^,F7R7!x#~!x#PR^,R<%1;RL#S%c;E=%bL%a;E=%`L%_;E=%\L%Z;E=%[L%X;E=!xD0!xN31b?@!xL81P?@!xJ41ZRZ/AN,3J1A!xL$1AZD!s4%K,3J!xP+8!xP+8!xP-8!xP+!#D6'!xP+5R!s0+W!s0+Y!xP~!xP&KD7P!xI~!xI61!#80?^eP5P6P2P3P4D^!s2-W59<eX68X28X58W1W7o"). Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_len_ref : ltac2:(zQ "50!kj1!h9!iu3!ig3!hta>2cs$3@1$2@2$0@2$0$4$1$1") := ltac2:(zQ "h71!h9!kj1!hta!iu3!in3!va!kka!ujf!ji2!jse!jv9!lp7!hg1!ig3!irc!jk4!uk9!iie!qg6!ik0!ooe!oq9!rs6&\1x@1$3$0@1$3@2$1@2$1$2$0$0\2cs$dM3~0@2$h0^1Nb\3len$0M5\0$5@1$3@2$1@2$1$2$0$0@2$bZ^1@2$8@2$1@2$1$2$0$0@4$6@2$1$2$0$0@4$6$2$0@1$h1@1$7^1@1$7^1@1$7^1@1$4@2$1@2$1$2$0$0=2le$2@2$f^1Nb=1k@1$c$h3@1$e^2M3~0@2$h5^1^2\2lo$0M3~0@2$h4^2^3\2hi$0M5\0$5@1$3@2$1@2$1$2$0$0@2$9@2$9@2$bZ^2@2$a+c@2$h2^3^4@2$a^1@2$h6+2+ie@2$8@2$1@2$1$2$0$0@4$6@2$1$2$0$0@4$6$2$0^4^2^1@1$4@2$1@2$1$2$0$0@1$4@2$1@2$1$2$0$0@1$4@2$1@2$1$2$0$0").
(* [comment removed for export] *)
Definition mmap_len : ltac2:(zQ "50!kj1!h9!iu3!ig3!hta>2cs$3@1$2@2$0@2$0$4$1$1") := ltac2:(zQ "h91!h9!kj1!hta!iu3!in3!va!kka!ujf!ji2!jse!jv9!lp7!hg1!ig3!irc!jk4!uk9!iie!ik0!kuc!qh0!lgf!pr0!pr8!rs6&\1x@1$3$0@1$3@2$1@2$1$2$0$0\2cs$dM3~0@2$h0^1Nb\3len$0M5\0$5@1$3@2$1@2$1$2$0$0@2$bZ^1@2$8@2$1@2$1$2$0$0@4$6@2$1$2$0$0@4$6$2$0@1$h1@1$7^1@1$7^1@1$7^1@1$4@2$1@2$1$2$0$0=2le$2@2$f^1Nb=1k@1$c$h2@1$e^2=2bc$h3@1$h5^1M3~0@2$h7^1^3\2lo$0M3~0@2$h6^2^4\2hi$0M5\0$5@1$3@2$1@2$1$2$0$0@2$9@2$9@2$bZ^2@2$a+c@2$h4^3^5@2$a^1@2$h8+2+ie@2$8@2$1@2$1$2$0$0@4$6@2$1$2$0$0@4$6$2$0^5^2^1@1$4@2$1@2$1$2$0$0@1$4@2$1@2$1$2$0$0@1$4@2$1@2$1$2$0$0").

Lemma mmap_len_eq : ltac2:(zQ "80!kj1!h9!iu3!ljb!ig3!ul3!ule!hta>2cs$4@3$3@1$2@2$0@2$0$7$1$1@1$5^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##6lp'0h01eh11oh22csh31zi002hii013leni022loi031xp;1p;2p;4p;3p;6g063Nj18Tg04[jj1Xj2?Tg00Gej2C!s/$CR0j1@Tg0153j1>Tg06PXj2DTg018Vj2BTg06Qdj1RTg016Rj1OTg023Zj47Tg00gjj2<Tg00Qoj1WTg00Kbj1=Tg06S0j25Tg045\j2Gj1KTg04?cj2Fj1ITg003aj16Tg002^j14!s8$Cj1;Tg000kj22Tg017[j20Tg030`j2STg0482j2Ej1MTg04@lj2Aj1NTg001Hj33Tg004Fj2LTg04:Bj1JTg00A[j69Tg04B2j1PTg04]3j1Qj2TTg04^?j1HTg06T8j1UTg06UEj1VTf0R1#>#>p=1g01<aR2g004`R3f1R4P1C7p=:g00hLP3^02R5%81R6#X1C23R7/C3R8#@R9P0P3P9g01=j#>#1!s$'R:,D4R;g005YR<!sG$>IR=/B1P7P3%R1R>#O/:>P>C7,<8%W8R>n010!s#$20000R?!t%%%84R@#=RA154:RB'GRC!s?%f2RD#8RE#=RF15D:RG'FP<P91B=4R=g006YRH#6#4#4#;RIPDf3RD/5:RJO1'2'0%4HRH#;%6H#6!sM$;'S,21RH'0P7P31:J!u|$,<8RKP!tk2P>n10110300021!sA%!s:4200!s82100!u2%P;P!uU&1E@B!s0&AEGP<P9%8D/?J,2I,0=/0HP!tK4!t]$!tM4RJ!tOIRD33X35%@!xD$2%N6!ta3P!w#&P4PGO1PK!uc]=39DX12P2%M!t451PBO1PJ!spQ!vH%D1:R2!v`+51:R:,E!t0&1A@B!xu$?EG!vc,!x?$G!x?+8!x?mR4,L9%=6R7#K%J6E9%I7%P6E9%Q7%H6E!|0&P!t~,G7:!s0&FA!ty%TF!ty-!tjn=394e%U1%V1539eW2o"). Qed.


(* [comment removed for export] *)
Fixpoint inside_maps (k : list kentry) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinside_c k b off len (am_base m) 0 (am_len m)) || inside_maps k rest b off len   (* [comment removed for export] *)
  end.

Local Open Scope lzb_scope.
Fixpoint inside_mapsB (bc : bctx) (ms : list amap) (b : expr) (off : Z) (len : expr) : bool :=
  match ms with
  | [] => false
  | m :: rest => (negb (is_fog m) && xinside_cB bc b off len (am_base m) 0 (am_len m)) || inside_mapsB bc rest b off len
  end.
Local Close Scope lzb_scope.

Lemma inside_mapsB_eqf : ltac2:(zQ "a0!hg1!hta!va!ljb!h9!hl3!umd!unb!ik0!lgf>2fk@1$0$8@3$3>2ms@1$0$5>1b$1>3off$4>3len$1$2@1$7@1$9^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##0\h01bh13offh23lenh32msh42IHh52cbh62ckh72cnh82fkh91mh:1nh;4restp;1p;2p;3p;4p;5p;7p;6p;8g00EVj1>Tg00Kbj10Tg06VVj1Cj2Mj3Jj4Aj53Tg06Wgj1?j2Kj3Bj4@j51Tg001Hj32Tg00PFj1LTg004Fj2=Tg05J9j1<Tg05KDj1;Tg05N<j18Tg05OHj17Tg05AHj7Ij1ETg017[j24Tg01OEj26Tg05BWj79j1DTg05Plj1FTg00A[j6:Tg01Y_j3GTg04<`j8HTg01;_j55Tg00j5#>g05R?R0#>R1g01<aR2g004`R3g005YR4^22R5]1R6]0f0R7#0#C%?7P2P6f1R6#0/M71K67P3P5f2R5#0?J67AB567P2P4f3R8#0P5P6P7CAP8!s0&@P0f8R9#0!s8'D3P9!s2+1524^22^13^02X31f7%L!sj&D1,=4X22X13X02f9!sjIP4f:R9f4R:!sD'R;f6R<#<#;R=f;R>!sl'%8<R?g01>IR@%7<R<FI'4/67P>!t$&?P@P<F9,4=P>f5R!s=&D1RA'6RB524X04P4^72^63^52^:!tQ&RC%D9P7!sl/O6,4=/6A=24BX0C%<>#;P9!tp%%8>P@%7>F9'4/6;,=4%09R;#E%F9E:P;P!u@'3!uh'O3E:P;AG0>:R>!v/->!v/-e!vX+W4X;1X9!vZ+GHX22D5X13D5X02D5X31D5W8o"). Qed.
#[local] Hint Rewrite inside_mapsB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_pg_early : expr := Eval vm_compute in eadd (escale 32768 (EVar 0%nat)) (escale 4096 (EVar 6%nat)).
Definition e_sp0_early : expr := Eval vm_compute in eadd e_pg_early (escale 16 (EVar 10%nat)).
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_entries (ms : list amap) : list (Z * Z) :=
  flat_map (fun m => if is_fog m then [] else
                     match am_base m, am_len m with
                     | ELit b, ELit n => [(zlit64 b, zlit64 n)]
                     | _, _ => []
                     end) ms.
(* [comment removed for export] *)
Fixpoint covers (fuel : nat) (parts : list (Z * Z)) (cur hi : Z) : bool :=
  if Z.leb hi cur then true else
  match fuel with
  | O => false
  | Datatypes.S f =>
      match List.find (fun p => Z.leb (fst p) cur && Z.ltb cur (fst p + snd p)) parts with
      | Some p => covers f parts (fst p + snd p) hi
      | None => false
      end
  end.
(* [comment removed for export] *)

Definition stack_side_x : ltac2:(zQ "50!va!hg1!h9!hta!ik0>1k@1$1$4>1b$3>3off$2$0") := ltac2:(zQ "b0!h9!hta!kj1!mo8!ina!kka!hg1!uoa!ik0!pt3!jv3\1k@1$6$8\1b$1\3off$0@3$9^3@3$3@2$2$1$0@4$5$1$0^2@2$a^1+ogggg0@1$4@2$2$1$0@3$3@2$2$1$0@4$5$1$0$7Z@1$4@2$2$1$0").

Definition safe_range : ltac2:(zQ "60!hg1!hta!va!h9!hl3!ik0>1k@1$0$5>2ms@1$0$4>1b$1>3off$3>3len$1$2") := ltac2:(zQ "hc0!h9!jv3!jse!jv9!iu3!kj1!va!mi7!up8!hge!hg1!hl3!upe!hta!loa!uqb!sm9!uqf!umd!ur8!us6!os4!osd!pq2!ik0!ji9!ooe!lp7\1k@1$a$h8\2ms@1$a$b\1b$d\3off$0\3len$d@2$7M4\1x@1$4$0$6@2$ha^5^1\2lh$0M4\1x@1$4@2$5$0$0$6@2$h7^6^4\1p@2$5$0$0M5\1p@2$5$0$0$6^1\2lo$0\2hi$0@2$7@2$7@2$2@2$2@3$h4^9^7^6@2$3Z@2$1^2^6@2$3@2$1@2$1^1^6^4$h9@2$2@2$3@1$h6?1A@2$1^2^6@2$3@2$1@2$1^1^6^4@1$h5?1A@2$2@2$2@2$2@2$3@2$e@1$c?1A+hgg0@2$1^2^6@2$hb@2$1^1^6$8@2$3@2$1@2$1^1^6^4$8@4$h1@1$f@2$h0$b^8@1$h3^8@2$e@1$c?1A+hgg0$8$9$9@5$h2^5^4^3^2^1").

(* [comment removed for export] *)
Definition stack_side_xB : ltac2:(zQ "40!va!h9!hta!kuc>2bc$3>1b$2>3off$1$0") := ltac2:(zQ "a0!h9!hta!kj1!mo8!ina!kka!uoa!kuc!pte!jv3\2bc$7\1b$1\3off$0@3$8^3@3$3@2$2$1$0@4$5$1$0^2@2$9^1+ogggg0@1$4@2$2$1$0@3$3@2$2$1$0@4$5$1$0$6Z@1$4@2$2$1$0").
Lemma stack_side_xB_eqf : ltac2:(zQ "90!va!hg1!ljb!h9!us6!ut5!hta!ik0!lgf>2fk@1$1$7@3$2>1b$6>3off$3$0@1$5@1$8^1@1$4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01bh12fkh23negh33offh43posh51xh62x0p;1p;2p;4p;3p;6p;5g00EVj1HTg00Kbj13Tg06Y7j1=j2Gj3BTg06ZIj1:j2Ej3CTg04TVj1>j37Tg00Gej2<Tg002^j10Tg003Cj19Tg0259j25Tg023Zj44Tg00PFj1FTg01Y_j32Tg001Hj36Tg004Fj2DTg04U`j1?Tg04Vmj1@Tg00A[j6ATg01;_j58Tf0R0#0#0p=;%00#0#0#0p=1g00j5#Hg01<aR1g004`R2g005YR3]3%30#=%:0P2P3f1R4#3/G01E40g04X>R5P3^25]4R5f2R6#>P01<12R7P1P2P6g006Y#0#;#1#1#1#1#1#9R8,54C4%F7R932R:P1P2g06[Zg01>IC4=279R;O2f3?7:;563X05P1P2P41508C4=279=76;,D3%36R;#?%@6EAAB;40AC640563eX62D8X51D8W1o"). Qed.
#[local] Hint Rewrite stack_side_xB_eqf : bceq.

Local Open Scope lzb_scope.
Definition safe_rangeB : ltac2:(zQ "60!hta!va!hg1!h9!hl3!kuc>2bc$5>2ms@1$2$4>1b$0>3off$3>3len$0$1") := ltac2:(zQ "hb0!va!h9!jv3!hge!jv9!iu3!kj1!hkc!up8!hl3!upe!hta!loa!uqb!sm9!hg1!uqf!unb!ur8!ut5!os4!osd!ji9!no0!kuc!pr0!lp7\2bc$h8\2ms@1$f$9\1b$b\3off$1\3len$bM0\0$0$0M5\1x@1$5$1$0@2$h9^5^1\2lh$1M5\1x@1$5@2$6$1$1$0@2$h7^6^4\1p@2$6$1$1M6\1p@2$6$1$1$0^1\2lo$1\2hi$1M0\0$0$0M0\0$0$0M0\0$0$0M0\0$0$0@3$h3^9^7^6@2$4Z@2$2^2^6$3@2$4@2$2@2$2^1^6^4$h6$3$7M0\0$0$0@2$4@1$h5?1A@2$2^2^6@2$4@2$2@2$2^1^6^4@1$h4?1A$3$7M0\0$0$0M0\0$0$0M0\0$0$0@2$4@2$c@1$a?1A+hgg0@2$2^2^6@2$ha@2$2^1^6$8$3@2$4@2$2@2$2^1^6^4$8$3@4$h0@1$d@2$e$9^8@1$h2^8@2$c@1$a?1A+hgg0$8$3$3$3$7@5$h1^5^4^3^2^1").
Local Close Scope lzb_scope.

Lemma safe_rangeB_eqf : ltac2:(zQ "a0!hg1!hta!va!ljb!h9!hl3!uu5!uv2!ik0!lgf>2fk@1$0$8@3$3>2ms@1$0$5>1b$1>3off$4>3len$1$2@1$7@1$9^1@1$6^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##<op'0h01bh11eh21oh33offh42fkh53lenh62msh71xi001xh82x0h92x1h:2x2i012hii022lhi032loi041pp;1p;2p;3p;4p;5p;6g00EVj1DTg00Kbj12Tg06\jj1Mj2dj3Qj4Kj5\Tg06^:j1Hj2Xj3Lj4Ij5]Tg06ZIj1Gj3?Tg04?cj2Fj1`Tg00GeR0j2ETg029@j2cj1bTg0259j23Tg000kj20Tg04Joj1WTg04L:j1VTg05X;j1UTg003Cj1PTg0189j2N!s/$Vj2@Tg06_Ij29Tg0153j1:!s8$ij1>Tg06a9j4;Tg06VVj5Jj1^Tg04@lj2<j1RTg04O\j2=j1STg017[j21Tg01OEj25Tg06Wgj5Aj1OTg001Hj36!uD$CR1j1BTg004Fj2TTg04Pij1aTg00A[j67Tg04B2j1_Tg06bDj1YTg06Y7j1ZTg06cYj1[Tg01;_j58Tg002^j1CTf0R2#C#Cp=4g00j5#Dg05R?R3#DR4g01<aR5g004`R6g005YR7^55R8]3R9]0R:%22#M%H2P5P9f1R9#2/d21X92P6P8f2R8#2?Q92AL892P5P7f3R;#2P8P9P2CKP;!s0&IP7^36^05R<f4R=#GP7P7P1P6P7f5R>#2R?/F9R@P11E66RAP7f6RB#2/c=RCP0P6P6P7P2!s\$!s$/=f7RDPBO2g01>IRE139BRF'0RGg02WeRHn010!s#$20000132BRI/3;RJg01>gRK'0RLP!sL2g0069RMP7P7p,1ARN#WRO/0FRP%VNRQ,0JRR!sZ3RS!s61PM!tv/%UNg006Y#4!s$-P'NRN/0FRFg05c_RT,@IRI!t#310JTRJ!s<3f8RU,93#:%>UPNPTC;RV!ta4W!s61n2001104000120103101PHn101!sL%210!sD$!s:42!uE$?P=!x=%DJ!ua2!x5$1<>9R?P1PAP71=B=!w{,f9??DBRX/1G/1L11PR'511FI/1J/1V'5!tf`>!td+ARV'5RJ567X0<P:^64R:%O=!z#,P@!tl%P!yg?XPG!vf3P!y74PMP!x]5!w4FRW!uN7RS!w8:2!uR'O4!t&1=67JX0:%B6^15R:%R!u\/2P9O1P!sz;V!sp62:%BA!sp%S!sp/!x<&P9P=O1PW!yBN!t49!y?'=2!y='>;!wQ,A?UB>139>RU,0E'1132>R>/3;RE/0K'110OU10EQ'1'510NU1@>T'110ET'1193D#:%>D!{r%'1!ylb!w>&P2DA'5,T7%2=RH#b%a=E7%`H%_=E7%^H%Y=E7%ZH%[=E7PH!s[+\!sg-]567eX:5D8X96D8X85D8X74D8W4o"). Qed.
#[local] Hint Rewrite safe_rangeB_eqf : bceq.



Definition grant_keep_b : ltac2:(zQ "40!hg1!ik0!va!hl3>1k@1$0$1>2ms@1$0$3>1K$1$2") := ltac2:(zQ "e6!io7!hta!h9!va!uu5!hkc!ik0!hg1!hg8!jse!hl3!iie!lp0!kg9&\1b$1\1o$2@5$4^7^6^2^1^3&M0\1a$0$3^2~0&\1l$1~1&\1a$0~2&\1b$1\1o$2@5$4^8^7^2^1^4&M0\1a$0$3^3~4\1k@1$7$6\2ms@1$7$a\1K$6M6\1K$6$3^1\1a$0\1w$8\1v$1M0\1a$0$3^3\1b$1\1o$2@2$9@2$c^4N8@5$4^8^7^2^1@1$b@1$d^4~3\1a$0\1l$1\2k0$8~5\2lo$2\2hi$2$5\1e$1\1m$2$5\1e$1\2lo$2\2hi$2$5\1a$0\1n$1~1\2a1$0\2n1$1\2a2$0\2n2$1$5\1a$0\1l$1\1c$2~5~3").

Local Open Scope lzb_scope.
Definition grant_keep_bB : ltac2:(zQ "50!va!hg1!hl3!ik0!kuc>2bc$4>2ms@1$1$2>1K$3$0") := ltac2:(zQ "f6!io7!hta!h9!va!uv2!hkc!ik0!hg8!jse!hg1!hl3!iie!kuc!lp0!kg9&\1b$1\1o$2@5$4^7^6^2^1^3&M0\1a$0$3^2~0&\1l$1~1&\1a$0~2&\1b$1\1o$2@5$4^8^7^2^1^4&M0\1a$0$3^3~4\2bc$c\2ms@1$9$a\1K$6M6\1K$6$3^1\1a$0\1w$7\1v$1M0\1a$0$3^3\1b$1\1o$2@2$8@2$d^4N8@5$4^8^7^2^1@1$b@1$e^4~3\1a$0\1l$1\1k$7~5\2lo$2\2hi$2$5\1e$1\1m$2$5\1e$1\2lo$2\2hi$2$5\1a$0\1n$1~1\2a1$0\2n1$1\2a2$0\2n2$1$5\1a$0\1l$1\1c$2~5~3").
Local Close Scope lzb_scope.

Lemma grant_keep_bB_eqf : ltac2:(zQ "80!hg1!ik0!va!ljb!hl3!vg0!vgf!lgf>2fk@1$0$1@3$3>2ms@1$0$4>1K$1$2@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##5%p'0h01bi001bh11Ki011Kh22fkh33lenh42msh53offh61xh72x0i021ai032a1i042a2i051ci061ei072hii081ki092k0i0:1li0;2loi0<1mi0=1ni0>2n1i0?2n2i0@1oi0A1vi0B1wp;1p;2p;5p;3p;6g00EVj14Tg00Kbj13Tg06doj1;j2Dj3>Tg06fAj17j2Aj3?Tg06^:j1<j51Tg0153j10!s/$Rj2:Tg0162j19!s/$Rj18Tg017[j22Tg001Hj36Tg004Fj2CTg06\jj1BTg06gRj1@Tg00A[j6=Tg01;_j55Tg00j5R0#4g05R?#4R1g005YR2^10f0R3#3#;%73P0P2f1R4#3/D31A43g01<aR5g004`P2^35]5]0^41R5f2R6#<P0P2P4g00mXR7P2P6f3R8g01=j#0!s$1':R9f5R:f7R;P4P3%98#8R<O4'2n0110200012010010@P7P2P4f4f6R=P4P3P6O4!sL5R>!sN$6P:P!sy$P8!sL8?g0069R@P@P@P>P@P?P>!sM$1000:3010210B10A2!s1%!s9':1082010;1072010610<3!s-%!s9'210=4010310>10410?!sb,5!su'!vB%!ty%f8R>!t{&<D1,29!ur;P;P!up&D1!uJ7!up&!ss'8!sL8>!ui$@P?!uo$?!ukJ9!ukg562X05!uq$3!tz&!uH'!uoB=P:!uo>:!ss2!uo98!uo&:P@P8P:!uo~!uo4,C2%36R:#B%@6E=A>:43A?643562eX70D5X61D5W2o"). Qed.
#[local] Hint Rewrite grant_keep_bB_eqf : bceq.



Definition kn_grant_filter : ltac2:(zQ "30!hg1!ik0!hl3>1k@1$0$1>2ms@1$0$2@1$0$1") := ltac2:(zQ "60!hg1!ik0!hl3!vg0!vhf!mk2\1k@1$0$1\2ms@1$0$2@1$4@3$5$1@2$3^2^1^2").

Definition kn_grant_filterB : ltac2:(zQ "40!hg1!hl3!ik0!kuc>2bc$3>2ms@1$0$1@1$0$2") := ltac2:(zQ "80!hg1!hl3!vgf!vhf!ik0!mkc!kuc!mk2\2bc$6\2ms@1$0$1@1$3@3$7$4@2$2^2^1@1$5^2").

Lemma kn_grant_filterB_eqf : ltac2:(zQ "70!hg1!ik0!ljb!hl3!vib!vjd!lgf>2fk@1$0$1@3$2>2ms@1$0$3@1$0$1@1$5@1$6^1@1$4^1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01Kh11bh22fkh31lh42msh51xp;1p;3p;2p;6p;5g00EVj17Tg00Kbj13Tg06hfj1;j2>Tg06j;j1:j2<Tg06fAj1Aj24Tg01LUj16Tg01M_j31Tg06kOj10Tg001Hj32Tg004Fj29Tg01Obj18Tg00A[j65Tg06doj1@Tg06l]j1?Tg01;_j5=Tg00j5R0#7R1g05R?#7R2P1f0R3#3#;%:3g005Y^00^42R4f1R5#AP3P5O1f2R6#3#6510#01465R7=106#0R6521X14P1P5A1073#0=216X311453=105#0,91%35R0#6%85E5%@0%?5E51>031<53521eX52D=W2o"). Qed.
#[local] Hint Rewrite kn_grant_filterB_eqf : bceq.

(* [comment removed for export] *)
Definition kn_grant_filterM : ltac2:(zQ "30!hg1!ik0!hl3>1k@1$0$1>2ms@1$0$2@1$0$1") := ltac2:(zQ "50!hg1!hl3!vjd!ik0!lgf\1k@1$0$3\2ms@1$0$1@2$2@1$4^2^1").
Lemma kn_grant_filterM_eq : ltac2:(zQ "60!hg1!ik0!ljb!hl3!vib!vl1@3$2>1k@1$0$1>2ms@1$0$3@1$0$1$5$4").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01kh12msp;1p;3p;5g00EVj10Tg06n3j15Tg06oLR0j12Tg06j;R1j11Tg001Hj34Tg01;_j53Tg00j5#0R2g05R?#0P2]1R3P0P1f0R1#5%21%11543eX02D3o"). Qed.



(* [comment removed for export] *)
Definition gap_ok (cs : acs) (nhi : Z) : bool :=
  let cnt := Z.of_nat (n_res A + length (a_maps cs))%nat in
  Z.leb (FLOOR + nhi + a_totsz cs + cnt * (nhi + 4095)) CEIL.

Definition budget_ok (cs : acs) (extra : Z) : bool :=
  Z.leb (a_eager cs + a_abytes cs + extra) LIMIT.

(* [comment removed for export] *)
Definition kdisj_new (ms : list amap) (nb : expr) (ne : expr) : list kentry :=
  flat_map (fun m => if is_fog m then [] else [KDisj (SA (am_base m) 0) (am_len m) (SA nb 0) ne]) ms.
Definition kdisj_fixed : ltac2:(zQ "30!hta!hg1!ik0>2nb$0>2ne$0@1$1$2") := ltac2:(zQ "d0!rvb!iie!ik0!mo8!vm5!osd!hta!rs6!ina!vme!uoa!os4!loa\2nb$6\2ne$6@3$3$2@4$4@2$0^2Z^1@2$0@1$1@1$5?1AZ@1$1@2$c@1$b?1A@1$5?1A@3$3$2@4$4@2$0^2Z^1@2$0$9-ogggg0@1$1@2$7+2+j0@3$3$2@4$4@2$0^2Z^1@2$0$a-ogggg0@1$1@2$7+2+j0@1$8$2").

Definition SHLO : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!upe!loa@2$1@1$0?1A+hgg0").
Definition kdisj_shadow : ltac2:(zQ "40!hg1!hta!hl3!ik0>2ms@1$0$2>2nb$1>2ne$1@1$0$3") := ltac2:(zQ "h30!vnb!ik0!up8!jse!va!hg1!ina!hl3!iie!rvb!hta!lp7!uqb!mo8!sm9!uqf!ur8!vm5!loa\2ms@1$5$7\2nb$a\2ne$aM4\0$4@1$5$1@2$3@2$3@2$bZ$0@2$b$0$2@4$f@1$c@2$e$7^3@1$h0^3$0$2@3$d$1@4$h1@2$9^2Z^1@2$9@1$8$0Z@1$8@2$h2$2$0@1$6$1@1$6$1").

(* [comment removed for export] *)
Definition with_maps0 (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs).

(* [comment removed for export] *)
Definition add_entry (cs : acs) (sr : list expr) (k' : list kentry) (nx' : nat)
           (m : amap) (nhi : Z) (eager : bool) (ylo' : Z) : acs :=
  ACS (mk_ss (pc cs + 4) sr k' nx')
      (m :: a_maps cs) (a_totsz cs + nhi) ylo'
      (if eager then a_eager cs + nhi else a_eager cs)
      (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (VNew (am_kind m) (am_base m) (am_len m) :: a_vmops cs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition null_kend : ltac2:(zQ "40!hta!hg1!h9!ik0>4base$0>2ne$0>3nlo$2@1$1$3") := ltac2:(zQ "e8!ik0!hta!ina!mo8!m6!sj9!si1!jv3!hg8!h9!va!jh0!jh9!hg1&@3$6@2$5^6^5@2$7+hgg0^4$4&@3$3$0~0@1$2$0&\1b$1~1&\1a$1~2&\2op$b~3&\2op$c~3&@3$6@2$5^7^6@2$7+hgg0^5$4&@3$3$0~6@1$2$0\4base$1\2ne$1\3nlo$9M1\2ne$1@1$d$0^2\1z$9@1$2$0\1n$8@3$3$0@3$6@2$5^4^3@2$7+hgg0^2$4@1$2$0~4~4~5~5\2sx$a\2lo$8\1n$8\1e$1~7\2sx$a\1k$8\1i$9\1n$8~7").

Definition mmap_null (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  match mmap_len cs with
  | Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && (negb eager || budget_ok cs nhi)
          && no_holes (a_maps cs))%bool then     (* [comment removed for export] *)
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        (* [comment removed for export] *)
        let kfacts := KRange (EVar v) 1 ((CEILMAX - nlo) / 4096) :: null_kend base ne nlo
                      ++ kdisj_fixed base ne ++ kdisj_shadow (a_maps cs) base ne ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filterM (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne kind) nhi eager (a_ylo cs - 2 * nhi) in
        if visible then vis_add cs1 base ne (kmem ++ kn cs1) else Some cs1
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition fixed_args (cs : acs) (top : Z) (inside : bool) : option (expr * Z * expr * Z * Z) :=
  let k := kn cs in let a := reg cs 10 in
  let '(b, off) := split_lit a in
  match mmap_len cs, xlo k a, xhi k a with
  | Some (ne, nlo, nhi), Some alo, Some ahi =>
      if (page_aligned k a && Z.ltb 0 alo && (inside || Z.leb (img_hi A) alo) && Z.leb (ahi + nhi) top && flat_x k b off ne)%bool then Some (b, off, ne, nlo, nhi) else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition same_val : ltac2:(zQ "40!hta!va!hg1!ik0>1k@1$2$3>1a$0>1b$0$1") := ltac2:(zQ "d2!hta!h9!kj1!va!mo8!ina!kka!pt3!hge!hg1!hkc!ju7!ik0&@3$4@2$2$0$1@4$6$0$1^2Z@1$5@2$2$0$1&@3$4@2$2$0$1@4$6$0$1^1Z@1$5@2$2$0$1\1k@1$9$c\1a$0\1b$0M3\0$3$3@2$b^2^1$aM3\0$3$3@3$7^3~0~1@3$7^3~1~0$8").
(* [comment removed for export] *)
Definition find_hole (k : list kentry) (ms : list amap) (a ne : expr) : option amap :=
  List.find (fun m => is_hole m && same_val k a (am_base m) && same_val k ne (am_len m)) ms.
(* [comment removed for export] *)
Definition unhole (ms : list amap) (h : amap) : list amap :=
  List.map (fun m => if (is_hole m && amap_eqb m h)%bool then AM (am_base m) (am_len m) KFOG else m) ms.

(* [comment removed for export] *)
Definition mmap_fixed_grant (cs : acs) (ms0 : list amap) (b : expr) (off : Z) (ne : expr) (nhi : Z)
           (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  let m := AM a ne kind in
  let kmem := [KWr (SA b off) ne; KZero (SA b off) ne] in
  let ksh := if mkind_eqb kind KRWLAZY then flat_map (fun p => shadow_facts k [m] (fst p) (snd p)) (a_vis cs) else [] in
  let k' := ksh ++ kn_grant_filterM k ms0 in
  let cs1 := add_entry (with_maps0 cs ms0) (s_regs (a_ss cs)) k' (nxt cs) m nhi eager (a_ylo cs) in
  if visible then vis_add cs1 a ne (kmem ++ kn cs1) else Some cs1.

Definition mmap_fixed_free (cs : acs) (kind : mkind) (eager visible : bool) : option acs :=
  let k := kn cs in
  let a := reg cs 10 in
  match fixed_args cs KHI false with
  | Some (b, off, ne, nlo, nhi) =>
      if (no_fog (a_maps cs)
          && forallb (fun m => ranges_apart_x k b off ne (am_base m) 0 (am_len m)) (a_maps cs)
          && (negb eager || budget_ok cs nhi)
          && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
      then mmap_fixed_grant cs (a_maps cs) b off ne nhi kind eager visible
      else None
  | None =>
      (* [comment removed for export] *)
      match fixed_args cs CEIL false with
      | Some (b, off, ne, nlo, nhi) =>
          match find_hole k (a_maps cs) a ne with
          | Some h =>
              let ms0 := unhole (a_maps cs) h in
              if (forallb (fun m => negb (is_hole m) || ranges_apart_x k b off ne (am_base m) 0 (am_len m)) ms0
                  && (negb eager || budget_ok cs nhi)
                  && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) a)%bool
              then mmap_fixed_grant cs ms0 b off ne nhi kind eager visible
              else None
          | None => None
          end
      | None => None
      end
  end.

(* [comment removed for export] *)
Definition kn_rezero : ltac2:(zQ "40!hg1!hta!ik0!h9>1k@1$0$2>2ub$1>2uk$3>2un$1@1$0$2") := ltac2:(zQ "c0!hta!io7!hkc!h9!ik0!mg1!hg8!va!hg1!mj6!lt3!mk2\1k@1$8$4\2ub$0\2uk$3\2un$0=2sp$a@4$9^4^3^2^1@3$b$4\1K$4M4\1K$4$7^1\1a$1\1w$6\1v$0@6$5^9^5^8^7^6^4\1a$1\1n$0$2\1a$1\1n$0\2k0$6@6$5^9^5^8^7^6^4\2lo$3\2hi$3$2\1e$0\1m$3$2\1e$0\2lo$3\2hi$3$2\1a$1\1n$0$2\2a1$1\2n1$0\2a2$1\2n2$0$2\1a$1\1n$0\1c$3@6$5^9^5^8^7^6^4\1a$1\1n$0$2^5").

Definition kn_rezeroB : ltac2:(zQ "50!hta!hg1!h9!ik0!kuc>2bc$4>2ub$0>2uk$2>2un$0@1$1$3") := ltac2:(zQ "d0!hta!io7!hkc!h9!ik0!mh3!hg8!va!lt3!mkc!kuc!ml5!mk2\2bc$a\2ub$0\2uk$3\2un$0=2sp$8@4$b^4^3^2^1@3$c$4\1K$4M4\1K$4$7^1\1a$1\1w$6\1v$0@6$5^9^5^8^7^6^4\1a$1\1n$0$2\1a$1\1n$0\1k$6@6$5^9^5^8^7^6^4\2lo$3\2hi$3$2\1e$0\1m$3$2\1e$0\2lo$3\2hi$3$2\1a$1\1n$0$2\2a1$1\2n1$0\2a2$1\2n2$0$2\1a$1\1n$0\1c$3@6$5^9^5^8^7^6^4\1a$1\1n$0$2@1$9^5").

Lemma kn_rezeroB_eqf : ltac2:(zQ "80!hg1!hta!ik0!ljb!h9!vo2!voe!lgf>2fk@1$0$2@3$3>2ub$1>2uk$4>2un$1@1$0$2@1$6@1$7^1@1$5^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##6}p'0h01Ki001Kh12ukh22unh31bh42b1h52fkh62k1h71lh82n1i012n1h91sh:2sph;2ubh<1xh=2x0h>2x1i021ai032a1i042a2i051ci061ei072hii081ki092k0i0:2loi0;1mi0<1ni0=2n2i0>1vi0?1wp;1p;2p;3p;4p;6p;5g00EVj1ITg00Kbj10Tg070aj1<j2Hj3=j4CTg0720j18j2Fj3;j4DTg01ADj1:j65Tg01KGj49j1?Tg01LUj16Tg01M_j31Tg01N:j47j1GTg001Hj32Tg004Fj2ETg01Obj1>Tg00A[j63Tg01Q1j1@Tg01?oj1ATg01RCj1BTg01;_j54Tg00j5R0#IR1g01<aR2g004`R3P1^22R4]1f0R5#0#<%85P3P4f1R4#0/H51F45P2P1f2R6#0?=45A;645g01FUR7g005YR8^00^22^13^;2]:R9f3R:#:P0P8P5f4R;f8R<#0f7R=f6R>f5R?C9P=P>P?P:O5R@g0069RAP@PA!s$+@PAn01100000:3010210?10>2!s1%<!s9&<1082010:1072010610;3!s-%!s9'210<4010310110410=!sb,5!sG'X00%0;#6R@510!u0%P<P<!tt%C7!t|'E5RBPAPB!tw-B!twL9!twj=10;RC521X39P7^82^63^42R7%G:!u1+;!u%%O3!u1-<PAP<!u1-<!w&~!u1<@=21CX97P1P!t|'!vq]!tfn5!tf$71!tb&=!vV&;C7!s-%!v`$;PAP;!tx-;!xk~!tx<:,E1%0:R0#6%>:E3%?0%@:E3%A0%B:E3P0P6P4P5CCP:!s0&D521eX>2D4X=3D4X<2D4W5o"). Qed.
#[local] Hint Rewrite kn_rezeroB_eqf : bceq.




(* [comment removed for export] *)
Definition rekind (ms : list amap) (m : amap) : list amap :=
  map (fun m' => if amap_eqb m' m then AM (am_base m') (am_len m') KRW else m') ms.

(* [comment removed for export] *)
Inductive fixed_in_arm := ArmE | ArmF | ArmG.

(* [comment removed for export] *)
Definition fixed_in_args_ref (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args cs CEILMAX true with   (* [comment removed for export] *)
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containing k (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition fixed_in_args (cs : acs) (arm : fixed_in_arm) : option (expr * Z * expr * Z * Z * amap) :=
  match fixed_args cs CEILMAX true with
  | Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let kinds := match arm with ArmE => [KRW; KNONE; KNONELAZY] | ArmF => [KRWLAZY] | ArmG => [KRW; KNONE; KNONELAZY] end in
      match find_containingB bc (a_maps cs) kinds b off ne with
      | Some m =>
          if (expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then Some (b, off, ne, nlo, nhi, m) else None
      | None => None
      end
  | None => None
  end.

Lemma fixed_in_args_eq : ltac2:(zQ "a0!kj1!h9!hta!iu3!ljb!ig3!hl3!vpb!vqb!vs0>2cs$5>3arm$9@3$4@1$3@2$0@2$0@2$0@2$0@2$0$2$1$2$1$1$6@2$7^2^1@2$8^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##8sp'0h03armi0!s,$h11bi011bh22csh35kindsh42msh51nh61oh73offi02!s,%31mi042nei053nhii063nloi071pi082p0i092p1i0:2p2i0;1xp;1p;2p;3p;4p;6g00EVj1<Tg00GCR0j1@Tg063Nj16Tg05Hej1Aj6>!sF$eR1j22Tg073>j3=Tg06>Mj1;Tg00PFj1DTg01Y_j33Tg064Uj18Tg065]j24Tg06S0j27Tg017[j2?Tg023Zj40Tg00gjj2KTg00Qoj1JTg001Hj35Tg004Fj2ITg00Kbj19Tg05GPj1Hj6FTg05gJj1CTg00A[j6ETg074Mj2BTg075_j2GTg0153j1:Tf0R2#:#:p=1g00hLg0775R3g05R?R4#<g05SJR5#<R6g01<aR7g004`R8%@4^57]7]1]3]4R9f1R:#6R;#A1278R</27R=/28R>/28R?/24R@#@RAP0P?PAf2RBg008GRCg0069RD3=REP1P>P8PAP2P1P=!s0$:P1P<P7!s0&7!s:&0P4PAf9RFf;RG#;RHP3P6f:RIg078Hg079Tg07:`%D5RJ535!s%%RKg05kO=35JRJPKn011000003!s+$0R5P:P2PBO5g005YRLPAf<RM#8RNf3RO'4g01=j#1!s$'RP,7M,4N'?P?P4!u0$=P8!t|$7P8PBP:C0POC0f5C0f7C0P2C0,K@RN%J@R@n0!tK%02!tJ$MP@n10110;00021010300n200110:000120!sE$2!s:&9!s:':104!s:&8!s:'9106!s:&7!s:$1108105!t21!sD%!wV%P!wBR%6GPHP!vO&E>P!u5~!u5A35X69!u:%A=:CDRD!u?SIRC%;IRIP3P6PFPKP!y17K!u`+LPA%8GRL/4O17GP,4L'?PNP!x>3N!v/~!v/@RL,IA%9;#H%C;EE!xM&!v4S9CPIP!uk'FP!uD~!uDA=5ALe1B:21G:255AeW0W2o"). Qed.


(* [comment removed for export] *)
Definition mmap_fixed_in_ref (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfill k b off ne)
                  | ArmF => kimg_clip (kn_rezero k b off ne)
                  | ArmG => kimg_clip (kn_cutout k b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                       (VFixIn (match arm with ArmF => true | _ => false end) (match arm with ArmG => true | _ => false end) (reg cs 10) ne :: a_vmops cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.
(* [comment removed for export] *)
Definition mmap_fixed_in (cs : acs) (arm : fixed_in_arm) : option acs :=
  match fixed_in_args cs arm with
  | Some (b, off, ne, nlo, nhi, m) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      if match arm with ArmE => budget_ok cs nhi | _ => true end then
        let k' := match arm with
                  | ArmE => kimg_clip (kn_unfillB bc b off ne)
                  | ArmF => kimg_clip (kn_rezeroB bc b off ne)
                  | ArmG => kimg_clip (kn_cutoutB bc b off ne)
                  end in
        let ms' := match arm with ArmF => a_maps cs | _ => rekind (a_maps cs) m end in
        let ss := a_ss cs in
        let cs1 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       ms' (a_totsz cs) (a_ylo cs)
                       (match arm with ArmE => a_eager cs + nhi | _ => a_eager cs end)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs)
                       (VFixIn (match arm with ArmF => true | _ => false end) (match arm with ArmG => true | _ => false end) (reg cs 10) ne :: a_vmops cs) in
        match arm with ArmE => vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1) | _ => Some cs1 end
      else None
  | None => None
  end.

Lemma mmap_fixed_in_eq : ltac2:(zQ "60!ig3!iu3!ljb!vs0!vsf!vtf>2cs$0>3arm$3@3$2@1$1$0@2$4^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##Lup'0h01lh13armi003armh22csh32ubh42ukh52uni011bi021mi032nei043nhii053nloi063offi071pi082p0i092p1i0:2p2i0;2p3i0<1xp;1p;2p;4p;3p;<p;6g00EVj1VTg063Nj12Tg03g2j1_j4RTg00GCR0j1]!s1$eR1j29Tg074Mj2NTg07;lj2TTg06=Fj1JTg002^j1CTg003Cj1^Tg0259j2:Tg00HEj1?Tg00O=j1>Tg00Kbj1=Tg01G_j4Yj1iTg06kOj10Tg070aj4Uj1gTg00Pfj1STg00WCj43Tg06>Mj1PTg07=:j2WTg06?Xj1LTg06@dj1ITg069`j1HTg066nj1DTg068Tj1ETg06:lj1FTg06Anj1GTg06C8j1BTg06DAj1KTg06S0j2ATg07>Ej4@Tg06ENj1MTg01Y_j3<Tg06FZl<5Tg02b4j2\Tg036[j2[Tg02e@j2ZTg06JMj46Tg00Qoj1mTg01Hnj4Xj1kTg0720j4Qj1lTg001Hj37Tg004Fj2jTg01S\j1hTg00A[j6;Tg07?Pj1fTg03ecj1cj4eTg07@cj1dTg07B6j2bTg07CHj2aTg0153j1OTg00gjj2`Tf0R2#O#Op=8g00j5R3f1R4;<2p=1g00hLR5/`2p=4g0775R6g01<aR7g004`R8%V3R3^57]4]3R9%24R:#_%]5R;P01978R</97R=/98R>/98R?g05R?R@'9RAP;f2RB/N4RCP1P?P@P;P2P1P>P8P;P4P1P=!s0+<P7!s0&7!s:%g005YRDP;P6PDf<REf=RFf6RG'Tg0069RHPHn011000003!s+$0RIP6P;PE%JFg006Y#C#C#^RJ':RK%?FRL#>RMP6P3PE%2FRN#=ROP4P2PBCY#0RPP!s4'U#0f;!sB'O3#0RQ!t:3%SLRLC3P6%V@RRPE%PFRSf8RT'WRUPSPU!tk4U%LFRS%IFRVP6P8PE%HFRW/:GPWPW!sT4W%DFRX%EFRY%FFRZ%GFR[%BFR\%KFR]g07D^R^P6PDPEg02WeR_PHP_!sn3!sG%P_P_!vM5g01=j#8!s$'R`,AFRaPBC@%MF3<RFM<5RbPaPB1\42Rc/[BRd1ZcBRc%2b'1'1C6%4bRbPb!t%-!s-$%m5Rbn!s2%0020100n200110;000121101106!s:&:!s:';103!s:&9!s:':105!s:&8!s:'9104!s:&7!s:'8102Pbn!t#$<00021!sD%P0PAP;P!zAVPDP;P!yi&PKP!yP&PN!y;&X#0!s2+Q#0Re!s4+R#0RN!wP4LC3PUPSPVPWPXPYPZP[P\P]P!w,$fPaPB%2f,1c,1dC6%4fRfPf!vv3P!vs~!vsORf37X09P9%l:!w#tPPQP!v]RP!v]%P!v],PRPPP!v]~!v]`=7;f!v]%k!v]uQPe!v]SF!v]%F!v],FRFPF!v]~!v]h!vX$1N42R9!v\Z6PDPO1TEGP!#9E6f!vz$O%JE/:JRJ%?ERF#>Ra!w/$O%2ER]!~j-]!~j,!s2+R#0!#9/4FRFC3P6PRPO%PERR/WTRTPRPT!tO4T%LERR%IER\P6P8PO%HER[/:GP[P[!sT4[%DERG%EERZ%FERY%GERX%BERW%KERV!uc%P!#8u<O!#8u81AE`R`!#8e$E5<^R^M<5REP`PB%2E!yI,EREPE!yI~!yI`RE,j;%=:RH#i%h:E;%gH%f:E;%cH%d:E;!}=&!y_[!yA&PJP!y4'=]!y4+Y!y$-U!s2-e!y45PFC3PTPRP\P[PGPZPYPXPWPVP!w;$^!w;%^!w;,^R^P^!w;~!}^cEe1b421a4257;eW1X25o"). Qed.


(* [comment removed for export] *)
Definition ENOMEM_RET : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!ji9!loa@2$1$0+c").

(* [comment removed for export] *)
Definition refuse : ltac2:(zQ "10!ig3>2cs$0$0") := ltac2:(zQ "70!vv4!ig3!qq1!hgg1!sl8!iie!jv3\2cs$1@2$3@3$4^1Na@1$5$0@2$6@1$2^1+4").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mmap_gate : ltac2:(zQ "50!kj1!h9!va!iu3!ig3>2cs$4@1$3@2$0@2$0$1$1$2") := ltac2:(zQ "h02!h9!kj1!va!jna!iu3!in3!uk9!hge!kka!ji2!hla!hkc!ig3!ji9!ln2!loa&\1x@1$4$0@1$4@2$1@2$1$0$0$2&\2p7$3@1$5@2$1@2$1$0$0$2\2cs$cM4~0@2$6^1Nh1\1z$0M0\1z$0@1$4@2$1@2$1$0$0$2^1@1$5@2$1@2$1$0$0$2\1p$3M3\1p$3@1$4@2$1@2$1$0$0$2^1\2p0$3@1$5@2$1@2$1$0$0$2\2p0$3M3\2p0$3@1$4@2$1@2$1$0$0$2^1\2p1$3M3\2p1$3@1$4@2$1@2$1$0$0$2^1\2p2$3M3\2p2$3@1$4@2$1@2$1$0$0$2^1\2p3$3M3\2p3$3@1$4@2$1@2$1$0$0$2^1\2p4$3M3\2p4$3@1$4@2$1@2$1$0$0$2^1\2p5$3@1$5@2$1@2$1$0$0$2\2p5$3M3\2p5$3@1$4@2$1@2$1$0$0$2^1\2p6$3M3\2p6$3@1$4@2$1@2$1$0$0$2^1~1~1M4~0@2$6^aNc\4prot$0M4~0@2$6^bNd\5flags$0M4~0@2$6^cNe\2m1$0M4~0@2$6^dNf\2z0$0M0\2z0$0@1$4@2$1@2$1$0$0$2^1M2\0$2@1$4@2$1@2$1$0$0$2@1$a@2$e^2@2$f$d+1@1$5@2$1@2$1$0$0$2@2$9@2$1@2$1$0$0$2@4$8@2$1$0$0$2@4$8$0$0^4^3M4\1x@1$4$0$2@2$6^eNa\1z$0M0\1z$0$2^1$b\1p$3$7\1p$3$7$7~1~1@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2\2p6$3@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2\2p4$3@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2\2p3$3@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2\2p2$3@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2\2p1$3@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2\1p$3@1$5@2$1@2$1$0$0$2@1$5@2$1@2$1$0$0$2").

(* [comment removed for export] *)
Definition node_mmap2 (cs : acs) : option (acs * acs) :=
  match mmap_gate cs with
  | Some (prot, flags, isnull) =>
      let g := if isnull then
                 match prot, flags with
                 | 3, 0x22 => mmap_null cs KRW true true               (* [comment removed for export] *)
                 | 3, 0x4022 => mmap_null cs KRWLAZY false true        (* [comment removed for export] *)
                 | 0, 0x22 => mmap_null cs KNONE false false           (* [comment removed for export] *)
                 | 0, 0x4022 => mmap_null cs KNONELAZY false false     (* [comment removed for export] *)
                 | _, _ => None
                 end
               else
                 match prot, flags with
                 | 3, 0x4032 => mmap_fixed_free cs KRWLAZY false false  (* [comment removed for export] *)
                 | 3, 0x32 => mmap_fixed_free cs KRW true true          (* [comment removed for export] *)
                 | 0, 0x4032 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | 0, 0x32 => mmap_fixed_free cs KNONE false false      (* [comment removed for export] *)
                 (* [comment removed for export] *)
                 | 3, 0x104022 => mmap_fixed_free cs KRWLAZY false false   (* [comment removed for export] *)
                 | 0, 0x104022 => mmap_fixed_free cs KNONELAZY false false (* [comment removed for export] *)
                 | _, _ => None
                 end in
      match g with Some csG => Some (refuse cs, csG) | None => None end
  | None => None
  end.

(* [comment removed for export] *)
Fixpoint opt_all {T : Type} (l : list (option T)) : option (list T) :=
  match l with
  | [] => Some []
  | Some x :: r => match opt_all r with Some r' => Some (x :: r') | None => None end
  | None :: _ => None
  end.
(* [comment removed for export] *)
Definition node_mmapgaps (cs : acs) : option (list acs) :=
  match mmap_gate cs, mmap_len cs with
  | Some (3, 0x22, true), Some (ne, nlo, nhi) =>
      if (fresh_ok cs && expr_vars_lt (nxt cs) ne
          && gap_ok cs nhi && budget_ok cs nhi
          && no_holes (a_maps cs))%bool then
        let v := nxt cs in
        let base := escale 4096 (EVar v) in
        let kfacts := KRange (EVar v) 1 ((CEILMAX - nlo) / 4096) :: null_kend base ne nlo
                      ++ kdisj_fixed base ne ++ kdisj_shadow (a_maps cs) base ne ++ kdisj_new (a_maps cs) base ne in
        let kmem := [KWr (SA base 0) ne; KZero (SA base 0) ne] in
        let k' := kfacts ++ kn_grant_filterM (kn cs) (a_maps cs) in
        let cs1 := add_entry cs (sr_upd (s_regs (a_ss cs)) 10 base) k' (S v) (AM base ne KRW) nhi true (a_ylo cs - 2 * nhi) in
        match gaps_of cs1 v 4096 with
        | Some gaps => opt_all (map (fun g => let csg := gap_child cs1 v g in vis_add csg base ne (kmem ++ kn csg)) gaps)
        | None => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_mmapin1 : ltac2:(zQ "20!ig3!iu3>2cs$0@1$1$0") := ltac2:(zQ "e0!jna!vs0!in3!iu3!h9!kj1!ig3!va!ji2!hgm1!hgm8!hgmf!vsf!hgkc\2cs$6M3\1x@1$3@2$5@2$5$4$4$7@1$3$6@1$d^1\1p@2$5@2$5$4$4$7M5\1p@2$5@2$5$4$4$7@1$3$6^1\2p0@2$5$4$4\1b$7M5\2p0@2$5$4$4@1$3$6^2\4prot$4\5flags$4M7\1b$7@1$3$6^3@1$2$6=3arm@1$3$1M4\4prot$4@1$3$1^2M4\5flags$4@1$3$1^1@1$2$1\1p$0M0\1p$0@1$3$1^1\2p0$0@1$2$1\2p0$0M0\2p0$0@1$3$1^1\2p1$0M0\2p1$0@1$3$1^1\2p2$0@1$2$1\2p2$0M0\2p2$0@1$3$1^1\2p3$0@1$2$1\2p3$0M0\2p3$0@1$3$1^1\2p4$0M0\2p4$0@1$3$1^1\2p5$0@1$2$1\2p5$0@1$2$1@2$8$1$b\2p4$0@1$2$1@1$2$1@1$2$1@1$2$1\2p1$0@1$2$1@1$2$1@1$2$1\1p$0@1$2$1\1p$0M0\1p$0@1$3$1^1\2p0$0M0\2p0$0@1$3$1^1\2p1$0@1$2$1\2p1$0@1$2$1M4\5flags$4@1$3$1^3@1$2$1\2p1$0M0\2p1$0@1$3$1^1\2p2$0@1$2$1\2p2$0M0\2p2$0@1$3$1^1\2p3$0M0\2p3$0@1$3$1^1\2p4$0@1$2$1\2p4$0M0\2p4$0@1$3$1^1\2p5$0@1$2$1\2p5$0M0\2p5$0@1$3$1^1\2p6$0M0\2p6$0@1$3$1^1\2p7$0M0\2p7$0@1$3$1^1\2p8$0@1$2$1\2p8$0M0\2p8$0@1$3$1^1\2p9$0@1$2$1\2p9$0M0\2p9$0@1$3$1^1\3p10$0@1$2$1\3p10$0M0\3p10$0@1$3$1^1\3p11$0@1$2$1\3p11$0M0\3p11$0@1$3$1^1\3p12$0@1$2$1\3p12$0M0\3p12$0@1$3$1^1\3p13$0@1$2$1\3p13$0M0\3p13$0@1$3$1^1\3p14$0@1$2$1\3p14$0M0\3p14$0@1$3$1^1\3p15$0@1$2$1\3p15$0M0\3p15$0@1$3$1^1\3p16$0@1$2$1\3p16$0@1$2$1@2$8$1$a@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1@1$2$1\2p7$0@1$2$1@2$8$1$9\2p6$0@1$2$1@1$2$1@1$2$1@1$2$1\2p3$0@1$2$1@1$2$1@1$2$1\2p1$0@1$2$1\2p0$0@1$2$1@1$2$1\1p$0@1$2$1M3\3arm@1$3$1@1$3$6^1\3arm$1@2$c^8^1@1$2$6@1$2$6").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition node_mprotect_ref (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs CEILMAX true with   (* [comment removed for export] *)
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in
      match find_containing k (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfill k b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (VProt (reg cs 10) ne :: a_vmops cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition node_mprotect (cs : acs) : option acs :=
  match reg_lit cs 17, reg_lit cs 12, fixed_args cs CEILMAX true with
  | Some 226, Some 3, Some (b, off, ne, nlo, nhi) =>
      let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      match find_containingB bc (a_maps cs) [KNONE; KNONELAZY] b off ne with
      | Some m =>
          if (budget_ok cs nhi && expr_vars_lt (nxt cs) ne && expr_vars_lt (nxt cs) (reg cs 10))%bool then
            let k' := kimg_clip (kn_unfillB bc b off ne) in
            let ss := a_ss cs in
            let cs1 := ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k' (s_next ss))
                           (rekind (a_maps cs) m) (a_totsz cs) (a_ylo cs) (a_eager cs + nhi)
                           (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (VProt (reg cs 10) ne :: a_vmops cs) in
            vis_add cs1 (reg cs 10) ne (KWr (SA b off) ne :: KZero (SA b off) ne :: kn cs1)
          else None
      | None => None
      end
  | _, _, _ => None
  end.
Lemma node_mprotect_eq : ltac2:(zQ "50!ig3!iu3!ljb!hgn6!hgo6>2cs$0@3$2@1$1$0@1$3^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##]vp'0h01bi001bh12csh25kindsh31lh42msh51nh61oh73offi013offh82ubh92ukh:2uni021mi032nei043nhii053nloi061pi072p0i082p1i093p10i0:3p11i0;3p12i0<2p2i0=2p3i0>2p4i0?2p5i0@2p6i0A2p7i0B2p8i0C2p9i0D1xi0E1zi0F2z0p;1p;2p;3p;4p;<p;6g00EVj1ATg00GCR0j1VTg063Nj11Tg05Hej1^j6UTg0153j1?Tg06PXj2>Tg00Qoj1`!sa$eR1j2:Tg073>j3FTg06>Mj1@Tg00PFj1]Tg01Y_j36Tg07;lj2\Tg064Uj1WTg065]j2=Tg017[j2<Tg06S0j2QTg06=Fj1NTg002^j1YTg003Cj1aTg0259j28Tg00HEj1JTg00O=j1ITg016Rj1_Tg07Eij3GTg00Kbj1;Tg01G_j4Hj1fTg06kOj17!ts$fj1KTg00WCj43Tg07=:j2ETg06?Xj1DTg06@dj1MTg069`j1CTg066nj1OTg068Tj1PTg06:lj1BTg06Anj1RTg06C8j1STg06DAj1[Tg07G2j2ZTg06ENj1XTg06FZl<4Tg02b4j2mTg036[j2lTg02e@j2kTg06JMj45Tg01Hnj4Tj1hTg001Hj39Tg004Fj2gTg01S\j1dTg00A[j6LTg05GPj1ej6bTg05gJj1cTg07H=j1iTg07IOj1jTf0R2#?#?p=2g00j5R3f1R4;62p=0g00hLR5g05R?R6#Ag05SJR7#Ag01<aR8g004`R9%V6^58]7]0]2]4R:%12R;#^%V5R<P0P9P<g01=j#2!s$'R=#2R>#?!s2$?,>4R@P9P<P2%`5R5g02TZRAP<P2P5P!s-%!s41!s-3!sJ15!tB%f:/>>RB!t#%!so45P01:89RC/:8RD/:9RE/:9RFP<f=g008GRGg0069RH3FRIP1PE!so&1PD!s0$4P1PCP8!s0&8!s:&0P6P<fERJfFRK#@RLg079Tg07:`%]7567567R7P4P2f2RMO5g005YRNP<fGROf7RP'\%WORQf3RR'='<1QO=RS,=Q'<RQ%NOg006Y#Y#Y#aRT'8RU%JORV#Ig01>I#_RW7G=RX%1ORY#;PMP4PRCH#7%KVRVC3%@O/E2RZ%DOR[%MOR\%CO/8PR]%OOR^%POR_%BOR`%RORa%SORb%[ORcg07D^Rd1ZSR%XO36ROM<4RePSPR1mM4Rf/lRRg1kfRRf%1e'0'0C5P5n010!s#$20100P5n10110D00021110200n200110;000121100101!s:&:!s:';103!s:&9!s:':105!s:&C!s:'9104!t24C00n0110B00031010C!s'$01P!tn%10A!s@$110B10!sN$!s>&F0003001110A1010A!t&4F!t&&@!t&'!sN%!t&-?!t&'@10!sN$!s@+>!s@'?10!sN$!s>&=!sr'>1!sL%!s>&<!s>'=1!sL%!s>&8!s>'<1!sL%!t0+7!t0'810!sN$!s>&6!sX'71!sL%!s>&E!uf,610106!uf4E00!|h%P@!|c2!}\^P!}W>PFP<P!}2R%1KRePLP!|r$PMEURhPNP<PQPUPXPY!{y&T#7PVC3PZP[P\P]P^P_P`PaPbPcP!{B$YPSPR%1Y,0f,0g!{3~!{3~!{3~!{3~!{3~!{32RY39X6:%A3^:8^99^88R3%h;!{K~!{KjP!{:/K!{:%O3!{:CO!{:%O!{:~!{:~!{:~!{:~!{:~!{:8=9<YX33!z5%1>2?R?!{,mf9/>>R>!{2Af<?FGHRH!#7]RJRG%@JRJ!#7`+PNP<1\KP%WKR3/=R'<1QK=RY,=3'<R3%NK/8TRT%JKRO#I?G=WRWPe!#80+%KOROC31EL2RL%DKR=%MKRS%CK/8PRP%OKRc%PKRb%BKRa%RKR`%SKR_%[KR^1ZYR%XK56dRdM<4RKPYPR%1K!|K~!|K~!|K~!|K~!|K~!|K8RK,g<%;;R]#f%d;EL%e]%c;EL!{e%P!|YnP!|TBP!|NS;GP!|I,bPNP<P3PTPW%;!{x'H#7POC3PLP=PSPPPcPbPaP`P_P^P!{I$d!{I%d!{I~!{I~!{I~!{I~!{I~!#8n:Ke%i2%j259<eW1o"). Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)

Definition amap_match (k : list kentry) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqb k n (am_len m))%bool.

Local Open Scope lzb_scope.
Definition amap_matchB (bc : bctx) (b : expr) (n : expr) (m : amap) : bool :=
  (negb (is_fog m) && expr_eqb b (am_base m) && len_eqbB bc n (am_len m))%lzb.
Local Close Scope lzb_scope.

Lemma amap_matchB_eqf : ltac2:(zQ "90!hta!va!hg1!ljb!hl3!hgpb!hgq8!ik0!lgf>2fk@1$2$7@3$3>1b$0>1n$0>1m$4$1@1$6@1$8^1@1$5^1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h01mh11nh21bh32fkh41xh52x0h62x1p;1p;2p;3p;6p;4p;5g00EVj1GTg00Kbj11Tg07Jej1=j2Fj3>j4ATg07L5j1:j2Ej3<j4BTg04SJj1;j38Tg05J9j14Tg05KDj13Tg05N<j17Tg02Omj26Tg05OHj19Tg017[j20Tg001Hj35Tg004Fj2DTg04R=j1CTg07MDj1?Tg00A[j6@Tg01;_j52Tg00j5#Gg01<aR0g05R?R1g005YR2]0R3^10f0R4#1#=%:4P0P3f1R3#1/F41E34P1P2f2R5#1?>34A<534P2^00^10R6f3R7#;P2P2P2P2%43#3R8%73,67R9g02WeR:n0100000020000P4P5%93R;O2P:n01000000200001089f4?85;'0552X26%44#3%74,65'0%949873'0,D2%17R6#C%?7E@P6P5P3P4CAP7P5P3P4CB552eX61D2X50D2X40D2W3o"). Qed.
#[local] Hint Rewrite amap_matchB_eqf : bceq.



(* [comment removed for export] *)
Definition node_munmap_ref (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_x k pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_x k pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_match k b ne) (a_maps cs) && page_aligned k b && flat_x k bb bk ne
          && match xhi k b with Some hi => Z.leb (hi + nhi) 0x800000000000 | None => false end   (* [comment removed for export] *)
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in
                               Z.leb 3 (ealign k (fst p)) && Z.leb 3 (ealign k (snd p))
                               && xinside k pb pk (snd p) bb bk ne && kzero_x k k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_of k (fst p) (snd p) in kn_unfill kk sb sk sn) gone (kn_unfill k bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_match k b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (VUnmap (reg cs 10) ne :: a_vmops cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_munmap (cs : acs) : option acs :=
  match reg_lit cs 17, mmap_len cs with
  | Some 215, Some (ne, nlo, nhi) =>
      let b := reg cs 10 in let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
      let '(bb, bk) := split_lit b in
      let gone := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in negb (ranges_apart_xB bc pb pk (snd p) bb bk ne)) (a_vis cs) in
      let kept := List.filter (fun p => let '(pb, pk) := split_lit (fst p) in ranges_apart_xB bc pb pk (snd p) bb bk ne) (a_vis cs) in
      if (existsb (amap_matchB bc b ne) (a_maps cs) && page_alignedB bc b && flat_xB bc bb bk ne
          && match xhiB bc b with Some hi => Z.leb (hi + nhi) 0x800000000000 | None => false end   (* [comment removed for export] *)
          && forallb (fun p => let '(pb, pk) := split_lit (fst p) in
                               let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in
                               Z.leb 3 (ealignB bc (fst p)) && Z.leb 3 (ealignB bc (snd p))
                               && xinsideB bc pb pk (snd p) bb bk ne && kzero_xB bc k sb sk sn)
                     gone)%bool then
        let k1 := fold_left (fun kk p => let '(sb, sk, sn) := shadow_ofB bc (fst p) (snd p) in kn_unfillM kk sb sk sn) gone (kn_unfillB bc bb bk ne) in
        let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (ELit 0)) k1 (s_next ss))
                 (List.filter (fun m => negb (amap_matchB bc b ne m)) (a_maps cs))
                 (a_totsz cs) (a_ylo cs) (a_eager cs) kept (gone ++ a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (VUnmap (reg cs 10) ne :: a_vmops cs))
      else None
  | _, _ => None
  end.

Lemma node_munmap_eq : ltac2:(zQ "50!ig3!iu3!ljb!hgr6!hgs4>2cs$0@3$2@1$1$0@1$3^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "#$S9p'0h01pi001ph11bh22kkh31mh41eh51nh61kh71lh82b1h92b2h:2csh;2k1h<2k2h=2n1h>2n2h?1oh@3offhA2ubhB2ukhC2unhD1zi011zi022bbi032bki042hii052nei063nhii073nloi082p0i092p1i0:2p2i0;2p3i0<2p4i0=2p5i0>2p6i0?2p7i0@2p8i0A2pbi0B2pki0C2sbi0D2ski0E2sni0F1xp%0p&0p;1p;2p;3p;4p;7p;5p;<p;6g063Nj1;Tg07L5k10Sj3\j4VTg00GCR0j1ZTg0153j1OTg06PXj2iTg00Qok10N!sM$eR1j2ETg06T8j1UTg06S0j2@Tg05ZSj1LTg06>Mj1fTg00:mj3HTg00Kbj1>Tg04YGj2qj1~Tg04MEj4oj1zTg04?cj2`k101Tg0259j2!t=$2^j12Tg003Cj1MTg000kj26Tg05TVj3Dk106!sE$ak103Tg04]3j2Ck10BTg017[j21Tg046ej7Rk102Tg04C?j5Tj1|Tg0193j7Qk108Tg05KDj1:Tg066nj1kTg01M_j33Tg0688j3<Tg06=Fj1PTg00HEj1STg00O=j1sTg016Rk10RTg07Eij3rTg00EVk10QTg01ToS00k40PTg01G_j4pk10?Tg00Pfj1nTg06?Xj1mTg06@dj1hTg069`j1g!tM$Tj1eTg03G<j3BTg06:lj1aTg06Anj1bTg06C8j1_Tg06DAj1cTg07NUj2dTg06ENj1^Tg01Y_j3]Tg06FZl<8Tg04ZYj2jk10!wc$NQj4[k10ETg04@lj2lk10;Tg05Uej3Fk10<Tg04[jj2Gk10FTg0498j7Yk10:Tg04DLj5Xk10CTg013bj7Wk10=Tg01HnS01j4Ik10DTg001Hj34Tg004Fk207Tg00A[j65Tg04;Ok104Tg04B2k105Tg05hck100Tg01:Gk109Tg07O`j1}Tg07Q6j1{Tg01S\k10!zJ$bOk10ATg04^?j1yTg07Jej1xj3wk40HTg07RGk10GTg07S[k10ITg07Tkj1v!y~$Nk30KTg05o>k30L!{4$0j5uTg00WCj4tTg00gjk20OTf0R2#O#Op==f2R3f1R4'1/12p=0%22#2p>0M!s/$#!s3%J!s3+!s$'p=Ag01<aR5@0K52p=JB0L552p=Kf7R6f6R7f5R8f4R9f3R:P3P4DuP2Ctp=9g00hLR;00O2p=7A<342,1:p=?g05R?R<g005YR=]3^55^15R>%;2R?$0S%Z;R@P0g004`RAP@g01=j#=!s$'RB#O!s0%S02,i4RCPAP@P2&0N;RDg02TZREP@P2P!s+5D!s4@DP01E5ARF/EARGP@f:RH#URIP1PF!t2%P1P5!s0$4!s0'f?/@B#LRJP=P@f@RKfARL/@BRMP:O2%fLRN5H<%;LRO#>RP/qMRQPPP4P2P:CoRR30P0PAP=1`PM1N28g006YRS$0MRT#2$0J#A!s$+M'6RUg02WeRVn10110F00021010400RW1E55RX!th&=%J2RY#LRZ!u5$5P=fD#;R[#>R\%J3R]%K3R^3DR_!sW'P4&03S#MRSfH#;R`#>Ra%J7Rb'C'6%K7Rc,Ca,6S'1PaP8P9Pcf8RdP6PHFRRePaP`!uM$3DTRa30n200110800012010C10D!s:&F!s:'810E!s:3A10BX0!u<+PZP\!s}$^P9P:P7FQR\#:!s[:%kLRf53XRg3<30%PL%MTS03'NRT%SLRh#sg01>I$0RS047rBRig00j5$0QRjPX!vF&jfCS05#;Rk#>S06%K2Rl7DY!t_&jP4P8!u^%H0P!u[7S07!u^7X0XX2jRmPg!xm+p%nhRhG9S08PLfBS09/@BS0:P9P2O3#:X3<=3<N%mLRn%hLRo%gLRp!v8/!u~:=3XfR\%eLRq9BXgRr%aLRs%bLRt%_LRu%cLRvg07D^S0;1dM:%^L3]RLM<8#7PDn010!s#$20100!t201102103!s:&@!s:'51!uk+?!s:'@106PD!zf/!sD%n0110>00031010?!s'$01PD!tF$10=!s@$110>10!sN$!s>&<!sX'=1!sL%!sX+;!sX'<10!sN$!s>&:!sX';1!sL%!sX+9!sX':10!sN$!s@+8!s@'910!sN$!s@+0!s@'810!sN$!s>&100030011100!s4$!uj410!~B%@P!#4X%!#4#1!#4OOPGP@P!#4@?PJP=P@A\OM:=H<NRw1jOMPO!z2&[Rx30Ry!#3{%lOMPUP!#3S5'1S0<P!}</!|'%=AF[]^S0=!s@+41G`b,6S1G`c!~{$RzP`!~}%P!~{%YP`!~y+XR{!~yo[!~y0WR[!~y<!{y$|C?S0>PTPiP!~N-AFkYlS0?!~@5CI!~?9@!~?=P|!w1+IR}PhG9Q09#;R~Q!~6%CV!~6+RNPnPoP!~//[!u4>S0:ABX|qS0APsPtPuPvP!}h~!}h~!}h~!}hlR[34X1>PA^45R>&0F?!}z~!}z:11wQRQ/1R!}=5P!#=L,fGRRPbO1,6SPRPc!s/$'1?0ea!|wb=<Xg70WQ08P!zi'\Pr!z;2S08!z>~!z>~!z>~!z>f=4@[XD>P=^55^@A^1!zD$E!zD~!zD;PK!#4~$O3S0B,1Q!zKA11zeRe/1!z:gS0C!z=&!yw~!yw~!yw~!ywj1>Pj^C5^BA^A5Ra&0D!yw~!yw;A0QxWRQQ0C'1!#=2'mPgQ0BPhG9!#4&=!y-~!y-~!y-~!y-k7aP>^6jR>&0C!y$~!y$;PQ!#EQ6!#3m-PR!#E%&O4,1e!#E$bgC?!z8/P}!z7BRr!z9~!z9~!z9~!#4Am=!#BR%>!z9~!#;4=MO1R\=0wx!#;0Be{!z67Re!z8NR_!#BC%P!yh~!yh~!yh~!yhq>5^<A^95^=5^;A^8!yw$=!yw~!#IK<yWRWPX!ya-ZQ05!#R#-O6R_!#R#@r!#4^/r!#4^1!zu,_!sk>ABXrq!#<?~!zB~!zB~!zB{1EF5!#i`%r&0<!z8~!z8;PW!#<D6Q05P]P^O2P!#4fNP|!z@-!sp%jQ09PYPlO2Q!#d0>P|!zl1Q0:Q!#Wx~!zF~!zF~!zF{0r%ZA^4!zB$;!zB~!zB<0!z<$\!#bT8!z\7=!zVP=<X|50y!zY5?!zSeRy!zU~!zU~!zU~!zUk?rP>&0:!zO~!zO;Q!#i]8Q!#iX-PR!#iF-O6=0z{!#K8b|C?P!yf~!yf~!yf~!#Cyna^6jRaQ01!yj~!yj<>!#4/5!#mu+fF!#mw&O4!y^K!#<'~!yl~!yl~!yl~!#Xd<!yb$Q02,i2Ra!yhif9#UR[!yl?f>!$,:$LP=P@%;KRv1@KBRu;\:%fKRt5H<1jvuPv!#x2&!$,''lvu!#<XJAFk]^!s=+4%;RRR/G!#x$$R!#x$$!#5^0FYPRPR!#w~&!#w|nk!#w|1k!$'w=KRs53XRp5<X30%PKQ03'NRo%SKRn#sQ!$'m$B!#x=0~YlQ!#wj?p!vi+I%nnRnG9POPM!#we0t%mKRO%hKRN%gKRh!u6/!#N4<s%eKRk9BXp%aKRp%bKR}%_KR|%cKRiQ0;1du:%^K3]RK!~'~!~'~!~'~!~'kRT-07@Q00g07V?E5%>?RJ$02&04?E5&01J&05!s0$6J&00!s0$8J&09?E5%~J%}?E5%|J%{!s@$?J&0@?E5%zJ&0A!s9$BJ%y?E5%xJ&0G?E5!#9y%!#37iP!#33?P!#3+$>vRv?wu:=H<t1q!~{-o!~{+`!~{MQ06?D!~}0>RR]/C!~}$C]!~}&]!~}0RP]!~}+T!~}nQ06!$7w17!#X{>sR^!~z$PoP!~e0%>~?DYl!#J5@^!vU+pPnG9PP!~d%H0H!~e+POPNP!~\/7!tZ>ABX^kPpP}P|PiP!~@~!~@~!~@~!#=EnTe&0I2%v254@eX:;o"). Qed.


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_req (cs : acs) : option Z :=
  match lit_diff (reg cs 10) (a_brk cs) with
  | Some d => if (Z.ltb 0 d && Z.eqb (d mod 4096) 0 && Z.leb d (2 ^ 40))%bool then Some d else None
  | None => None
  end.

(* [comment removed for export] *)
Definition brk_base_ok (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (page_aligned k b
   && match xlo k b, xhi k b with
      | Some lo, Some hi => Z.ltb 0 lo && Z.leb (img_hi A) lo && Z.leb (hi + d) KHI
      | _, _ => false
      end)%bool.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_grow_admissible (cs : acs) (d : Z) : bool :=
  (brk_base_ok cs d && no_fog (a_maps cs) && budget_ok cs d)%bool.

(* [comment removed for export] *)
Definition brk_grow_blocked (cs : acs) (d : Z) : bool :=
  let k := kn cs in let b := a_brk cs in
  (brk_base_ok cs d
   && existsb (fun m => negb (is_fog m)
                        && lin_ge0 k [(am_base m, -1); (am_len m, 0)] [(b, 0)]      (* [comment removed for export] *)
                        && lin_ge0 k [(b, d - 1)] [(am_base m, 0)])               (* [comment removed for export] *)
              (a_maps cs))%bool.

(* [comment removed for export] *)
Definition node_brk1 (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 214 =>
      let ok := match reg_lit cs 10 with
                | Some 0 => true
                | _ => match brk_req cs with Some d => brk_grow_blocked cs d | None => false end
                end in
      if ok then Some (set_pc (set_reg cs 10 (a_brk cs)) (pc cs + 4)) else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition brk_range_facts : ltac2:(zQ "30!hg1!ig3!ik0>2cs$1@1$0$2") := ltac2:(zQ "e0!h9!ik0!hg1!iu3!kj1!ina!mo8!kj8!kje!ig3!uh3!ug9!sh9!si1\2cs$9M3\1x@1$3@1$2@2$4$0$0@1$2$1@3$b^1N5+hgg0\4gaps@1$2@2$4$0$0M3\1x@1$3@2$4$0$0@1$2$1@1$a^1\1g@2$4$0$0@3$6$1@3$d@1$cN5@3$7$0$0^1@3$8$0$0^1@1$5$1@1$5$1@1$5$1").

(* [comment removed for export] *)
Definition node_brk2 (cs : acs) : option (acs * acs) :=
  match reg_lit cs 17, brk_req cs with
  | Some 214, Some d =>
      if (brk_grow_admissible cs d && expr_vars_lt (nxt cs) (reg cs 10))%bool then
        let k := kn cs in let b := a_brk cs in let '(bb, bk) := split_lit b in
        let csA := set_pc (set_reg cs 10 b) (pc cs + 4) in
        let k' := kdisj_new (a_maps cs) b (ELit (d + 4096)) ++ kn_grant_filterM k (a_maps cs) in   (* [comment removed for export] *)
        let ss := a_ss cs in
        let csB0 := ACS (mk_ss (pc cs + 4) (s_regs ss) k' (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) (a_vmops cs) in
        (* [comment removed for export] *)
        let csB := ACS (mk_ss (pc cs + 4) (s_regs ss) (brk_range_facts csB0 ++ k') (s_next ss))
                       (AM b (ELit d) KRW :: a_maps cs) (a_totsz cs + d) (a_ylo cs) (a_eager cs + d)
                       (a_vis cs) (a_ghost cs) (a_abytes cs) (reg cs 10) (a_fd cs) (a_tidset cs) (a_vmops cs) in
        match vis_add csB b (ELit d) (KWr (SA bb bk) (ELit d) :: KZero (SA bb bk) (ELit d) :: kn csB) with
        | Some csB' => Some (csA, csB')
        | None => None
        end
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)

Definition node_settid (cs : acs) : option acs :=
  match reg_lit cs 17 with
  | Some 96 =>
      if (negb (a_tidset cs) && fresh_ok cs)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (pc cs + 4) (sr_upd (s_regs ss) 10 (EVar v)) (KRange (EVar v) 1 (PID_MAX - 1) :: s_know ss) (S v))
                 (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) true (a_vmops cs))
      else None
  | _ => None
  end.

Definition node_exit : ltac2:(zQ "30!iu3!h9!ig3>2cs$2@1$0$1") := ltac2:(zQ "8b!h9!jna!in3!iu3!uk9!ji2!hgt6!ig3&M3\1x@1$3$0@1$3$0@2$4^9Na\4code$0@2$5$0@2$6^1+vf@1$2$0&M1\2p5$1@1$3$0^1\2p6$1@1$2$0\2p6$1@1$2$0~0&\2p5$1~1&M1\2p4$1@1$3$0^1\2p5$1@1$2$0~2@1$2$0&\2p4$1~3&M1\2p3$1@1$3$0^1~4\2p4$1@1$2$0@1$2$0&\2p3$1~5&M1\2p2$1@1$3$0^1~6\2p3$1@1$2$0@1$2$0&\2p2$1~7&M1\2p1$1@1$3$0^1~8\2p2$1@1$2$0@1$2$0&\2p1$1~9\2cs$7M3\1x@1$3$0@1$3$0@2$4^1Nh1\1z$0M0\1z$0@1$3$0^1@1$2$0\1p$1M1\1p$1@1$3$0^1\2p0$1M1\2p0$1@1$3$0^1\2p1$1@1$2$0~a@1$2$0\2p0$1M1\2p0$1@1$3$0^1~a\2p1$1@1$2$0@1$2$0@1$2$0\1p$1@1$2$0@1$2$0").

(* [comment removed for export] *)

Fixpoint list_set_nth {T} (i : nat) (x : T) (l : list T) : list T :=
  match l, i with
  | [], _ => []
  | _ :: r, O => x :: r
  | y :: r, S i' => y :: list_set_nth i' x r
  end.
Fixpoint list_insert_nth {T} (i : nat) (x : T) (l : list T) : list T :=
  match i, l with
  | O, _ => x :: l
  | S i', y :: r => y :: list_insert_nth i' x r
  | S _, [] => [x]
  end.

Definition fog_token : ltac2:(zQ "20!h9!hl3>2sz$0$1") := ltac2:(zQ "40!iie!h9!hgtd!hgu2\2sz$1@3$2@1$0Z@1$0^1$3").

Definition with_maps (cs : acs) (ms : list amap) : acs :=
  ACS (a_ss cs) ms (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs).

(* [comment removed for export] *)
Definition node_fog (cs : acs) (i : nat) (sz : Z) : option acs :=
  match nth_error (a_maps cs) i with
  | Some m =>
      if (negb (is_fog m) && Z.leb 0 sz && Z.ltb sz two64
          && match xhi (kn cs) (am_len m) with Some h => Z.leb h sz | None => false end)%bool
      then Some (with_maps cs (list_set_nth i (fog_token sz) (a_maps cs)))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition node_fognew (cs : acs) (i : nat) (sz : Z) : option acs :=
  if (Nat.leb i (length (a_maps cs)) && Z.leb 0 sz && Z.ltb sz two64)%bool
  then Some (with_maps cs (list_insert_nth i (fog_token sz) (a_maps cs)))
  else None.

(* [comment removed for export] *)
Definition node_ghost (cs : acs) (b n : expr) : option acs :=
  match xhi (kn cs) n with
  | Some nhi =>
      if (expr_vars_lt (nxt cs) b && expr_vars_lt (nxt cs) n && Z.leb (a_eager cs + a_abytes cs + vis_cost nhi) LIMIT)%bool
      then Some (ACS (a_ss cs) (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs ++ [(b, n)])
                     (a_abytes cs + vis_cost nhi) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs))
      else None
  | None => None
  end.

(* [comment removed for export] *)
Definition vis_here : ltac2:(zQ "30!hta!va!kj1>1b$0>1n$0>1p@2$2$0$0$1") := ltac2:(zQ "60!hta!ju7!jse!kj8!kj1!kje\1b$0\1n$0\1p@2$4$0$0@2$2@2$1@3$3$0$0^1^3@2$1@3$5$0$0^1^2").

Definition node_unvis_ref (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_of k b n in
  match xhi k b, xhi k n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealign k b) && Z.leb 3 (ealign k n) && flat_x k bb bk n && Z.leb (bh + nh) 0x800000000000
          && flat_x k sb sk sn && kzero_x k k sb sk sn)%bool
      then
        let k1 := kn_unfill k bb bk n in
        let k2 := kn_unfill k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs))
      else None
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition node_unvis (cs : acs) (b n : expr) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  let '(bb, bk) := split_lit b in
  let '(sb, sk, sn) := shadow_ofB bc b n in
  match xhiB bc b, xhiB bc n with
  | Some bh, Some nh =>
      if (existsb (vis_here b n) (a_vis cs)
          && Z.leb 3 (ealignB bc b) && Z.leb 3 (ealignB bc n) && flat_xB bc bb bk n && Z.leb (bh + nh) 0x800000000000
          && flat_xB bc sb sk sn && kzero_xB bc k sb sk sn)%bool
      then
        let k1 := kn_unfillB bc bb bk n in
        let k2 := kn_unfillM k1 sb sk sn in
        let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) k2 (s_next ss))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs)
                  (List.filter (fun p => negb (vis_here b n p)) (a_vis cs)) (a_ghost cs ++ [(b, n)])
                  (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs) (a_vmops cs))
      else None
  | _, _ => None
  end.

Lemma node_unvis_eq : ltac2:(zQ "60!ig3!hta!iu3!ljb!hgu9!hgv6>2cs$0>1b$1>1n$1@3$3@1$2$0@3$4^3^2^1@3$5^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##QFp'0h01bh11nh21pi001ph31eh41kh51lh62csh71oh83offh92ubh:2ukh;2unh<1zi012bbi022bhi032bki042nhi052sbi062ski072sni081xp&0p;1p;2p;3p;4p;5p;<p;6g063Nj14Tg04[jk101j2ATg00GCR0j1WTg05ZSj1E!s:$eR1j2CTg00Kbj19Tg05TVj3Yj1mTg04?cj2Bj1oTg07WQj2Zj3MTg066nj1HTg00:mj3GTg003aj1e!s/$Cj1TTg000kj23Tg04MEj4@j1iTg0259j2~Tg002^j10Tg04C?j5Vj1kTg00HEj1STg00N6j1XTg00O=j1QTg01G_j4Rj1sTg01ToR2j4<Tg00Pfj1ITg00WCj45Tg06>Mj1JTg06?Xj1KTg06@dj1FTg069`j1LTg05KDj1NTg01M_j3OTg068Tj1PTg023Zj4D!t$$Fj1dTg01Y_j3UTg03G<j3cTg06:lj1bTg06Anj1aTg06C8j1`Tg06DAj1_Tg06ENj1^Tg06FZl<6Tg00Qok100Tg05Uej3]j1rTg04@lj2?j1qTg04NQj4>j1|Tg017[j2:Tg04DLj5[j1wTg01HnR3j4=j1xTg001Hj32Tg00EVj1yTg004Fj2pTg00A[j67Tg04B2j1nTg05hcj1lTg07Q6j1jTg01S\j1tTg05bOj1uTg04]3j1vj2\Tg04^?j1hTg07X^j3gTg07Ymj3fTg00gjj2{Tf2R4f1R5':f0R6':p=1%06#0p=}!s-$#0#0p=z!s2+!s$'p=;g00hLR7/{6p=8g01<aR8g004`R9^38R:%44R;$01%W7R<P1P8P9P<%E4R=P11C89R>P8P<f5#4R?#9f4R@f3RA3YRB!sS'P5P0P9P<f9RC#4RD#9REf8RF'BRG!s@&:RH#4RI#9RJ/BFRKg005YRLP<1C88RM1ZHCf;RN#HRO3GRPg006YRQ#e#TRRPFPHO1'3PFPCO1,3R31%4NRS#9RTf7RUf6RVPCC@1~56%0Q#}#z#;!s$+T'3RQ31PTPAP4P@C@PTPS!s2%DVRW31%SNRX#XRY%QXRZPTPUPVPCCR!sV&<%IXRXC5%JNRT%KNR[%FNR\%LNR]AMNH6#NX2M=OMORO%PNP8P8PHPCCD%dMR^5UM5cMR_%bNR`%aNRa%`NRb%_NRc%^NRNM<6#8Rd&007Ren010!s#$20000Pen101108000210104!s:3110200n2001!s_%121105106!s:&8!s:'0107!s:31103!x1+=P1P!xW$A]?@AR?!xJ31?DFRf!s2'IFRgPLP<1ASH,3R1ASC,3R51PRPPS!v_&>':!w/'C>71QRhPS!w@+[':RiPYPZ!sU+=Rj!sS&=PXC5PTP[P\P]POP_P`PaPbPcP!vL%P!vF~!vF;Rk32X<:PL^18^89^08R:%|;!v]5P!{|4P!{j&PKPLP<PF!uf%O3Rl=1PQPF!ul%O3;1WPd!uR~!uR<=2<kX0:g00j5#yRd^;8^:9^98RP%x!uYV1:hW!xI$l!|Q'!x?~!uk`5PP:^4dR:%w!x9Y!{5&O4,:h!ui$j!uiJRh!uk~!xXC1C>8^18!{'%r!up74P@PAO2!uvBiP!u<4!uN$!u>~!u>-2:%W!#:`%q!u:7!#4q3PVPFO1!s2&U!s2$!t|~!t|27:PP^4dRdP3!tzH!#6i%Pg!w0&YPZPF!yu'O4!|`~!|`ad!#?$+5Rd!uW'%4@Rk?]A4!u^3%4FRN/?U!#9['UPLP<1ZCF%HHRD5GMRc1AIC,3R1AIF,3R31PIPUPVPFC>;1QPI!}$&>PI!s2'D[31%SHRb#XRa%QbR`!sY+=!sT&=%IbRbC5%JHR_%KHRO%FHR]%LHR\AMHC!#=l'DRD%PHP8P8PCPFCD=UM^5cMRM%bHR^%aHR[%`HRT%_HRX%^HRH!wG~!wGARj,p<P2g07V?E7%9;R2#o%n;E7%m2%l;E7%k2%j;E7%s2%t;E7%i2%u;E7%v2%h;E7!wd+!x#,9k?Y!w}69N/B!w{'BE!w{%\J!wm$\JF,3R51cPJ!w;&@;1QPJ!#B^'J!wn+V31PaP`!sO+!#BR'PbC5P_POP]P\PDPMP^P[PTPXP!v|G1!{E{jeAg456Af45652<eX18W0X67o"). Qed.


(* [comment removed for export] *)
Definition node_havocbrk (cs : acs) (lo hi : Z) : option acs :=
  match xlo (kn cs) (a_brk cs), xhi (kn cs) (a_brk cs) with
  | Some l, Some h =>
      if (fresh_ok cs && Z.leb lo l && Z.leb h hi)%bool then
        let v := nxt cs in let ss := a_ss cs in
        Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) lo hi :: s_know ss) (S v))
                  (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (EVar v) (a_fd cs) (a_tidset cs) (a_vmops cs))
      else None
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition node_intro : ltac2:(zQ "30!h9!ig3!iu3>2cs$1>2lo$0>2hi$0@1$2$1") := ltac2:(zQ "h90!ig3!jse!va!h9!jv9!in3!uqb!ji2!mo8!hg8!iu3!ii7!kn2!ipa!sh3!iq2!sh9!si1!ik0!ika!il4!ij6!im6!ji9!lp7\2cs$0\2lo$3\2hi$3M2\0$2@1$a$0@2$1@2$1@2$1@1$c^3@2$4Z^2@2$4^2^1@2$h8^1$h7=1v$9@1$e^3=2ss$h6@1$b^4@2$7$0@2$f^5@4$d@1$h4^1@1$h5^1@3$8$h2@3$h1@1$h0^2^4^3@1$h3^1@1$6^2@1$5$0").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition summary_fill_ref (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xlo k ne, xhi k ne, xhi k dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_x k k db dk ne && kwritable_x k k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_x k k db dk ne then
              let k1 := kn_havoc k0 db dk ne in
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.
(* [comment removed for export] *)
Definition summary_fill (cs : acs) (entry : Z) (cmax : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs, reg_lit cs 11 with
  | Some ret, Some c =>
      if negb (Z.ltb c cmax) then None else
      let dst := reg cs 10 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in
      let c8 := c mod 256 in
      match xloB bc ne, xhiB bc ne, xhiB bc dst with
      | Some nlo, Some nhi, Some dhi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64)%bool then
            if (Z.eqb nhi 0) then after_call cs ret (Some dst) k else
            if (Z.eqb c8 0 && kzero_xB bc k db dk ne && kwritable_xB bc k db dk ne)%bool then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if kwritable_xB bc k db dk ne then
              let k1 := kn_havocM k0 db dk ne in
              let k2 := if Z.ltb 0 nlo then (if Z.eqb c8 0 then KZero (SA db dk) ne else KFill (SA db dk) ne c8) :: k1 else k1 in
              after_call cs ret (Some dst) k2
            else None
            end
          else None
      | _, _, _ => None
      end
  | _, _ => None
  end.

Lemma summary_fill_eq : ltac2:(zQ "60!h9!ig3!iu3!ljb!hhg7!hhh6>2cs$1>5entry$0>4cmax$0@3$3@1$2$1@3$4^3^2^1@3$5^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##bZp'0h01bi001bh11kh21oh34cmaxh42csh51ei011eh65entryh71lh81ni021nh93offh:2ubh;2ukh<2uni031ai041ci051di062dbi073dhii082dki093dsti0:1ii0;2k0i0<2loi0=2nei0>3nhii0?3nloi0@2opi0A3reti0B2sxi0C1xp;1p;2p;4p;5p;3p;6g00EVj1nTg063Nj12Tg04>Sj1[j5BTg00GCR0j1DTg06=Fj1UTg04H1j2:Tg05KDj1=Tg00Qoj1MTg07[@j1LTg0153j1>Tg06PXj2GTg018Vj2@Tg06S0j20Tg05ZSj1TTg00Kbj16Tg045\j2Qj1gTg04?cj2?j1cTg000kj2PTg002^j19Tg003Cj1E!s/$aj1\Tg030`j2ZTg017[j21Tg0259j2YTg00gjj24Tg07\Lj45Tg03=`j2CTg04C?j5Jj1d!uN$Nj4Kj1aTg07][j3ITg02b4j2XTg02e@j2HTg0391j3NTg03XXR1j4OTg01Y_j3;Tg0482j2Fj1jTg04@lj2Aj1kTg04DLj5Sj1mTg04I_j4Wj1lTg01jER2j4VTg001Hj33Tg004Fj2hTg00A[j67Tg04:Bj1fTg04B2j1bTg07^hj1`Tg07Q6j1eTg04=Bj1_j5RTg07`=j1^Tg07aRj3]Tg07bcj3iTf0R3#>#>p=8%93#9p=<g00hLR4g004`R5g00j5R6#nR7g01<aR8g005YR9^88^95]0R:]1R;f2R<#2R=#[%D4R>P9P>f3R?#U/:<#=R@%M4R4P0P5P>%L?RA!s1%f4RBg01=j#8!s$'RC#>RD'GREP9P>1@3?#=RFP4g00GeRGP8!s^$5RH/0C#TRI!so&7RJ#2RK#6RL%>DRM,0JRN'QRO!sF&8RP#2RQ#6RR10PMRS'?RT!sB&9RU#2RV#6RW10UCRX'?RYP9P>g01>IRZ/P<f1R[g006Y#9R\#E%\\#9#<#E'Z'P'11Y3[g01>gR]'@'1R^!u1$:[ZR_f:R`f6Ra10`CRb,48Rc%2`RdC5ReP9P>%9\#<!s$$ER\,CH/:ZRf%6dRgPdPBP?10`MRhDJ'1PJ!s8%PhO4Ri'1PeP0P7P>P9%D7RjPg!sC%CK147dRkP8PjPbP8Pjf;Rb/0MRlf<#21C[]R];I3,47%M7RmP!s$-n0110=000810102!s'$3010@103100!s1D4010B10<!sb%!s4&;10:102P!t859!t8'5!t8pRnn010!s#$20000RoP9P>PP%2bRpPHPBPlO4PbPJ10bC,48RqP9P71@Z?RrP9P61Ca\R\/:ZRZ1XHBRs/HlANsl\!s}2tP3!st%CORu5;6Pu!sG1C5RuP4!s:1P4n10110C00!v~%;00!sH01!s41!sf01!sf31107!s:6>!s:6?00n20!s9'121106108!t<4!s\14!sp6A!u$3!v|$@P!~<&P!~9&P!}v$PFP4P!}k&P!}b&1FKNRv!s2&AQSRw!s2'VXRx!s\$!|O$P_P!|1$Pd!{_'DS,1f!s5-BRy'1Rz!{p,Pj!sB'CWPkP!xw3{!su$pP!xt&DBR|PbPJP!xo$Pr!x>+VR}9;6tP}!x?3!x=~!x=~!x=QR}33X0;P;%m=!xISP!#6m%P!#6Y%PY!x=511fi/1y!w{+!}T%|P!|:4!|L$!v}~!v}~!v}>=3>}X0;P:%l!v}xP!{u1J!{u%O3!{u5P!v~~!v~~!v~H:%D5^58R:%k!w+]HPSO1!s2&aPXO1!w4@{!vne!{X3!vp~!vpS2:P:%j!vjUBPN!vb+!#86%PxP!u^~!u^e7^<8^;5^:8^17R:P2!ukTv!ug4!yOA!#5W$!#:$-P!#:&&O4Rl9;6tPl!#:&~!~'~!wYe7:P9P>%U</:[#=R:!wO'%L<R}!s1%1G?DRD!#JO%<#=Rl!w\,10BC#TRt!s[&2aRq10aMRb'F!sc&AKN!s0&0PCRP,AQ!wv0UPa148XPVC5Ra!s:$VPV!#Hj$UMRU!#?{$!s9&PUDB'1Pa!#7$,!s>&CW147VRMP8PjPX!s+$hAIp]3,47P!#HT~!#HT~!t8>Rm!z]2!#CP&HPBPhDBP`PJPc!{U&9P6PZ1HshANsh!#H62s!{r&hCVR\5;6P\!{q~!{q~!{qaR\,h>P1g07d8E7%6=R1#g%f=E7%c1%b=E7%a1%`=E7%d1%e=E7%_1%^=E7!w@$!|D+P!|A&P!|=$P!|7-P!|1'6q/Qb!{x&?L!|&'?RP!{}0!{q%W!{^+J,1f!s5-R!{m2W!{m&KPMP!y17g!y1+R!y10!xj'ORh9;6sPh!xk~!xk~!#5^c\eA]<[3Ai<[353>eX35W6W4o"). Qed.


(* [comment removed for export] *)
Fixpoint copy_facts (fuel : nat) (k : list kentry) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8e k sb sk with Some _ => true | None => match kread_bytes 8 k sb sk with Some _ => true | None => false end end)%bool then
        match (match kread8e k sb sk with
               | Some v => Some v
               | None => match kread_bytes 8 k sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_facts f k sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookup segs k sb sk 1 false [] [], copy_facts f k sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.

Local Open Scope lzb_scope.
Fixpoint copy_factsB (bc : bctx) (fuel : nat) (sb : expr) (sk : Z) (db : expr) (dk : Z) (n : Z)
  : option (list kentry) :=
  match fuel with
  | O => Some []
  | S f =>
      if (Z.leb 8 n &&
          match kread8eB bc sb sk with Some _ => true | None => match kread_bytesB bc 8 sb sk with Some _ => true | None => false end end)%lzb then
        match (match kread8eB bc sb sk with
               | Some v => Some v
               | None => match kread_bytesB bc 8 sb sk with
                         | Some bs => Some (ELit (zbytes_le_to_Z bs))
                         | None => None
                         end
               end), copy_factsB bc f sb (sk + 8) db (dk + 8) (n - 8) with
        | Some v, Some rest => Some (KWord (SA db dk) 8 v :: rest)
        | _, _ => None
        end
      else if Z.leb 1 n then (* [comment removed for export] *)
        match know_lookupB segs bc sb sk 1 false [] [], copy_factsB bc f sb (sk + 1) db (dk + 1) (n - 1) with
        | LHit v [] _, Some rest => Some (KWord (SA db dk) 1 v :: rest)
        | _, _ => None
        end
      else Some []
  end.
Local Close Scope lzb_scope.

Lemma copy_factsB_eqf' : ltac2:(zQ "a0!h9!hg1!hta!ik0!hg8!iu3!ljb!hhia!hhj7!lgf>2fk@1$1$3>4fuel$4@3$6>2sb$2>2sk$0>2db$2>2dk$0>1n$0@1$5@1$1$3@2$8@1$9^2^1@2$7^1^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##I~p'0h04fuelh11oh21bh31nh43offh51xi001xh62x0h72x1h82x2h92x3h:2IHh;3acch<2dbh=2dkh>1fh?2fkh@5hintsi01!s/%hA1li021lhB2rbhC2rkhD2sbhE2skhF2sxi032bsi041ei054resti061si073scsi081vp;1p;2p;3p;4p;5p;6p;7p;8g00EVR0j19Tg00GCR1j1CTg00Kbj11Tg07eIj2@j3Oj4Kj5Gj6Jj7ZTg07fYj2<j3Mj4Hj5Ej6Rj76Tg001Hj34Tg004Fj2QTg01;_j57Tg0153j10Tg002^j1BTg003Cj1NTg000kj28Tg040fj3Xj1^Tg05;`j4Wj1\Tg00gjj23Tg07ghj1VTg016Rj1UTg00Qoj1ITg0259j22Tg0189j2:Tg02b4j2;Tg02`ij3?Tg01Y_j3=Tg00PFj1ATg03m7j8Tj2`Tg0423j3Pj1bTg05=1j4Fj2STg017[j2DTg03kij8Lj2aTg03nHj2_Tg00A[j6>Tg07i9j1]Tg07jJj1[Tg05?Qj4Y!v+$`R2f3R3f2R4f1R5f0R6D7p=5g00j5R7#9R8g00iVR9g01<aR:%C8R;^32R<^=2R=^<:R>^E2R?]DR@%14RA/@61<6434RBX09P:P?%15g01=jRC'@1<C5P>AOAC6AMC46P:P=%13RAPCP5P6CKPCP3!s0$HP<f4RD#1REPCP4P5P6DGPCPD!s2&EP;f5RF#1RG!sZ$!s<$EJPCPF!s4+RPCf6RHPD!s8'F6,Q;X92C5X82C5X7:D7X62C5X5:D7!t{$05R?,@A1<?3P>%04R>=OE6AM>D!t{$PG%03RG!t{&GPF!t{'%1H%0DR<!ty+<PH!ty-7R<#1%0FRG!tz-GP<!tz-@f8RG,<Hg005YR=P;P=P=g006YR>#B!s$$NRE/85R?P1P:P=f9RA#1RI?XFDRJg0069RKP1%92RLP=PI%0CRC#0!s$/RMPFPDCWRNPKg02WeROn10110000021010200!s82400POn0!s8%020000!tN$;P1P:%C:RPPJ13:6RQP1PLPPPN%V6#U,3:RN%I:RR!sv23!t048!sx$8P;P5PH12FERSPD123ERT1:4ERUO51;FD??M5==76,38RV%I8RW!sn2500PW!t&6=P;%N>R>/85RXg03o]RYP;p,4segsRZPIPFPDPCPO%A=RIg00k@R[#AR\GTR]P0P[!th$!tp%3PG12<>R^!tx$>R_1:D>R`O51;<H??C3!tp'aP!tm>7!vh%20106102PWPWn!sR'33010810710120!s-%00%A7,38Rb!wO1!w]2=!w[%P=APAFDRcPK!wY$=PMPA!xg$FRdPKP!xb6Re!xd5Rf,D?!xY,PPPcP!xR'dPNP!xG6Rd!xI<Gf:RcPHPSPDPTPUF6PV!v@7RV!x17RU!uR$XPYP;PZ!uC%PCPOPIP\GL!wi2cf<PGP^PHP_P`F6P!wPORa!wRFP!wL@R`54;X1@%CL^42^2:^09R@1S6AX09P!~6&P!}z&PJ!wj+6P!}S$O3R_!wj9!}NOPPPJ!ws+_!ws9!wq6V!|N;!wA&]P!v>WR]!s61=4;`X1@PP!v>%R@%bG!v746!v'$2!v'$e!uqR_PQPd!uUL!tl9%9=%9[PY];]@^F=^39^C2^B:R@1aZ!t}/f!tY4!zk/6!zi/O6P!yve!tn$A@P=P;18E6!~O'GD3R@!~O-GPDP3CFR`!ycK'D!vb0@!yU+`!yUL!}6%<PAPF12DEP3124E1:5EF61;D3!#7g,P!#7bM18>6!~W&!uK$!~W<Af;P<12H>!tM$>1:3>F61;HF!#7>,!#7<p!wpA,Q;%1GRb,`Z1_GZE>%^b%]GE>%\b%[GE>1@bHPFE>Pb%0H!#@7/ZPH!uc&!s6%654;e!#@H;X:BX>9P6CYW0W?o"). Qed.
Lemma copy_factsB_eqf : ltac2:(zQ "a0!h9!hg1!hg8!hta!ik0!iu3!ljb!hhia!hhj7!lgf>2fk@1$1$4@3$6>4fuel$2>2sb$3>2sk$0>2db$3>2dk$0>1n$0@1$5@1$1$4@1$8@1$9^1\4fuel$2@2$7^1^2").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) ["WithSegs"] "h04fuelh12dbh22dkh32fkh41nh52sbh62skp;1p;2p;5g00EVj16Tg00GCj15Tg00Kbj10Tg07eIj11Tg07fYj24Tg07k_j22Tg01;_j53Tg00j5#6R0g00iVR1g01<aR2g004`R3%50^43^23^12]6]5f0R2#0#1f1R3,42X011232X01D3W3o"). Qed.
#[local] Hint Rewrite copy_factsB_eqf' copy_factsB_eqf : bceq.



(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kblob_prefix : ltac2:(zQ "40!h9!hg1!hta!ik0>1k@1$1$3>2sb$2>2sk$0>2db$2>2dk$0>3nlo$0@1$1$3") := ltac2:(zQ "h60!hta!ik0!h9!ina!io7!hge!hg8!va!hg1!jh0!jh9!jse!iu3!mo8!iie!hhk5!rvb!ju7!hhke!ln2!jv9!lp7\1k@1$8$1\2sb$0\2sk$2\2db$0\2dk$2\3nlo$2Mc\1x@1$c$1@1$8$1@3$h2$1\1K$1M1\1K$1$7^1\1a$4\1w$6\1v$0$5\1a$4\1n$0$5\1a$4\1n$0\2k0$6M4\1a$4$7^3\1b$0\1o$2M0\1n$0$7^4\2n0$2@2$b@2$b@2$b@2$h1^3^c@2$h3^2^b@2$h5Z^1@2$h4^1^8\2n0$6$5\2op$9\2a0$0\2b0$0$5\2op$9\2a0$0\2b0$0$5\2op$a\2a0$0\2b0$0$5\2op$a\2a0$0\2b0$0$5\2sx$7\2lo$6\2n0$6\1e$0$5\2sx$7\2k1$6\1i$2\2n0$6$5\2lo$2\2hi$2$5\1e$0\1m$2$5\1e$0\2lo$2\2hi$2$5\1a$4\1n$0$5\2a1$4\2n1$0\2a2$4\2n2$0$5\1a$4\1n$0\1c$2$5\1a$4\1n$0$5^6\2k0$1M1\2k0$1@1$8$1^1\1a$4\1w$6\1v$0@1$3$1\1a$4\1n$0@1$3$1\1a$4\1n$0\1j$6M0\1n$0@1$8$1^2\2n0$2@3$d$1@3$f@2$h0^8^7@1$e^1^2@1$3$1\2n0$6@1$3$1\2op$9\2a0$0\1b$0@1$3$1\2op$9\2a0$0\1b$0@1$3$1\2op$a\2a0$0\1b$0@1$3$1\2op$a\2a0$0\1b$0@1$3$1\2sx$7\2lo$6\2n0$6\1e$0@1$3$1\2sx$7\2k1$6\1i$2\2n0$6@1$3$1\2lo$2\2hi$2@1$3$1\1e$0\1m$2@1$3$1\1e$0\2lo$2\2hi$2@1$3$1\1a$4\1n$0@1$3$1\2a1$4\2n1$0\2a2$4\2n2$0@1$3$1\1a$4\1n$0\1c$2@1$3$1\1a$4\1n$0@1$3$1@1$3$1").

Definition summary_copy_ref (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xlo k ne, xhi k ne, xhi k dst, xhi k src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_x k db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_x k k db dk ne && ranges_apart_x k db dk ne sb sk ne)%bool then
              let k1 := kn_havoc k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_x k k sb sk ne && flat_x k sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_x k k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_x k sb sk ne)%bool then
                         match copy_facts (Z.to_nat nhi) k sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ KUnk (SA db dk) ne :: k1)   (* [comment removed for export] *)
                         | None => havoc_src
                         end
                       else havoc_src
                   | _ => havoc_src
                   end
            else None
            end
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_copy (cs : acs) (entry : Z) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) entry) then None else
  match ret_lit cs with
  | Some ret =>
      let dst := reg cs 10 in let src := reg cs 11 in let ne := reg cs 12 in
      let '(db, dk) := split_lit dst in let '(sb, sk) := split_lit src in
      match xloB bc ne, xhiB bc ne, xhiB bc dst, xhiB bc src with
      | Some nlo, Some nhi, Some dhi, Some shi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.ltb (dhi + nhi) two64 && Z.ltb (shi + nhi) two64)%bool then
            if Z.eqb nhi 0 then after_call cs ret (Some dst) k else
            match (if off_image_xB bc db dk ne then Some k
                   else match dst, ne with ELit d, ELit n => Some (kimg_cut k (d mod two64) n) | _, _ => None end) with
            | None => None
            | Some k0 =>
            if (kwritable_xB bc k db dk ne && ranges_apart_xB bc db dk ne sb sk ne)%bool then
              let k1 := kn_havocM k0 db dk ne in
              (* [comment removed for export] *)
              let nx := nxt cs in
              let words := if (Z.eqb nlo nhi && Z.eqb (nhi mod 8) 0 && Z.leb nhi 256 && Z.ltb 0 nhi)%bool then Z.to_nat (nhi / 8) else 0%nat in
              let kfresh := map (fun i => KWord (SA db (dk + 8 * Z.of_nat i)) 8 (EVar (nx + NCS + i)%nat)) (seq 0 words) in
              let havoc_src := if (kwritable_xB bc k sb sk ne && flat_xB bc sb sk ne)%bool
                               then after_call2 cs ret (Some dst) (kfresh ++ kblob_prefix k sb sk db dk nlo ++ (if Z.ltb 0 nlo then KUnk (SA db dk) ne :: k1 else k1)) words else None in
              if (Z.ltb 0 nlo && kzero_xB bc k sb sk ne)%bool then after_call cs ret (Some dst) (KZero (SA db dk) ne :: k1)
              else match ne with
                   | ELit _ =>
                       if (Z.leb nhi 2048 && flat_xB bc sb sk ne)%bool then
                         match copy_factsB bc (Z.to_nat nhi) sb sk db dk nhi with
                         | Some kc => after_call cs ret (Some dst) (kc ++ KUnk (SA db dk) ne :: k1)   (* [comment removed for export] *)
                         | None => havoc_src
                         end
                       else havoc_src
                   | _ => havoc_src
                   end
            else None
            end
          else None
      | _, _, _, _ => None
      end
  | None => None
  end.

Lemma summary_copy_eq : ltac2:(zQ "60!ig3!iu3!ljb!h9!hhl6!hhm5>2cs$0>5entry$3@3$2@1$1$0@2$4^2^1@2$5^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "#$Hjp'0h01bi001bh11ii011ih21oh34fuelh41kh51ni021nh62b1h72b2h82csh92dbi032dbh:2dki042dkh;1ei051eh<5entryh=2k1h>2k2i062k2h?1lh@2n1hA2n2hB3offhC2sbi072sbhD2ski082skhE2ubhF2ukhG2uni091ai0:1di0;3dhii0<3dsti0=2k0i0>2kci0?2loi0@2nei0A3nhii0B3nloi0C2opi0D3reti0E3shii0F2sxi0G1xi0H1zp%0p&0p;1p;2p;4p;3p;5p;7p;6g00EVk10@Tg00GCR0j1\Tg063Nj14Tg07fYj2nj7cTg06=Fj1jTg04H1j2<Tg05KDj1eTg00Qoj1aTg07[@j1`Tg06S0j22Tg05ZSj1UTg0153j1TTg00Kbj15Tg045\j2kj1yTg04?cj2Cj1wTg000kj2ETg002^j1GTg003Cj1O!s/$ak10=Tg030`k20<Tg017[j20Tg0259j2MTg018Vj2BTg07\Lj46!u%$Nj4ij1tTg00gjj2NTg03=`j2VTg07][j3bTg04=Bj5=k100Tg0193j7_j1uTg04C?j5^j1|Tg02b4j2@Tg02e@j2]Tg03XXS00j48Tg04MEj4Fj1rTg07m4j1XTg03:<j2?Tg0162k10?!sB$Tk20>Tg064Uj1RTg07n1j2:Tg02fKj1QTg02`ij3JTg05`bj2[!sJ$Hj2Z!s/$dj6ITg0482j2gj1~Tg04@lj2Hk102Tg04I_j4fk104Tg04>Sj5>k10:Tg013bj7dk103Tg04DLj5hk109Tg01jES01j49Tg04NQj4Dk10;Tg001Hj37Tg004Fj2}Tg00A[j6;Tg04:Bj1xTg04B2j1vTg01:Gj1zTg07^hj1{Tg07Q6j1sTg07`=k101Tg05bOj1qTg07eIk105k706Tg0805j1pTg081Ik207Tg082Zj2oTg01Y_k308Tg03G<j3YTg083oj4mTg084Kj5lTf0R1#T#Tp=P%G1#Gp=Lf2R2f1R3'0/01p=Wg01<aR4/N1p=Ag00j5R5@0831p=1AY531p=Sg00iVR6P5P3P1Cmp=Kf6R7f5R8f4R9f3R:AY5235Y5P1Dlp=3g00hLR;g004`R<&0@5R5#\R=^5<^:<^94^D<^C4^36R>%42,n1X36%\;R?g005YR@P?%j2/<3#eRA%a;R;P0P<P?%`2RBg00GeRCP4P<P?g01=jRD#P!s$%RE#PRF,2:#URGP!sJ&%TFRH,28#URI!sn%f7RJ#4S02#5S03%THRK,2JRL'kRM!sH&8RN#4S04#5S0512NKS06'CRO!sE&9RP#4RQ#5S0712PFS08'CRR!sD&:RS#4RT#5S0912SHS0:'CRUP@!u#$>IRV/E:g006Y#GRW#O&0=W#G#L#O+0<,E2'01M32g01>gRX'B1M12/BX3WRYP@P?1<2VRZf;R[PN12[FR\#AS0;%4[R]C6R^P0P5P?P@P=%5]S0<PJP712[KR_Ci1N5]S0=P4P=P\P4P=f<R\/2KR`f=Ra#4Rb1V3XS0>;b1,N5%a5RXP!s$-n0110@000810102!s'$3010C109100!s1D4010F10?!sb$5!s4&=101102P!t85<!t8':!t8pS0?n010!s#$20000S0@P@P?%4\Rc#5RdPcPNPJP`D=Pd!s0%P7P8P`F_Re'0Rf!wM$BV9RgPdPc!sB%D^'0S0AP\PP12\F#AS0B1@NJS0C/]`RhP1!sp%C8'1C6RiP4P?P`!tE$LWR!xn%LRj!xv%,E9Rk%5bRl!x+%aKRmCFRn'0!xL&[%X9S0DPJP7PPPNP9O6f>RoP[12o!tJ$E1@SPS0F12oKRp'?RqP2PSPPPpC8'1,S1C6S0GP@P?PlPb!sn$mD=S0H/0nPaPS12a!sn$I%OWRW&0?1+0>Rn,MP,@SS0J%Rog085[Rl':/:1#Q7JEX16P@P61<891V9W/<V'0%OjRj,E9;Wg1[9W#XPD!wB1Rr,ZDS0K'KS0L!tX&PPNP8EIS0MP@P51BV8S0N1@PNS0O/?mRsP3!sJ$mC8Rt'1Pt!sy1PrF3S0PP;!s=-100Rtn!xn$G00!zy%>0!sa1101PtP@P?f?Rt#4Ru#5S0QPuPPPN12tKRvD=S0RQ0Q!tL$vCF'0PtP\12t!vJ$S1M[n,@\S0Tf@Rw#R/:l!v:$S0U!v=/J71V7!v=%1E7j1BV73W1[7!v<7x!v<$V'KS0W!tX%P[PSPJEIS0X!v<&JRy1@[SS0Y/?vRzP:!sI$vC8R{'1P{!v;2xF3S0Z!v;4{P!s$%!{n$wR{#5R|P{PSPP12wKR}D=S0[P|!yZ$}!up$wPa12w!up$\1M\n,@aS0]fA!un,!uk/NJ1VJ!uk'Jj;Wy1[J!uh7W!uh$^'KS0_!tO%P\P[PNEIS0`!uh&NS0a1@\[S0b/?}RVP9!sJ$}C8RD'1!sy3PWF3S0c!ui4D!sO$!#5#&110H1110231!#3W+!s1C41!#3m/!s4%6!y}$2!tS01!tL3P;!zL/110=00!sXRE!s:6;!s:6A!s:6B00n20!s9'121107108!s:33104!sb4D!tx4@P?PAP!#==%PB!#<i&P!#<s'P!#<i%Q02/gLS0d!s5'4Q06'HS0e!s7'8,HQS0f!s5':,HTS0g!t0$Y!s+$ZP!#;%,P]PJP7P_CfQ0=Q!#7~4h!sY$c!#7w'>RD!s2'!#7y%d'0S0i!sM+!s;$Dh,0gS0jP\PPQ0B!#7a'9,1hC6!#7`+!#67&CDRj,0kS0k!th%Q0D!#4x,9FcRnPoP[Q0E!#7''9,1q,S1C6!sn&!sp&D>/0jS0lPaPSQ0IQ0LQ!#5[$Q0N!#5K'9R|,1sP|!#5L4!{I4|!#5I5|!#5I1|!tQ$u!#3d%vD>!s0'CDS0m'0S0nPtP\Q0SQ0WQ!#3|$Py!#3l'!t\$z!t\4x!t\7P!s$%@P?P{!~:&}D>!s0'CDS0o'0S0pPwPaQ0\Q0_Q!~R%Q0a!~B+!t?$V!t?4W!t?9!~@~!~@~!~@~!~@XR|37X2>P@^54^B<^04R>%43R~$0;!~\MP!#H,%P!#Gn%P!#GX%PU!~>7Q!#Bt$PfP@P?Q0AP!#Aj,P[!|>%O3Rf,!},'PnQ!#@a$Q0H/0fQ!#>A5f!{v6f!{v2!t>&RPa!{m%O3'0Q!#;x5fP!s$%!sT$[Po!{'%!sT%c!sT7!zI~!zI~!zI~!zIX=7?|X0>P>^45Rf&0:~!z?~!s7$S!#9%&O4/0e!zL6Q!z@4P[!#7x&O4/0j!zI7j!zI6j!zI2j!sr$a!#77&O4Q0m!zK9jP!s$%@P?Po!#6O&O4Q0o!zM9{P{!zM~!zM~!zM~!zM^fPf&09!zH~!zH$10DeRe!zR+7P8P`O4,0g!zKAQ0l!z?7{!z?6{!z?2{!sf%nQ!#JP@Q0p!y{~!y{;R{!y}~!y}~!y}_>&04!y}|P@P=PP!#Gx$O3!#Gx6!sV$!#5Y%jPi!#Pk11R{!wJ~!wJ~!#9pP@^A4^><^74^@4^=<^64R>&03!~]~h!~S&!#L$,O6,0DP!w7~!w7~!w7Q%\<^;!w%$2!w%W7Q06O1!s3&JQ08!s3+NQ0:O1!w8>Q0i!w$g!{}$!w&~!w&d2>P>%~!v{O8PL!ve'Q!#Tk+!#Te'gP!ui~!uik5^G4^F<^E4^45R>Q!#WoPd!ut?!yiA!#6=%!#V\%S!#V^&O4!#V^1!#=a,!#V>&\!#V@&O4!#V@-Q!#V19[!#V3&O4Rq,1sPq!#V3Eq!#>W5q!#>W1q!tD%!#Up7a!#Ur&!tC%z!tC4!#Ur6qP!s$%!s}$!#UW8o!#UY&O4R},1VP}!#UYE}!sL$!#Fg~!#?h~!|D~!|DX?>P@P?%j3/<1#eR>!|9'%`3R|!|2'122F#UR}!s6,9H#URV!sQ&47Rw127KRq'g!#aL+HL!s2'412NFRz'H!s7%12PHRH,HQ!|c0SPN12SFRF#APTC6RQ!#@P,T!#pC$SKRKCf1N5TRTP4P=PF!s+$_Q0>=bc1,N5P!#u3~!#u3~!t8>RX!#C85]P]PNPJP_D>!s0'P7P8P_Fd'!sH,!s8$Dh,0gP[PPQ0;Q0C/]_RF!#4O%_C9'1!#4N%_!#d`%JP7P`CDRs,!#d'-c!#d'-PaP[Q0IQ0F/?mRn!#4o%mC9!#t6%!#eR'!sr$D>/0sP\PSQ0BQ0J%Ra!#md0Q0K'KRs!t1-8EIRh!#5G%Q0O/?`R^!#5M%`C9RI'1PI!#5LEI!#5L5I!#5L1I!{d$4oRIPI!t/$pD>!s0'CD'0PoP\Q0EQ0T%Rt!u-3V'KRl!sT&!#qz%RG!#61$Q0Y/?pRB!#67%pC9RA'1PA!#66EAP!s$%!#fB&SPP!#fB%!s0$!td$tPaQ0SQ0]Q!#t7&Q0^'KR6!sL&!#pn%RE!vd%aQ0b/?vRA!#6n%vC9!#sP7!#6m6!#OY~!#6m~!#6m~!#eHX{,}?Q00g07d8E;%5~RM#y%x~E;%wM%v~E;%uM%z~E;%tM%{~E;%|M%s~E;&00M&01~E;%rM%q!s8$5M%p~E!#f&$!#7\'P!#7Y'P!#7S'P!#7M&5w/kq!#7:&3/C!#7F'5/Cz!s2'7/CH!#7>/!#7-,Q09!}Z$KCiPTP!#4E5Q0<!#4F'=Q0<!#4G/_'!sJ-!s9$D^!#4H+!#4@'8,1F!#4A/d!#4A%FR_!#g?+dQ!$%b-K06!#4B%!#4:'8,1n!#4;+d!#4;'=/0_!#4;%PsPh!#q@0`C8R`,1^P`!#3eEr!#3e5r!#3e1rP@P?%5IRr!#3e'=Pr!s0%CF!#3e'PlPG!#q;/pC8Rp,1BPp!#37ExP!s$%!v{$Q!#38'=Q0Q!s1%!$$e%aQ0SP6PE!#q50vC8Rv,1APv!~kFWPW!~k~!~k~!~k~!#BZZ{e207311o3157?eW<W8o"). Qed.


(* [comment removed for export] *)
Definition summary_miz_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xlo k ne, xhi k ne, xhi k beg, xlo k sp, xhi k sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritable k k qb qk 16
              && ranges_apart_x k qb qk (ELit 16) bb bk ne && kzero_x k k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havoc k qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Definition summary_miz (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_memiszero A)) then None else
  match ret_lit cs with
  | Some ret =>
      let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
      let '(bb, bk) := split_lit beg in
      let spm := eaddz sp (-16) in let '(qb, qk) := split_lit spm in
      match xloB bc ne, xhiB bc ne, xhiB bc beg, xloB bc sp, xhiB bc sp with
      | Some nlo, Some nhi, Some bhi, Some splo, Some sphi =>
          if (Z.leb 0 nlo && Z.leb nhi (2 ^ 40) && Z.leb (bhi + nhi + 8) two64
              && Z.leb 16 splo && Z.ltb sphi two64
              && kwritableB bc k qb qk 16
              && ranges_apart_xB bc qb qk (ELit 16) bb bk ne && kzero_xB bc k bb bk ne)%bool
          then after_call cs ret (Some (ELit 1)) (kn_havocB bc qb qk (ELit 16))
          else None
      | _, _, _, _, _ => None
      end
  | None => None
  end.

Lemma summary_miz_eq : ltac2:(zQ "50!ig3!iu3!ljb!hhn9!hho7>2cs$0@3$2@1$1$0@1$3^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##T^p'0h01bh11kh21nh31oh43offh52b1h62b2h72csh81eh92k1h:2k2h;1lh<2n1h=2n2h>2ubh?2ukh@2uni002bbi013bhii022bki033nhii043nloi052qbi062qki073reti084sphii094sploi0:1xp;1p;2p;5p;7p;4p;3p;6g00EVj1nTg063Nj14Tg01jEj1Vj4KTg00GCR0j1ETg06=Fj1PTg086cj1]Tg04H1j2OTg05KDj1MTg00Qoj1STg07[@j1FTg06S0j20Tg05ZSj1<Tg002^j16Tg032\j1kTg0883j2NTg00Kbj12Tg0153j1ATg045\j2?j1bTg04?cj28j1\Tg000kj2=Tg003Cj1:!s/$aj1UTg030`j2TTg0259j2HTg018Vj2RTg043?j5Gj1dTg017[j25Tg016Rj1ITg0193j7Jj1[Tg04C?j5Dj1aTg00gjj2QTg07\Lj4@Tg0482j2>j1fTg04@lj27j1hTg044Nj5Cj1mTg013bj7Bj1jTg04DLj5Lj1lTg001Hj33Tg004Fj2cTg04:Bj1_Tg00A[j69Tg04B2j1^Tg01:Gj1`Tg07Q6j1ZTg089=j1eTg01i7j1Yj4gTg03V5j1XTg08:Pj1WTg08;`j1iTf0R1#A#Ap=;f2R2f1R3'5/51p=1g00hLR4g01<aR5g004`R6g00j5#nR7^@5]?]>R8%41R9#V%E4R:g005YR;P:%P3p,1A#]R<'O#MR=%S4R4P0P6P:%F3R>g00GeR?P5P6P:g01=j#;R@#;!s$%RA,02#<RBP!sH&f4RC/0@g006YRD#6RE#6#6RF#6RG#kRH'N#<RI!t-%f6RJ#4RK#2RL%AARM,0JRN'?RO!sF&7RP#4RQ#2RR10PMRS'8RT!sB&8RU#4RV#2RW10UARX'8RY!sB&9RZ#4R[#2R\10Z@R]'?R^!sB&:R_#4R`#2Ra10_@Rb'8RcP;!uR$>I/=Cf3RC%:E%U!u0$#6#:'T'=1H2C%:F'Hg01>gRF'=31%:GRG/=31R1F31RFf;R2#4RE#2RdPEPJf5RePGDG'5PdPJPe%IGRfPUPP102MRgFJRhPdPEPUPPPgDDRd31P2PZ%:D#I,Q5RDP_PJPePfO3C@P4n010!s#$20000P4n10110:000210108!s:69!s:61!s:31103!s:6400n20!s9'121105106!s:30102!sb4700!t|01P;P:P=P!yo&P>!yE'P!yO+P!y'&1>KN!s0&7QSRi!s2'VXRj!sH'[]!s<'`b!t$$EPE!vH$GDC,5FRk!s5&!w3$PgFB!sG$!w,%LRl!w,%PD!sL'CKC@R2!w#3Rm!w%7Rn!w'Y0!w'~!w''Ro33X;8P;^26^46^05^17R8%m9!wEMP!}2&P!|v&P!|b&P!|N&P!|:$P_!w7'O4,5F?1hdP2!z`~!v[~!v['=3:oX0!v[$5!v[,7%l!v[y!zK$O491kh!vX~!vX~!vX37P;^=5^:6^65^<5^96^55R7%j!v^w!~;-O6=1kl!vb~!vb~!vb4%E6^85R7%h!vTWJPSO1!s2&PPX!s2+!v\'ZPbO1Pm!v8m!#5'~!v8037P7%f!v2OePN!uv+!#9:%P!#96%PUP]O1P!#7o~!ujj;P:%P1/O<#MR<!um'%F1R7!uf'103A#<R3!s6,C@/NH#<RH!sT&4eRC10eMRo'>!#;|&!#<P'0PARA,7Q!s5'U@R@,>V!sN'[]!w8$`P`!#<L,!s3&!#@W%_MRMFB!sI$UPPPMDL31P_PZPD!sN'CK!#@K~!wU~!wU+R[,c:%29RV#b%_9E9%\V%^9E9%[V%`9E9%aV%Z9E9%dV%e9E9%YV%X9E!zn%!x#+P!w|+P!wv+P!wm'2C/?o!w>&8L!wf'8RA!s0&?W@!s:'\!w\%a!w\+G,5FPa!w\,PMFJ!sE$!wX%D!wX+!sJ&Cg!wX~!#6,~!|//[e%W1%i153:eW7o"). Qed.


(* [comment removed for export] *)
Definition img_cov : ltac2:(zQ "40!h9!va!hg1!ik0>1k@1$2$3>1a$0>1b$0$1") := ltac2:(zQ "b0!hta!hge!h9!io7!ik0!hg8!jv9!jse!va!hg1!nlb\1k@1$9$4\1a$2\1b$2@3$a$4\1K$4M4\1K$4$8^1\2a0$3\1w$5\1v$0$1\2a0$3\1n$0$1\2a0$3\1n$0\2k0$5$1\2lo$2\2hi$2@2$7@2$6^2^5@2$6^4^1\1e$0\1m$2$1\1e$0\2lo$2\2hi$2$1\2a0$3\1n$0$1\2a1$3\2n1$0\2a2$3\2n2$0$1\2a0$3\1n$0\1c$2$1\2a0$3\1n$0$1^3").

Local Open Scope lzb_scope.
Definition img_covB : ltac2:(zQ "30!h9!va!kuc>2bc$2>1a$0>1b$0$1") := ltac2:(zQ "b0!hge!hta!h9!io7!va!ik0!hg8!jv9!mkc!kuc!nlb\2bc$9\1a$2\1b$2@3$a$5\1K$5M5\1K$5$4^1\2a0$3\1w$6\1v$1$0\2a0$3\1n$1$0\2a0$3\1n$1\1k$6$0\2lo$2\2hi$2M4\0$4$4@2$7^2^5@2$7^4^1$0\1e$1\1m$2$0\1e$1\2lo$2\2hi$2$0\2a0$3\1n$1$0\2a1$3\2n1$1\2a2$3\2n2$1$0\2a0$3\1n$1\1c$2$0\2a0$3\1n$1$0@1$8^3").
Local Close Scope lzb_scope.
Lemma img_covB_eqf : ltac2:(zQ "80!h9!va!hg1!ljb!hhp9!hhq3!ik0!lgf>2fk@1$2$6@3$3>1a$0>1b$0$1@1$5@1$7^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##0]p'0h01Ki001Kh11bh22fkh31lh41xh52x0i012a0i022a1i032a2i041ci051ei062hii071ki082k0i092loi0:1mi0;1ni0<2n1i0=2n2i0>1vi0?1wp;1p;2p;3p;6p;5g00EVj1@Tg00Kbj12Tg08=4j17j2?j3=Tg08>Aj16j2;j3<Tg000kj20Tg00:mj31Tg017[j23Tg001Hj34Tg004Fj28Tg01LUj19Tg01Obj1:Tg00A[j6>Tg01;_j55Tg00j5R0#@R1g004`R2g005YR3^12f0R4#2#7%64P2P3f1R5#2/?41;54P1f2R6P0P3P4g02WeR7P7P7P3P3f5,05R8f4R9/04R:P7n010!s#$20000!sN$!s$&n01!sA%:3010110?10>2!s1%;!s9&;10720109106201051!sT%5!s9,110;4010210<10310=!sb,4!sG'X00=104!u&%!tM%138:!t]V8!t]jf3R:510543X31!tf005910:4'3!tl~!vKF6,83%26R0#9%:6E>A=054A<654543eX52D5X42D5W2o"). Qed.
#[local] Hint Rewrite img_covB_eqf : bceq.



(* [comment removed for export] *)
Definition SEALED_W : Z := 0x3e64656c6165733c.

(* [comment removed for export] *)
Definition summary_istrncpy_ref (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_istrncpy A)) then None else
  match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some ret, Some src, Some n =>
      if negb (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool then None else
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      match xhi k dst with
      | Some dhi =>
          match (if off_image_x k db dk (ELit 4095) then Some k
                 else match dst with ELit d => Some (kimg_cut k (d mod two64) 4095) | _ => None end) with
          | None => None
          | Some k0 =>
              if (Z.ltb (dhi + 4095) two64 && Z.leb 0 (x_sealed A) && Z.ltb (x_sealed A + 9) two64
                  && kwritable_x k k db dk (ELit 4095) && img_cov k0 (x_sealed A) (x_sealed A + 9)
                  && ranges_apart_x k db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9))%bool then
                after_call cs ret (Some dst)
                  (KWord (SA db dk) 8 (ELit SEALED_W) :: KZero (SA db (dk + 8)) (ELit 4087) :: kn_havoc k0 db dk (ELit 4095))
              else None
          end
      | None => None
      end
  | _, _, _ => None
  end.
(* [comment removed for export] *)
Definition summary_istrncpy (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in   (* [comment removed for export] *)
  if negb (Z.eqb (pc cs) (x_istrncpy A)) then None else
  match ret_lit cs, reg_lit cs 11, reg_lit cs 12 with
  | Some ret, Some src, Some n =>
      if negb (Z.eqb src (x_sealed A) && Z.eqb n 4095)%bool then None else
      let dst := reg cs 10 in
      let '(db, dk) := split_lit dst in
      match xhiB bc dst with
      | Some dhi =>
          match (if off_image_xB bc db dk (ELit 4095) then Some k
                 else match dst with ELit d => Some (kimg_cut k (d mod two64) 4095) | _ => None end) with
          | None => None
          | Some k0 =>
              if (Z.ltb (dhi + 4095) two64 && Z.leb 0 (x_sealed A) && Z.ltb (x_sealed A + 9) two64
                  && kwritable_xB bc k db dk (ELit 4095) && img_cov k0 (x_sealed A) (x_sealed A + 9)
                  && ranges_apart_xB bc db dk (ELit 4095) (ELit 0) (x_sealed A) (ELit 9))%bool then
                after_call cs ret (Some dst)
                  (KWord (SA db dk) 8 (ELit SEALED_W) :: KZero (SA db (dk + 8)) (ELit 4087) :: kn_havocM k0 db dk (ELit 4095))
              else None
          end
      | None => None
      end
  | _, _, _ => None
  end.

Lemma summary_istrncpy_eq : ltac2:(zQ "50!ig3!iu3!ljb!hhqe!hhs2>2cs$0@3$2@1$1$0@1$3^1@1$4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##Rap'0h01bi001bh11kh22b1h32b2h42csh51ei011eh62k1h72k2h81lh91ni021nh:2n1h;2n2h<1oh=3offh>2ubh?2ukh@2uni031ai041di052dbi063dhii072dki083dsti091ii0:2k0i0;2loi0<2n0i0=2opi0>3reti0?3srci0@2sxi0A1xp;1p;2p;4p;3p;7p;5p;6g00EVj1nTg063Nj18Tg04>Sj1Zj5ITg00GCR0j1CTg06=Fj1STg08?Mj1dTg04H1j2@Tg05KDj1ETg00Qoj1LTg07[@j1JTg0153j1BTg06PXj2>Tg08@\j1mTg003aj16!s/$Cj1ATg017[j20Tg06S0j25Tg05ZSj1OTg00Kbj1:Tg04?cj2Nj1bTg016Rj19!tX$Nj4Mj1^Tg00gjj24Tg03=`j2YTg07][j3KTg0259j2DTg018Vj2HTg000kj2XTg002^j1?Tg08>Aj3WTg0193j7Gj1`Tg02b4j2FTg02`ij3VTg02e@j2UTg03XXR1j4TTg07\Lj4=Tg04@lj2Rj1hTg04I_j4Qj1kTg013bj7Pj1jTg01jER2j4lTg001Hj31Tg004Fj2cTg00A[j67Tg04B2j1_Tg01:Gj1aTg07^hj1eTg04=Bj1fj5\Tg07`=j1]Tg08Aij1gTg08C>j1[Tg01Y_j3iTf0R3#B#Bp=;%63#6p=3f2R4f1R5'0/03p=<g00j5R6?i53p=2g00hLR7%n6R6g01<aR8g004`R9g005YR:^98]=]0R;]1R<%83R=#Z%C7R>P:P>%S5p,1AR?#dR@'@#ERA%L7R7P0P9P>%J5RB!s1%g01=j#;!s$%RC#;RD#BRE,>4RF!sH%f3RG%BERH'>RI!t&$m?R?,@5g006YRJ#6#3#3#3RK!s-$ARL,@3'0#ERMP7g00GeRNP8!sp$4/5D#ORO!t#&6RP#8RQ#:RR15PDRS'NRTP0P6P>P:%C6RUf7RV#8RW#:RXP4P5%9LRYCM146WRZP8PU15VDR[f8R\#8R]g01>gR^,Y3R_;KL,46%L6R`P!s$-n011080008101041010<3010=103100!s1D4010@10;10<101!s4&:10910<Ran010!s#$20000P:P>1D5L/H^g01>IRb/X?%?J#?!vT$ARc,D?Rd/H^3<R^PVP]PGP4PYO4'0AW3?dRd%:!s:&%9bRbP?%9cRcFGRe3<P\PP15\D,48Rf1FG4g08DW#97VCRC%?J#A,D4,FG%?K!wi$A#9'URKP3!sw%CT'2'2RJC=RgP7!u/27n10110A00021110:!s:6600n20!s9'12110510!sp11!s\42!sp6?!s:6>00!sp2:P>PAP!{$&P!z}&P!zc&P!zX$PMP7P!z'&P!y|&1RQSRh!yl'PUPWP4P5PYCQPZP!ww2Ri!sl$]!wO'DI=<^dRj!s6'PbP?PcFP'0R]P\PPPf!vl+l,2K,2CRkC=!vl~!vllRl31X0<P;%k=!vx[PT!vt-P!vt%O3!vt5!{m$0jeP!y~~!v8m=1>lX0;P:^;8^79^38^:8^69^28R;%j!vLe!yz%V!yh/O6,0j!v=~!v=u%C9^58R;%h!v/\f5RjPSO1!v50]!u|~!u|s<;P6^@8^?9^>8^16R;P2!y4\h!u}2!#3d$V!#3f&O4!#3f$!#3d~!v=r8;!#?o$3/@@#ER@!v3'%J3R;!s1%1>5ERE!s2'4HRH!v>315GD#ORl!sa&8jRC15jDRj'R!#4',Q!#7y&146QRQP8PUPSAKW_L,46P!#>>~!#>>0`!#5O4PWPW!#9C&,0^!s3'!#9@&7<dPVPP148[R[P!#93~!xMnRk,c>P1g07d8E7%:=R1#b%_=E7%`1%a=E7%^1%e=E7%f1%]=E7!v$$!xp+P!xm&P!xi&P!xe4P!x_':C/Nj!xX-R!xX&MPQP!w47X!w4+\,0^PX!w40G!w4&P[PJ!w0~!|Wqke%g3%[351>eW4o"). Qed.


(* [comment removed for export] *)
Definition popfree_facts : ltac2:(zQ "50!h9!hg1!hg8!hta!ik0>2lb$3>2lk$0>3cnt$0>1c$0>1s$0>1K$2@1$1$4") := ltac2:(zQ "e0!h9!hg8!jv3!qp5!kg9!loa!op5!hhta!iie!rv2!rvb!hta!ik0!qof\2lb$b\2lk$0\3cnt$0\1c$0\1s$0\1K$1@4$6$1$c\1t$1@3$9@2$a^7@2$2^6@2$3+4@2$5@2$5^5+1@1$4^1N4@1$8@2$d@2$2^4@2$3@1$4^1^3+h0@2$7N0^1").
Definition summary_popfree (cs : acs) (args : list expr) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (x_popfree A)) then None else
  match args, reg_lit cs 10, reg_lit cs 12, reg_lit cs 21, reg_lit cs 19 with
  | [ELit K], Some i, Some c, Some s, Some n =>
      let e := reg cs 11 in
      let cnt := n - i in
      let lo := eaddz e (- (4 * n)) in
      let '(lb, lk) := split_lit lo in
      match xlo k e, xhi k e with
      | Some el, Some eh =>
          if (Z.leb 0 i && Z.ltb i n && Z.leb (4 * n) el && Z.ltb eh two64 && Z.leb 0 c && Z.leb 0 s
              && Z.ltb (c + cnt * s) two64 && Z.leb 0 K && Z.leb K cnt && Z.ltb (pc cs + 32) two64
              && fresh_ok cs && kwritable_x k k lb lk (ELit (4 * cnt)) && off_image_x k lb lk (ELit (4 * cnt)))%bool then
            let k1 := kn_havoc k lb lk (ELit (4 * cnt)) in
            let kunk := if Z.ltb K cnt then [KUnk (SA lb lk) (ELit (4 * (cnt - K)))] else [] in
            let sr := s_regs (a_ss cs) in
            let sr' := sr_upd (sr_upd (sr_upd (sr_upd sr 10 (ELit n)) 12 (ELit (c + cnt * s)))
                                      14 (ELit ((c + (cnt - 1) * s) / 16))) 15 lo in
            Some (with_ss cs (mk_ss (pc cs + 32) sr' (popfree_facts lb lk cnt c s (Z.to_nat K) ++ kunk ++ k1) (nxt cs)))
          else None
      | _, _ => None
      end
  | _, _, _, _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
Definition V_S1 : nat := 0.     (* [comment removed for export] *)
Definition V_ARGC : nat := 1.
Definition V_ENVC : nat := 2.
Definition V_L0 : nat := 3.     (* [comment removed for export] *)
Definition V_W : nat := 4.      (* [comment removed for export] *)
Definition V_BRK : nat := 5.    (* [comment removed for export] *)
Definition V_S2 : nat := 6.     (* [comment removed for export] *)
Definition V_L1 : nat := 7.     (* [comment removed for export] *)
Definition V_UID : nat := 8.    (* [comment removed for export] *)
Definition V_HW : nat := 9.     (* [comment removed for export] *)
Definition V_S3 : nat := 10.    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_pg : ltac2:(zQ "10!hta$0") := ltac2:(zQ "50!sk0!sh9!hhu1!hhu8!sj9@2$4@2$0+ogg0@1$1$2@2$0+hgg0@1$1$3").
Definition e_sp0 : ltac2:(zQ "10!hta$0") := ltac2:(zQ "50!hhuf!hhv6!sj9!sk0!sh9@2$2$1@2$3+h0@1$4$0").
(* [comment removed for export] *)
Definition e_sp8 : ltac2:(zQ "10!hta$0") := ltac2:(zQ "60!sk0!sh9!sj9!hhu1!hhu8!hhuf@2$2@2$0+hgg0@1$1$3@2$2@2$0+ig0@1$1$4@2$0+2@1$1$5").
(* [comment removed for export] *)
Definition e_envp : ltac2:(zQ "10!hta$0") := ltac2:(zQ "60!sj9!hhvd!hig6!sk0!iie!sh9@2$0$2@2$0@2$3+8@1$5$1@1$4+h0").
Definition e_auxv : ltac2:(zQ "10!hta$0") := ltac2:(zQ "60!sj9!hige!hih7!sk0!iie!sh9@2$0$2@2$0@2$3+8@1$5$1@1$4+8").
Definition e_str0 : ltac2:(zQ "10!hta$0") := ltac2:(zQ "20!hii0!tp7@2$1$0+q0").
Definition e_str1 : ltac2:(zQ "10!hta$0") := ltac2:(zQ "50!hii9!hij0!sj9!tp7!sh9@2$2$1@2$3@1$4$0+1").
Definition e_atrandom : ltac2:(zQ "10!hta$0") := ltac2:(zQ "50!hij9!hij0!sj9!sk0!sh9@2$2$1@2$3+8@1$4$0").
(* [comment removed for export] *)
Definition e_atr8 : ltac2:(zQ "10!hta$0") := ltac2:(zQ "60!sj9!sh9!hhvd!hige!hij9!hijf@2$0$5@2$0@1$1$2@2$0@1$1$3@1$1$4").

(* [comment removed for export] *)
Definition e_argv1w : ltac2:(zQ "10!hta$0") := ltac2:(zQ "80!hik7!jm9!hhvd!hil3!hilc!iie!him4!sh9@3$6$1@3$4$0@1$5+1@1$7$2$3").

(* [comment removed for export] *)
Definition node_envscan : ltac2:(zQ "20!ig3!iu3>2cs$0@1$1$0") := ltac2:(zQ "h70!ig3!va!sj9!jk4!sl8!iie!in3!ji2!jse!hg1!iu3!hige!hih7!sk0!irc!pua!qq1!hgg1!himb!hin7!sh9!ik0!ln2\2cs$0=1k@1$9$h5@1$e^1M1\0$1@1$a$0@2$8@2$h6@1$h0^2@1$h2?1A@3$f^1@2$3^2N9$c@2$7$0@2$h1@3$4@3$4^2N9@2$2@2$3^2N9@2$2@2$d+8@1$h4$b@1$5+8Na@1$5Z@1$h3?1A@1$6$0").

(* [comment removed for export] *)
Definition node_smear : ltac2:(zQ "20!ig3!iu3>2cs$0@1$1$0") := ltac2:(zQ "h90!ig3!iu3!sl8!iie!in3!va!h9!rs6!jk4!hio5!ji2!jse!hg1!hla!irc!qq1!hgg1!ik0!ooe!oq9!jv3!ln2!jv9!lp7!loa\2cs$0=1k@1$c$h1@1$e^1M5\0$5@1$1$0@1$d@2$h5@1$f^2@1$9?1A@1$4$0M1\1x@1$1$6@1$1$0@2$h3^1@2$8^2Na\2lo$6M1\1x@1$1$6@1$1$0@2$h2^2@2$8^3Na\2hi$6M5\0$5@1$1$0@2$b@2$h6@2$7+2+ie^2@2$h7^1@2$7+2+if@2$a$0@2$h0@3$2@3$2@3$2@3$2@3$2@3$2^4Na@1$3@2$h8@2$7+2+if+1Nb@1$3+lllllllllllllll5Nc@1$3+jjjjjjjjjjjjjjj3Nd@1$3+vgvgvgvgvgvgvgfNe@1$3+hghghghghghghg1Nf@1$3+nvvf@2$h4@1$9?1A+n0@1$4$0@1$4$0@1$4$0").

(* [comment removed for export] *)
Definition node_pnscan : ltac2:(zQ "20!ig3!iu3>2cs$0@1$1$0") := ltac2:(zQ "i70!ig3!jna!in3!iu3!h9!jse!iie!va!hg1!uk9!ik0!iqc!jv9!uqb!ji2!hg8!ii7!hij0!tp7!kn2!hiof!irc!nha!pi5!pua!ipa!sh3!qq1!jk4!iq2!os4!osd!hipa!hiq5!sh9!ij6!im6!jv3!ln2\2cs$0=1k@1$8$a@1$h5^1M3\1x@1$3$4@1$3$0@2$9^2Na\1p$4M3\1x@1$3$4@1$3$0@2$9^3Nc\1z$4M4\1z$4@1$3$0^1@1$2$0\2p0$1M1\2p0$1@1$3$0^1\2p1$1M1\2p1$1@1$3$0^1\2p2$1M1\2p2$1@1$3$0^1\2p3$1M1\2p3$1@1$3$0^1\2p4$1M1\2p4$1@1$3$0^1\2p5$1@1$2$0\2p5$1M1\2p5$1@1$3$0^1\2p6$1@1$2$0\2p6$1@1$2$0M7\0$7@1$3$0@2$5@2$5@2$5@2$5@2$5@2$i6@1$hb^a@1$i0?1A@3$h8^9@2$hc^aNb@2$h2$h1+1@5$h7^9^9@1$6Z^8+8@2$c@1$hf?1A^8@2$c@2$i5^8+8@1$he?1A@1$h3^a=1v$f@1$ha^a=2k'@1$8$a@4$h6@3$h4^a^9+8@1$6Z^9@1$6+8=2ss$i4@1$h0^c@2$e$0@2$hd^d@4$h9@1$i1?1A@3$b@3$b@1$i3^1Nb@1$i2^3Nd@1$6Z^2@1$d^3@1$2$0@1$2$0\2p4$1@1$2$0@1$2$0\2p3$1@1$2$0@1$2$0\2p2$1@1$2$0@1$2$0\2p1$1@1$2$0@1$2$0\2p0$1@1$2$0@1$2$0@1$2$0").

(* [comment removed for export] *)
Definition kw_argv1 : ltac2:(zQ "20!hta!ik0>1v$0$1") := ltac2:(zQ "40!hig6!rv2!rvb!hta\1v$3@3$1@2$2$0+h0N8^1").

Definition node_layout : ltac2:(zQ "40!ig3!hg1!iu3!hta>2cs$0>4args@1$1$3@1$2$0") := ltac2:(zQ "hd0!ig3!hta!in3!iu3!hg1!va!h9!ik0!jna!hg8!hir2!ji2!mo8!hla!jh0!jh9!hhvd!hird!his8!is1!sh9!jv9!hil3!irc!iie!ooe!oq9!nlb!mk2\2cs$0\4args@1$4$1=1k@1$4$7@1$h7^2M5\0$5@1$3$0@1$d@3$hb$7@1$h2@1$a$h1^1@1$2$0=2k'@1$4$7@3$hc$7\1K$7@1$d@2$h2@1$a$h1^1^1M4\4args@1$4$1@1$3$0^3@1$2$0\1e$1\1l@1$4$1M1\1e$1@1$3$0^2\1z$6M6\1z$6@1$3$0^1M4\1l@1$4$1@1$3$0^2M3\1x@1$3$6@1$3$0@2$h9^5@1$h4$h0\2hi$6M5\0$5@1$3$0@2$h5^1+1@2$b$0@2$h3^8@3$c$7@1$a@1$h8Z^5@1$2$0@1$2$0\2e0$1\2l0@1$4$1@1$2$0\1p$8M8\1p$8@1$3$0^1\2p0$8@1$2$0\2p0$8@1$2$0M4\1l@1$4$1@1$3$0^3M3\1x@1$3$6@1$3$0@2$ha^6@1$h4$h0\2lo$6M5\0$5@1$3$0@2$h5+2^1@2$b$0@2$h3^9@3$c$7@1$a$h6^6@1$2$0@1$2$0\2e0$1\2l0@1$4$1@1$2$0\1p$8@1$2$0\1n$9@1$2$0\2op$e\1a$1\1b$1@1$2$0\2op$e\1a$1\1b$1@1$2$0\2op$f\1a$1\1b$1@1$2$0\2op$f\1a$1\1b$1@1$2$0\2sx$5\2lo$9\1n$9\2e0$1@1$2$0\2sx$5\2k0$9\1i$6\1n$9@1$2$0").


Definition vmop_eqb : ltac2:(zQ "20!hp2!va>1a$0>1b$0$1") := ltac2:(zQ "94!hta!va!hge!hp2!ju7!jse!hk4!hiu7!hiuf&\9prot_none$1\2a0$0\1n$0$2&\darm_noreserve$1~0&\2n2$0@2$5@2$4^4^2@2$4^3^1&\2a2$0~2\1a$3\1b$3M3\1a$3$1^2\2k1$6\2a1$0\2n1$0M3\1b$3$1^4\2k2$6\2a2$0\2n2$0@2$5@2$5@2$8^6^3@2$4^5^2@2$4^4^1~1\2a0$0\1n$0$2\2a0$0\1n$0$2\2x1$1\2y1$1\2a1$0\2n1$0M3\1b$3$1^5\1k$6\2a0$0\1n$0$2\2x2$1\2y2$1\2a2$0\2n2$0@2$5@2$5@2$5@2$7^8^4@2$7^7^3@2$4^6^2@2$4^5^1\2a0$0\1n$0$2\2a0$0\1n$0$2\2a1$0\2n1$0M3\1b$3$1^3\1k$6\2a0$0\1n$0$2~1~3\2a0$0\1n$0$2\2a1$0\2n1$0M3\1b$3$1^3\1k$6\2a0$0\1n$0$2~1\2a0$0\1n$0$2~3").

(* [comment removed for export] *)

Local Open Scope lzb_scope.
Definition entails (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && list_eqb expr_eqb (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && forallb (fun K => existsbL (kentry_eqb K) (kn cs)) (kn ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && list_eqb vmop_eqb (a_vmops cs) (a_vmops ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%lzb.
Local Close Scope lzb_scope.

(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint esubst (J : nat) (e : expr) (x : expr) : expr :=
  match x with
  | ELit _ => x
  | EVar n => if Nat.eqb n J then e else x
  | EAlu op a b => mkAlu op (esubst J e a) (esubst J e b)
  | EAluw op a b => mkAluw op (esubst J e a) (esubst J e b)
  | EMd op a b => mkMd op (esubst J e a) (esubst J e b)
  | EMdw op a b => mkMdw op (esubst J e a) (esubst J e b)
  | EExt sx lo n a => EExt sx lo n (esubst J e a)
  | EBlob _ _ _ _ => x
  end.
(* [comment removed for export] *)
Definition asubst : ltac2:(zQ "30!io7!hg8!hta>1J$1>1e$2>1a$0$0") := ltac2:(zQ "70!hg8!hivb!rvb!jvf!hjg4!hta!io7\1J$0\1e$5\1a$6@2$2@3$1^3^2@1$3^1@1$4^1").
Definition ksubst : ltac2:(zQ "30!ik0!hg8!hta>1J$1>1e$2>1K$0$0") := ltac2:(zQ "h00!hta!hivb!hjgd!io7!h9!ik0!hg8!hjh6!hhk5!vm5!hji0!si1!hji9!rv2!ohc!hjj1\1J$6\1e$0\1K$5M5\1K$5$5^1\1a$3\1w$6\1v$0@3$d@3$2^6^5^3^2@3$1^6^5^1\1a$3\1n$0@2$f@3$2^5^4^2@3$1^5^4^1\1a$3\1n$0\1k$6@3$8@3$2^6^5^3@3$1^6^5^2^1\2lo$4\2hi$4^3\1x$0\1m$4@2$7@3$1^5^4^2^1\1x$0\2lo$4\2hi$4@3$b@3$1^6^5^3^2^1\1a$3\1n$0@2$e@3$2^5^4^2@3$1^5^4^1\2a1$3\2n1$0\2a2$3\2n2$0@4$9@3$2^7^6^4@3$1^7^6^3@3$2^7^6^2@3$1^7^6^1\1a$3\1n$0\1c$4@3$a@3$2^6^5^3@3$1^6^5^2^1\1a$3\1n$0@2$c@3$2^5^4^2@3$1^5^4^1").
Definition psubst : ltac2:(zQ "30!hta!kj1!hg8>1J$2>1e$0>1p@2$1$0$0@2$1$0$0") := ltac2:(zQ "70!hta!hivb!kj8!hg8!kka!kj1!kje\1J$3\1e$0\1p@2$5$0$0@4$4$0$0@3$1^3^2@3$2$0$0^1@3$1^3^2@3$6$0$0^1").
Definition msubst (J : nat) (e : expr) (m : amap) : amap := AM (esubst J e (am_base m)) (esubst J e (am_len m)) (am_kind m).
Definition fsubst : ltac2:(zQ "30!kk4!hg8!hta>1J$1>1e$2>1f$0$0") := ltac2:(zQ "50!kk4!hta!hg8!hivb!hjja\1J$2\1e$1\1f$0M0\1f$0$0^1^1\1k$2\1l$1\1o$1@3$4^3@3$3^6^5^2@3$3^6^5^1^1").
(* [comment removed for export] *)
Definition inst (inv : acs) (J : nat) (e : expr) : acs :=
  ACS (mk_ss (pc inv) (map (esubst J e) (s_regs (a_ss inv))) (map (ksubst J e) (kn inv)) (nxt inv))
      (map (msubst J e) (a_maps inv)) (a_totsz inv) (a_ylo inv) (a_eager inv)
      (map (psubst J e) (a_vis inv)) (map (psubst J e) (a_ghost inv)) (a_abytes inv)
      (esubst J e (a_brk inv)) (fsubst J e (a_fd inv)) (a_tidset inv) (map (vmop_map (esubst J e)) (a_vmops inv)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint nt_set (t : list (option nat)) (i : nat) (d : nat) {struct i} : list (option nat) :=
  match i, t with
  | O, [] => [Some d]
  | O, _ :: rest => Some d :: rest
  | S j, [] => None :: nt_set [] j d
  | S j, x :: rest => x :: nt_set rest j d
  end.
Definition nt_get : ltac2:(zQ "30!hg8!iu3!hg1>1t@1$2@1$1$0>1i$0@1$1$0") := ltac2:(zQ "50!hg8!iu3!in3!hg1!ii0\1t@1$3@1$1$0\1i$0@4$4@1$1$0^1^2@1$2$0").
Lemma nt_get_set : ltac2:(zQ "90!hg8!iu3!va!hjk3!ji2!hg1!ljb!hjkc!hjd>1t@1$5@1$1$0>1i$0>1d$0>1j$0@3$6@1$1$0@2$3@3$7^4^3^2^1M2\0$2@1$1$0@2$8^1^3@2$4$0^2@2$3^4^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##:Ap'0h01jh11th21dh31ih44resth51xh62IHh71bi001bh81oi011oi021li031mi041np;1p;3p;2p;4p;6p;5g00GCj1BTg00EVR0j1ATg08Edj32Tg00Qoj1<Tg08Foj20Tg08GOj44Tg00PFj1=Tg004Fj25Tg001Hj33Tg0153j17Tg01Y_j3:Tg00A[j6@Tg05?Qj5>!sn$kj2;Tg00gjj2?Tg00iVR1f0R2'?p=8f5R3f4R4f3R5f2R6f1R7C4;32p=1g01=jR8=272p=6P6P8P7P2C4p=9%B1R9#AR:P9P9P2A2657%<1R;g005YR<P91025%87R=P9P2P6P;C4R>n010!s#$20000E1^01^21^1:R?X31P0!st$9P71626P;P!sm$78%86R@P9P7P2!sm$A!sm3P6P1!tW%%=9RB/6!sc+28RCP@!tQ$B!sb$D!sb42159=16B7=99!s\&88REP=A99B;RF!sW1539eP1!t=$2P;P;n01104!sD%10103=39;!sz$;RGPGX01P2O1RH!sN34P9P9%72RI16B5!t}'I8RJ%85RKP9PI!u$&L!u$3e!s{&!sy5!u{&A:967RMf6RN'!v$&PC%8NRC!u+$M!s}$O!v#44%83RP,59A:972RQ/63!v1'PEPPA99Q;RE!v,5159>!tG$IA:956R>f7RR!tG+J%8RRJ!uF$>!tG$S!uFLX4:X5!xe$O2n1011!sX$20020!s4%X01X21X1:!yP,%73R0=2!yU-0P@P!yH>A2B0!yE,0P@P!y96PG%74R@=2!y<0@P=P!y579!ss&NRFPK!su3!td&R%84R@!yV$!sC-9392X89PFP<!s$$9P2PPP9P6!xz%!sp5!sF$;!tR4P2P1A39PPP7159@159C!yK=A39D;P7PGP!zd5!s7$!t$+b7!vP&N5P;C4P3PBP5P2O3E@!xo%%7NRH=2!{7-HPKP!{$Uf9RL#7RK=2MN!wb+KPCP!zt61597f8#7R4=2Q3!we-4PPP!zm6PLP6PRP2O3!u&%f:#7RL=2>R!u'+LPJP!zee1!ze4X6?X31P2P7D>X31W1A2567/;2!uX&6P=1;52!u&4!#5}%31^1:eo"). Qed.
(* [comment removed for export] *)
Fixpoint mk_fwd (m : list (nat * nat)) : option (list (option nat)) :=
  match m with
  | [] => Some []
  | (s, d) :: rest =>
      match mk_fwd rest with
      | Some t => match nt_get t s with None => Some (nt_set t s d) | Some _ => None end
      | None => None
      end
  end.
(* [comment removed for export] *)
Fixpoint mk_bwd (m : list (nat * nat)) : option (list (option nat)) :=
  match m with
  | [] => Some []
  | (s, d) :: rest =>
      match mk_bwd rest with
      | Some t => match nt_get t d with None => Some (nt_set t d s) | Some _ => None end
      | None => None
      end
  end.

Fixpoint erename (t : list (option nat)) (e : expr) : expr :=
  match e with
  | ELit _ => e
  | EVar v => match nt_get t v with Some d => EVar d | None => e end
  | EAlu op a b => EAlu op (erename t a) (erename t b)
  | EAluw op a b => EAluw op (erename t a) (erename t b)
  | EMd op a b => EMd op (erename t a) (erename t b)
  | EMdw op a b => EMdw op (erename t a) (erename t b)
  | EExt sx lo n a => EExt sx lo n (erename t a)
  | EBlob _ _ _ _ => e
  end.
Definition arename : ltac2:(zQ "40!io7!hg1!hg8!iu3>1t@1$1@1$3$2>1a$0$0") := ltac2:(zQ "80!hg1!hg8!iu3!hjl5!rvb!jvf!hjg4!io7\1t@1$0@1$2$1\1a$7@2$4@2$3^2@1$5^1@1$6^1").
Definition krename : ltac2:(zQ "40!ik0!hg1!hg8!iu3>1t@1$1@1$3$2>1K$0$0") := ltac2:(zQ "h20!hjl5!hta!hjlf!io7!h9!ik0!hg8!hg1!iu3!hjh6!hhk5!vm5!hji0!si1!hji9!rv2!ohc!hjj1\1t@1$7@1$8$6\1K$5M5\1K$5$5^1\1a$3\1w$6\1v$1@3$f@2$2^5^3^2@2$0^5^1\1a$3\1n$1@2$h1@2$2^4^2@2$0^4^1\1a$3\1n$1\1k$6@3$a@2$2^5^3@2$0^5^2^1\2lo$4\2hi$4^3\1x$1\1m$4@2$9@2$0^4^2^1\1x$1\2lo$4\2hi$4@3$d@2$0^5^3^2^1\1a$3\1n$1@2$h0@2$2^4^2@2$0^4^1\2a1$3\2n1$1\2a2$3\2n2$1@4$b@2$2^6^4@2$0^6^3@2$2^6^2@2$0^6^1\1a$3\1n$1\1c$4@3$c@2$2^5^3@2$0^5^2^1\1a$3\1n$1@2$e@2$2^4^2@2$0^4^1").
Definition prename : ltac2:(zQ "50!hta!kj1!hg1!hg8!iu3>1t@1$2@1$4$3>1p@2$1$0$0@2$1$0$0") := ltac2:(zQ "90!hta!hjl5!kj8!hg1!hg8!iu3!kka!kj1!kje\1t@1$3@1$5$4\1p@2$7$0$0@4$6$0$0@2$1^2@3$2$0$0^1@2$1^2@3$8$0$0^1").
Definition mrename (t : list (option nat)) (m : amap) : amap := AM (erename t (am_base m)) (erename t (am_len m)) (am_kind m).
Definition frename : ltac2:(zQ "40!kk4!hg1!hg8!iu3>1t@1$1@1$3$2>1f$0$0") := ltac2:(zQ "70!kk4!hg8!hjl5!hta!hg1!iu3!hjja\1t@1$4@1$5$1\1f$0M0\1f$0$0^1^1\1k$1\1l$3\1o$3@3$6^3@2$2^5^2@2$2^5^1^1").

(* [comment removed for export] *)
Fixpoint evars_all (ok : nat -> bool) (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar v => ok v
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_all ok a && evars_all ok b
  | EExt _ _ _ a => evars_all ok a
  | EBlob _ _ _ _ => true
  end.
Definition kvars_all : ltac2:(zQ "30!va!hg8!ik0>2ok>0$1$0>1K$2$0") := ltac2:(zQ "a4!hjm9!hta!jse!jvf!io7!h9!hg8!ik0!va!hkc&@2$2@2$0^4@1$3^2@2$0^4^1&\1n$1~0&\1a$4~1&@2$2@2$0^5@1$3^3@2$0^5^2\2ok>0$6$8\1K$7M7\1K$7$8^1\1a$4\1w$6\1v$1@2$2@2$0^5@1$3^3@2$0^5^1~2\1a$4\1n$1\1k$6~3\2lo$5\2hi$5$9\1x$1\1m$5@2$0^4^2\1x$1\2lo$5\2hi$5@2$0^5^3~2\2a1$4\2n1$1\2a2$4\2n2$1@2$2@2$2@2$2@2$0^6@1$3^4@2$0^6^3@2$0^6@1$3^2@2$0^6^1\1a$4\1n$1\1c$5~3~2").
Definition csvars_all (ok : nat -> bool) (cs : acs) : bool :=
  (forallb (evars_all ok) (s_regs (a_ss cs)) && forallb (kvars_all ok) (kn cs)
   && forallb (fun m => evars_all ok (am_base m) && evars_all ok (am_len m)) (a_maps cs)
   && forallb (fun p => evars_all ok (fst p) && evars_all ok (snd p)) (a_vis cs)
   && forallb (fun p => evars_all ok (fst p) && evars_all ok (snd p)) (a_ghost cs)
   && evars_all ok (a_brk cs)
   && match a_fd cs with FdFile _ l o => evars_all ok l && evars_all ok o | _ => true end
   && forallb (vmop_all (evars_all ok)) (a_vmops cs))%bool.

(* [comment removed for export] *)
Fixpoint emaxv (e : expr) (acc : nat) : nat :=
  match e with
  | ELit _ => acc
  | EVar v => Nat.max acc (S v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => emaxv a (emaxv b acc)
  | EExt _ _ _ a => emaxv a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kmaxv : ltac2:(zQ "20!hg8!ik0>1K$1>3acc$0$0") := ltac2:(zQ "71!hjn5!hta!jvf!io7!h9!hg8!ik0&\1a$3\1n$1@2$0@1$2^2@2$0^1^3\1K$6\3acc$5M6\1K$6$5^2\1a$3\1w$5\1v$1@2$0@1$2^3@2$0^1^4~0\1a$3\1n$1\1k$5@2$0@1$2^3@2$0^2^4\2lo$4\2hi$4^3\1x$1\1m$4@2$0^2^3\1x$1\2lo$4\2hi$4@2$0^3^4~0\2a1$3\2n1$1\2a2$3\2n2$1@2$0@1$2^4@2$0^3@2$0@1$2^2@2$0^1^5\1a$3\1n$1\1c$4@2$0@1$2^3@2$0^2^4~0").
Definition csmaxv (cs : acs) : nat :=
  let acc := fold_right emaxv 0%nat (s_regs (a_ss cs)) in
  let acc := fold_right kmaxv acc (kn cs) in
  let acc := fold_right (fun m acc => emaxv (am_base m) (emaxv (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => emaxv (fst p) (emaxv (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => emaxv (fst p) (emaxv (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => emaxv l (emaxv o acc) | _ => acc end in
  let acc := fold_right (fun op acc => emaxv (fst (vmop_an op)) (emaxv (snd (vmop_an op)) acc)) acc (a_vmops cs) in
  emaxv (a_brk cs) acc.

Definition rename_cs (t : list (option nat)) (cs : acs) (nx : nat) : acs :=
  ACS (mk_ss (pc cs) (map (erename t) (s_regs (a_ss cs))) (map (krename t) (kn cs)) nx)
      (map (mrename t) (a_maps cs)) (a_totsz cs) (a_ylo cs) (a_eager cs)
      (map (prename t) (a_vis cs)) (map (prename t) (a_ghost cs)) (a_abytes cs)
      (erename t (a_brk cs)) (frename t (a_fd cs)) (a_tidset cs) (map (vmop_map (erename t)) (a_vmops cs)).

(* [comment removed for export] *)
Definition node_rename : ltac2:(zQ "50!hg8!ig3!hg1!iu3!kj1>2gb$0>2cs$1>1m@1$2@2$4$0$0@1$3$1") := ltac2:(zQ "he0!hg8!iu3!ig3!va!hg1!in3!kj1!hkc!ip0!jse!hge!ii7!hjk3!lp0!ji2!kj8!kje!hjnd!hjo6!irc!hjp3!hjpc!ipa!qq1!hjq5!iq2!ko6!ij6!hjr1!hnd\2gb$0\2cs$2\1m@1$4@2$6$0$0M3\0$3@1$1$2@3$hd@2$6$0$0\1p@2$6$0$0@2$9@2$d^4@3$f$0$0^1@2$d^4@3$h0$0$0^1^1M1\1x@1$1@1$4@1$1$0@1$1$2@1$h5^1\2fw@1$4@1$1$0M1\1x@1$1@1$4@1$1$0@1$1$2@1$h4^2\2bw@1$4@1$1$0=2ok>1v$0$3\1v$0M1\1x@1$1$0$3@2$c^3^1\1n$0$7M1\1x@1$1$0$3@2$c^2^1\1n$0$a$7M3\0$3@1$1$2@2$9@2$h2^1^5M4\1x@1$4$8$3@1$ha@1$b^5$7\1s$8\1l@1$4$8$a=3cs1$2@3$h8^3^5N0@2$e$2@2$h9^1@4$h6@1$h7^1@1$hb@1$b^1@1$h3^1@2$hc^7@1$h1^1@1$5$2@1$5$2@1$5$2@1$5$2").

(* [comment removed for export] *)
Fixpoint bt_set (t : list bool) (i : nat) {struct i} : list bool :=
  match i, t with
  | O, [] => [true]
  | O, _ :: rest => true :: rest
  | S j, [] => false :: bt_set [] j
  | S j, x :: rest => x :: bt_set rest j
  end.
Definition bt_get : ltac2:(zQ "30!va!hg1!hg8>1t@1$1$0>1i$2$0") := ltac2:(zQ "50!va!hge!hg1!hg8!ii0\1t@1$2$0\1i$3@4$4$0^1^2$1").
(* [comment removed for export] *)
Fixpoint evars_fo (gb : nat) (e : expr) (acc : list nat * list bool) : list nat * list bool :=
  match e with
  | ELit _ => acc
  | EVar v => if Nat.ltb v gb then acc else if bt_get (snd acc) v then acc else (v :: fst acc, bt_set (snd acc) v)
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => evars_fo gb b (evars_fo gb a acc)
  | EExt _ _ _ a => evars_fo gb a acc
  | EBlob _ _ _ _ => acc
  end.
Definition kvars_fo : ltac2:(zQ "50!hg1!hg8!va!kj1!ik0>2gb$1>1K$4>3acc@2$3@1$0$1@1$0$2@2$3@1$0$1@1$0$2") := ltac2:(zQ "a2!hjr8!hta!jvf!io7!h9!hg8!hg1!ik0!va!kj1&\1n$1@3$0^5^1@3$0^5@1$2^2^3&\1a$3~0\2gb$5\1K$7\3acc@2$9@1$6$5@1$6$8M7\1K$7@2$9@1$6$5@1$6$8^2\1a$3\1w$5\1v$1@3$0^6^1@3$0^6@1$2^3^4~1\1a$3\1n$1\1k$5@3$0^6^2@3$0^6@1$2^3^4\2lo$4\2hi$4^3\1x$1\1m$4@3$0^5^2^3\1x$1\2lo$4\2hi$4@3$0^6^3^4~1\2a1$3\2n1$1\2a2$3\2n2$1@3$0^7^1@3$0^7@1$2^2@3$0^7^3@3$0^7@1$2^4^5\1a$3\1n$1\1c$4@3$0^6^2@3$0^6@1$2^3^4~1").
Definition csvars_fo (gb : nat) (cs : acs) : list nat :=
  let acc := fold_left (fun acc e => evars_fo gb e acc) (s_regs (a_ss cs)) ([], []) in
  let acc := fold_left (fun acc K => kvars_fo gb K acc) (kn cs) acc in
  let acc := fold_left (fun acc m => evars_fo gb (am_len m) (evars_fo gb (am_base m) acc)) (a_maps cs) acc in
  let acc := fold_left (fun acc p => evars_fo gb (snd p) (evars_fo gb (fst p) acc)) (a_vis cs) acc in
  let acc := fold_left (fun acc p => evars_fo gb (snd p) (evars_fo gb (fst p) acc)) (a_ghost cs) acc in
  let acc := match a_fd cs with FdFile _ l o => evars_fo gb o (evars_fo gb l acc) | _ => acc end in
  let acc := evars_fo gb (a_brk cs) acc in
  rev (fst acc).
Fixpoint number_from (i : nat) (l : list nat) : list (nat * nat) :=
  match l with [] => [] | v :: rest => (v, i) :: number_from (S i) rest end.
Definition compact_map : ltac2:(zQ "40!hg8!hg1!kj1!ig3>2gb$0>2cs$3@1$1@2$2$0$0") := ltac2:(zQ "40!hg8!ig3!hjs3!hjsf\2gb$0\2cs$1@2$3^2@2$2^2^1").
Definition node_compact : ltac2:(zQ "30!ig3!hg8!iu3>2gb$1>2cs$0@1$2$0") := ltac2:(zQ "40!hg8!ig3!hjtd!hjub\2gb$0\2cs$1@3$3^2^1@2$2^2^1").

(* [comment removed for export] *)
Fixpoint regs_match_h (lo hi : nat) (seen : list nat) (rs ts : list expr) : bool :=
  match rs, ts with
  | [], [] => true
  | r :: rs', t :: ts' =>
      match t with
      | EVar v => if (Nat.leb lo v && Nat.ltb v hi)%bool
                  then (negb (existsb (Nat.eqb v) seen) && regs_match_h lo hi (v :: seen) rs' ts')%bool
                  else (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')%bool
      | _ => (expr_eqb r t && expr_vars_lt lo t && regs_match_h lo hi seen rs' ts')%bool
      end
  | _, _ => false
  end.
(* [comment removed for export] *)
Definition saddr_eqb_h : ltac2:(zQ "20!io7!va>1x$0>1y$0$1") := ltac2:(zQ "70!tp7!jvf!hjg4!io7!mi7!ju7!lm5\1x$3\1y$3@2$4@2$6^2^1@2$5@2$0@1$1^2@1$2^2@2$0@1$1^1@1$2^1").
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint cover1 (k : list kentry) (b : expr) (i : Z) : option Z :=
  match k with
  | [] => None
  | K :: rest =>
      let hit := match K with
                 | KWord (SA kb kk) w _ =>
                     if (expr_eqb b kb && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool then Some (kk + Z.of_nat w) else None
                 | KZero (SA kb kk) (ELit l) | KFill (SA kb kk) (ELit l) _ | KBlob (SA kb kk) (ELit l) _ | KUnk (SA kb kk) (ELit l) =>
                     if (expr_eqb b kb && Z.leb 0 l && Z.ltb l two64 && Z.leb kk i && Z.ltb i (kk + l))%bool then Some (kk + l) else None
                 | _ => None
                 end in
      match hit with Some e => Some e | None => cover1 rest b i end
  end.
Fixpoint cover_x (fuel : nat) (k : list kentry) (b : expr) (i : Z) (stop : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.leb stop i then true else
           match cover1 k b i with
           | Some e => if Z.ltb i e then cover_x f k b e stop else false
           | None => false
           end
  end.
(* [comment removed for export] *)
Definition kunk_covered : ltac2:(zQ "30!ik0!va!hg1>1k@1$2$0>1K$0$1") := ltac2:(zQ "h70!hta!hge!io7!h9!hg8!jse!va!ik0!jh0!jh9!iie!jv9!uqb!sm9!hg1!hjv9!ps0!po5!os4!osd!jv3!lp7!rs6\1k@1$e$7\1K$7M7\1K$7$6^1\1a$2\1w$4\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\2k0$4$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$1\2a1$2\2n1$0\2a2$2\2n2$0$1\1a$2\1n$0\1c$3$1\1a$2\2n0$0M2\1a$2$6^2\1b$0\1o$3M0\2n0$0$6^3\1n$3@2$5@2$5@2$5@2$5@2$5@2$h5Z^1@2$b^1@2$h6+2+i8@2$b@1$h3?1A@1$h2?1A@4$h0^7^3^2@1$a^1@4$h1^7^3^2@1$a^1@5$f@1$c@2$d$7^7^7^3^2@2$h4^2^1\1n$4$1\2op$8\2a0$0\2b0$0$1\2op$8\2a0$0\2b0$0$1\2op$9\2a0$0\2b0$0$1\2op$9\2a0$0\2b0$0$1\2sx$6\2lo$4\1n$4\1e$0$1\2sx$6\2k0$4\1i$3\1n$4$1").

Definition kentry_eqb_h : ltac2:(zQ "20!ik0!va>1x$0>1y$0$1") := ltac2:(zQ "e3!hta!hge!io7!h9!ik0!hg8!jse!va!hkg3!ju7!hjd!mi7!his8!ln2&\2a1$2\2n1$0\2a2$2\2n2$0$1&\2n'$0@2$6@2$8^4^2@2$9^3^1&\2a'$2~1\1x$4\1y$4@2$b@2$c^2^1M4\1x$4$7^2\1a$2\1w$5\1v$0M4\1y$4$7^4\2a'$2\2w'$5\2v'$0@2$6@2$6@2$8^6^3@2$a^5^2@2$9^4^1\2a0$2\1n$0$1\2a0$2\1n$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\1n$0$1~0\2a0$2\1n$0\1c$3$1\2a0$2\1n$0$1\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$0$1~2\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a0$2\2n0$0\1c$3$1\2a0$2\2n0$0$1\1a$2\1n$0\1k$5M4\1y$4$7^4\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a'$2\2n'$0\2k'$5@2$6@2$6@2$8^6^3@2$9^5^2@2$a^4^1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a0$2\2n0$0\1c$3$1\2a0$2\2n0$0$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1~2~0\2a0$2\2n0$0\1c$3$1\2a0$2\2n0$0$1~0\1a$2\1n$0\1c$3M4\1y$4$7^4\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a'$2\2n'$0\2c'$3@2$6@2$6@2$8^6^3@2$9^5^2@2$d^4^1\2a0$2\2n0$0$1\1a$2\1n$0M4\1y$4$7^3\2a0$2\1w$5\1v$0$1\2a0$2\2n0$0$1\2a0$2\2n0$0\1k$5$1\2lo$3\2hi$3$1\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\2a0$2\2n0$0$1~0\2a0$2\2n0$0\1c$3$1~2").
(* [comment removed for export] *)
Definition kflat_h : ltac2:(zQ "30!ik0!va!hg1>1k@1$2$0>1K$0$1") := ltac2:(zQ "b4!io7!hta!h9!va!ps0!hkc!ik0!hg8!hg1!iie!kg9&M0\1a$0$3^2\1b$1\1o$2@4$4^6^2^1^3&\1n$1~0&\1a$0~1&M0\1a$0$3^3\1b$1\1o$2@4$4^7^2^1^4\1k@1$8$6\1K$6M6\1K$6$3^1\1a$0\1w$7\1v$1M0\1a$0$3^3\1b$1\1o$2@4$4^7^2^1@1$9@1$a^4~2\1a$0\1n$1\2k0$7~3\2lo$2\2hi$2$5\1e$1\1m$2$5\1e$1\2lo$2\2hi$2$5~2\2a1$0\2n1$1\2a2$0\2n2$1$5\1a$0\1n$1\1c$2~3~2").
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kimg_sub_covered : ltac2:(zQ "30!ik0!va!hg1>1k@1$2$0>1K$0$1") := ltac2:(zQ "b1!hta!hge!io7!h9!ik0!hg8!va!jv9!jse!hg1!nlb&\2a1$2\2n1$0\2a2$2\2n2$0$1\1k@1$9$4\1K$4M4\1K$4$6^1\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\2k0$5$1\2lo$3\2hi$3@3$a$4\1X$4M4\1X$4$6^1\1a$2\1w$5\1v$0$1\1a$2\1n$0$1\1a$2\1n$0\2k0$5$1\3lo'$3\3hi'$3@2$8@2$7^2^5@2$7^4^1\1e$0\1m$3$1\1e$0\3lo0$3\3hi0$3$1\1a$2\1n$0$1~0\1a$2\1n$0\1c$3$1\1a$2\1n$0$1^4\1e$0\1m$3$1\1e$0\2lo$3\2hi$3$1\1a$2\1n$0$1~0\1a$2\1n$0\1c$3$1\1a$2\1n$0$1").
Definition kn_incl1_h : ltac2:(zQ "30!ik0!va!hg1>1k@1$2$0>1K$0$1") := ltac2:(zQ "b0!va!ik0!hkc!nlb!hge!hg1!his8!hkh1!hki0!hkia!hkje\1k@1$5$1\1K$1M0\0$0$0@3$3$1\1X$1@2$6^1^2^2$2M0\0$0$0M0\0$0$0@2$8^2^1@3$3$1\1X$1@2$7^1^2^2$4$2M0\0$0$0@2$9^2^1$2@2$a^2^1").
Definition kn_incl_h : ltac2:(zQ "30!hg1!ik0!va>1k@1$0$1>2tk@1$0$1$2") := ltac2:(zQ "40!ik0!hg1!hkkd!hnd\1k@1$1$0\2tk@1$1$0@3$3$0@1$2^2^1").

Definition entails_h (lo hi : nat) (cs : acs) (ch : acs) : bool :=
  (Z.eqb (pc cs) (pc ch)
   && match s_log (a_ss ch) with [] => true | _ => false end
   && match s_resv (a_ss ch) with None => true | _ => false end
   && regs_match_h lo hi [] (s_regs (a_ss cs)) (s_regs (a_ss ch))
   && kn_incl_h (kn cs) (kn ch)
   && kn_vars_lt lo (kn ch) && maps_vars_lt lo (a_maps ch) && pairs_vars_lt lo (a_vis ch) && pairs_vars_lt lo (a_ghost ch)
   && expr_vars_lt lo (a_brk ch) && fd_vars_lt lo (a_fd ch) && forallb (vmop_vars_lt lo) (a_vmops ch)
   && list_eqb amap_eqb (a_maps cs) (a_maps ch)
   && list_eqb pair_eqb (a_vis cs) (a_vis ch)
   && list_eqb pair_eqb (a_ghost cs) (a_ghost ch)
   && expr_eqb (a_brk cs) (a_brk ch)
   && afd_eqb (a_fd cs) (a_fd ch)
   && Bool.eqb (a_tidset cs) (a_tidset ch)
   && list_eqb vmop_eqb (a_vmops cs) (a_vmops ch)
   && Z.leb (a_totsz cs) (a_totsz ch) && Z.leb (a_ylo ch) (a_ylo cs)
   && Z.leb (a_eager cs) (a_eager ch) && Z.leb (a_abytes cs) (a_abytes ch))%bool.

(* [comment removed for export] *)
Inductive loopctx : Type :=
| LC (lc_head : Z) (lc_next : acs) (lc_lo lc_hi : nat)
| JC (jc_id : nat) (jc_st : acs) (jc_sh : shape) (jc_b jc_lo : nat).
Definition lc_bnd : ltac2:(zQ "20!hg8!hkla>1c$1$0") := ltac2:(zQ "50!hg8!hkla!ig3!h9!hkm4\1c$1M1\1c$1$0^1\7lc_head$3\7lc_next$2\5lc_lo$0\2hi$0^1\5jc_id$0\5jc_st$2\5jc_sh$4\1b$0\5jc_lo$0^2").

(* [comment removed for export] *)
Definition loop_ok (cs0 : acs) (J : nat) (N : expr) (inv : acs) : option Z :=
  let lo := S J in let hi := nxt inv in
  if (fresh_ok cs0 && Nat.leb (nxt cs0) J && Nat.ltb J hi && fresh_ok inv
      && expr_vars_lt (nxt cs0) N
      && match s_log (a_ss inv) with [] => true | _ => false end
      && Nat.eqb (length (s_regs (a_ss inv))) 32
      && kn_vars_lt lo (kn inv) && maps_vars_lt lo (a_maps inv) && pairs_vars_lt lo (a_vis inv) && pairs_vars_lt lo (a_ghost inv)
      && expr_vars_lt lo (a_brk inv) && fd_vars_lt lo (a_fd inv) && forallb (vmop_vars_lt lo) (a_vmops inv)
      && forallb (fun r => match r with EVar v => true | _ => expr_vars_lt lo r end) (s_regs (a_ss inv))
      && regs_match_h lo hi [] (s_regs (a_ss inv)) (s_regs (a_ss inv)))%bool
  then match xhi (kn cs0) N with Some nhi => if Z.ltb nhi two64 then Some nhi else None | None => None end
  else None.

(* [comment removed for export] *)
Definition loop_body_state : ltac2:(zQ "40!ig3!hg8!h9!hta>1J$1>1N$3>3nhi$2>3inv$0$0") := ltac2:(zQ "c0!ik0!mo8!sh9!si1!hg8!ina!h9!ig3!ru9!pvf!hta!loa\1J$4\1N$a\3nhi$6\3inv$7@2$8^1@3$1$0@3$3@1$2^4Z@2$b^2+1@3$1$0@3$3@2$9^3@1$2^4+1^2@1$5$0").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition branch_probe : ltac2:(zQ "30!iu3!ig3!hta>2cs$1@1$0$2") := ltac2:(zQ "hfh1!qpb!qs3!hta!in3!hkmc!va!jh0!iu3!hkn4!hknd!hko7!hkp0!hkpb!jh9!ii7!ij6!hkq4!ji2!kj8!hkqe!hkr7!hks6!hkt0!hkta!hku3!hkv0!hkva!ig3!qq1!hlg4!hlh2&\2rd@1$1@1$0#5\3imm@1$1@1$0#h4@1$3$2&\3rs1@1$1@1$0#5\3imm@1$1@1$0#c@1$3$2&\2rd@1$1@1$0#5~1&\3rs2@1$1@1$0#5\3imm@1$1@1$0#c@1$3$2&\3rs1@1$1@1$0#5~3&\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5@1$3$2&\2rd@1$1@1$0#5~5&\2op$6~6&\2rd@1$1@1$0#5\3rs1@1$1@1$0#5@1$3$2&\2op$d~6&\2rl$5~6&\2aq$5~a&\1w$9~b&\3rs1@1$1@1$0#5\2rm@1$1@1$0#3@1$3$2&\2rd@1$1@1$0#5~d&\3fmt$4~6&\3fmt$4~8\2cs$hbM7\1x@1$7$8@1$7$2@2$he?2IT@1$hc^1\1i$8M8\1i$8@1$7$2^1~0~0\2rd@1$1@1$0#5\3imm@1$1@1$0#h5@1$3$2~2\1c$h4\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3imm@1$1@1$0#d@2$h1$2@3$h2$2$5@3$hd^4@2$h0@1$f@1$e^6^3@2$h0@1$f@1$e^6^2\2sz$c\6signed$5~2\2sz$c~4\2op$6~2\2op$6\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\5shamt@1$1@1$0#6@1$3$2~7~2\2op$6\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\5shamt@1$1@1$0#5@1$3$2~7\2fm@1$1@1$0#4\4pred@1$1@1$0#4\4succ@1$1@1$0#4~8~2@1$3$2@1$3$2~9~9\1w$9\2aq$5\2rl$5~8~c\2op$h3~c\2op$a\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3csr@1$1@1$0#c@1$3$2\2op$a\2rd@1$1@1$0#5\4uimm@1$1@1$0#5\3csr@1$1@1$0#c@1$3$2\3fmt$4~2\3fmt$4~4\2op$h7\3fmt$4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3rs3@1$1@1$0#5\2rm@1$1@1$0#3@1$3$2\2op$h5\3fmt$4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\2rm@1$1@1$0#3@1$3$2\3fmt$4~e\2op$ha~f\2op$h8~f\2op$h6~f\3dst$b\3src$b~e\3dir$h9~h0~h0@1$3$2").

(* [comment removed for export] *)
Fixpoint diff_regs (i : nat) (ra rb : list expr) : list nat :=
  match ra, rb with
  | a :: ra', b :: rb' => if expr_eqb a b then diff_regs (S i) ra' rb' else i :: diff_regs (S i) ra' rb'
  | _, _ => []
  end.

(* [comment removed for export] *)
Definition node_diamond_join : ltac2:(zQ "50!ig3!hg8!hg1!iu3!h9>2nx$1>6joinpc$4>2rs@1$2$1>2ca$0>2cb$0@1$3$0") := ltac2:(zQ "i30!hg8!jse!ig3!ik0!hg1!ii7!ij6!va!sm9!hli1!irc!sh3!qq1!hta!sib!hjr1!ln2!in3!ji2!ir6!iu3!itc!h9!hlid!his8!ipa!qo4!iq2!hlj9!hjd!lp0!nlb!mk2!hnd!hlk3\2nx$0\6joinpc$h6\2rs@1$4$0\2ca$2\2cb$2=2hv@1$4$0@3$i2$0$hc@3$h3$0@3$h7N0@1$6@1$5^2@1$6@1$5^1^3=2v0$0@2$f^6@2$f@1$b^3@1$b^2=2hi$0@2$h5^1@2$8$0^2=5regsJ@1$4$d@3$ha@1$6@1$5^5^3^2=3knJ@1$4$3@3$i0$3\1K$3@3$hf$3\1X$3@2$h8^1^2@1$a^6@1$a^6=3csJ$2@2$hb^7@4$h9^9^2^1^3M7\0$7@1$h4$2@2$1@2$1@2$1@2$1@2$1@2$1@2$h0@1$c^8^a@2$h0@1$c^7^a@3$i1$0\1r$0@2$1@2$eN0^1@2$e^1Ni0^6@2$hd@2$8$d^3Ni0@2$he?3nx0^5@4$9^5^4^8^1@4$9^5^4^7^1@2$h2$2^1@1$h1$2").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition via_ok : ltac2:(zQ "30!ig3!va!hg8>2cs$0>2js$0>2lo$2$1") := ltac2:(zQ "h00!jse!hg1!sh3!ip0!lp0!ii7!ig3!va!hge!sm9!hg8!hkc!hta!ko6!ij6!hjd\2cs$6\2js$6\2lo$a@2$0@2$0@2$0@2$0M1\1x@1$1$3$7@1$d@1$5^2$b\1s$3\1l@1$1$3$8@2$f@2$9$c@1$e@1$5^2Ni0@2$4?3nx0@1$2^3@2$4@1$2^3^1@2$4^1@1$2^2").

(* [comment removed for export] *)
Definition node_abstractcell (cs : acs) (b : expr) (n : Z) : option acs :=
  let '(bb, bo) := split_lit b in
  let K := KUnk (SA bb bo) (ELit n) in
  if kunk_covered (kn cs) K then Some (set_kn cs (K :: kn_cutout (kn cs) bb bo (ELit n))) else None.

(* [comment removed for export] *)
Definition respell_ok : ltac2:(zQ "40!hta!va!hg1!ik0>1k@1$2$3>1a$0>1e$0$1") := ltac2:(zQ "h04!h9!va!kj1!iu3!ln2!jse!hge!jle!qja!hta!jl5!hg1!hkc!hlkc!hll5!ik0&\2hi$0@2$5@2$4^2Z@2$4^1Z&\2lo$0~0&M2\1p@2$2$0$0$1^1~1&\1p@2$2$0$0~2\1k@1$b$f\1a$9\1e$9M3\1x@1$3$1$1@4$e^3$d^2^1\1b$1M1\1b$1$1^1$cM3\1x@1$3@2$2$0$0$1@2$8^4@3$a$7^3^2~3$6M3\1x@1$3@2$2$0$0$1@2$8^3@3$a$7^2^1~3$6").
Definition node_respell : ltac2:(zQ "40!ig3!hg8!iu3!hta>2cs$0>1r$1>1e$3@1$2$0") := ltac2:(zQ "f0!ig3!jse!va!sib!in3!ji2!hg8!iu3!kh2!irc!sh3!jk4!hlm6!sl8!hta\2cs$0\1r$6\1e$eM2\0$2@1$7$0@2$1@2$1@2$1@2$3N0^2@2$3^2Ni0@2$8@1$a^3^1@3$c@1$9^3@2$b^3^2^1@2$5$0@3$d^3^2^1@1$4$0").

(* [comment removed for export] *)
Definition sa_of (b : expr) : saddr := let '(bb, bo) := split_lit b in SA bb bo.
Fixpoint hw_apply (k : list kentry) (a : saddr) (x : nat) (found : bool) : list kentry :=
  match k with
  | [] => []
  | KWord a' w v :: r =>
      if saddr_eqb a' a then (if found then hw_apply r a x true else KWord a' w (EVar x) :: hw_apply r a x true)
      else KWord a' w v :: hw_apply r a x found
  | K :: r => K :: hw_apply r a x found
  end.
(* [comment removed for export] *)
Fixpoint hw_val (k : list kentry) (a : saddr) : expr :=
  match k with
  | [] => ELit 0
  | KWord a' _ v :: r => if saddr_eqb a' a then v else hw_val r a
  | _ :: r => hw_val r a
  end.
Fixpoint hw_go (k : list kentry) (bs : list expr) (x : nat) : list kentry :=
  match bs with
  | [] => k
  | b :: r => hw_go (hw_apply k (sa_of b) x false) r (S x)
  end.
Definition node_havocwords : ltac2:(zQ "40!ig3!hg1!iu3!hta>2cs$0>2bs@1$1$3@1$2$0") := ltac2:(zQ "h30!ig3!va!hta!ilc!in3!ji2!sm9!hg1!iu3!itc!ii7!kn2!hln3!ipa!iq2!ika!il4!ij6!im6\2cs$0\2bs@1$7$2M1\0$1@1$8$0@1$b^2=2ss$h2@1$a^2@2$5$0@2$e^3@4$d@1$h0^1@1$h1^1@3$c@1$f^1^2@1$3^1@2$9@1$3^1@2$6$2^2@1$4$0").

(* [comment removed for export] *)
Definition node_namecell (cs : acs) (b : expr) (n : nat) : option acs :=
  let k := kn cs in let '(bb, bo) := split_lit b in
  if (Nat.leb 1 n && Nat.leb n 8 && fresh_ok cs && expr_vars_lt (nxt cs) bb && flat_x k bb bo (ELit (Z.of_nat n))
      && kn_readable segs k k bb bo n)%bool
  then Some (with_ss cs (mk_ss (pc cs) (s_regs (a_ss cs)) (KWord (SA bb bo) n (EVar (nxt cs)) :: k) (S (nxt cs))))
  else None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition hull : ltac2:(zQ "00T") := ltac2:(zQ "30!kj1!h9!hta@2$0$2@2$0$1$1").       (* [comment removed for export] *)
Definition hull_wf : ltac2:(zQ "20!va!hlnb>1h$1$0") := ltac2:(zQ "b2!h9!kje!kj1!hta!kj8!jse!hlnb!ji9!jv9!lp7!loa&@3$4$0$0@3$1$3@2$2$0$0^1&@3$1$0$0@3$1$3@2$2$0$0^1\1h$6@2$5@2$8~0~1@2$9@2$a~1~0$7").

(* [comment removed for export] *)
Definition kfoot : ltac2:(zQ "50!kj1!h9!iu3!hta!ik0>1K$4@1$2@2$0@2$0$3$1$1") := ltac2:(zQ "h0h4!h9!hta!kj1!in3!hg8!io7!kka!iu3!va!jh0!jh9!ji2!ik0!iie!kg9!loa&\2n0$1@1$7@2$2@2$2$1$0$0&@4$6@2$2$1$0$0@4$6$1$0^3^2^1&@2$b@2$2@2$2$1$0$0~1&\1n$0~2&\2b0$1@1$3@2$2@2$2$1$0$0&\2a0$1~4&\2op$9~5&\2op$a~5&\1n$4\1e$1@1$3@2$2@2$2$1$0$0&\2lo$4~8&\2sx$8~9&\1i$0\1n$4@1$3@2$2@2$2$1$0$0&\2k0$4~b&\2sx$8~c&M1~0^3~3\1n$4@1$3@2$2@2$2$1$0$0~6~6~7~7~a~d&\1k$0~e&\1b$1~f&M5\1a$5@1$7@2$2@2$2$1$0$0^2~h0&\2n0$1~h1&\1a$5~h2\1K$cMc\1K$c@1$7@2$2@2$2$1$0$0^1\1a$5\1w$4\1v$1M5\1a$5@1$7@2$2@2$2$1$0$0^3\1b$1\1k$0@2$b@2$2@2$2$1$0$0@4$6@2$2$1$0$0@4$6$1$0^2^1@1$e^4~h3\1a$5\2n0$1\2k0$4M5\1a$5@1$7@2$2@2$2$1$0$0^3\1b$1\1k$0M1~0^4~3\1n$4@1$3@2$2@2$2$1$0$0~6~6~7~7~a\2sx$8\2k1$4~b\2lo$0\2hi$0@2$b@2$2@2$2$1$0$0@4$6@2$2$1$0$0@4$6$1$0@1$dZ^2@2$f^1^2\1e$1\1m$0@1$3@2$2@2$2$1$0$0\1e$1\2lo$0\2hi$0@1$3@2$2@2$2$1$0$0\1a$5\1n$1@1$3@2$2@2$2$1$0$0\2a1$5\2n1$1\2a2$5\2n2$1@1$3@2$2@2$2$1$0$0\1a$5\2n0$1\1c$0M5\1a$5@1$7@2$2@2$2$1$0$0^3\1b$1\1k$0M1~0^4~3\1n$4@1$3@2$2@2$2$1$0$0~6~6~7~7~a~d~h3").
(* [comment removed for export] *)
Definition kpure : ltac2:(zQ "20!va!ik0>1K$1$0") := ltac2:(zQ "80!hta!io7!hge!h9!hkc!ik0!hg8!va\1K$5M5\1K$5$7^1\1a$1\1w$6\1v$0$2\1a$1\1n$0$2\1a$1\1n$0\1k$6$2\2lo$3\2hi$3$2\1e$0\1m$3$4\1e$0\2lo$3\2hi$3$4\1a$1\1n$0$4\2a1$1\2n1$0\2a2$1\2n2$0$4\1a$1\1n$0\1c$3$2\1a$1\1n$0$2").
Local Open Scope lzb_scope.
Definition hull_covers : ltac2:(zQ "30!va!hlnb!ik0>1h$1>1K$2$0") := ltac2:(zQ "h00!h9!va!kj1!hta!hge!kje!jv9!kj8!iu3!hlnb!hlo2!ju7!ik0!ji9!jv3!lp7\1h$9\1K$cM8\1x@1$8@2$2@2$2$3$0$0$1@1$a^1\1p@2$2@2$2$3$0$0M2\1p@2$2@2$2$3$0$0$1^1\2p0@2$2$3$0\1n$0M2\2p0@2$2$3$0$1^2\1b$3\1k$0M1\0$1$1M1\0$1$1M1\0$1$1M1\0$1$1@2$b^2@3$7$3@2$2$0$0^7@2$6@3$7$0$0@3$5$3@2$2$0$0^7^1$4@2$6@2$e^1^3@3$5$0$0@3$5$3@2$2$0$0^7$4@2$6Z^3$4@2$f^3$d$4$4").
Local Close Scope lzb_scope.

(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition fz_sel : ltac2:(zQ "50!hg1!va!hlnb!hta!ik0>2hs@1$0$2>4cold@1$0$3>1K$4$1") := ltac2:(zQ "d2!hlnb!hta!hls7!hlt4!io7!h9!va!ik0!hg1!hg8!jvf!ju7!hkc&\1n$1@3$2$0\1h$0@2$3^1^4^5&\1a$4~0\2hs@1$8$0\4cold@1$8$1\1K$7M7\1K$7$6^1\1a$4\1w$9\1v$1@3$2$0\1h$0@2$3^1^5^6~1\1a$4\1n$1\1k$9@3$2$0\1h$0@2$3^1^5^6\2lo$5\2hi$5@3$2$0\1h$0@2$3^1^4^5\1e$1\1m$5@3$2$0\1h$0@2$3^1^4^5\1e$1\2lo$5\2hi$5@3$2$0\1h$0@2$3^1^5^6~1\2a1$4\2n1$1\2a2$4\2n2$1M6\0$6$6@3$2$1@1$b@1$a^4^6$c@3$2$1@1$b@1$a^2^6\1a$4\1n$1\1c$5@3$2$0\1h$0@2$3^1^5^6~1").
Local Close Scope lzb_scope.

(* [comment removed for export] *)
Definition range_apart_hulls : ltac2:(zQ "60!hta!va!hg1!h9!hlnb!kuc>2bc$5>2hs@1$2$4>2b1$0>2k1$3>2n1$0$1") := ltac2:(zQ "e1!h9!hta!kj1!kje!kj8!hlnb!hg1!iie!lt3!kuc!ml5!lue!hnd!loa&@3$4$0$0@3$3$1@2$2$0$0^1\2bc$9\2hs@1$6$5\2b1$1\2k1$0\2n1$1=2sp$8@4$a^5^3^2^1@3$c$5\1h$5@8$b^7^2^5^4^3@3$4$1@2$2$0$0^1~0@1$7@2$d@3$3$0$0@3$3$1@2$2$0$0^1~0^5").
(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition in_win : ltac2:(zQ "40!h9!va!hlnb!hta>1b$3>1k$0>1n$0>1w$2$1") := ltac2:(zQ "b0!h9!va!hta!kj1!kje!hge!kj8!jv9!hlnb!ju7!jv3\1b$2\1k$0\1n$0\1w$8M1\0$1$1M1\0$1$1@2$9^4@3$6$2@2$3$0$0^1@2$7@3$6$0$0@3$4$2@2$3$0$0^1^3$5@2$7@2$a^3^2@3$4$0$0@3$4$2@2$3$0$0^1$5").
Local Close Scope lzb_scope.
Definition hs_nil : ltac2:(zQ "30!va!hg1!hlnb>2hs@1$1$2$0") := ltac2:(zQ "50!hg1!hlnb!va!hge!hkc\2hs@1$0$1M0\2hs@1$0$1$2^1$4\1h$1\1l@1$0$1$3").   (* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition store_in_wins : ltac2:(zQ "40!va!hg1!hlnb!ip0>2ws@1$1$2>1e$3$0") := ltac2:(zQ "a0!hlnb!hlu2!hg1!hluc!jvf!hjg4!hlv5!ip0!hls7!kg9\2ws@1$2$0\1e$7@3$8$0@3$3@1$4@1$1^1@1$5@1$1^1@1$9@1$6^1^2").
Local Close Scope lzb_scope.
Definition wins_apart_hulls : ltac2:(zQ "40!hg1!hlnb!va!kuc>2bc$3>2hs@1$0$1>2ws@1$0$1$2") := ltac2:(zQ "c1!h9!kj1!kje!hlnb!hta!kj8!hg1!hmg0!iie!kuc!hnd!loa&@3$5$0$0@3$2$4@2$1$0$0^1\2bc$9\2hs@1$6$3\2ws@1$6$3@3$a$3\1w$3@5$7^4^3@3$5$4@2$1$0$0^1~0@1$8@2$b@3$2$0$0@3$2$4@2$1$0$0^1~0^1").
Definition hulls_vars_lt : ltac2:(zQ "40!va!hg1!hg8!hlnb>2n0$2>1l@1$1$3$0") := ltac2:(zQ "90!hlnb!h9!kj8!hg1!hg8!kj1!kh2!hta!hnd\2n0$4\1l@1$3$0@3$8$0\1h$0@2$6^3@3$2$7@2$5$1$1^1^1").

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition range_apart_hulls_ref : ltac2:(zQ "60!hg1!hta!va!h9!hlnb!ik0>2fk@1$0$5>2hs@1$0$4>2b1$1>2k1$3>2n1$1$2") := ltac2:(zQ "d1!h9!hta!kj1!kje!kj8!hlnb!hg1!iie!ik0!mj6!ltc!hnd!loa&@3$4$0$0@3$3$1@2$2$0$0^1\2fk@1$6$8\2hs@1$6$5\2b1$1\2k1$0\2n1$1@3$b$5\1h$5@8$a^6@4$9^6^4^3^2^4^3^2@3$4$1@2$2$0$0^1~0@1$7@2$c@3$3$0$0@3$3$1@2$2$0$0^1~0^4").
Lemma range_apart_hulls_eq : ltac2:(zQ "a0!hg1!hta!va!ljb!h9!hlnb!hmg0!hmh5!ik0!lgf>2fk@1$0$8>2hs@1$0$5>2b1$1>2k1$4>2n1$1@3$3$2@5$6@1$9^5^4^3^2^1@5$7^5^4^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##-Ih01hh12b1h22k1h32n1h41bh52b2h62fkh72hsh82k2h92n2h:1sh;2spp;1p;2p;3p;8p;4p;6p;5g08I6R0p608000R1p108J?p4p710p8P1p103G<!s6,g0688R1!s7'g00EVj15Tg01N:j1Ej42Tg00Kbj13Tg00Gej29Tg000Nj38Tg05o>j37Tg0189j2<Tg016Rj1;Tg01Cij8:j1BTP1j30Tg01BXj84j1DTg001Hj31Tg004Fj2CTg01E=j1=Tg00A[j66Tg01KGj1>Tg01Q1j1?Tg08KFj5@Tg08L\j5ATg00j5#5%50g01<aR1g004`R2g01FUR3^31^22^11R4f4R5#Eg005YR6f6R7#3f1R8P5f3R9f2R:O3P5P9P:1922R;f0R<581R=A71;<R;9822R>A722;/<>#;R;G:X00=005P7P7!sa%C2R!s0&P=P>P;G4!sI&R?31X:4P6^91^82^51!th+^;3R3%D5P8P!sb0O7!sb&=16?X43f5R3P3!sF$8C2!s-%!t419,C6%35R0#B%=5E6%>0%?5E6P0!sT&<D@!t0&8P<DA516eX31W2W1W7W6o"). Qed.

(* [comment removed for export] *)
Definition kentry_vars_t : ltac2:(zQ "30!jqd!jr4!ik0>1K$2>3acc@1$1$0@1$1$0") := ltac2:(zQ "91!hmie!hta!jvf!io7!h9!ik0!hg8!jqd!jr4&\1a$3\1n$1@2$0@1$2^2@2$0^1^3\1K$5\3acc@1$8$7M5\1K$5@1$8$7^2\1a$3\1w$6\1v$1@2$0@1$2^3@2$0^1^4~0\1a$3\1n$1\1k$6@2$0@1$2^3@2$0^2^4\2lo$4\2hi$4^3\1e$1\1m$4@2$0^2^3\1e$1\2lo$4\2hi$4@2$0^3^4~0\2a1$3\2n1$1\2a2$3\2n2$1@2$0@1$2^4@2$0^3@2$0@1$2^2@2$0^1^5\1a$3\1n$1\1c$4@2$0@1$2^3@2$0^2^4~0").
Definition live_vars_seed (seed : ptree unit) (cs : acs) : ptree unit :=
  let acc := fold_right expr_vars_t seed (s_regs (a_ss cs)) in
  let acc := fold_right (fun K acc => match K with
                                      | KWord a _ v => expr_vars_t (a_base a) (expr_vars_t v acc)
                                      | KZero a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KBlob a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KWr a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KFill a n _ => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | KUnk a n => expr_vars_t (a_base a) (expr_vars_t n acc)
                                      | _ => acc end) acc (kn cs) in
  let acc := fold_right (fun m acc => expr_vars_t (am_base m) (expr_vars_t (am_len m) acc)) acc (a_maps cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_vis cs) in
  let acc := fold_right (fun p acc => expr_vars_t (fst p) (expr_vars_t (snd p) acc)) acc (a_ghost cs) in
  let acc := match a_fd cs with FdFile _ l o => expr_vars_t l (expr_vars_t o acc) | _ => acc end in
  expr_vars_t (a_brk cs) acc.
Definition cs_gc_seed (seed : ptree unit) (cs : acs) : acs :=
  let '(spb, spk) := split_lit (reg cs 2) in
  let live := live_vars_seed seed cs in
  set_kn cs (List.filter (kn_gc_entry_t spb spk live) (kn cs)).

(* [comment removed for export] *)
Local Open Scope lzb_scope.
Definition fill_in_wins (hs ws : list hull) (cs : acs) : bool :=
  if hs_nil hs then true else
  let '(db, dk) := split_lit (reg cs 10) in
  match xhiB (mkbc (kn cs)) (reg cs 12) with
  | Some nhi => existsbL (in_win db dk nhi) ws
  | None => false
  end.
Local Close Scope lzb_scope.

Definition fill_in_wins_ref (hs ws : list hull) (cs : acs) : bool :=
  if hs_nil hs then true else
  let '(db, dk) := split_lit (reg cs 10) in
  match xhi (kn cs) (reg cs 12) with
  | Some nhi => existsb (in_win db dk nhi) ws
  | None => false
  end.
Lemma fill_in_wins_eq : ltac2:(zQ "70!hg1!hlnb!va!ljb!ig3!hmjc!hmkb>2hs@1$0$1>2ws@1$0$1>2cs$4@3$3$2@3$5^3^2^1@3$6^3^2^1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) ["WithSegs"] "##-gp'0h02csh11eh22hsh31oh42wsi002dbi012dki023nhii031xp;1p;2p;3p;6g00EVj1DTg00GCR0j1CTg063Nj12Tg04@lj19j23Tg08N6j18Tg06S0j21Tg05ZSj14Tg08OAj3;Tg08J?j3:Tg00:mj35Tg001Hj36Tg004Fj2BTg00Kbj1ATg04?cj1@Tg04B2j1=Tg00A[j6>Tg08PLj3?Tg08Q]j3<Tg0153j17Tf0R1#7#7p=0g08I6R2#DR3g00hLg01<aR4g004`R5#C]1R6%21R7#9g005YR8P8P8f3R9#8R:g0069R;g00GeR<P4P5P8f1R=g01=j#0!s$'R>'1#4R?P0!sG$2R@%0>RA,19RBO1A;@=1RCf5RD5:2g02WeREn10110300021010200n20!s9'120100101n010!s#$20000P8P8P:P;P!tX&P!t?&%29/3BA52CDP!t#X36X36P8P8%8@!t,,111>#4!t1'@11@A'3f4952C!t5Y,B8%A7#@%=7E>A?@=1A<@=1568eW0X43W2o"). Qed.

(* [comment removed for export] *)
Definition frozen_entry_ok : ltac2:(zQ "40!hg1!hlnb!va!ig3>2hs@1$0$1>2ws@1$0$1>2cs$3$2") := ltac2:(zQ "d0!hlnb!jse!hg1!hmlf!hnd!ir6!ig3!kn2!hmm9!irc!sh3!hmn9!lgf\2hs@1$2$0\2ws@1$2$0\2cs$6@2$1@2$1@2$1@2$1@1$7^1@3$4$0$3^3@3$4$0$3^2@2$8@1$a^1@3$5$0^2^3@3$b@1$c@1$9^1^3^2").

(* [comment removed for export] *)
Inductive fitem : Type := FRun (gc : bool) (stops : list Z) | FFill (internal : bool).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition STOPS : ltac2:(zQ "20!hg1!h9@1$0$1") := ltac2:(zQ "d0!h9!mo8!ir6!ina!hmod!himb!hmpa!hmq6!hmr2!hmrd!hmsb!hipa!hio5@3$2$0@3$1$0@1$7?1A@3$1$0@1$6?1A@3$1$0@1$a?1A@3$1$0@1$8?1A@3$1$0@1$9?1A@3$1$0@1$5?1A@3$1$0@1$b?1A@3$1$0@1$c?1A@1$3$0@1$4?1A").

(* [comment removed for export] *)
Fixpoint mk_itab_ranges_acc (rs : list (Z * nat)) (t : itab) : itab :=
  match rs with
  | [] => t
  | (lo, n) :: rs' => mk_itab_ranges_acc rs' (mk_itab_fuel segs n lo t)
  end.
Definition mk_itab_ranges : ltac2:(zQ "50!hg1!hg8!kj1!h9!hmt6>2rs@1$0@2$2$3$1$4") := ltac2:(zQ "70!hg1!hg8!kj1!h9!hkn4!hmte!hmv4\2rs@1$0@2$2$3$1@2$5^1@1$6$4").

End WithSegs.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition BRK_ASLR : Z := 0x80000000.
Definition NX0 : nat := 11.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition e_auxb : ltac2:(zQ "30!kj1!h9!hta@2$0$2$1") := ltac2:(zQ "20!hmve!opc@1$1$0").
Definition e_atrb : ltac2:(zQ "30!kj1!h9!hta@2$0$2$1") := ltac2:(zQ "20!hng7!opc@1$1$0").
Definition auxw : ltac2:(zQ "40!h9!hg1!hta!ik0>1i$0>2ty$0>1v$2@1$1$3") := ltac2:(zQ "d0!h9!hta!hnh4!ik0!jv3!mo8!kj8!kje!rv2!rvb!qp5!ina!iie\1i$0\2ty$0\1v$1@3$5$3@3$8@2$9@3$6$1$0$2@2$4@3$7$1$0$2@2$a+h0^3N8@1$c^2@3$5$3@3$8@2$9@3$6$1$0$2@2$4@2$4@3$7$1$0$2@2$a+h0^3+8N8^1@1$b$3").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition K_RND : nat := 25.

Definition init_kn_with : ltac2:(zQ "30!ik0!hg1!hnhd>3atr$0>1A$2@1$1$0") := ltac2:(zQ "ic0!ik0!mo8!si1!sh9!ir6!hni6!iie!hnid!rvb!hnj5!os4!ina!hnjd!hnk6!hng7!rv2!ohc!qof!hnkd!hnl8!hnm0!hnm9!hnn0!hnn7!hnne!hno5!hnoc!hnhd!hnp2!hnpd!hnq6!hnqd!hnr5!hnre!osd!hns6!hnt1!hntd!hnu8!hnv3!hnvc!or0!hjj1!jv3\3atr$0\1A$hb@3$4$0@3$1$0@3$2@1$3$h7+vvvvggg0+vvvvvvvf@3$1$0@3$2@1$3$h8Z+7@3$1$0@3$2@1$3$h9Z+vf@3$1$0@3$2@2$i1$e+h0+nvvvogggggs0+ogggggggggg0@3$1$0@3$2$hd+vvvvgggggg1+vvvvvvvvvu7@3$1$0@3$2$7+nvvvogggggg0+nvvvvvvvvvk0@3$1$0@3$2$he+nvvvogggggg0+nvvvvvvvvgg0@3$1$0@3$2$hf+vvvvgggggg0+vvvvvvvvvu8@3$1$0@3$2@1$3$c+1+kg0@3$1$0@3$2@1$3$h4Z+hg0@3$1$0@3$2@1$3$h5Z+hvvvf@3$1$0@3$2@1$3$h6Z+hvvvf@3$1$0@3$2@1$3$9Z+vvvvvvve@3$1$0@3$2@1$3$d+hhid+ighhid@3$1$0@3$2@1$3$haZ+kkls0@3$1$0@3$2@1$3$h3@2$h1@1$a^1+hgg0@2$h1@2$ib@1$a^1$h2+hgg0@3$1$0@2$h0@2$8$7-ogggg0@1$6+ogggg0@3$1$0@2$ia@2$8$7-ogggg0@1$6+ogggg0@3$1$0@3$f@2$8$7ZN8@1$3$c@3$1$0@3$f@2$8$7+8N8$i0@3$1$0@1$i3$hc@1$b$0@3$4$0@3$5Z+3@1$6@1$i4^1@3$4$0@3$5+1+4@1$6@1$i5^1@3$4$0@3$5+2+5@1$6@1$i6^1@3$4$0@3$5+3+h0@1$3$d@3$4$0@3$5+4+6@1$6+hgg0@3$4$0@3$5+5+b@1$3$9@3$4$0@3$5+6+c@1$3$9@3$4$0@3$5+7+h7@1$6Z@3$4$0@3$5+8+h9$e@3$4$0@3$5+9Z@1$6Z@3$1$0^2@3$1$0@2$i9@1$i2^1@1$a^1@3$1$0@2$h0@2$8@1$6Z@1$i8^1@1$6@1$i7^1@1$b$0").

(* [comment removed for export] *)
Definition atr_entry : ltac2:(zQ "10!ik0$0") := ltac2:(zQ "90!h9!hog4!hta!kj8!kje!hogd!iie!hhk5!rvb@3$7@2$8@3$3$2$0$1@3$4$2$0$1@1$6+h0$5").
(* [comment removed for export] *)
Definition init_kn : ltac2:(zQ "30!hg1!hnhd!ik0>1A$1@1$0$2") := ltac2:(zQ "30!hnhd!hoh5!hoi1\1A$0@2$2$1^1").

Definition init_regs : ltac2:(zQ "20!hg1!hta@1$0$1") := ltac2:(zQ "50!hoj0!hnid!iie!hta!iqc@3$4@3$0$3@1$2ZNi0N2$1").
(* [comment removed for export] *)
Definition e_stk : ltac2:(zQ "10!hta$0") := ltac2:(zQ "20!hnq6!hnre@2$1$0-ogggg0").
Definition e_stklen : ltac2:(zQ "10!hta$0") := ltac2:(zQ "40!hnq6!hoja!iie!jv3@2$1@1$2@2$3+ogggggggggg0+ogggg0$0").
Definition STKLEN_MAX : ltac2:(zQ "10!h9$0") := ltac2:(zQ "20!lf!loa@2$1+ogggggggggg0$0").
Definition init_vis : ltac2:(zQ "40!hta!hg1!kj1!hnhd>1A$3@1$1@2$2$0$0") := ltac2:(zQ "c0!hta!kj1!mo8!kka!osd!iie!ina!hnhd!hok1!hok9!os4!loa\1A$7@3$2@2$1$0$0@4$3$0$0@1$5@1$4^1@1$5@2$b@1$a^1@1$4^1@3$2@2$1$0$0@4$3$0$0$8$9@1$6@2$1$0$0").

Definition init_acs_of_with : ltac2:(zQ "40!hg1!hol4!hnhd!ik0>3kn0@1$0$3>1A$2$1") := ltac2:(zQ "ha0!ina!os4!osd!hola!hta!loa!hge!hg1!kj1!hom5!homb!hon3!honf!hoo5!hnl8!hop2!hopc!hnhd!hoq3!hoqc!hor8!hos3!hosb!sh9!ik0!jv3\3kn0@1$7$h8\1A$h1@c$9@4$h5@1$f^1$h3^2$c@1$0$h0@2$5@1$1^1@1$2^1$bZ@1$h4^1@1$0@2$8$4$4@2$h9@1$3@2$5@1$1^1@1$2^1@1$3$d@2$h2+hgg0@1$h7$e$a$6@1$0$h6").
Definition init_acs_of : ltac2:(zQ "20!hol4!hnhd>1A$1$0") := ltac2:(zQ "30!hnhd!hot2!hou6\1A$0@2$1@1$2^1^1").        (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma e_pg_early_eq : ltac2:(zQ "40!ljb!hnq6!hov0!hta@3$0$3$2$1").
Proof.
ltac2:(KReplay.run1z (kr_t_AsanPlanCore ()) [] "##%=p;1p;3p;2g002^j12Tg003Cj14Tg016Rj13Tg02fKj16Tg02ifj35Tg0153j11Tg02gTj39Tg004Fj28Tg001Hj37Tf0#2#2p=0g01<aR0g08S2g08S^R1g006Y#0!s$,R2#2#0#4#3g01=jR3#635%42#3%13#1!s$+655139'8g08TJg08UY570do"). Qed.
Lemma e_sp0_early_eq : ltac2:(zQ "40!ljb!hnid!hovd!hta@3$0$3$2$1").
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanCore ()) [] "p;1p;3p;2g002^j16Tg003Cj12Tg016Rj13Tg02fKj15Tg02ifj34Tg02gTj38Tg004Fj2:Tg001Hj39Tg0153j17Tf0R0#6#6p=0%70#7p=1g01<aR0g08S2R1g08S^R2g006Y#0#0R3#0#0#0#0R4#6#0#2#3g01=jR5#534%24#3%15#1#1R5#5542%23#3%15#1#554258138':g06[Zg08Vb590do"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

End APC.
(* [comment removed for export] *)
