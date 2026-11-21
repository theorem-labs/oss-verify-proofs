(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame Arr CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsStack0 AsPrintfFirst AsDrvDefs AsMainPre.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import CatExec RefLayout ArgvEnv FileSim MuslStrlen.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec AxSymExec3 AxSymExec3Sound AxSymExec3B AsanAcct AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanInit AsanHexScan
  BothImages BothPlanImages AsHSTab BsStartupHSF AsMainVM BsMainState BsMainFacts BsMainLazyChk BsMainLazy BsMainCells BsMainIface LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AsMainSyms.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_BsMainIfaceArgs () := KReplay.lz_vm "#%@yK47Corelib4Init5Logic2eq01I!s@;0!s@29Datatypes4bool00K!sFA1c79OSSVerify6Proofs:boost_json:fuzz_parse3lib?BsMainIfaceArgs:args_checkC13~~~C4ELinuxProcessSemantics?!s<22Fs4path!u4,5Lists7!s+#Def6Forall00C8!tmN:AxSymExec33AX23lin!te'!v]66eq_ind!sB88eq_trans!sD87f_equal!vZ`6isSome!to>8!to%_r!vtK5State7in_argv!s\Uenvp!s\Q6in_uid!s[Q8in_hwcapC!v^O8Asan!v;$SINV0!vV&!shYargH0!zpQ!u1%5in_fs!zSP=!tD#PlanSound3APS7co_sinv!xi9Peano2lt!}o,7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv!|na2ev!wL_2E!wI&!#4q;6op!tx#00!t/QProp!ts#8wrap_mem!t58!|r%3and!#5{=3nat02!tMP;!~F%Facts2vE!uYB4list!#7L>!sF$1C!#5~93nthC!v]<lengthC56Stdlib6ZArith6BinInt1Z6of_natC!y<@;bv_unsigned!z+>Z02!t6<2le!|tK3Run?total_arg_bytes!{oG1!u;A7Z_to_bvC4!tq&!vd%4!s+#2In!#6|73notC6!u,JSys2Fs5Namei>path_has_slash!#;YM8!s`$eqb!tv8tl!w$<3pow!wE>t!sB34Znat5Nat2Z9is_nonnegK!tC'9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!{Q#!sQ47Env!sT#5PExpr01!sIE2!sI65Tauto8G!t8'3K!#3^B2C!sl<B!sl&!sH6:Z!uL+=Z!sT$CheckerC!vA<4f!#?O#!sq?C!sq0_sou!sX8;ZifyClasses;rew_iff_re!{@86nth_!{D#!sA5=!#B>$_f!s,$!{f85proj1!yl<>pow_po!yS'!sN<:!sN#!sJB7compare!xfE7!#:NO3Lib2Nd:and_elimF5!#:NXMainVM6u_of_Z!si%!|;@1!x#B5mkrelK!|BL1!{TF4!sJF5!sJF8!#83?1I!#;p?!#KT,!sc60!#45=6inj_!#A'-!t,71!vQD3Op203!~5<5eKind!#<{<unit!#4P7!se%4kind!tT#!sf@!ttJ5!zDP>BothPlanImages5ASEGS!{4V:!sn#!sj%6BOTH_H!#Go_LIMIT!shV!uE23AP!tV'8!tVS!sl#2AP3NX0!}Q'!#>nD3!#RuA2!#>8W;dotdot_!#R8$!xs4!#8<,;!{g%!uW$!#Tr3!#6~$4True!#U6=:!#63$is!#GG#!#?KI;StackLayoutAbuild_s!s8#!#BH$!#?F<sub!sC=mu!#@$=add!sC=div!}b69SatDivModCZ_div!#95%!#9<C!sQ#mo!t==6modulo!sF<=mod!#:q#b!#<k#!sM@!t^#!sM15!u2$8PreO!s/#1Z;!t^#0_r_ext!sL>!st#!sL'!#:{R9LiaTuning9zify_done!{kC1Z!{d#!w;4!#<W&3Pol!#4qE5Psatz!#Bf7!sO84!sOK6K!|GM2!#MMA2!#=<?3!#?UD5!sIE4!sIE3!#`f7!#Q0#1!#6vX7W_range!#62U!#AJ33!yG3!#4231!wYN!#;CI1!#86[2kn!ulV;!#W`+B4AX2B4mkbc!#D<^8lin_ofxB!t\V!#[Y42uE!snV!#Z-16!ta%!soV?!so,!ta$!vA#S4lden!vA_7!vA&!sj_<!w,'_eqf!w1iMr!t__=!t_&!#N`%!w{d;!sv#nowrapR!st%!#Eu<prod!#`A`5snorm!~P8!t631!t6_4ladd!{8gscal!#jB>9False_ind!#UDC1I!uG_expr0!#c7'!#BL85Riscv5Instr5aluop00!sRHmul!sR%!uX65!uX$00K!u4d2!wWV!#6y-5e_sp0!skb6e_str!sli1!y/8!#PC,fst!sC=snd!tN_atrb!|W&!}G`addr01!spe6kentry!sq'!#i&[8has_fact!wib8kw!#t5#!wkC4andb!t|WCells>all_holes_here!urb<!sp#_granted!srb:!sr$class!uxB9!ux#_prop!~_3!#rj%e!#ohQ!tU/3qlo!u@b3qhi!sicw!tTew!tT+!zQO2Bs:!#=R$Syms<pm!#RO%top!st&!#QT;leb!#?Ra3TOP!u&d9page_dow!#FwV!#C`7!#ED+!wS[6uE_var!t_k4t!#EA'!$&2_7no_wrap!uTV:!sq%Lazy5f!uY#!uRV!#Mr%;!#Mr'14!uKf=!$03+_o!$06%I!#7<Z3acs0!#<lb8e!#8$$w!snb9atr_!#:T#!zMb5K_R06!skeB!skgTID!xdf5cs_v3!sof:lin_!#@=-!stg!#B[+!stj0!stf9!st&p!ssg7W_!~e/7!{ISInit6bsb_ge!si_7usp_fit!tU`len_av!sid!$1e'!$'SM8valid_s!$8fQ<sp_window_lo!sa\hi!udP7CatExec<cat!#57#_pt!#;%&!#Bw'!$?N1firstn!vsQ!$3f&C!$-g1!$0[#!wkU!u,'?!u,#struct_siz!#S<83Nat!#kZ#!s=6mu!#~H88!$#J$fl!#zuA3inj!sIB7!$$A%!uWP9Ref!#nq$>u_!wb7!tA@6mkapp2!#}%Dapp!#km+!#D9#8!#HN#!v9#!vT'!#z_<7inj_!sI/!si7!#p85!si3!wK$!ty48!ty#Inst7Inj_Z_Z!#@jPMuslStrlen=!vZ'_room!~-UA!#=E#!#Gj%image!#AXS3Mem2wa!tJQ!#tg-<!#I8&_mem!$LH9x!$#T4!#IO,t!#t|<6to!$:s$!x5'!$/[+9nth_error!sd=leb_le!|U86eq_sym!uhW8ed_slack!wqO;!wq&!s^%!#XT:!{\/!uD38ltb_spec!#bq;8BoolSpec!$?i3!wO,1!vj7>!vj+_None!sI7:!$?e$_!tp?3max!u5=max!u57!ti&or!$'q7!#tD77!sOK!$01F6!|AX;wa!$B#'!#5O;!#3-'@!$Bz$_!{4%_eq!#3~=!$0J$e!$8Q;ok!#B$_3la!#IVb3X!#o='!{/<or!~3>!{/#lt!#tvM3!x6F7!t[<?!#Zp#true_introK!z?;!#:5+4!|X#!s'$>or!sb/!#C7X5argB0!w=]!#_C#8pmc_arg!#G'W!#@t&=!$M\#above_sp!zx2!z%-7ex!s2#!$F:7>!sB&_!s-%!#Q#[:!#dR$!$GI#!tW%!#Z~`=!sv,!|q#!syU!#X\79!s|&!#UC&!#lhd1!tik5elenZ!stk4fla!#h5V!$VF3b!t`k6estart!|F]!#5L#7uE_lit'!uQe6edeno!vBf6a_base!soe5a_off!v?b8Mr_some!v@W!$-?37!sk%!#x+^!#pJ&!#^Wb5K_RN!#[Df9arg!#V~[!zI0pm_v!$]Y'!ww]pd!t]0!#<W:;lt_ge_cases!$=0B!$;M#!$=0-!vP`A!#J3-!ys$!wMf:block_full!stf8atr!sr-!wS]v!#o'%!snV!#=,'3rd!$oC'!wn4!#Rx-9!|w#morph!t7Y7seg_ro!$,K'!$gyB!$_qA6bv!#Sm#!sK@5bv_eq!$`bAbv!#mB$!sL@:b!$DB#ulu!{6,!#Gh'divAZplus!{2$idemp_l!svA@!$b$%!#IA+!sU@?!ud%!sT-!#EH97nat!$t<#!#I]<8inj_succ!$Sk=N00!t_AD!u1-_in!$?,%!sY@=!w/&_small!#6ZO2Bs9!#u_$Pre7astr_!#>o&!#j{`u!#\,+!so`4!#Y<,!snO!#`B&I!#a92!#b-$_l!#g[V!#^f+:lay_bsb_nw!u[f7wa_word!#3u^9u64!$EJ/!#3RXrdn!$LW#!w8VFileSim@read!#ax$c!yf#k!#5[G!$~&#ff!#wn`upper_v!#:<k;!v+#!sr#!$C;X!#DP3!#EAZ!#Gp8flat_u!v|'!#]MH>!$:s#!sE+@!z4#_to_le!$V_%!#Nm`3hi!$1L]!#Rq#9hid!#<k[!so/!x'$Mr!#?Bj9slot_mai!$+SV!#Gy36!w}A!$?b$3Sem5alu64!#iJBiff!#d@77iff!#dA#!#D}:9mod!#9,%!sI;7mul_1_l!zpe8u_lit64a!{ik8u_slt!v>#!vlJ!uB$div!tIe7u_mul!tH'!#V?d3!sok5!z]]!$/},!$Vr'!$GnK5!#O:[6V_ARGC!t@N!$H\$1!uZT3Arr<!#j6+l!#72&!#^O5=!sM,nth!#K\arg_p!$'Vh8!#>h%!$&_f:!tf#string!thg!u\&!th&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool04andb69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsMainVM~~~~~~i48lin_ofxB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanPlan2AP~~~~~~ma2kn79OSSVerify6Proofsaboost_jsonafuzz_parse3libaAxSymExec33AX2~~~~~~qd3lin79OSSVerify6Proofsaboost_jsonafuzz_parse3libfBsMainIfaceArgs7AT_MAIN~~~~~~v46isSome69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBsMainFacts~~~~~~hk78has_factma5e_sp0ma6e_str003fst03nat37Corelib7Numbers7BinNumshqc1Zma3acsma9atr_entryma8e_argv1wma6e_atrbma6e_str1ma8kw_argv1qd5KWordqd2SAqd4expr79OSSVerify6Proofsaboost_jsonafuzz_parse3libbAxSymExec3B4AX2B~~~~~~ih84bctxih84mkbc69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBsMainCells~~~~~~imb9all_holes04true37Corelib4Init5Logicirc2eqv4aargs_checkhqc4Npos35stdpp9bitvectorbdefinitionsiub2bv06length04list03nil37Corelib5Lists7ListDefji13nth3h5LinuxProcessSemanticsfLinuxProcessSem5Statejjf7in_argvhk72vE46Stdlib6ZArith6BinInt1Zjne6of_natjne3mulirc3andjjf7in_envpjne3addjne2lejne3sub3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutjsdh1build_stack_bytesjjf8in_hwcapjjf6in_uid69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothPlanImages~~~~~~kid3APH79OSSVerify6Proofsaboost_jsonafuzz_parse3libdAsanPlanSound3APS~~~~~~kn52uEqd6lin_of79OSSVerify6Proofsaboost_jsonafuzz_parse3libfAxSymExec3Sound4AX2S~~~~~~ks84lden04prod04pair04consqd4EVar03sndiubbbv_unsignedjne3pow37Corelib4Init5Peanolkb2ltji16firstn69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~lmfccat_argv_ptr69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~lr9h3total_arg_bytes_nat04Some06optionirc2ex3h5LinuxProcessSemanticsfLinuxProcessSem3Runmi0h1entry_stack_imagejsdcstack_to_mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mn22wajne2lthk73Xofhk7chole_granted69OSSVerify6Proofsaboost_jsonafuzz_parse3libbBsMainIface~~~~~~msf7pm_vmemkid5ASEGSlr93rdniub7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsMainPre~~~~~~nj37astr_at3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsnndh0word_to_le_bytesqd6edenotlkb2le69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~nt8floaded_segments36Stdlib5Lists4Listoi59nth_errormi08valid_spmi09valid_brkmi0avalid_argvmi0avalid_envpmi0h0entry_stack_fits69OSSVerify6Proofsaboost_jsonafuzz_parse3libcBsStartupHSF~~~~~~oof8HSF_asanjjf5in_fs69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8AsanInit~~~~~~ou35LIMITou35SINV0ou35argH0kn55cs_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3libaBothImages~~~~~~pk26BOTH_Hkid4A_PC69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9AsanInitPpp15SINVmpp15argHp" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Existing Instance fx0.

Section AT_MAIN.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : ltac2:(zQ "10!ok5@1$0?3sp0").
  Hypothesis Vbrk : ltac2:(zQ "20!ol1!nh8@2$0$1?4brk0").
  Hypothesis Vav : ltac2:(zQ "20!ole!jmd@1$0@1$1?3inp").
  Hypothesis Vev : ltac2:(zQ "20!omc!jqe@1$0@1$1?3inp").
  Hypothesis Vfit : ltac2:(zQ "30!ona!jmd!jqe@3$0?3sp0@1$1?3inp@1$2?3inp").
  Hypothesis Hh : ltac2:(zQ "50!hsa!mgc!mh2!it0!ose@3$3@1$2$0@1$4?1h@2$1$0?2ch").
  Hypothesis HC : ltac2:(zQ "90!pj9!nh8!pnf!phe!ps7!kme!po9!pt0!ota@b$0$1$2$3@6$4$5$6?3sp0?5rdraw?4brk0?3inp@3$7?3sp0?5rdraw?3inp@1$8?3inp?1E?2ch?1R?4FULL?5model").
  #[local] Notation g := (hole_granted h).
  #[local] Notation cls := (hole_class h).
  #[local] Notation X := (Xof g E).
  #[local] Notation brk0z := (bv_unsigned brk0).
  #[local] Notation sp0z := (bv_unsigned sp0).
  #[local] Notation argc := (Z.of_nat (length (in_argv inp))).
  (* [comment removed for export] *)
  #[local] Notation VM := (pm_vmem (bv_unsigned sp0) (bv_unsigned brk0) (Xof g E) FULL).
  (* [comment removed for export] *)
  Let MC : PMC sp0 rdraw inp brk0z X FULL := PMC_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC.
  Let SOK : pm_syms_ok sp0z brk0z 0 X := pm_syms_ok_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[local] Notation kp_apart := (BsMainIface.kp_apart sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_apart_ne := (BsMainIface.kp_apart_ne sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_facts := (BsMainIface.kp_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_align := (BsMainIface.kp_align sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation pd_facts := (BsMainIface.pd_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b06 := (BsMainIface.kp_b06 h E) (only parsing).
  #[local] Notation kp_b08 := (BsMainIface.kp_b08 h E) (only parsing).
  #[local] Notation kp_b22 := (BsMainIface.kp_b22 h E) (only parsing).
  #[local] Notation vm_full := (BsMainIface.vm_full sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_img := (BsMainIface.vm_img sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_S := (BsMainIface.vm_S sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_obj := (BsMainIface.vm_obj sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_ri := (BsMainIface.vm_ri sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_stack := (BsMainIface.vm_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_brk := (BsMainIface.vm_brk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation seg_rom_above := (BsMainIface.seg_rom_above sp0 brk0 inp) (only parsing).
  #[local] Notation seg_rom_below := (BsMainIface.seg_rom_below sp0 brk0 inp) (only parsing).
  #[local] Notation mrd_above := (BsMainIface.mrd_above sp0 brk0 inp) (only parsing).
  #[local] Notation mrd_outside := (BsMainIface.mrd_outside sp0 brk0 inp) (only parsing).
  #[local] Notation vrange := (BsMainIface.vrange sp0 brk0 inp h E FULL) (only parsing).
  #[local] Notation vr_sub := (BsMainIface.vr_sub sp0 brk0 inp h E FULL) (only parsing).
  #[local] Notation vr_img := (BsMainIface.vr_img sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_stack := (BsMainIface.vr_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation G_cases := (BsMainIface.G_cases sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation zinP_of_In := BsMainIface.zinP_of_In (only parsing).
  #[local] Notation vr_kobj_gen := (BsMainIface.vr_kobj_gen sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation kp_b04 := (BsMainIface.kp_b04 h E) (only parsing).
  #[local] Notation kp_b05 := (BsMainIface.kp_b05 h E) (only parsing).
  #[local] Notation kp_b09 := (BsMainIface.kp_b09 h E) (only parsing).
  #[local] Notation kp_b10 := (BsMainIface.kp_b10 h E) (only parsing).
  #[local] Notation kp_b11 := (BsMainIface.kp_b11 h E) (only parsing).
  #[local] Notation kp_b12 := (BsMainIface.kp_b12 h E) (only parsing).
  #[local] Notation kp_b16 := (BsMainIface.kp_b16 h E) (only parsing).
  #[local] Notation kp_b20 := (BsMainIface.kp_b20 h E) (only parsing).
  #[local] Notation kp_b21 := (BsMainIface.kp_b21 h E) (only parsing).
  #[local] Notation kp_b23 := (BsMainIface.kp_b23 h E) (only parsing).
  #[local] Notation kp_b24 := (BsMainIface.kp_b24 h E) (only parsing).
  #[local] Notation kp_b25 := (BsMainIface.kp_b25 h E) (only parsing).   (* [comment removed for export] *)
  #[local] Notation vr_b04 := (BsMainIface.vr_b04 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b05 := (BsMainIface.vr_b05 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b09 := (BsMainIface.vr_b09 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b10 := (BsMainIface.vr_b10 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b11 := (BsMainIface.vr_b11 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b12 := (BsMainIface.vr_b12 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b16 := (BsMainIface.vr_b16 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b20 := (BsMainIface.vr_b20 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b21 := (BsMainIface.vr_b21 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b23 := (BsMainIface.vr_b23 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b24 := (BsMainIface.vr_b24 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vr_b25 := (BsMainIface.vr_b25 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).   (* [comment removed for export] *)
  #[local] Notation vm_sw := (BsMainIface.vm_sw sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation vm_b22 := (BsMainIface.vm_b22 sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation world_ok_X := (BsMainIface.world_ok_X sp0 h E) (only parsing).
  #[local] Notation bytes_main := (BsMainIface.bytes_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation word_main := (BsMainIface.word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zero_main := (BsMainIface.zero_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation fill_main := (BsMainIface.fill_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation bytes_at_const := (BsMainIface.bytes_at_const sp0 brk0 inp) (only parsing).
  #[local] Notation u8arr_const := (BsMainIface.u8arr_const sp0 brk0 inp) (only parsing).
  #[local] Notation bytes_at_constZ := (BsMainIface.bytes_at_constZ sp0 brk0 inp) (only parsing).
  #[local] Notation rw_cells_img := (BsMainIface.rw_cells_img sp0 brk0 inp) (only parsing).
  #[local] Notation rw_cells_above := (BsMainIface.rw_cells_above sp0 brk0 inp) (only parsing).
  #[local] Notation cellsZ := BsMainIface.cellsZ (only parsing).
  #[local] Notation cells_wfb := BsMainIface.cells_wfb (only parsing).
  #[local] Notation cells_wfb_sound := BsMainIface.cells_wfb_sound (only parsing).
  #[local] Notation map_b8_unsigned := BsMainIface.map_b8_unsigned (only parsing).
  #[local] Notation map_b8_cellsZ := BsMainIface.map_b8_cellsZ (only parsing).
  #[local] Notation length_cellsZ := BsMainIface.length_cellsZ (only parsing).
  #[local] Notation img_cells_check := BsMainIface.img_cells_check (only parsing).
  #[local] Notation img_cells_main := (BsMainIface.img_cells_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation lowsh_vm := (BsMainIface.lowsh_vm sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation lowsh_vis := (BsMainIface.lowsh_vis sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation u8arr_constZ := (BsMainIface.u8arr_constZ sp0 brk0 inp) (only parsing).
  #[local] Notation fact_ivl := BsMainIface.fact_ivl (only parsing).
  #[local] Notation ivls_of := BsMainIface.ivls_of (only parsing).
  #[local] Notation cover_sweep := BsMainIface.cover_sweep (only parsing).
  #[local] Notation cover_check := BsMainIface.cover_check (only parsing).
  #[local] Notation cover_sweep_sound := (BsMainIface.cover_sweep_sound sp0 brk0 inp) (only parsing).
  #[local] Notation ivls_of_In := BsMainIface.ivls_of_In (only parsing).
  #[local] Notation Mr_some' := (BsMainIface.Mr_some' sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation Mr_nonnull := (BsMainIface.Mr_nonnull sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation uE_lit' := (BsMainIface.uE_lit' E) (only parsing).
  #[local] Notation estart_lit := (BsMainIface.estart_lit sp0 brk0 inp E) (only parsing).
  #[local] Notation fact_ivl_sound := (BsMainIface.fact_ivl_sound sp0 brk0 rdraw inp ch E R FULL model HC) (only parsing).
  #[local] Notation cover_main := (BsMainIface.cover_main sp0 brk0 rdraw inp h ch E R FULL model Hh HC) (only parsing).
  #[local] Notation lowsh_stk := (BsMainIface.lowsh_stk sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation img_word_main := (BsMainIface.img_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation zscanN := BsMainIface.zscanN (only parsing).
  #[local] Notation zscanN_sound := (BsMainIface.zscanN_sound sp0 brk0 inp) (only parsing).
  #[local] Notation segment_byte_at_zero1 := (BsMainIface.segment_byte_at_zero1 sp0 brk0 inp) (only parsing).
  #[local] Notation obj_word_main := (BsMainIface.obj_word_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_bytes_main := (BsMainIface.obj_bytes_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation obj_zero_main := (BsMainIface.obj_zero_main sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC) (only parsing).
  #[local] Notation world_uw := (BsMainIface.world_uw sp0 h) (only parsing).
  #[local] Notation rw_cells_cons1 := BsMainIface.rw_cells_cons1 (only parsing).

  (* [comment removed for export] *)
  #[local] Notation all_holes_w_here := (BsMainCells.all_holes_w_here sp0 brk0 h ch Hh) (only parsing).
  #[local] Notation all_holes_here := (BsMainCells.all_holes_here sp0 brk0 h ch Hh) (only parsing).
  #[local] Notation hole_sel_here := (BsMainCells.hole_sel_here sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hole_short_pm := (BsMainCells.hole_short_pm sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation csym_den := (BsMainCells.csym_den sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation uE_lit := (BsMainCells.uE_lit E) (only parsing).
  #[local] Notation zero_sound := (BsMainCells.zero_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation fill_sound := (BsMainCells.fill_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation bytes_sound := (BsMainCells.bytes_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation word_sound := (BsMainCells.word_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation img_sound := (BsMainCells.img_sound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vav Hh HC) (only parsing).
  #[local] Notation argH0_low := (BsMainCells.argH0_low sp0 brk0 rdraw inp E Vsp Vav) (only parsing).
  #[local] Notation hid_img := (BsMainCells.hid_img sp0 brk0 rdraw inp ch E model Vsp Vav) (only parsing).
  #[local] Notation brk_facts := (BsMainCells.brk_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation VISK_bound := (BsMainCells.VISK_bound sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation VM_Z := (BsMainCells.VM_Z sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_vis := (BsMainCells.hid_vis sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_sh := (BsMainCells.hid_sh sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation hid_stack := (BsMainCells.hid_stack sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation visibleZ_hid := (BsMainCells.visibleZ_hid sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) (only parsing).
  #[local] Notation args_block := (BsMainCells.args_block sp0 brk0 rdraw inp ch E R FULL model Vsp Vav Vev Vfit HC) (only parsing).
  #[local] Notation Mr_some := (BsMainCells.Mr_some sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation Mr_vis_none := (BsMainCells.Mr_vis_none sp0 rdraw inp ch E FULL model) (only parsing).
  #[local] Notation rdn_Mr_full := (BsMainCells.rdn_Mr_full sp0 brk0 rdraw inp ch E FULL model) (only parsing).

  (* [comment removed for export] *)
  #[local] Notation MR := (Mr ASAN_H (AsanInitP.argHp sp0 rdraw inp) E ch model FULL).
  #[local] Notation HID := (hid ASAN_H (AsanInitP.argHp sp0 rdraw inp) E ch model).
  #[local] Notation argv := (in_argv inp).
  #[local] Notation envp := (in_envp inp).
  #[local] Notation envc := (Z.of_nat (length (in_envp inp))).
  (* LPS 727298f3: the entry block is [entry_stack_image inp mb APH ENTW sp0 rdraw], laid at a launch
     base [mb] that [SINVm] binds existentially, so no single block is named here.  Its top [UTOP]
     (the stack VMA's end), its head [CHD] (sp0 to the top of the AT_RANDOM bytes), the string bytes
     [LSTR] (argv, envp, the exec name, each with its NUL) and argv[0]'s address [STRB] are
     functions of the run alone (StackLayout.block_head_size, CatExec.cat_string_off); the
     restatement of boost-beast/http_request's As/AsMainIfaceArgs.v. *)
  #[local] Notation UTOP := (bv_unsigned (ed_top rdraw)).
  #[local] Notation CHD := (Z.of_nat (block_head_size (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp))).
  #[local] Notation LSTR := (Z.of_nat (launch_string_bytes (in_argv inp) (in_envp inp) (in_execfn inp))).
  #[local] Notation STRB := (sp0z + Z.of_nat (cat_string_off (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw) (in_argv inp) (in_envp inp) (in_execfn inp))).
  #[local] Notation ENTW := (Z_to_bv 64 (Z.of_N A_PC)).
  Let KNF := co_know _ _ _ _ _ _ _ _ _ _ _ HC.

  (* [comment removed for export] *)
  Definition isSome {T} (o : option T) : bool := match o with Some _ => true | None => false end.
  Definition args_check : ltac2:(zQ "10!h8$0") := ltac2:(zQ "h80!he!lf!q8!ue!hje!ho5!hp1!hp9!h8!hq2!hq7!hs5!hsa!ht0!htc!hu7!hv0!hv9!ig4!igc!ih1!ilb!im3!iq9@1$h7\1g$8\3cls$a\2ch$c=2bc$h5@1$h6@1$2^1@2$0@2$0@2$0@2$0@2$0@2$0@2$5@1$2^2@3$h2@2$h3$6+8N8$7@2$5@1$2^2@1$h1$e@2$5@1$2^2$d@2$4$3@2$1^1$6@2$4$3@2$1^1$7@2$4$3@2$1^1$h0@2$4$3@2$1^1@3$9$h4$b$f").
  Lemma args_check_ok : ltac2:(zQ "40!h8!ir6!it0!it6@3$2$0$3$1").
Proof.
ltac2:(KReplay.run1 (kr_t_BsMainIfaceArgs ()) ["AT_MAIN"] "p;2p;3g0000j21Tg000Jj30Tg000dR0g001DR1'1g001d=001do"). Qed.

  (* [comment removed for export] *)
  Lemma cs_v3 : ltac2:(zQ "b0!iu3!jg8!jge!jh6!jhc!it0!jj8!hs5!jmd!jn8!jp6@3$5$7@2$9?1EN3@1$a@2$2@1$1@1$0#8@4$6@1$3@1$1@1$0#8N0@1$8?3inp@1$4@1$1@1$0#8").
  Proof.
    pose proof (AsanInitP.SINVm_ev _ _ _ _ _ _ _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as HE. unfold vE. rewrite (HE 3%nat) by (unfold NX0; lia).
    unfold AsanInitP.E0p. cbn [ev AsanInit.E0 AsanInit.vals0 nth]. apply u_of_Z.
    npose Vav as (Hl & _ & Hs & _ & _). assert (Hin : In (nth 0 argv []) argv) by (apply nth_In; lia).
    pose proof (proj1 (Forall_forall _ _) Hs _ Hin) as L. cbv beta in L. lia.
  Qed.

  (* LPS 727298f3: the block's arithmetic at a launch base [mb].  [Run.valid_launch_sp] puts sp0
     between [launch_sp_lo] and [launch_sp_hi], so the [arch_align_stack] pad
     [StackLayout.block_pad_len] does not clamp and is at most 4110; argv[0] sits [LSTR + 8] below
     the stack VMA's end; [Run.valid_stack_top_va] keeps that end at or below STACK_TOP
     ([PropExec.entry_page_top_within_window]).  Text of boost-beast/http_request. *)
  Lemma launch_lay : forall mb, entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mb rdraw) inp ->
    0 <= Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw) argv envp (in_execfn inp)) <= 4110
    /\ STRB + LSTR + 8 = UTOP /\ UTOP <= 0x800000000000.
  Proof.
    intros mb Hlau.
    pose proof (entry_page_top_within_window Sv48 inp mb sp0 brk0 rdraw Hlau) as HT.
    unfold entry_page_top, va_stack_top, sp_window_hi in HT.
    cbn [entry_launch_ok_va] in Hlau. destruct Hlau as (_ & Hsw & _). destruct Hsw as (_ & Hslo & Hshi).
    unfold launch_sp_lo, launch_sp_hi, align_down16 in Hslo, Hshi.
    pose proof (Z.mod_pos_bound (UTOP - 8 - LSTR) 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound (UTOP - 8 - LSTR - 4095) 16 ltac:(lia)).
    unfold cat_string_off, block_pad_len. rewrite Nat2Z.inj_add, Z2Nat.id by lia.
    split; [lia|]. split; lia.
  Qed.

  (* V_W (vals0 index 4) is the [arch_align_stack] pad, 0..4110, between the AT_RANDOM bytes and
     argv[0]; it no longer counts words up to the old fixed string offset 184 *)
  Lemma W_facts : 0 <= vE E 4 <= 4110 /\ STRB = sp0z + CHD + vE E 4.
  Proof.
    pose proof (AsanInitP.SINVm_ev _ _ _ _ _ _ _ _ (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC)) as HE.
    destruct args_block as (mb & (_ & Hlau) & _). pose proof (launch_lay mb Hlau) as (HP & _).
    unfold vE. rewrite (HE 4%nat) by (unfold NX0; lia).
    unfold AsanInitP.E0p. cbn [ev AsanInit.E0 AsanInit.vals0 nth]. rewrite u_of_Z by lia.
    unfold cat_string_off. rewrite Nat2Z.inj_add. split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma no_wrap : ltac2:(zQ "d0!it0!h8!ir6!hs5!lf!q8!kr9!ih1!ue!krf!im3!lgf!hje>1e$7>0@3$0$1@2$c$8@2$4@1$a@1$5?2ch^1$2@3$0$3@2$6?1E^2@2$b?1E@1$9^2").
Proof.
ltac2:(KReplay.run1z (kr_t_BsMainIfaceArgs ()) ["AT_MAIN"] "#$#$p%0p'0p%1p'1p%2p'2p%3p'3p%4p'4p%5p'5p%6p'6p%7p'7p%8p'8p%9p'9p%:p':p%;p';p%<p'<p%=p'=p%>p'>p%?p'?p%@p'@p%Ap'Ap%Bp'Bp%Cp'Cp%Dp'Dp%Ep'Ep%Fp'Fp%Gp'Gp%Hp'Hp%Ip'Ip%Jp'Jp%Kp'Kp%Lp'Lp%Mp'Mp%Np'Np%Op'Op%Pp'Pp%Qp'Qp%Rp'Rp%Sp'Sp%Tp'Tp%Up'Up%Vp'Vp%Wp'Wp%Xp'Xp%Yp'Yp%Zp'Zp%[p'[p%\p'\p%]p']p%^p'^p%_p'_p%`p'`p%ap'ap%bp'bp%cp'cp%dp'dp%ep'ep%fp'fp%gp'gp%hp'hp%ip'ip%jp'jp%kp'kp%lp'lp%mp'mp%np'np%op'op%pp'pp%qp'qp%rp'rp%sp'sp%tp'tp%up'up%vp'vp%wp'wp%xp'xp%yp'yp%zp'zp%{p'{p%|p'|p%}p'}p%~p'~p/I89OSSVerify6Proofs:boost_json:fuzz_parse3lib:AxSymExec33AX24expr00p/I47Corelib4Init5Logic2eq!sB69Datatypes4bool!sH#c7!tQN?BsMainIfaceArgs6isSomep/C!u?^3linp/C!tVO8A!tV$VM8lin_ofxB!tQR;!tQ,B4AX2B4mkbc!skR8AsanPlan2AP2knp,2chO1O1S00f0O2O2p/K!wFA1O3!updQ00f1!t:#!xZ<6option!x\#!wncO1!uJ4!z.,1!#$R~!tR/!v|#!{^Z!v)r!x)f2O2f0!xv#!#()~!|v,!#)T~!#)T~!vT24!vT:!#5T~!#5T{!}v(!#32F!udI7Numbers7BinNums1Z!x$T=!#52)Sound3APS2uEp,1Ef6!tz#!srP?!uh,!st$4AX2S4lden!sw#!v]a6!y*(f6O1O2O3i001HpB1100!s1#L!s1(f!z2#!#0H~!#0H~!|Hs5!z)@!t~*!vPf!#;J#!#1X~!#1X~!xl4!#)P~!~f/!#>tK!vt76eq_ind!#.N~!zNt7!#@J~!t~3!#1z~!#@JJ!#,b~!yb.3!#5f)opB0!#5[)!wuX7!wu)!#GEg!x^(!tWY<!yN*_eqf!t\lO6!#,.~!#0Z~!wcz!#.]~!z]+2!#8k$!ukY=!uk)_sound!slR>Both!uq#Images5ASEGS!#?pU!#AY5Mr!tZR:!tZ#!tV(6BOTH_H!sgR9!tS#!wl#P5argHpp,3sp0p,5rdrawp,3inpO3!uT$!xQ#p,5modelp,4FULL!{a#!yMfp,3KNFf8f3f0O8!#E|~!#E|K8!#E|q!#6M$!{^a;!zt#nowrapR!}ei9!#<)?!#Az*!sHT!#5V~!#=2J!u>O!#=8~!#5Y{!#Lgh;O!#PK@!u#*!{uS!v98n010!s#$2!s*#!#)E~!#8x,6!#JeN!#3[~f<!#RY~!xp\<!#RY+!#RN)!#20~!#a`\!#0T~!vbb:!|TJ!{6g5!#9@(!wg77f_equal!#*j~!#EL1!#Xfr!#8n~!#$6~!ydf!#XD$!}4$!#r7f!tYc!~p#e!~p(!#sqj!#(M~!w$M!#Xp>prod!#nH0!#8a8!#?T<list!sHA!t2$!#9mE!vMfO2S02O1S!#4$b5snormf0!#7=?!uq(1Q!t@(3O4!w/eQ!sI#!sk,!sI6!t_E2Q0!#^S?!xaL!z|g!uB@!tu0!sF38positive03O1f1O4Q03O!w*$I4ELinuxProcessSemantics5Riscv5Instr5aluop!|Nh!#D9a4laddf4f1O1f4!yh#!#ALS!sw=!#=dbscale!wkB3!wkM!uU)!#M|#!#5Q~!#5QN!v?hC56Stdlib6ZArith6BinInt1Z3pow!{Ki!{rM!xe$!t_;6modulo!#8C0!#$d~!##M~!##M~!vw8!s$.2O2f5f2!#FgA!#7}~!#7}~!#7}~!#7}N4!#7},!#**~!#**~!#**~!w*h6!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!w*R7!#**~!#**~!#**~!w*}i101bi111si121ni133op0i142a0i152b0i16!s9(7!s9$8!s9$9!s9(:!s9$;!s9$<!s9(=!s9$>!s9$?2sxi1@2loi1A!t*#B2e0i1C!s=$D1ki1E1ii1F1nn011!#m(#81!s0#!s*#230113114115!s1#6117118!s1#911:11;!s1#<11=11>4011?11@11A11B!s4#C11D11E11F!#,^~!#,^~!#,^~!y^j3!#1c~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!w*Fi102op!#DS*:!$2[$!s#1!#*O~!#*O~!#*O~!{Tv!#sjGmul!#sjl!#p@~!tWM!#sYhf0f5f!#jd#!#(N~!#(N~!uN<6f3!#m)~!#1=~!#1=~!}=n5!#9k~!#**~!#**~!#\n~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!w*G8!#**~!#**~!#**~!w*}i101ai111ki122n0!#m*21b!#m)2!s8#!#m(0!s8#!#m$0!s8#!#m#/!t$$!#m$92n0!#m(~!#HK~!#HKN!$fGa!#HK+8f5!#HK~!#0,~!#0,~!#87~!#**~!#**~!#**~!w*c9!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!w*R:!#**~!#**~!#**~!w*}!#HK/!$6O)1!#HJ#1!$6O.1!#HK#1!$6O.1!#HL#1!$6O.1!#HM#1!$6O~!#HL~!#HL~!#HL~!#0.~!#0.~!#0.~!#HL~!#**~!#**~!#**~!#<=~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#HL~!#**~!#**~!#**~!#HL~!#HL~!#HL~!#HL~!#HL~!#0.~!#0.~!#0.~!#HL~!#**~!#**~!#**~!#<=~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#HL~!#**~!#**~!#**~!#HL~!#HL~!#HL~!#HL~!#HL~!#0.~!#0.~!#0.~!#HL~!#**~!#**~!#**~!#<=~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#HL~!#**~!#**~!#**~!#HL~!#HL~!#HL~!#HLz4!#HLj9!)[7$!#0.~!#0.~!#0.~!|.j!$ar~!#**~!#**~!#88~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!w*H;!#**~!#**~!#**~!w*}!$v3}3sx0i1@3lo0!$v5,1i1C!s@(!$v6~!#HN~!#HN~!#HN~!#00~!#00~!#00~!#HN~!#**~!#**~!#**~!#<?~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#HN~!#**~!#**~!#**~!#HN~!#HNe!(?\4!#HM.2i0!#HN~!#HN$!#lQ7!(B7s!#lM32k0!#lN~!)09~!#08~!#08~!(kJ~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!#**~!)09J8!*;p)!)05~!#*K~!#*K~!#/P~!#**~!#**~!#**~!w*g!)p#~!#**~!#**~!w*~i101ei111z!#RP)2opi141a!#RN)!s6$7!s6#!#RL$!s6$:!s6#;!s*#<!s6$=!s1#!#RHE!$?oC1!#RG71!#TwS!*:1$0100iv0!*B\(p?!t=#1v0f<O1!uo#o!uo#ln!tM$!*K4#!s0(1i002e0!se(!xj>!*E4~!#vnQ!*NbP!*MDif0!*cYB!#)5~!v5Pf6!*OAB!#$y~!tyM<!$bn#!*q,C!#${~!t{M=!*INw!*w^~!*w^~!#1*~!*{0.!#:+?!+*H~!tv:!*Wm<?!*dJr!*V~#!#(Q~!uQL@!*Z@~!}G\@!*Z@+S!+,s+!+,~,l!#:r)!#1)~!#1)~!#1)~!#6(~=!*Ce)!#1q~!{Fn>!#/F~!vd\>!{F(f!{2$S!#Ce(!{H(!+#`#8!)Q]#4O8i002H!#CG(f0O!#CW#!s6#2!+6n+!{n^!*cD~!t67!*jqg!#0<~!#:@,!*bS>!+2T~!#)x~!t6D!#(F~!#$6~!#5F7-!*lE<5False!|F<4True00!#Mp#!#Mk/!s#$!#Mk?!sg/!#.i~!#L0L!ub,!{289!sE$!{58!#7V~!*s8~!*s8{f0O2!#7$9!*3e#!#U_*2!#7V#2!#7V#1b!sS,S!s^0!s1*!#8D(!st/!#@q+!*b`$!#8,~!}kK!+?ae3!*|h~!t~1!+G/~!#DK~!#DKU!vNi2S0!#c0?!+G0c!vw)Q!t5#!wDE!sHD!#8,g!}i/!#8(j!vH)!#79~!#79~!+V~~!+V~t!#796!#6N5!#dR7!#f)#0f!+aH#!#791o!st8!#e_(o"). Qed.

  (* [comment removed for export] *)
  Lemma lin_e_sp0 : ltac2:(zQ "c0!hs5!ih1!lh7!lhd!li3!li9!jh6!jhc!it0!hp1!ue!krf@3$8$a@1$b$9@4$3$0@1$6@2$2$0$1Z@3$4@2$2$0$1@4$3$0$1+ogg0@1$5N0@3$4@2$2$0$1@4$3$0$1+hgg0@1$5N6@3$4@2$2$0$1@4$3$0$1+h0@1$5Na@1$7@2$2$0$1").
Proof.
ltac2:(KReplay.run1z (kr_t_BsMainIfaceArgs ()) ["AT_MAIN"] "##&<p;2p;1p;3p;4g01P6j29Tg00GJj1>Tg00@=j16Tg00JPj15Tg01XMj14!sJ$jj1<Tg01<aj32Tg01Q^j47Tg0000j2;Tg01H3j1:!s8$Jj3=Tg00Eij18Tf0R0#6#6p=0g00c2R1g01UOR2f1P0C7p=3%80#8p=11912R2#>R0,91P1P0g00b5g00m6#0#0R0#!s$&R1#6#0#5g00d2R3#4'3%51%13#1#1!s6'0!s6%4'3%<252!s%&C7R2';g004Cg01YV#:;=2do"). Qed.
  (* LPS 727298f3: argv[0] is [e_atrandom + 16 + V_W] (AsanPlanCore), so its linear form holds the
     pad, the STACK_ROUND gap and the CONFIG_RSEQ flag; the AT_RANDOM bytes sit 456 above e_atrb's base *)
  Lemma lin_e_str0 : lin_of e_str0 = (472, [(32768, EVar 0); (8, EVar 1); (8, EVar 2); (1, EVar 4); (4096, EVar 6); (16, EVar 10); (8, EVar 11); (32, EVar 12)]).
  Proof. vm_compute. reflexivity. Qed.
  Lemma lin_e_str1 : lin_of e_str1 = (473, [(32768, EVar 0); (8, EVar 1); (8, EVar 2); (1, EVar 3); (1, EVar 4); (4096, EVar 6); (16, EVar 10); (8, EVar 11); (32, EVar 12)]).
  Proof. vm_compute. reflexivity. Qed.
  Lemma lin_e_atrb : lin_of (fst e_atrb) = (0, [(32768, EVar 0); (8, EVar 1); (8, EVar 2); (4096, EVar 6); (16, EVar 10); (8, EVar 11); (32, EVar 12)]) /\ snd e_atrb = 456.
  Proof. vm_compute. split; reflexivity. Qed.

  Lemma arg_facts :
    has_fact (kn ch) (KWord (SA e_sp0 8) 8 e_str0) = true /\ has_fact (kn ch) (kw_argv1 e_argv1w) = true /\ has_fact (kn ch) atr_entry = true
    /\ uE E e_sp0 = sp0z /\ uE E e_str0 = STRB
    /\ uE E e_str1 = STRB + Z.of_nat (length (nth 0 argv [])) + 1
    /\ uE E (fst e_atrb) + snd e_atrb = sp0z + CHD - 16.
  Proof.
    pose proof args_check_ok as H0. unfold args_check in H0. pose proof (all_holes_here _ H0) as H. cbv beta in H. clear H0.
    apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H _].
    apply andb_prop in H as [H F3]. apply andb_prop in H as [F1 F2].
    (* LPS 727298f3: the plan's stack pointer and argv[0] pointer through [SINVm] (AsanInitP), not
       through the old literal offset 184 (the text of boost-beast/http_request) *)
    pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as SI.
    pose proof (AsanInitP.SINVm_sp0 _ _ _ _ _ _ Vsp Vav Vev _ _ SI) as USP.
    rewrite e_sp0_early_eq in USP.
    pose proof (AsanInitP.SINVm_vals _ _ _ _ _ _ Vsp Vav Vev Vfit _ _ SI) as (_ & _ & US0).
    destruct args_block as (mb & (_ & Hlau) & _). pose proof (launch_lay mb Hlau) as (_ & HS & HT).
    pose proof W_facts as (W1 & W2). pose proof cs_v3 as V3.
    pose proof Vsp as [VS1 [VS2 _]]. unfold sp_window_lo, sp_window_hi in VS1, VS2.
    pose proof Vav as ([Hl _] & _ & Hs & _ & _).
    assert (HL0 : Z.of_nat (length (nth 0 argv [])) <= 131071).
    { assert (Hin : In (nth 0 argv []) argv) by (apply nth_In; lia).
      exact (proj1 (Forall_forall _ _) Hs _ Hin). }
    pose proof (Nat2Z.is_nonneg (launch_string_bytes argv envp (in_execfn inp))).
    assert (HCH : 16 <= CHD) by (unfold block_head_size; cbv zeta; lia).
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|].
    split; [exact USP|]. split; [exact US0|]. split.
    - (* e_str1 = e_str0 + (V_L0 + 1), V_L0 = |argv[0]| ([cs_v3]) *)
      unfold e_str1, eadd, eaddz, uE. unfold uE, AX2S.uE in US0.
      rewrite !mkAlu_denot, !edenot_lit, !u_add64, US0.
      change (bv_unsigned (edenot E (EVar V_L0))) with (vE E 3). rewrite V3, (u_of_Z 1) by lia.
      rewrite (Z.mod_small (Z.of_nat (length (nth 0 argv [])) + 1)) by lia.
      rewrite Z.mod_small by lia. lia.
    - (* the AT_RANDOM bytes: e_str0 = e_atrandom + 16 + V_W and STRB = sp0z + CHD + V_W ([W_facts]),
         so e_atrandom = sp0z + CHD - 16; [e_atrb] splits off its literal (AsanInit.split_u) *)
      assert (UA : uE E e_atrandom = sp0z + CHD - 16).
      { pose proof US0 as U. unfold e_str0, eadd, eaddz, uE, AX2S.uE in U.
        rewrite !mkAlu_denot, !edenot_lit, !u_add64, (u_of_Z 16) in U by lia.
        change (bv_unsigned (edenot E (EVar V_W))) with (vE E 4) in U.
        unfold uE. pose proof (u64_range (edenot E e_atrandom)). lia. }
      assert (Hab : split_lit e_atrandom = (fst e_atrb, snd e_atrb))
        by (unfold e_atrb; destruct (split_lit e_atrandom); reflexivity).
      assert (Hak : 0 <= snd e_atrb <= 456) by (vm_compute; split; discriminate).
      pose proof (split_u E e_atrandom (fst e_atrb) (snd e_atrb) Hab ltac:(lia) ltac:(lia)) as HSU.
      unfold uE, AX2S.uE in HSU, UA |- *. lia.
  Qed.

  (* [comment removed for export] *)
  (* LPS 727298f3: the block runs from sp0 to the stack VMA's end [UTOP], with the strings at its top *)
  Lemma lay :
    8 * argc + 8 * envc + 200 <= UTOP - sp0z /\ UTOP <= 2 ^ 47 /\ 1 <= argc <= 1024 /\ 0 <= envc <= 256
    /\ 0x7fff80000000 <= sp0z <= 0x800000000000 /\ STRB + LSTR + 8 = UTOP.
  Proof.
    destruct args_block as (mb & (_ & Hlau) & _). pose proof (launch_lay mb Hlau) as (HP & HS & HT).
    pose proof Vav as [[LA1 LA2] _]. pose proof Vev as [LE _]. pose proof Vsp as [V1 [V2 _]].
    unfold sp_window_lo, sp_window_hi in V1, V2.
    assert (HCH : 8 * argc + 8 * envc + 472 <= CHD).
    { pose proof (auxv_size_rseq (kb_rseq (in_kernel inp))) as HA. pose proof (rseq_z_range (kb_rseq (in_kernel inp))).
      unfold block_head_size, block_items. cbv zeta. lia. }
    assert (HSO : STRB = sp0z + CHD + Z.of_nat (block_pad_len (kb_rseq (in_kernel inp)) sp0 (ed_top rdraw) argv envp (in_execfn inp)))
      by (unfold cat_string_off; rewrite Nat2Z.inj_add; lia).
    pose proof (Nat2Z.is_nonneg (launch_string_bytes argv envp (in_execfn inp))).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
  Qed.

  (* The k-th argv pointer: argv[k] = argv[0] + the bytes of the strings before it
     (CatExec.cat_argv_ptr_offset), argv[0] = sp0 + cat_string_off (CatExec.cat_string_base_offset) *)
  Lemma u_ptr : forall k, (k < length argv)%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k) = STRB + Z.of_nat (total_arg_bytes_nat (firstn k argv)).
  Proof.
    intros k Hk. pose proof lay as (_ & HT & _ & _ & VS & ST).
    destruct args_block as (mb & (_ & Hlau) & _).
    pose proof (total_arg_bytes_firstn_le k argv) as TF. pose proof (length_flatten_strings argv) as LF.
    unfold launch_string_bytes in ST.
    rewrite (cat_argv_ptr_offset (ed_top rdraw) argv envp (in_execfn inp) k Hk).
    rewrite (cat_string_base_offset Sv48 inp mb sp0 brk0 rdraw Hlau).
    rewrite !word_add_nat_Z2bv.
    rewrite (u_of_Z (sp0z + _)) by lia.
    apply u_of_Z. lia.
  Qed.

  (* Above argv[k]'s NUL lie at least the exec name's NUL and the 8-byte top slot, so ten bytes
     from argv[k] + |argv[k]| still lie in the block; the old 17 counted the AT_RANDOM bytes, which
     are no longer above the strings *)
  Lemma room : forall k, (k < length argv)%nat ->
    bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k) + Z.of_nat (length (nth k argv [])) + 10 <= UTOP.
  Proof.
    intros k Hk. pose proof lay as (_ & _ & _ & _ & _ & ST). rewrite (u_ptr k Hk).
    pose proof (total_arg_bytes_firstn_within argv k Hk) as TW. pose proof (length_flatten_strings argv) as LF.
    unfold launch_string_bytes in ST. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_to_mem_some : forall mb, entry_launch_ok_va Sv48 (mkEntry sp0 brk0 mb rdraw) inp ->
    forall (x : Z), sp0z <= x < UTOP ->
    exists b, stack_to_mem sp0 (entry_stack_image inp mb APH ENTW sp0 rdraw) (wa x) = Some b.
  Proof.
    intros mb Hlau x Hx. pose proof lay as (_ & HT & _ & _ & VS & _).
    pose proof (length_entry_stack_image_launch Sv48 inp mb APH ENTW sp0 brk0 rdraw Hlau) as HL.
    unfold stack_to_mem. cbv zeta. rewrite !(wa_unsigned x) by lia.
    replace (sp0z <=? x) with true by (symmetry; apply Z.leb_le; lia).
    replace (x - sp0z <? Z.of_nat (length (entry_stack_image inp mb APH ENTW sp0 rdraw))) with true
      by (symmetry; apply Z.ltb_lt; lia).
    destruct (nth_error (entry_stack_image inp mb APH ENTW sp0 rdraw) (Z.to_nat (x - sp0z))) as [b|] eqn:Hn; [exists b; reflexivity|].
    apply nth_error_None in Hn. lia.
  Qed.

  (* The hidden half of the block is the whole string area [STRB, UTOP) ([AsanInit.argB0]), and the
     invariant pins it to the image at SOME launch base ([args_block]) *)
  Lemma block_full : exists mb, AsanInitP.launch_base_ok sp0 rdraw brk0 inp mb /\
    forall x : Z, STRB <= x < UTOP ->
      FULL (wa x) = stack_to_mem sp0 (entry_stack_image inp mb APH ENTW sp0 rdraw) (wa x).
  Proof.
    destruct args_block as (mb & Hb & HA). exists mb. split; [exact Hb|].
    intros x Hx. pose proof lay as (_ & HT & _ & _ & VS & _).
    rewrite <- (wrap_above_sp inp mb APH ENTW sp0 rdraw (wa x)) by (rewrite wa_unsigned by lia; lia).
    apply HA. unfold AsanInitP.argBp, AsanInit.argB0. cbv beta zeta. rewrite wa_unsigned by lia.
    unfold cat_string_off in Hx. rewrite Nat2Z.inj_add in Hx.
    apply orb_true_intro. right. apply andb_true_intro.
    split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
  Qed.

  (* [comment removed for export] *)
  (* The sixteen AT_RANDOM bytes now sit [CHD - 16] above sp0, below the pad and the strings *)
  Lemma atr_full : forall x : Z, sp0z + CHD - 16 <= x < sp0z + CHD -> exists b, FULL (wa x) = Some b.
  Proof.
    intros x Hx. pose proof arg_facts as (_ & _ & F3 & _ & _ & _ & UA).
    unfold has_fact in F3. apply existsb_exists in F3 as [K [HK HE]]. apply kentry_eqb_eq in HE. subst K.
    pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO. unfold atr_entry in KO. cbn [kentry_ok] in KO. ndestruct KO as (FL & LEN & BL).
    unfold elenZ in BL, LEN. fold (uE E (ELit 16)) in BL, LEN. rewrite (uE_lit' 16 ltac:(lia)) in BL, LEN.
    assert (ES : estart E (SA (fst e_atrb) (snd e_atrb)) = sp0z + CHD - 16).
    { unfold estart. cbn [a_base a_off]. fold (uE E (fst e_atrb)). exact UA. }
    specialize (BL (x - estart E (SA (fst e_atrb) (snd e_atrb))) ltac:(lia)).
    replace (estart E (SA (fst e_atrb) (snd e_atrb)) + (x - estart E (SA (fst e_atrb) (snd e_atrb)))) with x in BL by lia.
    eexists. apply Mr_some'. exact BL.
  Qed.

  (* [comment removed for export] *)
  (* The string area [STRB, UTOP) is all in the image, so every byte of it is present *)
  Lemma upper_vm_some : forall x : Z, STRB <= x < UTOP -> exists b, VM (wa x) = Some b.
  Proof.
    intros x Hx. pose proof lay as (_ & HT & _ & _ & VS & _). pose proof pd_facts as PD.
    rewrite (vm_stack x ltac:(lia)).
    destruct block_full as (mb & (_ & Hlau) & BF).
    rewrite (BF x Hx). apply (stack_to_mem_some mb Hlau). lia.
  Qed.

  Lemma rdn_some_of : ltac2:(zQ "h30!iu3!jg8!jh6!mh2!js0!mgc!it0!mha!hs5!jr9!jp6!hq7!jq7!nh8!mqc!ni1!mr2!lk4!ni8>1m>1x@1$1@1$0#k0@1$3@1$1@1$0#8>1n$b>1a$8>0@2$4Z^1>0@2$4@2$9^2@1$a^3@2$h1+2+k0>0>1x$8>0@2$c@2$4^4^1@2$h0^1@2$9^4@1$a^5@2$7@1$1@1$0#8\1b@1$1@1$0#8@3$6@1$3@1$1@1$0#8@1^8@1$e^3@2$5@1$1@1$0#8^1@2$7@1$2@1$1@1$0#8\2bs@1$2@1$1@1$0#8@3$6@1$3@1$2@1$1@1$0#8@4$f$d^7@2$h2@1$0#k0^5^6@2$5@1$2@1$1@1$0#8^1").
Proof.
ltac2:(KReplay.run1z (kr_t_BsMainIfaceArgs ()) ["AT_MAIN"] "##SXp'0h02bsh11xi001xh26__sat2h34__x1h41bi011bh54__x2h61nh72Hah83Hn0h97__arithh:4__ffh;!sf%1h<8__varmaph=5__with>4cstrh?1zh@1ahA1HhB2H0hC2HnhD4__x3hE2b1hF2b2hG1ehH1mhI1ohJ1yhK2HbhL3HbshM2HxhN2IHi024restp&0p;1p;2p;3p;4p;6p;<p;Bp;7p;8g00@=j1BTg00@bj1iTg00A@j1@Tg00CgR0j1YTg00IFR1j13Tg012jR2j20Tg00JPj1RTg00PPj2p!s8$nR3j22!s:$mR4j25Tg00ENR5j28Tg02Zej1KTg01Tmj2:Tg000Jj31Tg02\dR6j26Tg00GJj1dTg00Lkj24Tg03Pfj4`!sA$jj1_!s^$0j2GTg02bmj4^!t5$iR7j1ETg02R2j1J!s/$Pj4nTg03Qfj6[Tg02S3j4OTg00QIj1QTg00ZCj2l!s/$kj3kTg00[Oj2j!sJ$nj2NTg00^[k10!uv$=Aj4hTg00RLk10!ua$Rjk101Tg00SUj2WTg00T8j2VTg00U?j1g!s/$ak20!vU$VCj2~!s/$oj3{Tg00WNj4zTg00X@j4fTg03ROj2aTg03SSj3yTg03T6j3MTg01<aj3HTg00\0j3x!vD$Fj1w!wm$fj29!sS$[j3uTg03U?j2?!s/$ej1tTg0156j2ITg03VNj3sTg007jj6CTg03W5j2Z!s/$dj3rTg005Ij6qTg03XRj4vTg02ULl<]Tg02TflBoTg00_9l<e!s/$^j4bTg00`Ij7cTg01>ej3|!s8$mj7}Tg00aQj8mTg00b5R8f0R9'2p=;g00g^R:f2R;f1R<P9C`p=<g00c2R=/G9p=7g00bSR>P>P=P=P7P1P1f3R7g03Y3P;P<P9M<]p=X!sG&=!sG$5R1f4R?P7!sH-D!sF&!s$%2P9P<P;P2P7P?P1f6R2f7R@f8RAf9RBMBop=F!sP$4P@P4P2P1P!sv-ep=\A1=<9p=!sv%3P@P3!sL6PP;g00e8R3g00eWR4P4g00f7RCP=P<g00dQP9Cbg00fWRDFcp=>A|!s~$A!sG&g7P9Cbp=UP<P3P4P4PCP9P!sQ$TP;!s9+<P9F}p=SP7!s9+!tT$Gmp=Lg00m6R3#BRD#B#BRE#B!s-$F#iRG#@RH%iE#@RE#YRI]1%;9RJ%3;,0<%RDRK%RFRF'pRL'21279RM%3?,07,59'8PA%K;RNO11:E9RO51IX4E,6E[^1=%dERP%YPRQ14G?RR=<@11:P9RS31X0P'6[[[^@=RTX6>g00d2RU#3RV,0</2L107V,59,8MP@PNO1=1IO!t%,PPP:P2PRPUC`=1QSX0P%_ERU1:PU,GQC^WAWCX7JX@=%E7#3!sz%%E1!t1'7RW!t+&B!t+69P71277RN157WRM'8%31RX%R3RY'0RZ,07R[,57R\,8NPNPMPNP\%JNP9X1=RN15<9#JXJ=X1=R\P7P7%77RMPWP[PN!s$$=P=g02X710<9Cn#7XH=X6=R]P7P7PMPVPZPNPN%39#7X1>R^PUPZ109YRZX1=R_P1PX%7XCXR`EDM:FG\E[12WL12[LR[PN12!tO-aPWPNP_PXO1RXO1RW,07!tU&!t>,W!s6$^PUPXP!sz%PLPL%7L1=LLeR`GPP<COP[%Q2%32#;1lKFR[158KRX%;F158L[RU[RW%;KRVg00ohRMAkKF<UW7RF%;L\M^7VRVP<g010D1j8K'GPXeO1RXPUg00o<RM#_Rb%dMRMP=1N=;RcP<&03=ChRd&02=Re&01=Rf1W=8Rg1V=DRD5>f%g4R41V=3Rh=>fh1W=YRi,AD,AhRj,Uh,Tf5SfCL200fCRCP9!}I$0dRkg001DRl'G1~9;=1kldA{=8<CzR8b:b<b=X3=X5=%;<12<<10;Y,0<,5<'8[^3=^5=P9f;Rl#3RkPBP?O3b9b2b;b2b>b8CfO2PA%K?!yt/P6PEPB%K1!s;+P0PEPQ!s+$If:Rm14G2RnO1PO1a:nn10110000021010100P0PPPQ14G@g01Al9yGYRn5MG=<lBAHE<9,:PRo%gPRp!sc2200Pp!sw5!|M&,6PP9Pl%K@!ti%PI1:E<!tl/P<PO14Gm,a:!te;f?R:14Gl=MGnf=RO3<RqPoP!tXTXIIPB10AY%EmRI#3Ro,0ARr/2L%3mRs/0Y,0A/2LRtPNPaPr!{G$sO1RrO1Ru,0A!{G+APA%7APoPu!{H&IPrP_PmPs%7sCX!{Q+P`GPP2CORsPt%QlRr%;kRIP[PWPFPVPXPUPbPM1N=<PePfA>fghP41AhiRu9>fgCLPCP!yK,10<YRg#;\J^3=P9f>RoPOO2!y5/PsPtPrP!t14PdPePf1W=K=x=GRK9>fjP41AuD=>fK!t62X5=109g/2L10g;/2L!zV,@Rg#3PoP1!zT110BYRB/2910Bk!#7h$@P<12m<Rkf<RK#ERj#3Rd,0mRI,5<Rr'8%3KRt/0YRs,0mRv,5<Rw,8kPkPrPkPw%JkPNP\P<P<%7<PIPv!wD+mPm%7mR\PdPs!wF&jPsP_PKPt%7tCXRs!#4o,IL12vLRv!xB$I!xB$tO1RtO1R_,0m!s|/P\PdP_!sy+tPs!x81ACOPv%QO%3O#;!w%4=PcP<1N=7Ch!x<&uD%w3,V=R3,Au,UD!#3:$P4A>fhD1A3i,Ah!s=+!wK5XD=12Z<10Z;!~}$12<;107!#35$;!#35'^D=P9fBRZ#3P@PgP2O4!#382WMX1=O414GB=<Ol!}S-6PP10mY,4G=<oK!s?&!},%PqAHE19,:P!|y7!~?/10K!sh%go=1QSg03YWR1%@9Rq%@<R6P5%@;?1<9197;197<'=R5[19;<19;9'=%@7?1;<[Rl%@??17;\5Au;<9P9n200!tF%012!s-%0WFWEW6Pl^F6^Eq^61P9PG10oYR1,4GRq14GoR6=MGnRlP=19G6R519GnR?'0,?G10:YRB,4G,9G/=9X?=P=1?G1R814G:,9G/0?,?G,!sA,oR:1?GB109?,?G'=!s>$%tGR?,I1RC1IB?!so%%7C1Io?/0Y/I?AsoY?EC10:Y!su$8eP51ZGoEC19Gq1ZG1!s0$lArG6nECO4bB10OY,4G14GO=MGn51HPHPq!wT%fD?<<ZAHEm9,:PRm!wZAX4HPQ1:P;!x9&<P!sWCIQPPAHEA7,:P!s=&AHE@;R@1:P@,GQC^A<ZqgP<ECPlP9EqbBWLX0PP<P9O2!wo0!t4&bGPK14GAO1P9ECWKX4E!sS21!sS/%E29<AR!tb,e!#BM+XNTX6>P9CvX6>WHo"). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma wa_word : ltac2:(zQ "50!iu3!jg8!it0!mqc!lj5>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@1$3@2$4@1$0#k0^1^1").
Proof.
ltac2:(KReplay.run1 (kr_t_BsMainIfaceArgs ()) ["AT_MAIN"] "h02b1h12b2h21nh31Hh41xh51zp;1p;3p;2p;6g00@=j13Tg00@bj1<Tg00A@j12Tg000Jj31Tg00Ifj20Tg03T[j3;Tg00Lkj2:Tg03U?j25Tg03Z5j26Tg03Zhj37Tg03W5j24Tg007jj68Tg02Zej19Tg00m6#3#3#3#3#3#3#<R0#2R1g03YWR2f0R3#2R4f1R5#2R6g00ENf2R7#2?153g00c2R8f3R9/07109531R:[10751073518%29?175[R;f4#2?197\:A;753P3n2001000000120000000W1W0W2P;^16^04^22P3P01005R2,:0R4P5P8150210079183X581605970210041402E8O4b31003#9=113eW4o"). Qed.

  Lemma arg_string : forall k, (k < length argv)%nat ->
    astr_at VM sp0 (bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k)) (nth k argv []).
  Proof.
    (* LPS 727298f3: the read goes through the image at the invariant's launch base ([block_full]),
       and the bound [p + |s| + 10 <= 2^47] is [room] with [UTOP <= 2^47] ([lay]); the text of
       boost-beast/http_request's As/AsMainIfaceArgs.v *)
    intros k Hk. pose proof lay as (_ & HT & LA & LE & VS & ST). pose proof pd_facts as PD.
    pose proof (u_ptr k Hk) as UP. pose proof (room k Hk) as RM.
    pose proof (total_arg_bytes_firstn_le k argv) as TF.
    destruct block_full as (mb & (_ & Hlau) & BF).
    unfold astr_at. change AsanUbsan.M.loaded_segments with ASEGS.
    set (p := bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k)) in *.
    split; [lia|]. split; [lia|]. split.
    { npose Vav as (_ & _ & _ & Hn & _). apply (proj1 (Forall_forall _ _) Hn). apply nth_In. exact Hk. }
    split.
    - rewrite <- (read_argv_cstr_k Sv48 ASEGS inp mb APH ENTW sp0 brk0 rdraw k Hlau Hk).
      replace (Z_to_bv 64 p) with (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) k) by (subst p; symmetry; apply wa_word).
      apply rdn_ext; [fold p; lia|]. intros x Hx. fold p in Hx. rewrite <- (wa_word x).
      rewrite (vm_stack (bv_unsigned x) ltac:(pose proof (u64_range x); lia)). apply BF. lia.
    - apply (rdn_some_of VM 8 (p + Z.of_nat (length (nth k argv [])))); [lia | lia |]. intros x Hx. apply upper_vm_some. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* LPS 727298f3: the visible slots are below argv[2]'s ([argH0_low], [hid_stack]) *)
  Lemma slot_main : forall off v w,
    has_fact (kn ch) (KWord (SA e_sp0 off) 8 v) = true -> 0 <= off -> off + 8 <= 24 -> edenot E v = w ->
    rdn ASEGS VM (Z_to_bv 64 (sp0z + off)) 8 = Some (word_to_le_bytes 8 w).
  Proof.
    intros off v w HF Ho1 Ho2 Hv. pose proof lay as (_ & HT & LA & LE & VS & _). pose proof pd_facts as PD.
    npose arg_facts as (_ & _ & _ & USP & _).
    unfold has_fact in HF. apply existsb_exists in HF as [K [HK HE]]. apply kentry_eqb_eq in HE. subst K.
    pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO. cbn [kentry_ok] in KO. ndestruct KO as (_ & FL & RD).
    assert (Ha : adenot E (SA e_sp0 off) = Z_to_bv 64 (sp0z + off)).
    { apply bv_eq. rewrite (flat_u E _ _ FL). unfold estart. cbn [a_base a_off]. fold (uE E e_sp0). rewrite USP, u_of_Z; [reflexivity | lia]. }
    rewrite Ha, Hv in RD.
    assert (RF : rdn ASEGS FULL (Z_to_bv 64 (sp0z + off)) 8 = Some (word_to_le_bytes 8 w)).
    { apply (rdn_Mr_full _ _ _ RD). intros i Hi. rewrite u_of_Z by lia. apply hid_stack. lia. }
    rewrite <- RF. apply rdn_ext; [rewrite u_of_Z by lia; lia|]. intros x Hx. rewrite u_of_Z in Hx by lia.
    rewrite <- (wa_word x). apply vm_stack. lia.
  Qed.

  Lemma arg_ptr0 : rdn ASEGS VM (Z_to_bv 64 (sp0z + 8)) 8 = Some (word_to_le_bytes 8 (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) 0)).
  Proof.
    pose proof lay as (_ & HT & LA & LE & VS & _). npose arg_facts as (F1 & _ & _ & _ & US0 & _).
    apply (slot_main 8 e_str0 _ F1); [lia | lia |].
    apply bv_eq. change (bv_unsigned (edenot E e_str0)) with (uE E e_str0). rewrite US0, (u_ptr 0 ltac:(lia)). replace (total_arg_bytes_nat (firstn 0 argv)) with 0%nat by reflexivity. lia.
  Qed.

  Lemma arg_ptr1 : (2 <= length argv)%nat ->
    rdn ASEGS VM (Z_to_bv 64 (sp0z + 16)) 8 = Some (word_to_le_bytes 8 (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) 1)).
  Proof.
    intros H2. pose proof lay as (_ & HT & LA & LE & VS & ST). npose arg_facts as (_ & F2 & _ & _ & US0 & US1 & _).
    npose (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V1 & _).
    unfold kw_argv1 in F2. apply (slot_main 16 e_argv1w _ F2); [lia | lia |].
    apply bv_eq. rewrite (u_ptr 1 ltac:(lia)).
    unfold e_argv1w. cbn [edenot]. rewrite u_mul64, u_sltu64, u_lit64a.
    change (bv_unsigned (ev E V_ARGC)) with (vE E 1). rewrite V1. change (1 mod 2 ^ 64) with 1.
    replace (1 <? argc) with true by (symmetry; apply Z.ltb_lt; lia).
    change (bv_unsigned (edenot E e_str1)) with (uE E e_str1). rewrite US1, Z.mul_1_l.
    assert (T1 : forall l : list (list byte), (2 <= length l)%nat -> total_arg_bytes_nat (firstn 1 l) = (length (nth 0 l []) + 1)%nat).
    { intros [|x0 l0] Hl; cbn [length] in Hl; [lia|]. cbv [firstn fold_right total_arg_bytes_nat nth]. lia. }
    rewrite (T1 _ H2).
    npose Vav as (_ & _ & Hs & _ & _). pose proof (proj1 (Forall_forall _ _) Hs _ (@nth_In _ 0 argv [] ltac:(cbn [length]; lia))) as L0. cbv beta in L0.
    rewrite Z.mod_small; lia.
  Qed.

  Lemma wa_word0 : ltac2:(zQ "50!iu3!jg8!it0!ni8!lj5>1x@1$1@1$0#k0@3$2@1$1@1$0#k0@2$3@1$0#k0@2$4@1$0#k0^1^1").
Proof.
ltac2:(KReplay.run1z (kr_t_BsMainIfaceArgs ()) ["AT_MAIN"] "###nh01xp;1g00@=j10Tg00@bj13Tg00A@j12Tg03aJj11Tg00m6#0!s$-3#2f0#1W0o"). Qed.

  (* [comment removed for export] *)
  Theorem pre_args : ltac2:(zQ "h91!iu3!jh6!jg8!lj5!mgc!mh2!it0!hs5!mr8!mrf!ngd!jr9!ni8!hq7!jq7!mha!llf!nr4!jmd!nn2!ni1!oh2!oj8!jq0!jp6&@4$a@2$3@1$0#k0?3sp0@2$3@1$0#k0?4brk0@2$8@1$9?1h?1E?4FULL>1i$d>1s@1$1@1$2@1$0#8>0@2$h0^2N2>0@3$6@1$5@1$1@1$2@1$0#8@3$h6@1$1@1$2@1$0#8@1$h2?3inp^3@2$4@1$1@1$2@1$0#8^2@2$f$7\1p$7@2$e@3$6@1$5@1$1@1$2@1$0#8@4$h4$h5~0@2$c@1$0#k0@2$b@2$b@2$3@1$0#k0?3sp0+8@2$h7+8@1$h8^5N8@2$4@1$1@1$2@1$0#8@2$h1N8@2$c@1$0#k0^1@4$h3~0?3sp0^1^4").
  Proof using sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC.   (* the argument list AsInstanceMain applies *)
    intros i s Hi Hs. change AsanUbsan.M.loaded_segments with ASEGS.
    assert (Hk : (i < length argv)%nat) by exact (nth_error_lt _ _ _ Hs).
    assert (Hn : nth i argv [] = s) by exact (nth_error_nth _ _ [] Hs).
    exists (bv_unsigned (cat_argv_ptr (ed_top rdraw) argv envp (in_execfn inp) i)). split; [| rewrite <- Hn; apply arg_string; exact Hk].
    rewrite wa_word0.
    destruct i as [|[|i]]; [ | | lia].
    - replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 0) with (sp0z + 8) by lia. apply arg_ptr0.
    - replace (bv_unsigned sp0 + 8 + 8 * Z.of_nat 1) with (sp0z + 16) by lia. apply arg_ptr1. lia.
  Qed.
End AT_MAIN.
(* [comment removed for export] *)
