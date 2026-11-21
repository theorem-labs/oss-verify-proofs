(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail Spec
  LazyRestrict LazySR LazyFdNodes LazySym.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib AsPrintfFirst AsSxKit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsRefused () := KReplay.lz_vm "#%LhC47Corelib7Program6Basics4flipC4ELinuxProcessSemantics?!s<22Fs4path!st,4Init5Logic8eq_ind_rC79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymAux7sregionC13~~~!t-,5Lists7!s+#Def3map!tJ86!tJ%C46Std!s]+4!s+#6nth_okK!uw,Numbers7BinNums8positive01!sKG2I!tO72eq00!s@29Datatypes4list00K8!v7N8SymExec23SX24expr02!v<%!smc1!smi3!sm&!vR<1Z02!t3]8sidecond!t~+!t7?3K!wBA1!wb<6option00!sh<3nat!u@_5sadd!w=f6kentry05!sok6!sok7!sok4!soV2Bs;AsStdioCall9s!s0#_res!yO5!xi:!y3=4prod!y1>!sF%!#3>=1N02I45stdpp9bitvector;defini!tK#s2bv!#3@3!#3Z$3an!tJ5!#3u+1K!s[<1C!{2<fstC!~W]s_pc!#7I2!t03sndC!x-^:!x-%call!t8&!ss^6sc_ret!soe4sc_f!sme5!sm#d!t]is!smil!uLiwb!snjp!snY7AsSxKit6kbytes!skbz!sk-!#9PA2!#5Ld!#8hk2!}R'!#3w>DZ_to_bv_obliga!s:#_1K!#4RC1K!#DS95Riscv5Instr5aluop!sRP:!v~=bool!srI;branch_!#>n#2!sxB2!sxT5!sXT1I!x;\!#A/+0!x=%!sq]!#C/$0!{-'!wZL7I!zId0!|K3!#C;5!#<f,!sD60!#H\F3!#C<@!zGO6!xST6!t+N9I!#5o]!#@b,!y&d9sym_state!sre7script!td+c!uZR9AsRefused5rf_rA!slc7rf_scs!sn&I!~eA0!t|ac!t|d6!t|#r!smhknA!wHgsc!wHgmsgZ!#:#%!#U`N4Spec;msg_r!sr%!yjhC!sldAEXIT!tZgc!tZ&!#HN\5s_log!vzV!#Y\%;log_cover!v|e:!v|#!#ZR#s!t_ZRun7vals_ev!sh&!#?k?;bv_unsignedC5!#[/%6ZArith6BinInt1Z2le!uI]3ENV!wiV=!wi'Sound4SX2S8sc_denot!uOG7!#Bo%C!#9D?3Sem5alu64K!#]|&9micromega6VarMap1!#X7#!sD>0!sD6=RingM!s4'7Formula00C!sQ55Tauto8B!sJ&!sH6:Z!sp+=Z!sT$CheckerC!te<4f!#`H-!sq8C!sq0_s!w-#!#_m8or!u/#!s@69False!#a[#!yR;3ad!sC=6modulo!#JpVcLibFbt_ne_and_add_lit_true!y5'!us49SatDivModCZ_mod_nonneg!s,&!xp@2!sD67Env!xU#5PE!#b##!#XaC!skF1!vJ<>pow_pos!t|&!}c>t!wS=pow!sC<:!t/#!v%<!tv27!sIE4!tU=sub!xb[@bt_ltu_not_f!z<#!#3bU!su-?!su&!yV&s!stege!stkDbt_eq!ss+!uegG!sy&!|@-!s|f>!}>&!ul1!xl;4la!#]cT!~Q/!u7&or!u63!}7,!#oH06Forall01!#9xb9scs!#9y0!#9SB<!#LI%takenK!#8vK1K!#8v;G!sJ'4!sJF6!#7]73not!}vE3!t-F8!sJF5!w]C2!v6D3Op201!#<&;5eKi!#:Z3!#K`,unit00!ty<4kind!#fx3!sf3!#g@84True01!#C,-!yh96images9AsanUbsan1M?loaded_segment!#^X'!v'G3!sMI5!|vS=AsPrintfFirst6ASP_LO!~|Y!sq6HI!sq%!#Ag5!#@#,;!#37$!t1$!#l495!#?_#!sC:!wZ%0!#9u<opp!#JM\6a_ba!#60W!sm1e!#3N-!sm\5a_of!#jb&!#L'U6r!tU-!#WZ\!#w4%!#WXc<!#Ln+_w!#6b&!x5&!$#e,2In!#7qb4flat!}$<!#5a16!vyW<!u?'!t8,!#8~@7Prelude5bv!$&q4!#D|,length!uwc7regs_ok!z@V!st7know!st,!$-yI5State5m_fds!sZQ9fd_lookupK!s^P7FdE!#m5$!s^K3Run6config01I!xvPLazySR4lzok!|%'!y_P<!sg#Restrict8r!s/&!soV8Prop!wx#7seg_rom!sjWSymDrive9junk_val!#Co&!#gS;app!t1P5Frame9f!s+#_mod!vQcEs!so#but_materialize!s|W!x8&8hid_!sz#!#4H<9nth_erro!$6oP9!v{'X8!|W$nth!}Ni9!#mP$!}P,!#T9;of_na!#PI34Znat5Nat2Z7inj_iff!#E%77iff_sym!sf>9i!#Qr&!#8n\?!#8n,!#6U+!sv]@!sv-!#<~-!#e9S1W!|aXhapeAlg6t_emi!#:,&!#<t[!#nD,1!yUV!#v/1ym_exec!soc5carry!uQ&!#<X4!#YY+3!x5]9!#na$!#:lX!#Bu0s!x~#s!}3jmem_!#CmZ!#d/6log!#?4-!#?{UA!#h{,_!#6g#!#4z&!~368!~3#refl!#N85;ZifyClasses3inj!sIB5mkre!snC;rew_!tB%v!#UwVxKit=!$-%$_rdn_sp!z5'!#?uOevent02!#;dX8blob!#kD-!#6'6f_equal!$I$;trans!#=xX5v_ad!#;&V7StepTac6u_Z2bv!shWLibTail7vadd_w!#t]V!#@7+alu!u?,!#5i\3env!$?Y9!#iS+2!z'S!$5v2!z#,!t0:1!#@S\I!#@S7!#GX#!tB$!$%9R<Ref!u3$Defs7s!#gz#t!#EuW!#C5$7outsid!#RoV3Lib2Nd:and_elimF3!skV!#Vh3A!uJ&_!#Dv2!wc13Nat!#n[#!#C-X@!#G+'_!#NN%!t3&!#DB4:!sG%_ap!$S-3Peano2lt!tSZ=!#x8%!t%#!$>rjsr!snikn!yi\D!x$+!#5`$!#HB-!|V\K!|V9!#6i$!t&U!#J1%>!#J1&!so0!z~`>rz_run_lf_lazy!wTe7sc_bufp!spe8!sp%sz!sqeE!$Jp+!#yq$!}j$!|S=9!{I#nil_r!#3iV;!#3i'1!#5@V!#:5'4mk!ts'I!#I`W8re!z7$!$7D'!#AIA7!#AI%!#k-E3!#BaD!#40#!sK@6!sK$2!v<Y3rd!~S&!t}F7!#kv;!$>c#0I!#C;I>!#^z#!sE+=machine!$<<'!u@O4Scfg=hunspe!zV#cf!$26&!#R5<6inj_lt!$44]FUELR!t6%!$9g]STOPS!smd4scr!skd!$:T#r!slg!#9;&I!#I8PModel!xjR!}Y+4TS!$WC&I!#b:X0I!#K7V!$A1]!$@C$F!yZd!w8$!sm&!$K4]s!$K4/!t^]7rf_covA!#6$;8ZifyInst7Inj_Z_Z!#<h`!{c#!u'k!$@qc<rf_itinera!#Y5&I!#Dl8e!$6\3!#FZ#sub!#8;A9and_morph!#aM;8max_spec!#yfC5Psatz!#}cE!sO&6!sO6!#xS:!$5O>3P!$W6$!tDI4!vH,7!u|&?Rel!$Yg#!s6&=eq_Tran!$R'$!$uL;n!$vp-!sr'9M!vl#isms:re!vU#tful!tAE<eq_Reflex!t@0!s|5Jr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^??eq!tM#per!tT;!sR,@!u$0per!#C@Yget!#LH&!t<>M!#K7$co_!$z[#v_impl!|2%ism!x{<seq!#9cQ!#O%%;nth_map_!sh#!#5=0!#F{,=!#F{#th2_plus!#cd\2!#],&!#55`!#rZ,!$&B;max!sC+5!sB$8!#4]#Na!#4L+!#B3<;inj_sub_!sm/!sM58!sM%cc!#B~Ce!#3tM1i!v<\3rfH!#YBW!$N9%6stk!#i<X!#:k38cells!#}%S!#Gu1@word_to_le_!$kE$!x`<div!#aePSeq!zX#9!}P#_zero!umg>!$$e%_by_idx!{Uc:rf_ev_jun!w[h9all!to#32!tgc5RF_F!#Hxc8rf_!y>$!zqV!#6Y'9u64_rang!$D5]xKit4sh!#[{'!{aakn!uL\!#_C+;!$-Q%!#`F#!~0\<kalign_int!{G+!smX!w#$!smc=kwr_of_!#3m/!snV:kimg!t[/I!#;`9!$C&&0!y'[7!y'#!tz`;k!#4r#!vX/!#5bX8store!tZ#!|5PAgentLib7!|5#li!%%-ZRefExitBase=!tW'_data!svV!#yR56estar!#_g=7f!x8$b!}Qa:!#:4$!|i#!t9'!#LB0!$B}$proj2!#@3]RF_OFFS!#3Sf9!u$#_wf_!%&&%!#>[\6rfP!#pz,!#:3`!$<l/!sqa!$<i0!{BO!#ku$B!#ku+!|0+!sr$k!vId1!uVc8rf!#h,$!#3F\7reg_va!#pmV!#Xe1r_ge!$<mW!#:2&5kread!}Z2!#fG9eq!$6k#!t6X9!t6$_!#fM'!uk^a!$5mZ!#<w,!sj%_lit!|I&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nil89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsRefused4FPX1~~~~~~k85AEXIThc3nat37Corelib4Init7Decimalpa2D0pa2D2pa3Nil37Corelib4Init3Nats0bof_num_uint37Corelib4Init6Numberu0bUIntDecimalhc4prodhc4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~hh16kentryhh14EVarhc3apphh12SAk85RF_FRhh14ELithh14KImghh13KWr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~hod6ASP_HIhod6ASP_LOhod8kn_cellsk87RF_OFFSk88rf_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsSxKit~~~~~~ih34shknhh16KAlignhh16KRangehh15KWord46Stdlib6ZArith6BinInt1Zin53opphc4boolhc4truehc5falsehh17scriptsk88rf_dirsAhh13SCRhh14exprhh18sidecond37Corelib4Init5Logicitb2eqitb3andhc3fstk85rf_schh19sym_statehc3sndhc4Somehc6option3h5LinuxProcessSemantics5Riscv5Instrjid7ALU_ADDk86rf_knAk87rf_msgZk85rf_rAk85rf_rC79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsStdioCall~~~~~~jnf9stdio_reshh14EAluhh14s_pc04Nposk85rf_cAk85rf_cCk87rf_scsAk86rf_srAjnf4sc_fjnf5sc_fdjnf4sc_ljnf6sc_retjnf4sc_sjnf5sc_wbjnf5sc_wpjnfastdio_callih36kbytesih36zbytes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~km5bmsg_refused35stdpp9bitvectorbdefinitionskqb2bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~kse7sregionhh15saddrk8arf_regionskseblog_coveredhh15s_loghh13env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~lk78blobs_evhh13Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~lp57vals_evkqbbbv_unsignedin52lek83ENV79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~lv49scs_denot69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~mk6floaded_segmentsin56modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsRefused~~~~~~mpd5RF_FRkqb7Z_to_bvin53sub37Corelib5Lists7ListDefmv73mapmpd3ENV89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsRefused5Sound~~~~~~nhccrf_regions_wmpdarf_regionskse6rdenotksecregions_flat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsnp9dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runnu15mkCfg3h5LinuxProcessSemantics5Riscv7Preludeoh65bvmap3h5LinuxProcessSemanticsfLinuxProcessSem5Stateok57FdEntryok55Model69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~oo78restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~ot24lzok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ph34mkstph37seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~pm1dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~pq98realizeslk79junk_valslv47know_oklv47regs_okhc6lengthok59FdChannelok55eventok59fd_lookupok55m_fdsmpd5AEXITmpd5rf_knmpd6rf_knFmpd5rf_srmpd6rf_srF69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~qn79frame_modoo7h5same_but_materializedot28hid_samepq94TSetpq96t_emitkm51Ws03sub37Corelib4Init5Peanoqvf2leqvf2lt89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AsRefused5Plain~~~~~~rhf7rf_valsph34getrhh12evin56of_natrhf3rfHrhf6rfPost" s.   (* [comment removed for export] *)
Import ListNotations.
Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition RF_FR : Z := 5600%Z.
Definition AEXIT : Z := 0x191274%Z.
Definition STOPSR : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "40!h9!jb!k2!oc@3$1$0+hporm0@3$1$0$3@1$2$0").
Definition FUELR : nat := 20000.

(* [comment removed for export] *)
Definition rf_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition rf_cells : ltac2:(zQ "40!hg3!h9!j4!p4@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!hg3!p4!hga!jb!k2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkig0N8+hppqsc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkjn8N8+hqijpc@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkjo0N8+hqinq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrthn8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul9N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+ikusvcN1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmti0N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtl8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtm8N8+hporm0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtn8N8+nhhrj0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmto0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtp8N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtq8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtqcN4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtr0N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvroi8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvroj0N8Z@1$5@2$1@2$1$0$2$0").

(* [comment removed for export] *)
Definition RF_OFFS : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0-ht0@3$1$0-hs3@3$1$0-jl1@3$1$0-jl8@3$1$0-hrb@3$1$0-hs2@3$1$0-hqb@3$1$0-hra@1$2$0").

Definition rf_kn : ltac2:(zQ "20!j4!hl0@1$0$1") := ltac2:(zQ "h40!hl0!jb!hla!hm2!hm8!k2!hme!hn6!hne!ho6!hte!hu8!hv2!hve!ig8!il0!il8!im2!imc!iod@3$3$0@3$1$0@2$h0@1$2N0+h0@3$1$0@3$h1@1$2N0$b$a@3$1$0@2$9@2$4@1$2N0@1$h3$6$6@3$1$0@2$8+hggg0+mngg0@3$1$0@2$8+hqqgg0+hrkgg0@1$5$0@3$3$0@1$f$d@3$3$0@3$1$0@3$h2@2$4@1$7Z+nhhjl8N8@1$2N1@3$1$0@2$9@2$4@1$7Z+hrmti0+u8@1$5$0@1$c$e").

(* [comment removed for export] *)
Definition rf_dirsA : ltac2:(zQ "20!ip4!j4@1$1$0") := ltac2:(zQ "50!ip4!jb!ipb!iq2!k2@3$1$0$3@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$3@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$2@3$1$0$3@3$1$0$3@3$1$0$3@3$1$0$3@3$1$0$3@3$1$0$3@3$1$0$3@3$1$0$3@3$1$0$2@3$1$0$3@3$1$0$2@1$4$0").   (* [comment removed for export] *)
Definition scrR : ltac2:(zQ "10!iqa$0") := ltac2:(zQ "50!k2!ip4!ir5!is0!is7@3$3$2@1$0$4@1$0$1").

(* [comment removed for export] *)
Definition rf_rA := Eval vm_compute in (sym_exec RSEGS FUELR true STOPSR scrR (SS 0x0beb04 rf_sr [] rf_kn 34) []).
Definition rf_cA := Eval vm_compute in (carry (s_log (fst (fst rf_rA))) rf_kn []).
Definition rf_srA : list expr := Eval vm_compute in (s_regs (fst (fst rf_rA))).
Definition rf_knA : list kentry := Eval vm_compute in (fst (fst rf_cA)).
Definition rf_scsA : list sidecond := Eval vm_compute in (snd (fst rf_rA)).
(* [comment removed for export] *)
Definition rf_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 rf_srA rf_knA with Some r => r
   | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end).
(* [comment removed for export] *)
Definition rf_rC := Eval vm_compute in (sym_exec RSEGS FUELR true STOPSR scr0 (SS (sc_ret rf_sc) (sc_sr rf_sc) [] (sc_kn rf_sc) 66) []).
Definition rf_cC := Eval vm_compute in (carry (s_log (fst (fst rf_rC))) (sc_kn rf_sc) []).
Definition rf_srF : list expr := Eval vm_compute in (s_regs (fst (fst rf_rC))).
Definition rf_knF : list kentry := Eval vm_compute in (fst (fst rf_cC)).

(* [comment removed for export] *)
Definition rf_msgZ : list Z := Eval vm_compute in (match kbytes rf_knA (EVar 0) (-464) 38 with Some l => l | None => [] end).

Lemma rf_itinerary : ltac2:(zQ "ie2!hg3!h9!j4!is7!isf!hga!iuf!iv5!ivc!jg2!jga!jh7!hn6!hl0!iqa!k2!hla!jhd!ip4!ji4!jl1!jlc!jm5!jmf!jn7!js0!jsd!jt5!jtd!oc!ju3!jub!jv3!jvd!kg6!kge!kh7!khf!ki9!kj1!kja!kk3!kl1!klb!kpc!ks8&@2$0@2$0@2$0@2$0$1$1$1$3$3&@2$0~0$3@2$7@3$6$1@1$hb@3$8$a@1$2$4@3$8@2$0$a@1$2$4$e$h7+hporm0@2$7@3$6@1$2$4@3$b$a@1$2$4@3$8@2$0$a@1$2$4$e$h7$i0@2$7@3$6@1$2$4@3$b@1$2$d@1$2$4@3$8@2$0@1$2$d@1$2$4@1$2$h2$he@1$f$4@2$7@3$6@1$h3$h9@3$i9Ni2$i1$h5@2$h1$h9$9@2$7@3$6@2$0~1$3@4$5~1$3@4$5~0$3@4$5@2$0@2$0@2$0$1$1$1$3$3@4$5@2$0@2$0$1$1$1$3@4$5@2$0$1$1$1@4$5$1$1@1$i5$9@1$i2$9@1$i3$9@1$i6$9@1$i4$9@1$i7$9@1$i8$9@4$5~1$3@4$5~0$3@4$5@2$0@2$0@2$0$1$1$1$3$3@4$5@2$0@2$0$1$1$1$3@4$5@2$0$1$1$1@4$5$1$1+hpprv4+hrmti0+2@1$cZ@1$cZ@3$ha$h4@1$h0N0@1$c-ht0@3$ha$h4@1$h0N0@1$c-hqa@2$7@3$6@1$h3@1$2$1@4$ia$h5@1$h0N0-ht0Ni6@2$h1@1$2$1$h6@2$7@3$6@1$2@1$id@1$hc#8@1$ib$h6$ic@2$7@3$6$1@1$hb@3$8$a@1$2$4@3$8@2$0$a@1$2$4$e$h8$hd@2$7@3$6@1$2$4@3$b$a@1$2$4@3$8@2$0$a@1$2$4$e$h8@1$f$4@3$6@1$2$4@3$b@1$2$d@1$2$4@3$8@2$0@1$2$d@1$2$4@1$2$h2$hf@1$f$4").
Proof.
ltac2:(KReplay.run1z (kr_t_AsRefused ()) ["FPX1"] "##zYp%0p%1p&0p;1p;3p;4p;2p;<p-1R0p10000R1p4p710p9P0P!s2$2!s3/3110p9!sQ$Np4p7!s\$1>!sZ%R1p8!s6$\!sA$!sy%2^!sw&8P!s6$3:!s6'!s4$V!s4%P1p8g0041j11Tg004Vj10Tg005;j3J!s/$Uj1oTg0065j1QTg007<j16Tg008Cj3ITg009Jj15!s/$hj4jTg00;3j18!s/$Qj1nTg00<1k10:!s0$Sj14Tg00=2j2BTg00>:k20UTg00?Ck30!sq$@Lk20=Tg00AUk20<Tg00B^m<0!tR$Clj2yTg00DNj2Z!s/$nj4rTg00ENk10N!s0$lk10LTg00FOj2M!s/$jj2\Tg00GDk40!ui$G_j3fTg00H<k109Tg00IAj3u!s/$^k30GTg00Jkk10FTg00L4k10ETg00M;k10DTg00NCk10CTg00OJk10HTg00PQk10!uU$QYk10!vG$Rak40!vu$Sfk10ATg00Tkj33Tg00UKj3!st$VTk20@Tg00W]k207Tg00XPk304Tf0R1#0#1p=9%11#0p==%11#1#0#0p=V%0!s0$#5p=E%01#8p=;g00Y3R0f1R2%613Ip=?%51#6p=>g00Y_R3?I21p=~g00ZKR4g00ZkR5P2P1Cjp>0>%8!sT$`g00[]R6g00\=!sD&=pP!s6$o!sT+3%1!tE$AP4P5f2R7%625I0!sT%7P4P5AI07!sd&c!t~$p=H!uB$#0p=bg00]aR5?321p>0PA35219357p>0Mf4R4f3R8!s;+535535p=<!uz$p=G!v&%!sz$X%01#5p>00%41#4p=w!s-$#4#4p=h!t?%!s[$}!vS%5#6p=Ng00^lR9%Q7%Q2=39133p=SA39219397p=t!s>&p>0?!w4'0p=F%1!t<%8!s;&p=C!uK&#1p=e!tg'!s$+p=R!s:+p=s!sq+!s$'p=m%0!sF+l!s2%0#0p>06!t#'0p=k!s_%!sK$|!s2+!tE%#1p={!s:'0p=q%81,B2p>!~?$`3?I87=I02=I31p=^1B87?D!w=$Sg00`_R3%58,B4?D72;31p=L%18!tn&5!s>&=331p=UA33219337p=z1B48!sA,2g00ahR0,B700@!s;&_B058!sH'd%88,B4%02!wL%7D7!s?%i!s?&Q2!s9+[!s9%!t,,:%08#!s91@!tt,!s?1P%0!s?9a%52#69D8!t4%>0R!tH&52!t],>0;!s<&6!t^+>02%1!tN3KP7P9!{v$rp=]g00bFR:A3:21737p>0O!s2$93:793:893:4p=T20721:0487p=Yf5R;20772:0448!wA$Of7f6R<!s<,=3;!zZ$WA37219348p=gP<P;P4P8P7P2P1H01H01p=vAJ872/M1p>0KAJ<;4!s7''Mp=xg00bdR1#1R8#0R7#0R2#1R<#1S00#0R;#0R4#9#9#=#V#ER==J:=%o5R>g00cIR?#QR@%17R7#1RA#1RB#0RC#1RD#;S01'?RE%>8RF'~%60R0+0!s^$hRG%`1RH7IE%01RI#0RJ#0RK#0RL#5S02#6RM'p%18!td$N#0RO#0RP#0RQ#1S03#;S04,?@RR/~FRS00>0AIGRH%>KRT'p%0!t_%U#1RV#0S05#0S06#;S07,?@RW=IGH/pT%0URU#0S08#0S09#;,?@,pRP6g00dTPWPECj203RW203S0RSPS%1NS0:#0RS#0R6#0RX#0S0;#8S0<,?@RY=IGH%>N'p%1KRN#1RH#1S0=#1RG#0RZ#0R[#0R\#AS0>%;\,?@R]57@S0?%1[R[#;S0@=7@]S0A%A[S0B!s3%C%1Z!sd&;S0D!s;%E!sH$F!s3%G!sH%;S0H!s7%I%AZS0J!s3%K%1G!tP-;S0L!s?%M!sj$N!s3%O!sj+P!s7%Q!sj$R!s3%S!sj,;S0T!s;%U!sH$V=7@]RZ!sG%;S0W!s6$[%AGS0X!s2$G%1J!xS$^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#;S0Y!sR$e%AdS0Z!s2$f%1cRc#;S0[!s6$g%AcS0\!s2$c%1b!sf$h#;S0]!s:$i%AhS0^!s2$h!sF%;S0_!s6$j%AbS0`!s2$b%1aRk#0Rl#0Rm#;S0a!s>$n%1m#`=c@]Rm%1lRl#0!s5&o%1l!s1&l%1k!sc$p!sD+q%1p!s1&p!sD&!s5&r%1k!s1&k%1`Rs#0Rt#0Ru#0Rv#;S0b!tG$w%AvS0c!s2$x%1uRu#;S0d!s6$y%AuS0e!s2$u%1t!sf$z#;S0f!s:${%AzS0g!s2$z!sF%;S0h!s6$|%AtS0i!s2$]g00eF%1I!sg$}#HR~#>%bs#;S0j,?@3I!}%%>'~0030RsQ0?Q0AQ0CQ0EQ0GQ0IQ0KQ0MQ0OQ0QQ0SQ0UPZP[PGPePfPgPcPiPhPjPbPnPmPoPlPqPpPrPkPwPxPyPuP{Pz%n5R5-0Ps:0M|]D<!s$MR];J]S0UAJ>55R|g00f2Rs$0:Rz%0ARA#1R{#1!vy$y#G#9S0S#0Rx#9S0Q#0S0O#0#ERw%5IRI%14R4#1Rk#0S0M#1S0K#G#X#=$00RrPY%1!~{$Rp#8,?@S0IPY%0~S0G#>S0EP0P0%08S0C#0Rq#0S0A#HS0?#8S0k,?@Rl%4?R?#4#wRo#4Rm#4Rn#wRb#wS0l#4S0m#hS0n#4S0o#4S0p#4S0q#4S0r#4S0s#4S0t#4S0u#4S0v#4Rj#4Rh#4Ri#4Rc#4Rg#4Rf#4#hRe%6r%heS0w#4RG%4G!s''6wR[%=JS0x#>%hGRG#Q!sD-!s'7bPS0y#9RJ#0#9#=#}#ES0z#6S0{%>1R1%=J#V#V#N%4G#w#h#h!sj2%n93S3S9Sgf9Sic9Sjh7t03t3S3S3S5t03t+0?3S9Smn7tl+0?P0%1xS0|!wp$0Rn#FPb%02R2!}P$0S0}#0S0~#;,?@S10P0PnPbPY!s]$!s/$@%1US11#8S12P?%5}RU#6S13P@Q06P?%0<R<!#8O$5RxP@Q05P?&08<R<#6RnP@%1VRVP?%1ORO#1S05#5Rh#6RjP@P!s>$SS14#5RV#6P@%0ARc#0RiP?%5;R;#6P@PiP?P!so$cRfP?%0OS15#5RO!sC$!s8$LRf#5Rg#6S1!sk${R{#0S17P?%1tS18#0RG#0S19#5RJP@P{P?PjP@Py!t$%PuP?%56Ru!tQ%CRnP?%1qS1:#5Rq!t5$!s8$2Rn$00Ry#6P@Q01P?Q!t=$1_S01#0S1;#CS1<PbP0P@PvPb%0QRv#1R_#=Rj#0R{#HS1=#1#NRZP@PdPbPMP@P\Pb%1{#9#NR{P@Q0=PbP[P@%0HRH!ss&HPbPZP@%0NRN#1RZ!s`&Z!sP'NS0=#1S1>#CPb%94#e#}P@%1L!};$!sY$#CPbP{P@PN!s['4R4Pb%>GP@P4Pb!#4K$1!sW$G#RS1?#1S1@#G#RRN#0#e#>P@%1fR{Pb%1N#sRN#>!vj$b%1^R^!sE$0!sE&k#9#V#9#NP@%ADS1AP?!#>u$5RD#6S1BP@%1BRk#0RMP?%5ARA#6RHP@%1M!s8%PR\#6RdP@%1kRkP?PdP@PkP?%5mRk#6S1C!w&$?%5nRv#6S1DP@P_P?%5BRB#6S1EP@Q04P?PHP@%CGS04!vj%%08R8#HRG#HPbPTP@%F4S1F!s2%Q07!sX&0{S07#C!vA$1Z#e#9#9P@Q1!xd$E!s0+DP@PpP?Q1CP@%0pRp!tx%Q08!wm$!u,%Z!sz%Q09#AS09P?Q1BP@P8!t_%Q15#HS15Pb%C4R4#CRH#m#N!vC$Q0kPb%8~!#5M$P@Q03#AR~!z8&Q0yP?Q0C!xM$5Rd!sr$Po%=G#F#l$06#l!u,&05#HRGPo%Gj#e#=#=$06#kP@Q0<Po%16#=!uX$=!w{$=#|!xH$Z!xW$S05#GRN#|#{!s$$9!sB-#s!y3&R#R!s=$GPbQ0M#0#G!sV$NP@Q0:!yg$CS0:Pb%0^R^!#8a$0RZ#k!yl%Q0;PbQ0{P@Q14!zf$0!sr%PlP@Q1:#CPbQ10P@Q0?Pb%8iRi,?@P0Q0Q#1#F!sV$0Q0O!s/'S#=Rl#1S0S#9RG#CPo%1N!tr%S0OP0%0!#?a$FPbQ0EP0Q0|#1R6#1PbPY1B0wRjPoPtP@Q0~!wj&06#0S06!yY'7Rt!tt&i!x3'8#1Ri!u3'Q!uc$8mS0:,?@RmP@Q19#0S19Pb%Q?S18P@%1}R}!uQ$0vP@Q0!vZ$u#QP@Q0x#HPbQ0tP@PaPbPm!~u-Q07Pb%l_!xF%APbQ04#b#eP@Q0bPbQ0OP@Q0>P?!tV%@!s/'B!s/'D!s/'F!s/'H!s/'J!s/'L!s/'N!s/'P!s/'R!s/'T!s/'V!s/'W!s/'X!s/'Y!s/'Z!s/'[!s/'\!s/']!s/'^!s/'_!s/'`!s/'a!s/'c!s/'d!s/'e!s/'f!s/'g!s/'h!s/'i!s/'j!s/%%1^PbQ!#:b$MPbQ1=#0#=#>P@%CZPb%8Q!||&1#1#=RZ!wT$1F!{>$qP@Q1;Pb%8X!sK%1<PbQ1>#k#9#q!{5%}!wz&19!s/%Pt!s-&2PbQ0pP@PfPbQ0o!~?&Q0n!xe%:Pb!~y$%8KR!sH$r#QP@PLPbQ0q!y:+sP@P`PbQ0m!#6}$Q0lP@PPPb%1i#=!}{$kQ02-0U@Q1?#0#s#X#F#m#m#E%5N605@%X}#FR}-0T@%5}+0=%5HQ00#=#m#E+0<%mp#EQ17#HRp#C#F!s;$PYPFQ1@#0RH!su$NR}%6fRfC^RN%G4R4#9#s#}#X#RRi#bRP#0#ER{%G4#R!s;$4#bR`!s;$L4051?@~PFP}PfC^R~P{PLQ09,?@!s:+2%qi#ERi%q4#ER4PW!s@+WPiP4Q1A!sT/4%1P#ERP%1`#ER`PR!s@+R!t&$12!sT/LPPP`PE!s6+f!s6$0Q0zPbQ18%5X-0=jP0%1pRp#H#F#EPbQ0K!#51%NH0S!sC'lPb%btRt#0#X#l#NP0%kp#FPb%1t#X#k!s8$HM#9#lPbP}P0%1M#G#q#VRM#0P?P1!s9$!s/&VZ#s#V!s3&06Pb%6=P0%1lPo%6IP0%bGPoQ05#>RG!#5B$1#FPoPGP0%1H#G#F#9RH#0!#5b$%1H!#5v$%n3DLDUDL!s+$!s-%!s6%U3zD29_fTCd9_L!s+$R!s+$4!s+$W!s+$2!s+$~!s+$NT3z3z3zDiD[!s$&2!s$$[D[D:!s$$@DPDiD:DPDa!sB&!s$_iDiD@D:D[D@!s&$:D:D2!s-%H0R!uK+L!s9$P!tM$@D@DaDPD2DiI0;I0!so%@!s8$@DKD:DKD@DKI0;D2!u&&2!s_$K!sk$@D2!u2$!s&':Di!s40!sX'K!ss'I0!s3'!s&&!tA%!w0$N<0Q,ysRN;JNRT1Z::R~/Z:R2/Z9RW/Z9R4/Z9RR/Z9R9P~P:!s$$rPwCrPICr=]20=]W0=]4YQ0I5]RRY;JYR0%o:RI$0:Rw&08nRn%5cRc&087R7%5SRSPgP7%5CRC%5QRQPVPuPg%58R8PdPgPAPBPvPkP\P\PAPDPgPyPqPuP<PhPJPgPOP<P;PVPhP<%n::0OxUDT!s$3,yIRr;JrRL&0NKRK$0LRf#oRbPfPKPn!s&$fPKPc!s&$fPKP7PKP7CYR7!s4$S!s&$fPKPgPKPgCYRgPfP!sB%C!s&$fPKPQ!s&$fPKPVPKPVCYRV!s4$uPKPuCYRuPfPg!s8$8!s&$fPKPd!s&$!s>'APKPACYRA!s4$B!s&$fPKPv!s&$fPKPk!s&$fPKP\PKP\CYR\PfP\PfP!sZ%D!s&$!sv'y!s&$fPKPq!s&$fPu!s4$<PKP<CYR<!s4$hPKPhCYRh!s4$J!s&$!sh'O!s&$fP!sP%;!s&$fPVPfPh!s<+x!s&$fPKPUPKPU%nfEOGWDgGWGWGWDgEO!s-'EOEO!s6%!s4%DgGWEOEORf;JfRUQ06!#Cx$!#T-%K=J:KRx1M||R<'MRh'MRV'MR;'MRO'MRg'MRJ'M1\:=Q0UPJ1\>]P|Pg1\>5RgPTPO1\zNP0P;1\9YPLPV1\wrPUPh1\bfPxP<1\:KP|P|PgPgH01Fv!s$%P:g00g@Rg1Zg>R|g00hLRKg00iV3fR<7f>$09P=P>Aug><g00j\P>%o3R31Z3>R<g00kd#oR=g00lD3f7u>P5Pzg00mJg00nQRz60Geg00oXRe,ysP!|_+&0Fe&0EeCr&0D!s+$Ce5]2&0He5]W&0Be5]4&0Ie5]RPYPwPzP@Q0<Q0wH0Jg010^R@,yIPb&0A@g011fP:g012j9f|KRK9fg>$09g0140!u5%KP5g01569f<=9u3>=J>5H0KFx!s$%do"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rf_regions : ltac2:(zQ "20!j4!lg7@1$0$1") := ltac2:(zQ "b0!h9!lh2!hg3!jb!hga!hme!hm8!k2!hn6!hla!iod@3$3@2$2$1$0@4$4$1$0@2$6@1$9N0@1$a$5$5@3$3@2$2$1$0@4$4$1$0@2$6@1$8Z+hrmti0+u8@1$7@2$2$1$0").

Lemma rf_covA : ltac2:(zQ "d0!ivc!j4!isf!jga!ip4!hg3!ipb!iuf!jmf!lhb!li8!lj7!iqa@3$7$4@2$a$9@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$8$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsRefused ()) ["FPX1"] "p;2p;1p;3g00Fjj26Tg005Uj15Tg00DNj21Tg00G_j30Tg016<j14Tg017Bj22Tg005;j33Tg00kdR0g00ZKR1'6g018Hg00g@R2g00]a#5R31123g00hLg00iV3030#4'2=301do"). Qed.
Lemma rf_covC : ltac2:(zQ "d0!ivc!j4!isf!jga!ip4!hg3!ipb!iuf!jn7!lhb!li8!lj7!iqa@3$7$4@2$a$9@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$8$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsRefused ()) ["FPX1"] "p;2p;1p;3g00Fjj26Tg005Uj15Tg00DNj21Tg00G_j30Tg016<j14Tg017Bj22Tg005;j33Tg00kdR0g00ZKR1'6g018Hg00g@R2g00]a#5R31123g00hLg012j3030#4'2=301do"). Qed.

Definition ENV : ltac2:(zQ "40!j4!jtd!lk0!ks8>4vals@1$0@1$3@1$1#k0$2") := ltac2:(zQ "70!j4!jtd!ks8!k2!lo2!loe!lse\4vals@1$0@1$2@1$1#k0@2$5@1$6^1@1$4@1$3@1$0@1$2@1$1#8").

(* [comment removed for export] *)
Lemma rf_scs_ok : ltac2:(zQ "h00!jtd!ks8!lt9!iuf!lu8!j4!ji4!h9!hte!hu8!lue!jv3!mj9!lse!mo0!mp3>4vals@1$5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$6@1$1@1$0#8>3sp0@1$1@1$0#k0>0@3$3@1$1@1$0#k0@2$d^3N0^1>0@2$4$9@2$2@1$0#k0^2>0@2$4@2$2@1$0#k0^3$8>0@3$3$7@2$f@2$2@1$0#k0^4+h0Z@4$c$e^6@1$a^7$b").
Proof.
ltac2:(KReplay.run1z (kr_t_AsRefused ()) ["FPX1"] "#$9;p'0h01bh11Hh21xh34__x1h47__arithh54__ffh68__varmaph75__with86__sat1h9!s/%2h:!s/%3h;2Hah<3Halh=3Hhih>3Hloh?1Mh@2P0hA!sO%0hB1ehC3sp0hD4valsi001zp%0p%1p%2p&0p;1p;2p;3p;4p;6p;7p;5p;8g004Vj13Tg00ENj1l!s/$lj1gTg005Uj1uTg00<1k10CTg019Sj2m!sB$;j3GTg01:Uj2TTg01;?j2ETg009Jj1F!s8$[j1xTg01<_k30Nj4{Tg0065k10LTg0041j12Tg007<j1HTg008Cj3ITg00;3j1d!ss$hj4Y!s8$Qj1pTg01=nj2KTg01>Tj3JTg01?<j1w!s/$Zj1vTg01@8k10M!s0$ck20KTg00Fjk20!sV$AEk20ITg01B1k30B!s0$Pk40ATg01CBj2q!s/$\k20@Tg01D;j2!s/%Xj2STg01E8j6oTg001>j64Tg01FMj2nTg01G>k20?!s0$\k20>Tg01H?k10=!s0$aj2jTg01IDk20<!s0$lj2^Tg01JHk20;!s0$ek309Tg01KIk308!s0$lk307Tg01LOj2i!s/$lj6\Tg01N;k706Tg01OIk705Tg01PWk40!ti$Qjk603Tg01S@j4:Tg01TMk202!s0$kk50!s:$V@k201!s0$ak400Tg00Tkj3~Tg01X1j3c!s/$`j4bTg01YKj7r!s/$oj7}Tg003:k60DTg01ZSj1s!s/$lk30ETg01[Oj8zTg01\3k70G!wX$Ok20H!s:$Wj6yTf0R0#3#3p=Pg00bFR1f1R2/S0g00ahR33Gp=|%20#2p=W%3!s-$a%30#dp=<g00Y3R4%H07I2p=Qg00ZKR5g00ZkR6P2P0CYp=kg00[]R7g00\=R8!s='XP!s8$oS00!s9'_%20#3p=]!t?$#2#2p=h%2!t;$?P5P6f2R9%H25I4!sW%;%30#Fp==g00]aS01?~20p=11K209J49p=Rg00kdR:Ac620;G5p=f1j10p=CP1P2g01]8P0Cbp=e!s4%_R;g01^>R<P<g01^^R=P0g01_>R>Frp=OP9P;P<P<P=P2P0F}p=tAG:05p>0FAG103p=7P1P9!su$_^P3P0J0Dp=6!sC$#sp=`g01`:S02P9!uo${p=5Ac920=G:7p=N1E30p=D!uz+!s$'p=V%3!ws$#3p=[!tW-!u@%aEP0CbP!tu$BB0E120p=Lf3R>!sO+!t?$Gzp=A!sZ'l!ut%U!uM1K0Gp=Z1E391^20+0Hp=M1i92/S0=G1!u<$81K929J4>=c60=G:5p=9%2!wT$>Q01f4R6P>!t?%Eyp=0g00bdR4#3R;#3R?#3R@#3RA#PRB#lRC#gRD#u%l@#g$0C\Dg00cIRE,m9=GD0g01bS1TC2'E1TC9g01c^!s1$>%FARA'|Q02f5RFf6S03#xRG40NRHg00Y_RI&0LERJ%24RK#3S04#2RL#W#a#<RM'QRN%FKRO#HRP3I%H3RQ'kRRg00chRS%d4RT#HRU7IN%HA'XS05%2KRK#3RV#P!sj$W,QJRX=IIPRP/kQS06AISXU%F@RY#HRZ'XS07%aLRL#2#P#<R[,QJR\=ISU/XZS08%3L!s>$L,QJ,XXS09!|$$dTS0:P\PNCYS0;1_X\S0<1_PQRP%]V!sX$\,QJ=ISU%FVRV#H'XS0=%h@!vx$U#3RX#3RN#?S0>%<NRN,QJRZ5;JS0?%2XRX#<S0@=;JZS0A%?XS0B!s3%C%2U!sf&<S0D!s;%E!sH$F!s3%G!sH%<S0H!s7%I%?US0J!s3%K%2!tR/<S0L!s?%M!sj$N!s3%O!sj+P!s7%Q!sj$R!s3%S!sj,<S0T!s;%U!sH$V!s3%W!sH%<S0X!s7%Y%?@S0Z!s3%[%]?#P!y~+!v+']#<S0\!sI%]%?]S0^!s3%_!v0+`!s7%a!tz$b!s3%c!v00d!s;%e!sH$f!s3%g!uD+h!s7%i!tz$j=;JZRU!uC'!tQ+k!s>$^!tP$l!s2$]!tO+m!s6$_!t+$n!s2$X!sf'`#<S0o!s:$a%?`S0p!s2$`!v%+q!s6$b!v$$r!s2$@%2?!u}$c#3Rd#3Re#<S0s!sB$f%?eS0t!s2$e%2dRd#<S0u!s6$g%?dS0v!s2$d%2c!sf$h#<S0w!s:$i%?hS0x!s2$h!sF%<S0y!s6$j%?cS0z!s2$Zg00eFS0{%2;#P#=Rc#H%2?#P#<S0|,QJ3I%2KRJ#FR?#H5II/_QRQQ0?Q0AQ0CQ0EQ0GQ0IQ0KQ0MQ0OQ0QQ0SQ0UQ0WQ0YQ0[Q0]Q0_Q0aQ0cQ0eQ0gQ0iQ01#pS0},1QS0~,1ZS10,1jS11,1hS12,1iS13,1dS14,1gS15,1eS16,1fS17,1@S18,1bS19,1`S1:,1aS1;,1XS1<,1_S1=,1]S1>,1^S1?,1US1@'1S1A'1S1B'1S1C'1S1D'1S1E'1S1F'1S1G'1S1H'1S1I'1S1J'1S1K'1S1L'1S1M'1S1N'1S1O'1S1P'1S1Q'1S1R'1S1S'1S1T'1S1U'1S1V'1S1W'1S1X'1S1Y'1S1Z'1S1['1S1\'1S1]'1S1^'1S1_'1S1`'1S1a'1S1b'1S1c'1S1d'1S1e'1S1f'1S1g'1S1h'1S1i'1S1j'1S1k'1S1l'1S1m'1S1n'1S1o'1S1p'1S1q'1S1r'1S1s'1S1t'1S1u'1S1v'1S1w'1S1x'1S1y'1S1z'1S1{'1S1|'1S1}'1S1~'1S20,1PS21'1S22'1S23'1S24'1S25'1S26'1S27'1Rk'1PDP6AR0CMS281KCOS295JI1KC3Rl'fX0DP6PMPOP0g01diRm#pRn%umRm%w1Ro%v1Rp&0M1Rq%CORr/er,Oq%FKRK#C,!s3%C?!s/%5tq3t20Kq=R=P0P920J:520I09$0FdB0B132H0AR:b5b6b7AG1OOAG1OKAG1O?'q'qP0b4S2:%F;R;#7P1p-0!tf$eURKg01f2R5PKn01100000300!s/$!s'$XB1Rr=6;0PK20@K0Rsb1W2S2;%F4Rt,@OS2<,SM#`dEoQ03/mEREP>E4A5FGRePHQ05PkPDP6Q!vE$TRT5JS1KCA5N8!vC'A1TC6Rk/nAS2=%Dk%DARRQ03,TCRu/SA#D[[S2>PnPm20?12RvPpPq%2J#W#VRJ#3#W#h#]#P#[!s$+=S2?#C20>14R45BqRw&0=<R<1j13Rx%CMS2@,L4S2A5BqS2BCAP=P!v`&X31Q2?/E0Ry1@2MS2C#D[^31P0PuP6O2S2Db4b8%FBRB-0<;Rz1^3;%DB20;;BR{,^3[[R3%D;R|B09;B2V5W;RB%D{\5^;|R|1nuAR5%Duf8,TCS2E!u\$\R[RuPnPmP!uW%VJ#V#V#VS2F#FRJ#C9Bq4R}P<Q2A%CAS2G'L%C;>081CR;%Ct6071R~5Bq!uD21E0JRJQ2C/@A1i{tRt'E!uG%Q2EPFO2S2Cb4b8b9b:!tN$oPpQ2G9Bqx!sn,PRP0b4E\P!xN$Q0595FG!xP$6Q27!{u'WRRQ!{p$S29/fl!xQ%WPOP0Q2:Q2;Q2<,SW#`dS2<Eo!sr'6!sr+7Q26!sr$JSRT1KCYS26!yA+WPYQ2=Q!xy%!vC%PwP<%CWS06!x<$;9BqxS27!uw3@2WS05#D\y^31Q!x-%PzP3PBP|P5P!w<-P!v~$;%CYRA'L=Bq~!y1305/@Y/Et\J!sr$!vX4ABqx!sY-%DY!}6$05!vZ,7!uf+8Q25!vZ'[S25=JSTQ!ui-[!ui;[S2!ui$07!ui%G!ui5[S2H!uiL07/LA!ue72H!ue9Q!uG/8!uG+9Q24!uG'L9N8R!x%'LP7!tM=!uL%Q27Q2;/U;,Oq5ZqCA!}L72RA1@9WS2?Q2?;M{[!tg$!{1&Q03O3S03!ts'1@kWS2EQ2E;M{e!tNC%CLS2E!y_$?9BqxQ2?!t[=1@9L!tS+\A!v=%!tH0!sE,e!|d,EQ065Bq!sq,1ELWRLP0b4PLeK06!vq'9!vq+;Q23PDP6Q0:Q25Q283N!y3'M!vsGGQ07!u>@[R7?M7!u;9!sB&!vZDQ2BQ2A!t5@MR9?M9!t59MRk?Mk!vG/6Q2@'U,O!vI/^[MRM!vI$MeK05!vI';!vI+<Q22!vI%0Q257N!z<+[Q04#3#]#W#=RR#7A6Rr0PKPsb1W2A8W[{dH04!sw'<!sw&PPQ21!sv+9;N!#5#3<J03P!#;8'PeRO!s\%0POPHQ0=Q1~!{t'\=JST1KCV!~;+\PV!~;9\,L4R49Bqx!~45\R\!~3K%CVR<,L4!~561@\V!#4rA<!#4r-V!#8K0=!w8+?Q1}PDP6P0PCQ0>AR0CNRVC9!uX$Q0>PNQ2F#2#W#VR<#2R1#2RJ#2Rt#2R\#2R~#>R4#7A64!wV,Q0>?8N{dC:!t>'?!t>$S0>PHQ0AQ1|!tA,@P!t<,@PN%=~R~#7A6~!sv/@!sv2A!sv&@PHQ0CQ1{!sv,B!sv-BPN%3\R\#>!sz6B!sz2C!sz&BPHQ0EQ1z!sz,D!sz-DPN%=\R\#7A6\!sv/D!sv2E!sv&DPHQ0GQ1y!sv,F!sv-FPN%3t!vn&!tv7F!s~2G!s~&FPHQ0IQ1x!s~,H!s~-H!tv;H!sv2I!sv&HPHQ0KQ1w!sv,J!sv-J!tv'>!sz6J!sz2K!sz&JPHQ0MQ1v!sz,L!sz-LPN%=tRt#7A6t!sv/L!sv2M!sv&LPHQ0OQ1u!sv,N!sv-NPN%3J!z^-!vn7N!t&2O!t&&NPHQ0QQ1t!t&,P!t&-P!vn;P!sv2Q!sv&PPHQ0SQ1s!sv,R!sv-R!vn?R!sz2S!sz&RPHQ0UQ1r!sz,T!sz-T!vn;T!sv2U!sv$RtPHQ0WQ1q!su,V!su-V!vm,!vi9V!s}2W!s}%~PHQ0YQ1p!s},X!s}-X!vh;X!su2Y!su%\PHQ0[Q1o!su,Z!su-Z!tt'!#476Z!sy2[!sy%4PHQ0]Q1n!sy,\!sy-\PN%=JRJ#7A6J!su/\!su2]!su%!{M$_Q1m!su,^!su-^PN%31R1#2R}#2Rv#2Ru#>R5#7A65!t,/^!t,2_!t,%5PHQ0aQ1l!t,,`!t,-`PN%=uRu#7A6u!su/`!su2a!su%uPHQ0cQ1k!su,b!su-bPN%3vRv#>Ry#7A6y!sy/b!sy2c!sy%yPHQ0eQ1j!sy,d!sy-dPN%=vRv#7A6v!su/d!su2e!su%vPHQ0gQ1i!su,f!su-fPN%3}!vj$2#>Rw#7A6w!s}/f!s}2g!s}%wPHQ0iQ1h!s},h!s}-hPN%=2R2#7A62!su/h!su2i!su%2PHPUQ1g!st,j!st-j!ts'>R8#7A68!sx/j!sx0A5FGUeR8PHP^Q1f!sv,k!sv-kPN%=}R}#7A6}!sr/k!sr4^eR}PHP]Q1e!sr,l!sr-l!zO,T#2RS#>RO#7A6O!s~/l!s~4]!#AU$_Q1d!s~,m!s~-mPN%=SRS#7A6S!sr/m!sr4_eRSPHPXQ1c!sr,n!sr-nPN%3TRT#>RP#7A6P!sv/n!sv4XeRPPHPaQ1b!sv,o!sv-oPN%=TRT#7A6T!sr/o!sr4aeRTPHP`Q1a!sr,p!sr-p!v^,W#>R[#7A6[!sz/p!sz4`eR[PHPbQ1`!sz,q!sz-qPN%=WRW#7A6W!sr/q!sr4beRWPHP@Q1_!sr,r!sr-r!tn'>!#GR3Q0r!sv4@eRRPHPfQ1^!sv,s!sv-sPN%=1R1#7A61!sr/s!sr4feR1PHPeQ1]!sr,t!sr-tPN%3<#WR<#2RM#2Rk#>RA#7A6A!t$/t!t$4eeRAPHPgQ1\!t$,u!t$-uPN%=kRk#7A6k!sr/u!sr4geRkPHPdQ1[!sr,v!sr-vPN%3MRM#>R9#7A69!sv/v!sv4deR9PHPiQ1Z!sv,w!sv-wPN%=MRM#7A6M!sr/w!sr4ieRMPHPhQ1Y!sr,x!sr-x!v`$!v^$7#>RL#7A6L!sz/x!sz4heRLPHPjQ1X!sz,y!sz-yPN%=7R7#7A67!sr/y!sr4jeR7PHPZQ1W!sr,z!sr-z!xP%>R<#7A6<!st/z!st4ZeRNPHPQQ1V!#Ng&0{1KCcQ0|9R0C3J1KC?5JI!#N{'cQ0|!#MJ'!#L^%%CcRp9Bqx1Up!#Qx%!#Ll+AMcc{P0b4bAb8%7YA6Y!tb,202c?#`dI0!tc-QeR>!#M3%UQ!#K{'TQ!#K6'SQ!#JE'RQ!#IX'QQ!#Hc'PQ!#Gv'OQ!#G,'NQ!#F@'MQ!#EG'LQ!#DZ'KQ!#Ci'JP!#B|&IP!#B/&HP!#AB&GP!#@Q&FP!#?d&EP!#>g&DP!#=z&CP!#=1&BP!#<D&AP!#;O&@P!#:b%?P!#9s%>P!#90%=P!#89%<P!#7N%;P!#6_%:P!#5t%9P!#5%%8P!#4>%7P!#3O%6P!~d&5P!}k&4P!}$&3P!|9&2P!{N&1P!z[&0P!yp%0~P!y'%0}P>Q01001HD0!s$~!s$|Q02PFPGg00j\H00RGePGeW<W=W>W@XCDW?WDo"). Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variables (L S Zr : list (word * word)).

  Definition rf_regions_w : ltac2:(zQ "50!j4!hg3!jtd!h9!ks8@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "b0!jtd!h9!ks8!hg3!jb!hga!mtc!mu5!k2!mv0!lt9@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$7@1$0#k0@2$9@2$a@1$0#k0?3sp0$6$6@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$7@1$0#k0+hrmti0+u8@1$8@2$3@1$2@1$0#k0$1").

  Lemma rf_regions_denot : ltac2:(zQ "h00!jtd!ks8!j4!hg3!iuf!h9!nge!hu8!nh5!nm1!nn1!nnf!lg7!lse!lu8!lt9>4vals@1$2@1$1@1$0#k0>0@3$4@1$1@1$0#k0@2$d^1N0?3sp0>0@2$e$7@2$f@1$0#k0?3sp0@3$4@1$2@2$3@1$1@1$0#k0$5@4$6$c@2$3@1$1@1$0#k0$5@1$b@1$8^3$a$9").
Proof.
ltac2:(KReplay.run1z (kr_t_AsRefused ()) ["Sound"] "##/Bh03Hloh12P0h21bh31rh44valsp;1p;2p;3p;4p;6g004Vj14Tg00ENj1K!s/$lj1CTg005Uj1ATg019Sj2?!s8$;j37Tg01:Uj28Tg01;?j2ETg00DNj2;Tg0041j10Tg009Jj19Tg01fNj1PTg01D;j2:Tg01=nj25!s\$nj43Tg00;Qj1>Tg00Tkj36Tg01LOj2OTg00Fjj2NTg001>j6M!tC$[j1<Tg00G_j3J!t1$kj1ITg01h2j2FTg01i9j1GTg00IAj3HTg0065j1DTg00=2j2@Tg007<j1LTg002^j4=Tg01j?j1BTf0R0#4#4p=1%00#4p=2g00bdR1#4R2#4#1#1#KR3#CR4#Ag00cIR5,?0p,3sp0R6574g01bS1836R7'EP4P6g00bFR6,;4R8#AR9P4P61830%22#0!s$$2!s}$9R2#PR:':,53P2C3!sb&ahR;,53,83%01R1#4!sW$!s&,1!se+<!sa$%2!s8%9R1C3%>8R=568568!tE$O72!t+-153<P1C3=68=568R=37X241N9=f2R7/?5f1EMg001\R>P!sg$f3#<g01k@R4?J60R?#I'F,83%G?!tK$AH460C3X3>1;46R0P4P6%D5/@:!tB'%L;/@!tD$%>056036C==79=eP>P8%<7#Bg018HC=g01lH579eW0W1W4o"). Qed.

  Lemma rf_regions_flat : ltac2:(zQ "c0!jtd!lu8!ks8!lt9!j4!iuf!hte!hu8!nh5!nn1!no9!lse>4vals@1$4@1$2@1$0#k0>0@3$5@1$2@1$0#k0@2$b^1N0?3sp0>0@2$1$7@2$3@1$0#k0?3sp0>0@2$1@2$3@1$0#k0?3sp0$6@2$a@1$8^4$9").
Proof.
ltac2:(KReplay.run1z (kr_t_AsRefused ()) ["Sound"] "##<sh01Hh11rh22Hah37__arithh44__ffh56__sat1h68__varmaph75__with84__x1h93Hhih:3Hloh;2Hrh<2P0h=!s_%0h>!s/%2h?1bh@4valsp;1p;2p;3p;4p;6p;7p;8g004Vj11Tg00ENj1g!s/$lj1bTg005Uj1XTg019Sj2V!s8$;j3JTg01:Uj2CTg01;?j22Tg01mUj3dTg0065j1aTg0041j10Tg009Jj19Tg01fNj1sTg00=2j2MTg00Dnj4STg007<j1iTg01CBR0j2N!t&$[j1;!t&$lj36Tg01D;j23Tg01JHj2cTg01Ilj27!s/$Dj2`!sA$ej3_Tg00;Qj1^Tg01G>j2]Tg01?Zj1\Tg01@8j1[!sA$\j2ZTg01H?j1v!s/$aj2WTg01o7j2uTg01Zlj3FTg01KIj3tTg01X`j4H!sn$cj2rTg00Fjj2qTg01AEj2pTg01B1j3o!s/$Pj4nTg001>j6j!u}$kj1RTg01h2j2QTg01i9j1LTg003:j6O!ty$<j1k!tU$Zj2hTg00G_j3lTg00IAj3m!tC$Oj2ITg01YKj7PTg01\3j7fTg01[Oj8eTf0R1#!s$&p=4%11#0p=D%0!s-$G%0!s>$Eg001\R2f1R3;J1p=>%1!s?$Kg01k@R4g00bFR5;l1p=<Am451p=8g00ahR6/21p=:f2R71I31'Ip=@1263/I1p=A!t7$#0#0p=Y!s2+!s$'p=B1W51p=?P7g01]_R8g01^>R9P9g01^^R:P5P3g01aEP1CHg01_>R;FPp=5P3P8P9P9P:P1P!s9$UP7!s9+3P1Ffp==f3R;!s;+7P3P1Gep=Tg00bdR8#1R<#1#4R=#gR>#bR?#Xg00cIR@,V1p,3sp0RA5J?g01bS1C>ARB'2g01c^,2Bg018HRC9d21P0P4P5%a@%0<#D#G#E#4#9RD#sRE'MPDCSRF/>3!sK$i6%08R4#1#G#D#E!s+$K!sW&G'M%04!sC$E#K#9RHCSRI/>3g01eURJ'Nf6RK#;%<7%8736P11>F7P2PFf8RL#;RM%<1RN%81RO36X12P?PA1C>1/3ERA%9<R<%9=R='cRP,7A%:DRQ13AD/2P3@'AX??1`<=R?176<%:=176P[[RA%:<RRg01f2RSA_<=3UW2R=%:P\S^2R!sA$diRS#^RT%XSRS1]53%\5RU%[5RV1Z58R8%Y4#BR4#B!s$&9RW#?55V%v9R9PV%D4#G#Y#4!s$-9R4#?=5V8P91W56R9%?DRX,u59F58R855VP5P8g01alRY%?<=t5>R<CH,UVA5V9XAF58X=5V<5=V!s%%CTCT1rV:R:P1P7g00kdR8g00ZKRX'q1p17=J8XdAo563CnRXb4b6b7X85121W1243137ERE17EP13ED/2P7@Q'A[[^85P1PBf7RBPLO3b3b5b>1VB@PKEj%;BRB%<FR@#R'Q,C>%L@'3RL17LP%8FRF#:13LF!wK&eA6B@FeP;P1EOW0P1O11>I7/NJP01>I;PJf4R0#<%8056MP11>I0P2PIf:#;R0?6NO!xf&P=PRPTPS%k5PU%?G9F59RU95V9P5PUPYP!vI%%?HRY95V9AF5UY!vM0P:P!uy&136GRG17GP%:H13GH!t{&P1b3b=b5f9#;RG%<IRH!uZ+H'3R>17>P%8IRI#:13>I!uZ,GHIef5RI!u\,PJ%<K%8K560P1n010!s#%X0JP1O1n20!s9'2110!s3&!s`%!sB51000%;I%<3%8336eW;X12%;;/hCeW9W:W<W@o"). Qed.

  (* LPS 75d69e00, the channel-reader premise.  stdio_call_sound_post gained
     [m_channel_reader mo = true] in Bs/AsStdioCall, so this file's replayed
     application of it is one argument short.  Measured before the edit, cold single-target
     from a verdict-grade staging (SOURCE: a clean tree, image 2c6b6db8):
       VOS-FAIL Bs/AsRefused.v - Illegal application: "@stdio_call_sound_post" at line 129
     Two sites, rf_sound and its Plain wrapper as_refused_k.  Unlike Bs/AsHdrErr this file has
     NO hf_sound-style Ltac, so both proofs are written out; unlike Bs/AsStdioWrite nothing is
     decoded beyond these two statements.  Every other replay here is untouched and NOTHING IS
     RE-ENCODED.  Statement faithfulness is measured, not asserted (see the commit).
     DONOR, statement and proof, with its branch (rule 23c):
       a donor tree:projects/openssl/echconfiglist_parser/
       proofs/lib/Both/As/AsRefused.v:160-290 and :340-387. *)
  Theorem rf_sound : forall vals R M msF mo (KX : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) rf_sr R -> know_ok RSEGS (ENV vals) M rf_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0xbeb04) M (seg_rom RSEGS) ->
    KX [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) rf_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' rf_knF ->
       frame_mod M M' rf_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 AEXIT) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') KX) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_refused) KX).
  Proof.
    intros vals R M msF mo KX HL P0 HR HK Hfd2 Hrd2 OK RS HKnil HCONT.
    pose proof (know_nth RSEGS _ _ rf_kn 1%nat _ HK eq_refl) as Hrg; cbn [kentry_ok edenot ev ENV] in Hrg; rewrite P0 in Hrg.
    pose proof (know_nth RSEGS _ _ rf_kn 0%nat _ HK eq_refl) as Hal; cbn [kentry_ok edenot ev ENV] in Hal; rewrite P0 in Hal.
    unfold ASP_LO, ASP_HI in Hrg.
    pose proof (rf_regions_flat vals P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF.
    pose proof (rf_regions_denot vals P0 ltac:(unfold ASP_LO; lia)) as RD.
    pose proof rf_itinerary as (PCA & SCA & CCA & SC & _ & KB & MSGEQ & PCC & SCC & CCC).
    eapply (rz_run_lf_lazy RSEGS L S Zr FUELR STOPSR scrR 0xbeb04 rf_sr rf_kn 34 (fst (fst rf_rA)) (snd (fst rf_rA)) (snd rf_rA)
              (fst (fst rf_cA)) (snd (fst rf_cA)) (snd rf_cA) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ rf_rA) | vm_cast_no_check (@eq_refl _ rf_cA)
      | exact HR | exact HK
      | rewrite SCA; apply (rf_scs_ok vals M sp0 P0); unfold ASP_LO, ASP_HI; first [lia | exact (proj2 Hal)]
      | rewrite CCA; constructor | exact OK | exact RS | ].
    clear HR HK. intros RA MA msFA moA HR HK EQA LFA OKA SBA HSA RSA.
    pose proof (log_covered_frame (ENV vals) M rf_regions _ rf_covA RF LFA) as FA. rewrite <- EQA, RD in FA.
    change (s_regs (fst (fst rf_rA))) with rf_srA in HR. change (fst (fst rf_cA)) with rf_knA in HK.
    rewrite PCA in RSA.
    pose proof (kbytes_rdn_sp (ENV vals) MA rf_knA 0 sp0 (-464) 38 rf_msgZ HK P0 KB ltac:(lia) ltac:(lia)) as MSG.
    rewrite MSGEQ in MSG.
    unfold W. rewrite <- (app_nil_r msg_refused).
    apply (stdio_call_sound_post vals (blobs_ev []) rf_srA rf_knA RA MA L S Zr msFA moA rf_sc msg_refused [] KX
             HR HK (eq_trans (f_equal (fun n => stdio_call n rf_srA rf_knA) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn rf_sc edenot ev ENV app];
      change (@length byte msg_refused) with 38%nat; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ].
    - rewrite P0, !alu_add, !vadd_wZ. unorm. lia.
    - rewrite P0, !alu_add, !vadd_wZ. unorm. lia.
    - rewrite P0, !alu_add, !vadd_wZ. unorm. lia.
    - reflexivity.
    - lia.
    - right. rewrite P0, !alu_add, !vadd_wZ. unorm. lia.
    - left. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite P0, !alu_add, !vadd_wZ. unorm. lia.
    - change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. lia.
    - rewrite P0, !alu_add, !vadd_wZ. unorm. replace (bv_unsigned sp0 + -464)%Z with (bv_unsigned sp0 - 464)%Z in MSG by lia. exact MSG.
    - reflexivity.
    - rewrite (same_but_materialized_fds _ _ SBA). exact Hfd2.
    (* LPS 75d69e00: the reader premise, transported through the same materialization as the
       fd one -- donor Both/As/AsRefused.v:216. *)
    - rewrite (same_but_materialized_reader _ _ SBA). exact Hrd2.
    - exact OKA.
    - exact RSA.
    - exact HKnil.
    - clear HR HK. intros Rj MC msFC moC HR HK HPOST OKC SBC HSC RSC.
      assert (FC0 : frame_mod MA MC rf_regions_w).
      { eapply sw_post_frame_mod; [exact HPOST|]. intros x Hx. unfold rf_regions_w, RF_FR in Hx. cbn [outside] in Hx.
        unfold in_rng in Hx. rewrite P0, alu_add, vadd_wZ. revert Hx. unorm. intros (N1 & N2 & _). lia. }
      set (vals' := vals ++ junk_vals Rj) in *.
      assert (HL' : length vals' = 66%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      pose proof (rf_regions_flat vals' P0' ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF'.
      pose proof (rf_regions_denot vals' P0' ltac:(unfold ASP_LO; lia)) as RD'.
      change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK.
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELR STOPSR scr0 0x199bf4 (sc_sr rf_sc) (sc_kn rf_sc) 66 (fst (fst rf_rC)) (snd (fst rf_rC)) (snd rf_rC)
                (fst (fst rf_cC)) (snd (fst rf_cC)) (snd rf_cC) (ENV vals') MC (seg_rom RSEGS) _ msFC moC);
        [ vm_cast_no_check (@eq_refl _ rf_rC) | vm_cast_no_check (@eq_refl _ rf_cC)
        | exact HR | exact HK | rewrite SCC; constructor | rewrite CCC; constructor | exact OKC | exact RSC | ].
      clear HR HK. intros RC MF msFF moF HR HK EQC LFC OKF SBF HSF RSF.
      pose proof (log_covered_frame (ENV vals') MC rf_regions _ rf_covC RF' LFC) as FC. rewrite <- EQC, RD' in FC.
      change (s_regs (fst (fst rf_rC))) with rf_srF in HR. change (fst (fst rf_cC)) with rf_knF in HK.
      rewrite PCC in RSF.
      apply (HCONT Rj RC MF msFF moF HR HK).
      + eapply frame_mod_trans_same; [exact FA|]. eapply frame_mod_trans_same; [exact FC0 | exact FC].
      + exact OKF.
      + eapply same_but_materialized_trans; [exact SBA|]. eapply same_but_materialized_trans; [exact SBC | exact SBF].
      + eapply hid_same_trans; [exact HSA|]. eapply hid_same_trans; [exact HSC | exact HSF].
      + exact RSF.
  Qed.
End Sound.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variables (L S Zr : list (word * word)).

  (* [comment removed for export] *)
  Record rfH (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z) : Prop := RFH {
    R2  : getr regs 2 = sp;
    Rsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    RspLo : (ASP_LO <= bv_unsigned sp)%Z;
    RspHi : (bv_unsigned sp <= ASP_HI)%Z;
    Rstk  : stk_ok RSEGS mem sp RF_FR;
    Rimg  : forall i, (0x10000 <= i < 0x67000)%Z -> mem (Z_to_bv 64 i) = None;
    Rgot  : forall i, (0x1aa000 <= i < 0x1b4000)%Z -> mem (Z_to_bv 64 i) = None;
    Rcells : cells_ok mem rf_cells;
    Rcan  : rdn RSEGS mem (Z_to_bv 64 0x711358) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Rcan64 : (0 <= can < 2 ^ 64)%Z;
    Rsh0  : forall a, (2147450880 + (bv_unsigned sp - 4096) / 8 <= a < 2147450880 + bv_unsigned sp / 8)%Z ->
              mem (Z_to_bv 64 a) = Some (Z_to_bv 8 0) }.

  (* [comment removed for export] *)
  Record rfPost (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := RFP {
    P_sp  : getr regs' 2 = sp;
    P_ra  : getr regs' 1 = Z_to_bv 64 0x0beb4c;
    P_a0  : getr regs' 10 = Z_to_bv 64 2;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - RF_FR), RF_FR); (Z_to_bv 64 0x1b6d20, 232%Z)];
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0x1b6d20) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0x1b6d28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0x1b6d30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0x1b6d40) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0x1b6d48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0x1b6d58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_buf   : rdn RSEGS mem' (Z_to_bv 64 0x1b6d78) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x711b30));
    P_bsz   : rdn RSEGS mem' (Z_to_bv 64 0x1b6d80) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0x1b6dac) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0x711358) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp RF_FR }.

  Definition rf_vals : ltac2:(zQ "50!jtd!ks8!j4!h9!ojc>4regs@2$4@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3can$3@1$2@1$1@1$0#k0") := ltac2:(zQ "90!jtd!ks8!jb!hm2!k2!h9!ojc!pv0!mu5\4regs@2$6@1$0#5@1$1@1$0#k0\2sp@1$1@1$0#k0\3can$5@3$3@1$1@1$0#k0@3$2@1$1@1$0#k0^2@3$2@1$1@1$0#k0@2$8@1$0#k0^1@1$4@1$1@1$0#k0@1$7^3").

  Lemma rf_ev_junk : ltac2:(zQ "h00!jtd!ks8!p4!iv5!iuf!qv9!rh3!rh9!h9!ojc!nh5!rm4!rmf!rn7!rnd!mu5>4regs@2$9@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3can$8>1i$2>0@2$3@2$6N2^1@2$7^1Ni2@3$4@1$1@1$0#k0@2$d@1$a@3$b^5^4^3^2@2$c^5@2$f@1$0#5@1$e@2$5^2N2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsRefused ()) ["Plain"] "##Iih04__p1h14__p2h24__x1h34__x2h42H0h53Hi0h67__arithh74__ffh84__p3h98__varmaph:5__with;4cstrh<1ih=1nh>1xh?2z0h@1HhA2HihB1bhC3canhD7defaulthE1lhF5lemmahG1mhH4regshI2sphJ1yp&0p;1p;2p;3p;<p;6p;4p;=p;9p;5p;Bp;7p;8g004Vj1<Tg0041j1lTg00ENj1O!s/$lj1`Tg020ak20ITg00<SR0j12Tg03Q`R1j2WTg02hbR2j2!sG$FOj20Tg03R:j2[Tg005;j31j1JTg02BcR3j13Tg009Jj1KTg01LOj27Tg01D;j2ATg02CCk20;!s0$fk305!s~$jj2!s9$T<l<PTg01;?R4j26Tg01IlR5j24!tE$Qj6dTg0394j4gTg02DCj1jTg03S:j2kTg01CBj2H!s8$\j2FTg03TEj3G!s/$nj2LTg00;3j1mTg03UZk20!sT$V;k30G!sC$Qj1]Tg00Tkj3!tm$5Uj1\Tg01G>k20FTg01?<k10ETg02Lak40D!s:$Zk10CTg01@8k10>!sX$\j2iTg01Haj2!sB$Klk30=Tg01X`j4@!sB$?k10<Tg01Zlj3e!sh$ck20:Tg01AEk20!va$B1k304!s0$Pk402!vO$aj4_Tg01=nj28Tg021Mj2VTg02f^j2T!uQ$dk100Tg02;0j1UTg02<6j3NTg03WTj4?j1zTg03X0j4Q!s/$Wj1~Tg03YFj4RTg03Z=j3{Tg03[3j1y!s/$bj6}Tg03\Mj2MTg03]9l=x!s/$fj2DTg03^gm901Tg03_aj2wTg002^j4vTg03`=k60!yB$1>j6^Tg03aEj5uTg019Sk206j1tTg02WNk10!uP$]Yk209!sP$gj2hTg03bjj3s!yF$[j1rTg03d2j2qTg03:dmB0?!s0$?m<0@!yM$[j6pTg01YKk70ATg01\3k70B!s:$oj7oTg01[Oj8nTf0R6#2!s$%p=9%26#2p=|g00ahR7/q6p==g00bFR8f1R9;16p=>g03<nR:P:P:P8P8P8g03dOP3P3P3f6R;g03dof5R<f4R=f3R>f2R?P9P6NB0?p=b!s_+0!sZ$>g03eVP!sH%<0@p=a!sF$1P3P4g03f:P<P=P>!sH%M<Pp=c!sG$2P3P5g03?Z!sG4SA1867p=ZP9g01]_R5g01^>R2P2g01^^R4P6Epp=YP8!sH%8P6C@p=XP9P5P2P2P4P6g01_>K0Ap=:P?!s=+9P6K0Bp=B!s:1Fop=fP>!s9+!tZ$Gnp=Eg00bdR5#<R1#l#OR0%<1#<R@#<#<RA#<#ORB#`RC+0Ig00cIRD#2RE#2RF/W6%2FRG#2#9!s$/RH#|RI,I6'01[9FRJ#2RK#2RL=1:9%39RM%K1RN'7#=RO%K5RP'ARQ/APRR/>MP:P8%J:RSP3%J8%36R3,>MA1:9620;96405XJ:X>:PLPR1A6PX>8RRPKPQPRPJPO1796#=XG8X=8ROP9PM1;8MRRPFPN1;8NRQFbCaCaP9PMPRM<P1WF9RK1I9IRL'016NMRT%l@#<#KRU,4MRV'0RWPKPLPTPVPFPNPQ!sc%Ec!s-%PIPU1;8URRESEdP6CgPW%j?%3?RW,67%3>RM/7NRV,k7147V%=VRT/>V'016V7%ZT'0'H%3=/7NRT#=RVP8p-0RLg01diRK1F8FRX1F8E1F8DRE5G85G8g03f\RY'LRZ1F8G%m5-0H8>0G8X=G8E!sM$/LY1LEY%]KRE55K55K35%\KRYP820F8?P9&0E8H0DRX&0C8RG&0>8R[1Y[=1i85R51i81R11C8NR\60=8R]'X,:[5B[R^P8P]g01aER]1C87R_C@,:[1X5_,:[R_5B[5f[&0<2R2P[P8P\P]P1!sJ%Y[<R]5B[P21C8PR\9e85=e8\/X1,:[CECE20:[4R4P6P?g00kdR\g00ZKR`';2076?=1\`dB04879H02R`b7b9b:X28X38X0LW1179NR\,>6,0?Ra16\7%Z6R\'0'H16N?/0=1A?P/AP/>>[[^28^38^0L^1LP6%3;RP/4U17PN,47PPP9P?P=O6b6b?b4b;b5C_18B?%]CRP55C95C>Rb,VC/TJ=1:9RcePc18B>=5CP95C=Rc,VC1[?FRd'TRe=1:?PC%JCRf&00CPCP>18B=!sT&<RP%U;5NCRg18B7RBC?PC1VCP1[>FRP'TRhPgPBC?%\CRiPC^DCRj]ERk^=:RlP:PkPSPiPj%JiPCPCPfPfCQRmCQRnCQRo!sG$nPiPjPm!sF%%~CCRCRCR9{lo%zCP>PhP:PS%y:PhP>P6E}PgPg1MigPBPB1MCBM=x%3P,80,D;RPPP1MCPN901WFP6!s{$d%U<RiPBC?RgA1C6PXBCRPPC%3d!s\$<RhPP1;ChPCPdP:PC1803,D;X<:R31wDHCvP!uo$P3PdPHPB1IdH17WN#=R3%KARA'4PdP3POP?PW1;8WRO!}R%FbPHPA1;8AES1WF?RH1I?IR3!~:$WRD14WURP'0RSPHP3PDPP!~2&?PWPOEc!s-%PIPUP!~-%9CgPS%j>167M1k7T147T1>VT'016T7%ZV!}u%</7N#=P8A5KZEPYPXPGP[AB[]_9f[^P2P[1Y[;P8P1g01al!|e$U!{v$!{p$P8P5P11C8A!s:$CECEP4P!{?3X1LX8L10>\,Ha14?U,0<14?A!{%1^8LP6f7#3R6,6N176NRN/67147NP6!{3&7!{3/J03E^A1CghePCPeANCci!wE&cPiPBPdDuE^O2b@%U=9NCbRb0069%3J!x;$=R051Ce%tb%O@#`#\#]$08+09/h9=1C0eAs=>?#r!s5'WAX<:XC8XICWHo"). Qed.

  Lemma rf_regs_ok : ltac2:(zQ "a0!jtd!ks8!ji4!h9!ojc!nh5!ro7!rm4!qm4!qg8>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2sp@1$1@1$0#k0>3can$3>0@4$6^4^3^2^1@3$9@1$5@3$7^5^3^2$8^5").
Proof.
ltac2:(KReplay.run1z (kr_t_AsRefused ()) ["Plain"] "#$Yip'0h02Hih17__arithh24__ffh38__varmaph45__with51ni001nh61bh71ih82Hah94__p1h:4__x1h;3Hi0h<2PHh=2R3h>5Rcan0h?6Rcan65h@7Rcells0hA5Rgot0hB5Rimg0hC4Rsh1hD5Rsp17hE6RspHi0hF6RspLo0hG5Rstk0hH7__sat66hI!s0&7hJ!s0&8hK1ahL3canhM4cstrhN3memhO4regshP2sphQ1xi012R2i024Rcani03!tn%4i046!to%i054Rgoti064Rimgi074Rsh0i08!tp$6i095!tq$i0:5!tq$i0;4Rstkp%0p&0p;1p;2p;4p;3p;6p;<p;7p;5p;8g004Vj1FTg0041j1ETg00ENj1]!s/$lj1`Tg020ak20!sB$<1j1mTg03gHR0k40;Tg021mj3~Tg009Jj1<Tg01:Uj2QTg01DXj2nTg005;j3KTg01;?R1j24Tg03hNk40ATg01IlR2j23Tg00FOj22Tg01=nj2VTg01H?j1hTg03iOj2}!ss$Uj1g!t]$SR3j10Tg03;Jj4wTg03j\j2vTg00Clj2kTg01JHj2qTg01LOj2pTg03kdj2b!tn$;j2OTg02hbR4j21Tg00XPj3[Tg007<j1oTg03lAk10DTg03WTj4UTg03bjj3aTg03Q`R5j2@Tg03RQj6=Tg00;Qk10@Tg01?<k10?!s0$Zk10>Tg01@8k10=!s0$ck20:!ul$jj2_Tg01AEk209Tg01B1k308!s0$Pk407Tg03agj2iTg02BcR6j1WTg0394k405Tg02DCk104Tg01FMk203!vx$Dk20!vn$Jek301Tg01G>j2|Tg02Laj4e!w%$aj2d!sA$\j2z!s|$[k60!vw$mFj4x!x$$[j1\Tg03]fj2TTg01h2j2^!up$:k206Tg02T<l<jTg01X`j4XTg01YKj7YTg01\3j7t!sJ$aj4sTg03nYk50<Tg001>j6rTg03:?l<lTg01Zlj3ZTg01[Ok80BTf2R7f1R8f0R93a#\p=6g01_^R:9[89p=uf3R;1T78;K9p=c%F9#Fp=P!s-$#F#Fp=I%F9#<p=J%E!sB$S%E9#Ep=Rg00ahR</49p=Lf4R=?a;7#\g00^lR>P8g03CNR?P9CU'^p=5f5R@P;P7g03odRAP8CU,T=!tF$91T;7%\8/^95K=p>0C20689#W,V7,T;p=DA[78:,T;=K=9p=>g00bFRB/_9p=8g03<nRCPBP5P6P1g03f:P@P=P;P7P8P9M<jp=CPCPBP4P6P2g03?Z!sG4;1dB9p=7f6R2g01]_R4g01^>R1P1g01^^R5P@P4P1P1P5PBP=g01aERDP;CXg01_>REFYP7!sH-8g01alRFP9CXPEFYFtp=?f7RGP2!tL/CsI0<p=AP!s>$1_=;1i78P9Erp=B!sO$AP;CU,T2P>P8P!vo$,^75KGp=:1O=;/O7/O8/O9p=HP!u^%BP3P6!ub&eVRH!sm$!sA1;PH!ut'lM<lp=G!u31PD!u-'p={AZB=;=ZB7=ZB8=ZB9p=M!sU2!u]+p=yP;!sA+!t1$L0Bp=f%09#0#0#0p=Ng00bdRE#FRF#ERD#]RH%FFS00#FR6#FS01#FS02#FR3#]RI#`RJ+0E%]6RK#`RL#mRM\J!v`'H0;P0!vo'A6@;7?~?@P9PJf?R0%<FRF,uHS03f=Ccf>,QIQ01#<RN'n=KB<g01bS1QI0'4f@,QIg01c^'4g01`:R0fBfAS04g0412H0A%P3#IRO#F#P#J/49%EERP#FRQ#FS05#ES06#E#S#P#I#I#J,39'2fERR1VI8RSO1%hLRT5KM[^7B%EQS07#FS08#S#E!sX$I!s|$Q07#ES09#F#S!s='!sq%FRUPSO1=KMT[^7Bg0428,}R%gLRT#mP0PU%EPS0:#FS0;#FS0<!sj$P#E!s&$S#S#R#P#J,VIg00cIRU#0R0#0RV#0RW#0RX#0RY#0RZ#0R[#0R\CwfD,VI,v\,kT3K%LR%<3R3,qFS0=,3R'2Q0:#ES0>#ES0?#E#R!s$+P!u3'RRfHRT,QIR]%<O'p%<6RO'b'O/491b]O,OR!uV%JRRPSO11VK<,kL!vG$KBfG96RTP?PR%0\RT#0RM#0RL#0RK#0RS#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk#0Rl#0Rm#0Rn#0Ro,19RpPCPJfNRq%`HRrP8A[H<:R:PqfLRsfKRtP8%o<RuD5E9^0pP811UofMRp$0DPJPpPrPUPAP:CUAaptRP>PUP?PuCUI0CeW0PC%09S0@/1oPJfPR?Pr%08S0AP:P?PqPpQ0AP!t'$]0P9110oPJfOR>PHPWPVCDRtPJP?PH%<EREP9D>X6JPJPtA6>psS0BPWP>PpPsPW1@VWRs%0oRp#0Rt,1WRR'2%<PRP,4FRA%E6S0C#JR6,3PRv'2S0DPsPRPAPvPVPF%8FRvPWPP%8PRAECPWPPPAPtP6%86RAE;E=g01diRR$0@Rs%gRRR&0?BRw&0>BRx&0=BRyPy%7FRz%7PR{PyP{%76R{F?20:y5R|P9P7g00kdR}g00ZKR~'_20997=K}~dB08B<8H07R~b2b3b4Q0DP9b1GAGBPJP>PrP0P:Q0BP0PuG:!v|$Q0@#0!v~+RR0PrQ0A#0S0BP:P0P?P>Q0B!w$/VoQ04PJfQR}Q03A6}>qR>/iUCcePJP}PrPVP:P>PV!t21R>!t1%TRUPrQ0B!tD$P:PUP0P}Q0@!t1/WoPJfSRqPHPYPVCDS03PJPUPHPP!x1+!tJ$q}?S03PYPqP}P?PY1@VYS0411YtS0D'2%<DR?,4FR}13?6RP'2S0EQ0!v7$}PPPVPFPvPYP?%8?RPECPYP?PPPtP6P!ww$!xN$wPxPyPyPz%7?RPPyPPP{F?P|P!w++E!w+-qPrPWP:Q03PW!ux+%0>!uv'VRWPr!w<&3P:PWPUPqQ03!uv/XoPJfURPPHPZ!{'$}PJPWPHQ00#<!{',}A6Pq0S0EPZPPPqP0PZ1@VZS0D11ZtS04'2%<QR0,4FRq1306R}'2S0FQ0DQ04!vR$!uw%ZP0%80R}ECPZP0P}!uw=0R}PyP}!uw3F!uw-PPrPXP:Q0EPX!uw7XRXPrQ03#0R}P:PX!|6$}!uu/YoPJfW!xm$[!xm%EPJPXPHP?!xm-EA6qPUS0EP[PqPPPUP[1@V[S0F11[!ut%Q0:#<RU,4FRP13U6R?'2S0:Q0FQ04PPP?!uv&[PU%8UR?ECP[PUP?!uv=UR?PyP?!uv3:!xo2Y!uv%Y!uv7ZRYPr%0}R?P:PYPXPqP?!ut/ZoPJfY!xk$\!ut,YPHP0!ut1PqWS0EP\!xj$WP\1@V\S0:11\tRW'214FORq13O6R0'2S0!tu$W!y=$!ul%\PO%8OR0ECP\POP0!ul=OR0PyP0!ul34!xd2Z!ul%Z!ul7\RZPr%0?R0P:PZPYPPP0!ul/[oPJf[!xb$T!{Y$WPJPZPHPU!{V,WA6qPXS0EPT!x`$XPT1@VT!~O$TtS0:'2Q00#ERX#<!#7[$W13P6RU'2S00Q!ux'U!uv&T!#7Q$UECPT!yV$!uv<PRUPyPU!uv30!xd2[!uv%[!uv7^R[Pr%00RUP:P[PZPqPU!uv/\oPJf]RWPHPM!xd,[PHPO!xd1WqYS0EPM!x9$YPM1@VMS0011M!ux%%FDRY#<Rq,4FS0413q6RO!~U&0Q0:Q04PO!ux&MPq%8qROECPMPqPO!ux=qROPyPO!~V?WPrP\!ux%\!ux/S0E!uy%`R>Pr%0UR\P:P>P[PWP\!uy/ToPJf_ROPHPL!uy%FPJP>!#8D1FA6OWZS0FPLPOPWPZPL1@VL!xs$L!uy&EDRD#<RZ!xq&Z!#8H%!xq,!#8H&LPZ%8ZRPECPLPZ!#8H>Z!#8H8!xq/OPrPTP:Q0FPT!#;B,E#0!uy+bRTPr%0\RPP:PTP>POPP!uy/MoPJfa!xt$K!uy,TPHPq!uy1WO[S0FPKPWPOP[PK1@VK!xt$K!{n'5#<R[,4FRO13[6Rq!~a&0Q0:POPq!uw&KP[%8[RqECPKP[Pq!uw=[RqPyPq!~b?WPrPM!uw%M!uw:dRMPr%0PRqP:PMPT!{+$!uw-LoPJfc!xr$S!uw,MPHPZ!xr3>S0FPS!xr$>PS1@VS!xr$S!uw'7#<R>!xp&>6RZ'2S07!xp+Z!uw&SP>%8>RZECPSP>PZ!uw=>RZPyPZ!uw37!xp2L!uw%L!uw:fRLPr%0qRZP:PLPMPOPZ!uw/KoPJfe!xp$]!uw,LPHP[!xp3TS0FP]!xp$TP]1@V]S0711]!uw';#<RT!xp&T6R[!xp&7!xp%[!uw&]PT%8TR[ECP]PTP[!uw=TR[PyP[!xpCK!uw%K!uw:hRKPr%0ZR[P:PKPLPWP[!uw/SoPJfg!xp$^!uw,KPHP>!xp3MS0FP^!xp$MP^1@V^!xp$^!uw'>#<RM!xp&M6R>!xp1>!uw&^PM%8MR>ECP^PMP>!uw=MR>PyP>!xpCS!uw%S!uw:jRSPr%0[R>P:PSPKPOP>!uw/]oPJfi!xp$_!uw,SPHPT!xp3LS0FP_!xp$LP_1@V_!xp$_tRL'214FNRO13N6RT!#A,%7PL!yC$!uo%_PN%8NRTECP_PNPT!uo=NRTPyPT!#A+>WPrP]!uo%]!uo1R]!un%l!#5R$>ROP:PTPS!u,$!un-^oPJfkRLPHP`!#;H+TPHPM!#;H0LWKS0EP`!yR$KP`1@V`S0F11`!xg'C#<RK!xg&K6RM'2S0CQ0F!xg%M!uv&`PK%8KRMECP`PKPM!uv=KRMPyPM!uv3C!uv-LPrP^!#;D$^!#;D,]!ut'nR^Pr%0ORMP:P^PT!~Z$!ut-_oPJfm!xd$a!ut,^PHPN!ut1WLSS0EPaPWPLPSPa1@VaS0C11a!ut%%JXRS,4FS0F13S6RL!{\&CQ0!#4G%!ut%aPS%8SRLECPaPSPL!ut=SRLPyPL!{]?WPrP_!ut%_!ut/!{[+pR]Pr%0MR_P:P]P^PWP_!uu/`oPJfo!xk$b!uu%7PJP]PHPK!uu-7A6LWTS07Pb!xk$TPb1@Vb!xk$btRT'2%EX#<RX!xj&X6RK!{a&FPT!yD$!us%bPX%8XRKECPbPXPK!us=XRKPyPK!{a?LPrP`P!|m$`!{a2`!ut%r!#5J$_RWP:PKP]!u3$!ut-aoPJfqRTPHPc!xk,KPHPS!xk1TL^S0EPc!yV$^Pc1@Vc!~Q$c!xk'YR^,4FRL13^6RS!#C~%7Q0:!yD$!ut%cP^%8^RSECPcP^PS!ut=^RSPyPS!#C}>TPrPa!xi%a!xi-`!ur'tRaPr%0WRSP:PaPK!~Y$!ur-boPJfs!xh$d!ur,aPHPX!~U2T]S0EPdPLPTP]Pd1@Vd!xh$dtR]'2%EY#<RY,4FRT13Y6RX!xh+]PTPX!ur&dPY%8YRXECPdPYPX!ur=YRXPyPX!xhCb!ur%b!ur7vRbPr%0SRXP:PbPaPLPX!ur/coPJfu!xf$ePVCDR]PJPbPHP^!uq+P]A6TLKS0EPe!xd$KPe1@VeS0:11etRK'2%JDRL,4FR]13L6R^!xc&!z$%^!un&ePL%8LR^ECPe!yR$!un<LR^PyP^!xbCc!un%c!un7xRcPr%0XR^P:PcPbPTP^!un/doPJfwR]PHPf!un$KPJPcPHPY!un,KA6]TaS0EPf!x/$aPf1@VfRa11f!~I&D#<RD,4FRK13D6RY!uo$PaPTPKPY!un&fPD%8DRYECPfPDPY!un=DRYPyPY!un?]PrPd!un%d!un7zRdPr%0^RYP:PdPcP]PY!un/eoPJfyRKPHPg!un$TPJPdPHPL!un,TA6K]bS0EPg!x/$bPg1@VgRb11g!{O$Q05#J!#C_$L13T6Ra'2S05PbP]PLPa!un&g!#C]$aECPg!v\$!#C]=aPyPa!un35!un-KPrPe!un%e!un7|RePr%0YRaP:PePdPKPa!un/foPJf{!~B$h!{N+ePHPD!{N0LKcS0EPh!{L$cPh1@VhRc11h!{M$Q06#<R],4FRD13]6Rb'2S06PcPKPDPb!un&hP]%8]RbECPh!v\$!un<]RbPyPb!un36!~>2f!un%f!un7~RfPr%0aRbP:Pf!|g$b!un/goPJf}RDPHPi!{N+f!#CP/PKA6DLdS0EPiPDPLPdPi1@ViRd11itRL'2Q08!#@]&T13K6Rc'2S08!#5_%c!un&i!#@[$cECPi!v\$!#@[=cPyPc!un38!un-DPrPg!un%g!un6p+01ARgPr%0bRcP:Pg!|j$c!uq/h!sN&@RTPHPj!ut$LPJPgPHP]!ut,LA6TDeS0EPjPTPDPePj1@VjRe11jtRD'2Q09#<!#55-d'2S09PePDP]Pd!ut&j!#54$dECPj!vb$!#54=dPyPd!ut39!#541h!ut%h!ut:CRhPr%0cRdP:Ph!|p$d!ut/i!sN&BR]PHPk!ut$DPJPh!#@_/PDA6]TfS0EPkP]PTPfPk1@VkRf11ktRT'2Q0<!#5:0e'2S0<PfPTPKPe!ut&k!#5:$eECPk!vb$!#5:=ePyPe!ut3<!#5:1i!ut%i!ut:ERiPr%0dReP:Pi!|v$e!ut/j!sN&DRKPHPl!#5@'i!#5@5gS0EPlPKP]PgPl1@VlRg11l!#5@%;#E!#Q{&!#5B$f'2S0;PgP]PLPf!uv&l!#5B$fECPl!vd$!#5B=fPyPf!uv3;!#5B1j!uv%j!uv:GRjPr%0eRfP:Pj!|~$f!uv/k!sN&FRLPHPm!#5H'j!#5H5hS0EPmPLPKPhPm1@VmRh11m!#5H%>#J!#5H-g'2S0>PhPKPDPg!ut&m!#5H$gECPm!vd$!#5H=gPyPg!ut3>!#5H1k!ut%k!ut:IRkPr%0fRgP:Pk!|~$g!ut/l!sN&HRDPHPn!#5N'k!#5N5iS0EPnPDPLPiPn1@VnRi11n!#5N%?!#5N0h'2S0?PiPLPTPh!ut&n!#5N$hECPn!vb$!#5N=hPyPh!ut3?!#5N1l!ut%l!ut:KRlPr%0gRhP:Pl!|~$h!ut/m!sN&JRTPHPo!#5N'l!#5N5jS0EPoPTPDPjPo1@VoRj11o!#5N%2!#5N0i'2S02PjPDP]Pi!ut&o!#5N$iECPo!vb$!#5N=]PyP]!ut32!#5N1m!ut%m!ut:MRmPr%0hRDP:Pm!||$D!ut/n!sN&LRlPHPp!ut$jPJPm!#5N0jA6lTkS0EPp!sj$kPp1@VpRk11p!#5N%1!~X$j!#5P%j6RH'2RmPkPTPKPH!uu&pPj%8jRvECPpPjPv!uu=jRjPyPj!uu1Pm!ut-lPrPn!ut%n!ut&%0`/1o%0D!ux$%W8RnPE!s$%DH!s0i/3LS0EP`1O9EXQBR`P!s$anO1S01O1S02O1S0?O1S0>O1S0;O1S0<O1S09O1S08O1S06O1S05O1S0FO1S0:O1S07O1S0CO1S04O1S00O1RlO1RmO1R{O1RjO1RzO1RAO1R6O1RtO1RvO1RpO1RVO1RHO1RKO1RTO1RkO1P`PDPkP`PhPTP`PgPKP`PfPHP`PePVP`PdPpP`PcPvP`PbPtP`PaP6P`PYPAP`P^PzP`PXPjP`PSP{P`PWPmP`P_PlP`PMQ00P`POQ04P`P>Q0CP`P[!#T5$ZQ0:P`PqQ0FP`PPQ05P`P\Q06P`PUQ08P`P0Q09P`P?Q0<P`P}Q0;P`Q03Q0>P`Q0@Q0?P`Q0BQ02P`Q0AQ01P`P8Pn%8nFG!s$A!}C%E;P9H05Q0E&047%W7#Lp+01N,QIRi003N%Li%LNp+01P,QI/nN#L[[202F313<F%L3Q0=,3<[[%LFRNg01f2RIB01F38UW8Q0=#L\I^8Np-0RN!{X$BPBPwP81|B8CeP8PwCePxPy1dB<1zBQRQ5{y%h1R<PyPQ%7ERQP!s$$DMP!s0h=yy]P<Py!$:0';J00CfCf!}',X:BW9%L9P8!|ZvP;[[^:B^9NP9!#48$TRNPr%NG#N!s$/RrP:P!w@$Rp+01QPr!#4t$%WGP=P@O4b1bHbIbJbMb;W0X7CP9O1n0110001020111100X5!s>_0!s>~!s>~!s>~!s>~!s>~!s>~!s>t0!sVXP9O1!{l$CxWCW?W>W@WAWBWGWEWFWDW=f:f9f8P!$H;1O;n40!{g$!s#$1;110110810:10910;106105104102103107W<XLBXPJWNWOo"). Qed.

  Lemma rf_know_ok : ltac2:(zQ "b0!jtd!ks8!ji4!h9!ojc!nh5!ro7!rm4!ql1!pvd!mo0>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2sp@1$1@1$0#k0>3can$3>0@4$6^4^3^2^1@4$9$a@1$5@3$7^5^3^2^4$8").
Proof.
ltac2:(KReplay.run1z (kr_t_AsRefused ()) ["Plain"] "##qap'0h07__arithh14__ffh28__varmaph35__with44__x1h51mh66__sat0h7!s/%1h81dh91zh:4__p1h;7!s>$66h<!s0&7h=!s0&8h>4__x2h?1xh@2HahA4__x3hB1bhC4cstrhD1ihE2E0hF2E1hG2HdhH2HmhI3HsphJ2PHhK2R3hL5Rcan0hM6Rcan65hN7Rcells0hO5Rgot0hP5Rimg0hQ4Rsh1hR5Rsp17hS6RspHi0hT6RspLo0hU5Rstk0hV2Z0hW1ahX3canhY3memhZ1nh[1oh\4regsh]2sph^1yi002R2i014Rcani02!tV%4i036!tW%i044Rgoti054Rimgi064Rsh0i07!tX$6i085!tY$i095!tY$i0:4Rstkp%0p&0p;1p;2p;4p;3p;5p;6p;7p;9p;8p;<p;@p;Bg004Vj10Tg0041j11Tg00ENj1o!s/$lk10@Tg020ak20cTg00<1k105Tg03gHR0k40XTg03bjj3PTg01;[j1QTg023;j4gTg009Jj1@Tg00XPk30DTg03]fk20vTg005;j3ATg01:Uj27Tg01DXj2W!sp$?S00j24Tg03hNk40]Tg01Ilj2;Tg01=nj2<Tg01H?k100Tg03iOk20K!s}$Uj1~!t|$Sj1FTg03;Jj4{Tg03j\j2zTg00Clj2hTg01JHk20FTg01LOk20uTg03kdk20=!t^$;R1j22Tg043Ak10!v7$Fjj2UTg03agj2wTg0065k108Tg00>:k20eTg00?Ck30>Tg01fNk10bTg00=2j2!up$@Lk207Tg00AUk206Tg00;Qj1uTg044Gk10`Tg007<k10_Tg00UKk30^Tg045Jk10\Tg02<6j3r!t_$Oj28Tg046Wj5qTg02ASk30[k40!uZ$?<k10Z!s0$Zk10YTg01@8k10!w1$Hak203!s:$ck20VTg01AEk20UTg01B1k30T!s0$Pk40STg001>j6^Tg01h2j2kTg047`k70RTg01FMk202!ws$Dk20Q!w&$ek30!y7$G>j2i!s/$\j2aTg048gk70MTg049nm90JTg01KIk30ITg04;6j8}Tg01V@k20;!vE$3j1BTg04<;k30H!s0$\m90GTg03Q`R2j2yTg02Taj4nTg02BcR3j1VTg02S;k10E!s0$Yk40L!sN$<m<01Tg04=bm@0!t%$>hj4_Tg01CBj2bTg02DCk10tTg02Laj4`Tg01Yok70sTg03S\j2pTg03TEk30!zr$Tnk20!wc$Tkj3tTg04?hk20<Tg04@lk40nTg00GDj4f!y:$kk10mTg01i9k10kTg01mlk30jTg04B<k20iTg00DNk209Tg04CIk30g!s0$ek50fTg04E4j4xTg01X`j4!x_$YKj7!x+$\3j7eTg01[Ok80l!s9$Wk60:Tg01Zlk30dTg03:?m<0!uB$:dmB0aTg039[k60qTf0R4#0#0p=Cg00bFR5g00ahR67A4p=c%0!sD$#0p=S!s2'@p=Y%14#1p=I%14#0p=>!sN+!s$&@p=Df2R7f1R8'4/84p=X%0!sZ$M1468!s8$G!sl$#1#1p==!sh30p=lg00`_R9?t84p=J!t:$!s@%sg01`:R:P7P8P4Cgp=920354p=3P5P8g01alP4CZp=d!s4$]_R;g01^>R<P<g01^^R=P4g01_>R>FTp=mg00kdR?g00ZKR@!us$Of3RA/471484'8p=51464p=6P7P;P<P<P=!t:'ERBP4CZP!sq$:!sF-8P4Fep>0NPA!s:+!u%$L0lp=Ef6RC!s>'f5RD!s~,f4REPBPA!s{%!t@1P!t;+Fep=?P9PEPA!s}%J0:p=NAt584p=LP5!s@2K1U54p=Rg03<nRFP5P2P3Q00g03f:PD!sT,N<01p=|B0d!sp$HP5P6!sB'E^p=]1278/44p=[PFP5!s$$3P3!si2pp>0C!sD&!s$%1P4P8P7P1PAPEPDPCf7R1f8R3f9S01NB0ap>0O1484,87p=j!vU0!vs,>FT!vw&APE!s>+!sR,5P7PBP8!v[&4Fep=\P8!sE+4J0qp>0?g00bdR>#0RB#1S02#oR2%0BS03#0RG#0RH#CRI#oRJ$0@RK+0c%oGRL$0@RM$05RN\K!ud'H0XP0!us+:APDA7#QPEg03DTS04CgP4f?R0%@BROg01_^60D2+0vf=R25AKf>,7J%@HRH'W#cg01bSRP17J0'4f@S05,7Jg01c^RQ'4P:fBfAg0412RRH0]%CI#SRS#0#YRT%1>RU#0RV#0#I#>#S#DRW,;47X4fERX1<J8RYO1&00MRZ5AN[^D5%1VRV#MS06#0S07#1S08#C!sa$[%1VS09#M!sw$!s:%\!su&FR]PYO1=ANZ[^D5g0428RZ-0KX%~MR^$05S0:P:P]%1U!tb$]#CS0;#1#CS0<#0#>#M#>#>#I#YR_,<Jg00cIR`#FRa#F#FS0=#FS0>#F!s$%RbC{fD,<J,zb,h^3A%@IRc-0FORd,;X,GX%1U#IS0?#1#=#=RU#1RX#l#DRefHRf,7JRg%@S+0u%@GRS+0='220=gS,2e!uJ&JRePYO11<L6,hM!v>$W5&0of1;gd,GgfIRg,UKfKRN?Pgf#Q/w`=AKg1<JgRf,UKfLRM?Peg#Q/wa=AKf1U561<J6!tN&#cfNRe?PMN#QRLfMRY&08`Rh00eHRiB0>hPQ&0bR,vh007RS0@206TWS0A206[\S0B%u9RQ'JS0C'JS0D'JRP'J'JRjg04EORk$0`Rl&0_6Rm/v_&08aS0E80^bS0F%>V#IS0G!wC&C#YRV,vmRn%s]S0H#@R]+07S0I/JQS0J'JRo&0\ZRp5r9Rq5r9Rr5r9Rs39fOS0K?PYM#QRt?9ejA9terS0L'8[A9LYjS0MA9LYrRu'8A9tes[P:PLPYPjPrDqQ0MPuB0[:LYRrPi%0U#I#=#>#l!wv$U%1X!s7$!s$/@RX60>hRi/JP!sr&hPHg01diRj#uRs%~jRv&0Z5Rw&0Y5Rx&0W5Ry20356Rz%3H'd'm20Vy=R{P4P71U?@S0N20U47#OdB0T568H0SR@b1b2b31;6HP4b0PKPM17J4R?/WH#cXBKP21wL`S0OP7E^1kLh,7JS0P!sE$eK0RPrPiP!ts,UPXPKPMPUP?P?PXC5XBK17JMR?002HS0Q%6?%6HS0R17Je/WH#6[[S0S20QOcRP1;6O%6c1;6dS0T[[Ri%6OR2g01f2R|B0POc8UW@Rc%6d\|^@2R2PsPv1i58S0UPxPy1a5>R|%3X5:yS0V&00<R}Py%3U=:y|R~P}Q0V:0Ny~CECEP{P!ux&X45144X14U8PUP7P7PXC5[[^45P4fPS0V!un$WP0Q05O3b0b;b<b=!u^,eQ!vA%PUQ0PQ0P!s:$K0MPrQ0@Q0D!v@+MPRP7f:S0DQ0QQ0SPPPiPcP!u>$Q!u:%P~P}PyPyPzQ02#0#=!z}$~#3RhPyPhP|F?!u14U414~8,G~!u%%Q0WQ05O2!tw+6PRPRP?C5eN90JPrQ0AQ0C!td&TPWPsPvPwPx%3T9:yz!t+,%6T!y0$!tu-!sN%W%3O>0I5JRO5:y!sW,14WdP4b0b6b7Q01G}PrQ0BPQ!t:&[P\!sj,[!t:3[!t:9\=:yO!t1/\!t1+P3G}20;9rS0BDN!s$'Q0MeA9telA9teqS0M'8\uA9LYlR!s,$qR9'8Q0L!}a'lPqDqPuP9!s4$MPkP7f<S0Lf;Q0?#C#S#BRuP4P4%BIRIC5X[5RqQ0H#0#BRlQ0;#MR\#1#BR[Q07#0#M#BRWQ06#s#BRTQ09#>R?#1RR#1S09#BR~%0\#BR\Q08!s^$U%0RRR#BRh%u5S08'LS06'LS07'LS0;'LS0H'LS0?'LS0C'L!v;'PyPy%3uRX%3lR0PyP0%3IR0F?!vM,PuPlPlPIC5!v|$qP[Q0C!sf/PX%3[RlPyPlP!s`3[P[!s`-WQ0?!s`3WR[PyP[!s`4WPW!s`-TQ0H!s`3TRWPyPW!s`4TPT!s`-~Q0;!s`3~RTPyPT!s`4~P~!s`-\Q07!s`3\R~!|p$!s`3\P\!s`-UQ06!s`3UR\PyP\!s`4UPU!s`-hQ08!s`3hRXPyPX!s`4hPh!s`'20;5qDK!s$1B0H5qkePEN90GA9teoA9tep'8\9A9LYoR!s,$pRt'8Q0M!{2'oPpDqP9PtPrQ0FQ0J!s>&mPfP_PbQ0E1<JN1UKfP81yab%@>R>/4SRfPaP>%R>PbPS%RSRaE|!}9,>%3SR>!~H0PfP4b0Cn1ybb14SSRfPbPSPa!s+%!sc,A:y>>!s]624_Rf#6X95!t5,_,HzRN!~u1126_R_#6!w$$gP4C]%VbRm=[fdX9512_mRt/4dR912_SRp/4dRoP5P5Q00P4X?!}`$01484$0EX^5X?5PtPpPq!s$$5P5g03M^1284H0L#RX55XZ5P_P_%R_PmPSPqPq%V4#RX?F!uQ%J0CN:0OPdPd%RdN<01!#4a21HN>!#4b0Po!#4`&CnP9e!u>%Q0:P:Pe1<JfPbC{1<JM!#Cy&X95PC!sL%N@0BPrQ0IPQ124VRQ1;Qd%6]Rr12Q];jd'8'G%68RQ%V8=[7]R^P:fRRb12EV/2A,<JP7C_#O[[^5F^85'8!vV$6VRM1;Md12M]=jr!sm$RfP:fQRe12MAR9,<JRo!sb%\^\Q!sd%!ub3!{L$z%3VRN,HzR>PyPy1d>O!s>']RaPy1H>aPOF?H0AD\!xz3b6b7PePoP7P5P9PVP4%VA,24RfQ0G#1#>#DRSC5%0?#M#I#C#DR?P4Pf%1R#I!sD$RC5Q09!sQ$=#s#YRqP4PfQ0<!s9$S#DRfC5'b'bX95&0t7Rm%V7#6R_17JeRp002HRt%6pQ0RfS,7J!#@$%RH!uc'p-0Rp!uh$51i57P8PwC`!#?W%BRB,H|=:yaP}PyA:yz|RkP}Py!#NF'yPyPN1H>|R>!v%$B%3SF?20?yEK0s!#?p3X>5W:A[48]12M7RBA[BAS5XV/bE\Q[^45^>5^:pP4P?12M3R?%V1RV,2?RBPRC5PqP?PBP!uh$PVP3PDPCO5!#>I&bC17JoPmP_PtP!uV+Q0>,p5Q0=,p51p5`60456045g03f\+0r=tj!us$P5!uw$AP7!uw$A!s+$!v'/GRG!}t$}Py1H|G!v4'P!v/%!#@d%3,a520?yDD\!s=&zP>1d>O,myD\CE!s$%!v23XA5X:p%67R>A[8A]1GEC12ME!{+%'G[\>[!v<'A!v?%fU,7JRp/;dPVPpP3!#T:$Q0LO8!v-,-0<9E^H0nXH^XGQX5FX85CfPg!{P9Pz1dz!tx%!tp,Q0T9X66!{4'-0<6C]&0mnR6,kL,7J&0knR@'2R{1;{d12{!}%+P:PeQ0VQ0K5Pb#QRb/k6,7J/2@!}r/!}6,'8eB0jLn]P:Pe20ibn!sN<!#8H$Q0IH0heQ!#AW$PLPYPZQ0N2095F0095g04FW<0gZ#OdP1I0fCfCx!s&'!si'4CgebVbFbEbIWQWMWLWNWOWPWUWSWTWRWKQ0DQ01P3P1PC!#Xn-O;n4000010!s#$1;110010710910810:105104103101102106WJXX5X]KWYW\o"). Qed.

  (* [comment removed for export] *)
  Theorem as_refused_k : forall regs mem msF mo (sp : word) (can : Z) (KX : TSet),
    rfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0xbeb04) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    KX [] ->
    (forall regs' mem' msF' mo', rfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 AEXIT) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') KX) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_refused) KX).
  Proof.
    intros regs mem msF mo sp can KX PH OK RS Hfd2 Hrd2 HKnil HCONT.
    pose proof (rf_regs_ok regs mem sp can PH) as HR; pose proof (rf_know_ok regs mem sp can PH) as HK.
    destruct PH; pose proof (u64_range sp) as Hsp; unfold ASP_LO, ASP_HI in *.
    apply (rf_sound sp L S Zr (rf_vals regs sp can) regs mem msF mo KX);
      [ unfold rf_vals; rewrite length_app, junk_vals_length; reflexivity | reflexivity | exact HR | exact HK
      | exact Hfd2 | exact Hrd2 | exact OK | exact RS | exact HKnil |].
    clear HR HK; intros Rj R' M' msF' mo' HR HK FM OK' SB' HS' RS'.
    set (vals' := rf_vals regs sp can ++ junk_vals Rj) in *.
    assert (P0 : vals_ev vals' 0 = sp) by reflexivity.
    assert (P1 : vals_ev vals' 1 = Z_to_bv 64 can) by reflexivity.
    assert (PJ : forall i, (2 <= i < 34)%nat -> vals_ev vals' i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2)))).
    { intros i Hi; subst vals'; rewrite vals_ev_app_l by (unfold rf_vals; rewrite length_app, junk_vals_length; cbn; lia).
      apply (rf_ev_junk regs sp can i Hi). }
    apply (HCONT R' M' msF' mo'); [| exact OK' | exact SB' | exact HS' | exact RS']. split.
    - regv HR (2 : reg); exact P0.
    - regv HR (1 : reg); reflexivity.
    - regv HR (10 : reg); reflexivity.
    - intros r Hr; cbn [In] in Hr;
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        lazymatch goal with |- getr R' ?rr = _ => regv HR rr end; cbn [edenot ev ENV]; rewrite PJ by lia; f_equal; apply bv_eq; reflexivity.
    - exact FM.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - let Hc := fresh "Hc" in krd HK 0x711358%Z 8%nat Hc; rewrite Hc; cbn [ev ENV]; rewrite P1; reflexivity.
    - intros a n Ha Hn; eapply frame_mod_store_ok; [exact FM|].
      match goal with Hs : stk_ok _ mem sp _ |- _ => apply Hs; assumption end.
  Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
