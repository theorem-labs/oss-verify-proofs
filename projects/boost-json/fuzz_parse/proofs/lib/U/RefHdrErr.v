(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare LibTail Spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefExitBase RefStdioDefs RefStdioWrite LibStdioCall RefPrintfBufBase RefPrintfFirst LibDiagKn.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefHdrErr () := KReplay.lz_vm "#%98C47Corelib7Program6Basics4flipC46Stdlib5Lists4!s+#6nth_ok!s_,4Init5Logic8eq_ind_rK!s},Numbers7BinNums8positive01I!si72eq00!s@29Datatypes4list00K!sFA1!sf<6option!sh/!to=2!sK=1Z02K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr01C13~~~!smc2!sm&!tz?3!t3c3!t33!vv23nat!v0_6kentry05!v2c!so'6!sok7!sok4!soc5sadd!yMY1U<LibStdioCall9s!s0#_res!st+!|?C!|a=4prod!}I?!sF$!~K93an!sa5!~f,1K!s[<1C!zI<fstC!{U]s_pc!v2%!t0=sndC!wE^:!wE%call!t8&!ss^6sc_ret!soe4sc_f!sme5!sm#d!t]is!smil!{JB!#9'$!#4le!|[&I!#6ka0!smc!t^'!so'!#8i>!#;PG3!tZ]8sideco!~F#!uMV!#4g<0!xC3!uR61K4ELinuxProcessSemantics5Riscv5Instr5aluop!#3r3!#:z11!ux]9sym_state!xHe7script!uu+c!vkQ9RefHdrErr5hs_rA!y63!|#3bool00!t3`cA!txb6hs_sr!slgknA!vTfsc!wAgC!skfc!skeo_rA!skf!xSfo!xSho!xSho!xSgo!xSgo!xSe!vy%F!}<h!sl&!#6s=N02I45stdpp9bitvector;definitions2bv00C!sI@DZ_to_bv_obliga!s:#_1!#ExC2!s{A7!s{&C7!uxN8PropExec3rdn!ur'!uTC1!t1/!t&96images5Ubsan1M?loaded_segment!#A,&!txO4Spec9msg_short!sh[;!sh#overru!uf&I!#;]?0!t1P6SymAux7sregio!t/&!#H5+!#Vc$7!s+#Def3map!#Vc76!#Vc$!#IZ\5s_log!vAV!u6&;log_c!vD#ed!{w3!#<071!},\9h_!vJ%s!t}ZRun7vals_ev!w5'!z~?;bv_unsignedC5!#[C%6ZArith6BinInt1Z2le!sB<3opp!sC=ad!s|=3sub!vF\3ENV!uV&!y,\6a_base!smdedenot!smc5a_off!zc]6r!tU-I!|:^!#Vs#!#EEb;!{-+_w!zF'!#b942In!#aJ8o!tP#!tJO=!u:'Sound4SX2S4fla!w\'!zB<pow!{]>t!sB<>pow_pos_nonneg!sN<:!sN#!sJ%K!uw'9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PE!#aw#!sIE1!sIE6!sIE3!sIE7K!uPL1C!sQ55Tauto8B!sJ&!sH6:Z!sp+=Z!sT$CheckerC!w7<4find!sqAC!sq0_s!z3#!xN@1!~1W<!|Q'!{0,K!uz<G!vF'4!sJF5!sJF8!w6<5eKind!#PT<unit!zG8!se%4kind!yy8!xh13Op2!yZ#!t5@!#bF85False!#mn3!sC%4True!|b8!xP-;!~#%!wp$!uB8!tz65C!#V}?7Prelude5bv!#@y4!#F^,length!#5Ub7regs_ok!#:6U!st7know!st,7!#9UQDrive9junk_vals!#D72!#E@2app!t1P5Frame9f!s+#_mod!ttW!#Ip&7seg_rom!#:T<9nth_error!t0P9!u~'X8!vk$nth!wbi9!#a4$!wd,!#:':6of_na!#:s34Znat5Nat2Z7inj_iff!#HV77iff_sym!sf>9is!#;4<!#3g23!#?D[>!#?D+!#5q+!st\?!st,!#Ay,!#b%:?!s<25State5event02!|$RhapeAlg6t_emi!tG'!#CB[!#bW,1!yqV!#D60carry!z_i8sc!vx1!#Og86Forall01!#HZ]s!x9#s!|fjmem_!#IRZ!u}7log!zn-!#>PVA!#Q@,_!#5E#!#77^8blob!#P8-!~S7f_equal!$+,;trans!tNP7StepTac6u_Z2bv!{\c3env!{VX!#tw5wb!snjp!vq>8iff_refl!#B?5;ZifyClasses5mkrel!#GjD4!snB;rew_!tB%v!sQB3inj!#@S@3Sem5alu64!#<MX5v_ad!#=7V7LibTail7vadd_wZ!{_W!#=z'alu!tU,K!#Q9:1!xucsp!ttV!#>f-img_!#bh'C!#:0Pm_fds!sZQ9fd_lookup!#;DP7FdE!#{W%!s^P8m_halted!tuRm_vm_lazy!#yRRRef!wg$Defs7s!#Tp#t!#X:&!#EHU7outside!y^'!|j4!#Og+3!ybR>RefPrintfFirstA!t{&_!#Fb2!zz13Nat!#_[#!z/Y@!#Hp'_!#KK%!t3&!#G'4:!sG%_ap!#f33Peano2lt!tSZ=!#cE%!t%#_l!#76hsr!snikn!yB\D!x$+!#;y$_s!#=T+!y1`9rz_run_l!$1Ce7sc_bufp!spe8!sp%sz!sqeE!$5U+!#Y`$!{p$!wOV!#oX#1W!#90^4mks!#J?Q3Run6config01I!#J>W8realiz!$/++!#=]A7!#>0%!#Go\8sym_exec!t>H5mk!~f$!sK@6!sK$2!#AI73not!#P@E7!x]Rcfg=hunspe!yQ#cf!#rb%!#}6\FUELH!skb6STOPSH!~Yg4scr!#kpb=!#y:'_le!#55&!#U8<6inj_lt!t=\4h!#73'!sj_!#7/W!|^+4TS!$A8&I!#U=V0!$&5_kn!$&5%!$=G]s!$=G/!t]\7hs_cov!$/hb<hs_itinera!#V2&!#d`H!#lB68ZifyInst7Inj_Z_Z!{Agimg!x^W!#FW'0!w%c!$1Lb?!$'/,!}_,!zF^o!zF,!uR^o!yUio!yU3!vFi!xd+!uXcC!yS'!#Fh7e00!#HV6sub!#;YA9and_morph!#f2;8max_spec!|_D5Psatz!#x+7!sO8!#wg6!#og:!#y%>3Pol!#r+E!tD&4!$aw,!u|&?Rel!$7[#!s6&=eq_Tran!$Jj$!$2M;nth!sr59M!vl#isms:re!vU#tful!tAE<eq_Reflex!t@0!s|5Jr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^??eq!tM#per!tT;!sR,@!u$0per!#G`Yget!#ND&!t<>M!#M3$co_!$7\#v_impl!|2%ism!x{<seq!#d2X;nth_map_!sh#!tl&!#RL4=app_nth2_plus!#G}\2!#eB&!#7_]!#v@-!$-V;max!#GvE6!sg+5!sf$8!#5##Na!#4n+!#D7<;inj_sub_max!sM>8!sM%cc!#E&Ce!#4>M1i!v^[3hfH!#M\'!#v#;modulo!yhP!$<'%6stk!#|dX1U9LibDiagKn8cell!#}T,!#@CI>!#ey#!sE+@word_to_le_bytes!t^\9cana!#yY-!#f8OSeq!{h#9!~`#_zero!{jb9h_ev_junk!}h2!yO,9SatDivModCZ!#Yj#!#z4$!$6m&!tHQ@!#N4'BufBase>!$&:%_by_idx!tT%!#gm7!$,B$1!t?c9all!tB#32!vYb5HF_FR!z\b:diag_!za$!x}V!#8`'9u64_range!|<ckn!t\\!}m&<kalign_int!z]'!smY!uF$!smc=kwr_of_!#3R/!snV:!#mW#!t[/!#3OX8store!tY#!{-b=data_!st+!ySVAgentLib7!yS#li!#}1i6estart!w0];k!#6j#!w1/!{4[;!#6j%know!sqb?!}_,!sug;!$7k%!#lc#!#5J1!$'Q82!t:\6CANARY!t5%i!#Ad\fP!#rA,!#9h^!$;U/!so_!$;P0!soO!$Q41!$,q-!zqO!#py+;!sj%!|V#!#u[\B!#o?+!~71k!w|c1!w3b8hs!#mG$!~6]7reg_val!wtdsr_ge!wtW!#Kp'5krea!#xE'!#A$3!#k1/eq!#lm#!t6X9!t6$!$#]+!wE^o!wE/!#_$^!$h`,".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nilhc3nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~ke6kentryke4EVarke2SAke4ELitke5KWordke3KWr89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9RefHdrErr4FPX1~~~~~~r75HF_FRhc3appke6KAlignke4KImgke6KRange79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9LibDiagKn~~~~~~hi16CANARYhi1adiag_cellshi18kn_cells46Stdlib6ZArith6BinInt1Zho33opp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcLibStdioCall~~~~~~hq29stdio_reske4exprhq24SCR_hc4prodke8sidecondhc3fsthc4pair37Corelib4Init5Logicihe2eqke9sym_stateihe3andr75hs_schc3sndke7scriptshc4boolke4s_pcr75hs_rAr75hs_rChc4Somehc6optionhq24sc_fhq25sc_fdhq24sc_lhq26sc_rethq24sc_shq2astdio_callr75hs_cAr75hs_cCr76hs_knAr76hs_srAr75ho_scr75ho_rAr75ho_rCr75ho_cAr75ho_cCr76ho_knAr76ho_srAr76ho_srFr76hs_srF04Npos35stdpp9bitvectorbdefinitionsjje2bvhc4None69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jm83rdn69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~jqa9msg_short69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~juefloaded_segmentsjje7Z_to_bvjqabmsg_overrunhc6length69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~kla7sregionke5saddrhc4trueklablog_coveredke5s_logr79h_regionske3env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~kt68blobs_evke3Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~li37vals_ev79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9RefHdrErr~~~~~~lm75HF_FRho33subjjebbv_unsigned37Corelib5Lists7ListDefls43mapkla6rdenot89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9RefHdrErr5Sound~~~~~~luc3ENVlucbh_regions_wlm79h_regionsho32leklacregions_flat3h5LinuxProcessSemantics5Riscv7Preludemm95bvmap3h5LinuxProcessSemanticsfLinuxProcessSem3Runmp85mkCfgjm84mkstjm87seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~mu0dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~ni88realizeskt69junk_vals79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~nnc7know_oknnc7regs_ok3h5LinuxProcessSemanticsfLinuxProcessSem5Statent75event69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~oge9frame_modni84TSetni86t_emitjqa1Wlm74h_knlm74h_srlm76hs_knFlm76hs_srFlm76ho_knFlm76ho_srF37Corelib4Init3Natoq23sub37Corelib4Init5Peanoorb2leorb2ltjm84getrke2evlm73ENV89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9RefHdrErr5Plain~~~~~~ouf6h_valsho36of_natouf3hfHouf6hfPostnt75Modelnt78m_haltednt79m_vm_lazynt77FdEntrynt79FdChannelnt79fd_lookupnt75m_fds" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition HF_FR : Z := 256%Z.
Definition STOPSH : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0+uiuu8@3$1$0+knht8@1$2$0").
Definition FUELH : nat := 5000.

(* [comment removed for export] *)
Definition h_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0 | 4 => ELit 0x10ebf8%Z
                          | _ => EVar (3 + i) end)%nat (seq 0 32)).

Definition h_kn : ltac2:(zQ "20!j4!od@1$0$1") := ltac2:(zQ "h10!od!jb!p6!pd!q2!q9!r1!va!hg2!k2!hg8!hh1!hh8!hlf!hm9!hn7!hpb@3$8$0@3$1$0@2$a@1$2N0+h0@3$1$0@3$c@1$2N0+hggggglg0+nvvvvvvvvvvf@3$1$0@2$6@2$3@1$2N0@1$h0$7$7@3$1$0@2$b+hggg0+vkgg0@3$1$0@2$6@2$3@1$4Z+vsgg0+jlgg0@3$1$0@3$5@2$3@1$4Z+hgurl0N4@1$2N1@3$1$0@3$5@2$3@1$4Z$dN8@1$2N2@1$9$0@1$f$e").

Definition sc_dummy : ltac2:(zQ "10!hu3$0") := ltac2:(zQ "50!q2!k2!hv0!od!hv7@c$4ZZZ@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$1$2@1$1$3").

(* [comment removed for export] *)
Definition hs_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x4719c h_sr [] h_kn 35) []).
Definition hs_cA := Eval vm_compute in (carry (s_log (fst (fst hs_rA))) h_kn []).
Definition hs_srA : list expr := Eval vm_compute in (s_regs (fst (fst hs_rA))).
Definition hs_knA : list kentry := Eval vm_compute in (fst (fst hs_cA)).
Definition hs_sc : stdio_res := Eval vm_compute in
  (match stdio_call 35 hs_srA hs_knA with Some r => r | None => sc_dummy end).
Definition hs_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0xe3780 (sc_sr hs_sc) [] (sc_kn hs_sc) 67) []).
Definition hs_cC := Eval vm_compute in (carry (s_log (fst (fst hs_rC))) (sc_kn hs_sc) []).
Definition hs_srF : list expr := Eval vm_compute in (s_regs (fst (fst hs_rC))).
Definition hs_knF : list kentry := Eval vm_compute in (fst (fst hs_cC)).

Lemma hs_itinerary : ltac2:(zQ "i10!h9!j4!hvf!ig6!ih1!ih7!ij2!hv0!ij8!ik4!ikb!k2!il3!od!il9!im3!q2!ima!hu3!in1!in9!io1!io8!ip1!ip9!iq2!iqa!ir4!irc!isa!it2!ita!iu3@2$9@3$6$0@1$h1@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h3+uiuu8@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h3@1$b$3@2$9@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$hd@1$b$3@2$9@3$6@1$h6$h2@3$hcNi3$i0$hf@2$h5$h2$a@2$9@3$6@2$2@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0@1$ha$a@1$h7$a@1$h8$a@1$hb$a@1$h9$a@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0+ujno0+vsuu8+2@1$h0+hjqga@1$h0+hf@2$9@3$6$0@1$h1@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h4+knht8@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h4@1$b$3@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$he@1$b$3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "##D:p;1p;3p;2p;<p;4p-1R0p10000R1p4p710p9P0P!s2$2!s3/3110p9!sQ$N!sO&1000i!s2&8g001Gj11Tg001lj3:Tg002Fj1Y!s/$fj1XTg003Fj1e!s/$hj10Tg004Mj1?!s/$kj1<Tg0062j18Tg0079j1^!s/$Wj3fTg008^j12Tg009=j2dTg00:Fj3cTg00;Oj2\Tg00<Xj2bTg00=aj2@Tg00>il<mTg00@7j2`!s/$Yj2QTg00A9j4G!s/$Yj2;Tg00B4j2U!s/$Nj4I!s/$ij3NTg00CFj1_Tg00DKj3W!s/$hj3lTg00F5j1kTg00G>j1jTg00HEj1hTg00IMj1gTg00JTj1iTg00K[j39Tg00L;j3LTf0R1#0#0#0p=R%01#!s$$p=F!s2$p=5%0!sF%?p==%1!s:$4%11#0p=7!s6$!sV%V!sN'0p=6!sF$#0p=K%?1#<p=>!s8%!s\$M%21#2p=T!s-$#2#2p=J!sX&#0p=Dg00MDR0f2R2#8f1R3#8=90139p=BA90319902p=P%83=901p=]!tV+!s$'p=O%^1,@3p=E!tg$p=C!to%?!s;$[f3R4/@2?L31p=ag00NKR5f4R6%?4'@?L23;91p=H%04!tf%#?,@6?L23=951p=3%1!s?9Af6f5;L6AL4!s9%595p=SA95319952p=Z!sA+p=ng00OTR1g00P2R4#1R3#1R2#RR6#1R7#F#F#5#=R8;:8g00PWR9#YR:%X9R9;:9R;g00QbR<#eR=%12R2#1R>#1R?#0R@#0RA#4RB#1RC#FRD!sp$E%04RF#?RG%77#V#6#=R7%0FRH#1RI#FRJ#K#VRK#7#6#>RLPLPLg00S0#<RM%1I#M#6#M#>RI%>>RNg00SNg00T:RO#8RP%0HRH#0RQ#0RR#0RS#^#<3fRT%2ORO#2RU#TRV#TRW#TRX#2#TRY#2RZ#2#J#JR[#2R\#2R]#2R^#2R_#2R`#2Ra#2Rb#2Rc#2Rd#2#JRe%<7%4QRf#M#4Rg#V#D#>%2e#JRh#8%2hRh!s'%>4%Jh!s:2!s'7<ER4%8]R]%8^R^%2h#T!ta$!sO1%X03B3B9Bcd9Bab9B_`3P5PN3B3B3B5PN7!s2$P,]W7PT']PM%1CRC#0RT#0RW#0R`#0PXPLPM%1`!s/'WRW!s<,DRDPXPMPMP!s-&%1TRT#1RD#1R`#0R_#RPV%4?#O#O#OR?#1#4#V#ORb#1!s:$>1EP6PXP^%03R3#CR^#0,EPPXP]%1FRF#R!s4$%8\1EPRPX%8[1EP^PX%8Z1EPQPX%8Y1EPHPX%4HRH#D#4#7#4#=RY#<%?Q,dP%CSRS#6#6RQ#0!y%$6#=%?b5cP1EPS%?S'\%?Q%02#DR2#6#6#='b%CA#6#6,[M%13R3#0!y}$6#='\PM%0g#M#=PV%8OCa%0J#4RJ#RRg#F#=RA,@MPX%8U%42#5R2!s;$U!s;%0H#V#5!s$$C#>%F>R>#5#7RH#C!{[$Q!sM$P4%1!z\%S#0#7,[MPX%43#5#M#D#6#>PM%1S!w:&7HPX%<QPM%K>R>#FPX%<APM%1>#5R>#0PX%K2!s['>PX%<U%0B!sr$=RB!te%<B1@MEPV%>F!xT$PX%<8PM%CTRT!x\%PT!t=&0DPV%<GPM%K_PV%>?R?PMP`PVP?PM%4CRC#5R`PXP4PM%7CRC!y9&!s-&%D@!~N$C#0R4#CR_!ye$!yR$_!s/'4#7#5#C!sy+#CPX%D`!u8$K@#4PO!sN%gRg#0R@#5R`#KPV!s;%@R@!v7'JRJ#5#7!s@&DJ#7!sb+0KRK!tH,K!s/&R`!sE%P@!sZ&7g!ul'f#D#7#DRf#R!si&KfPOPM%X5DHDHD3D3!s++ADA!s+$!s8'A!s+&H!s2'FS!s0$!s2&FS3Z3Z3ZCnFSFSFS!sN,DAM<m,`<RM;:MRO1Q11Rf/Q1RX/Q0Rg/Q0RVPgP0PXP0PfP1!s$$7PECGPGCGPICGPNCGRN;:NRIA:1YYRG1;;;RE';R7';R@';R`,;;RK';1U18P;PK1U:9RKP;P`PKPOP@1U=MPIP71UVNPGPE1U1YP;P;PKPKCI!s$/g00TYRK1QK:R;g00UeREg00Vo3NRG7N:#_=:18AWK:G=::9%Y5R51Q5:RGg00X4#YR8g00XT3N7W:=::9g00YYg00Z_5leg00[eRe,`<5:=!ul3%ke%jeCG%heCG%geCG%ieCG=:VNg00\j9N;ERE9NK!tS%YAWK:E!t1&]o9NG89W5!tB$';!s$/do"). Qed.

(* [comment removed for export] *)
Definition ho_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x471b8 h_sr [] h_kn 35) []).
Definition ho_cA := Eval vm_compute in (carry (s_log (fst (fst ho_rA))) h_kn []).
Definition ho_srA : list expr := Eval vm_compute in (s_regs (fst (fst ho_rA))).
Definition ho_knA : list kentry := Eval vm_compute in (fst (fst ho_cA)).
Definition ho_sc : stdio_res := Eval vm_compute in
  (match stdio_call 35 ho_srA ho_knA with Some r => r | None => sc_dummy end).
Definition ho_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0xe3780 (sc_sr ho_sc) [] (sc_kn ho_sc) 67) []).
Definition ho_cC := Eval vm_compute in (carry (s_log (fst (fst ho_rC))) (sc_kn ho_sc) []).
Definition ho_srF : list expr := Eval vm_compute in (s_regs (fst (fst ho_rC))).
Definition ho_knF : list kentry := Eval vm_compute in (fst (fst ho_cC)).

Lemma ho_itinerary : ltac2:(zQ "i10!h9!j4!hvf!ig6!ih1!ih7!ij2!hv0!ij8!ik4!iuc!k2!il3!od!il9!im3!q2!ima!hu3!iv4!ivc!io1!io8!ip1!ip9!iq2!iqa!ir4!irc!jg4!jgc!jh4!jhd@2$9@3$6$0@1$h1@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h3+uiuu8@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h3@1$b$3@2$9@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$hd@1$b$3@2$9@3$6@1$h6$h2@3$hcNi3$i0$hf@2$h5$h2$a@2$9@3$6@2$2@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0@1$ha$a@1$h7$a@1$h8$a@1$hb$a@1$h9$a@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0+ujno0+vsuu8+2@1$h0+hhko1@1$h0+hf@2$9@3$6$0@1$h1@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h4+knht8@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h4@1$b$3@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$he@1$b$3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "##CLp;1p;3p;2p;<p;4g001Gj11Tg001lj3:Tg002Fj1Y!s/$fj1XTg003Fj1e!s/$hj10Tg004Mj1?!s/$kj1=Tg0062j18Tg0079j1^!s/$Wj3fTg008^j12Tg009=j2dTg00:Fj3cTg00;Oj2\Tg00<Xj2bTg00=aj2@Tg00>il<mTg00@7j2`!s/$Yj2PTg00A9j4G!s/$Yj2;Tg00B4j2U!s/$Nj4I!s/$ij3MTg00CFj1_Tg00DKj3W!s/$hj3lTg00F5j1kTg00G>j1jTg00HEj1hTg00IMj1gTg00JTj1iTg00K[j39Tg00L;j3LTf0R0#!s$$p=Q%00#1#1#1p=F!s2$p=4%0!sF%?p=>%1!s:$7%1!sV$6!s6$!sV%V!sN'0p=5!sF$#0p=K%?0#=p=<!sD$p=A%20#2p=T!s-$#2#2p=J!sT%1#0p=S!s`&#0p=Dg00MDR1f2R2#8f1R3#8=91039p=CA91309912p=O%83=910p=]!t^+!s$'p=N%^0,@3p=E!to%?!s3$[f3R4/@2?L30p=ag00NKR5f4R6%?4'@?L23;90p=H%04!t^%#?,@6?L23=950p=3%1!s?9Bf6f5;L6AL4!s9%595p=RA95309952p=Z!sA+p=ng00OTR0g00P2R4#1R3#1R2#QR6#1R7#F#F#4#>R8;:8g00PWR9#YR:%X9R9;:9R;g00QbR<#eR=%12R2#1R>#1R?#0R@#0RA#7RB#1RC#FRD!sp$E%04RF#?RG%67#V#5#>R7%0FRH#1#FRI#K#VRJ#6#5#<RKPKPKg00S0#=RL%0HRH#1RM#4#A!sH$4#<RN%<>ROg00SNg00T:RP#8RQ%0HRR#0RS#0RT#^#=3fRU%2PRP#2RV#TRW#TRX#TRY#2#TRZ#2R[#2#J#JR\#2R]#2R^#2R_#2R`#2Ra#2Rb#2Rc#2Rd#2Re#2#JRf%=7%7RRg#S#7Rh#V#D#<%2f#JRi#8%2iRi!s'%<4%Ji!s:2!s'7=ER4%8^R^%8_R_%2i#T!ta$!sO1%X13C3C9Cde9Cbc9C`a3O5OO3C3C3C5OO7!s2$O,]X7OU']PL%1CRC#0RU#0RX#0Ra#0PYPKPL%1a!s/'XRX!s<,DRDPYPLPLP!s-&%1URU#1RD#1Ra#0R`#QPW%7?#N#N#NR?#1#7#V#NRc#1!s:$<1EQ6PYP_%03R3#AR_#0,EQPYP^%1FRF#Q!s4$%8]1EQSPY%8\1EQ_PY%8[1EQRPY%8Z1EQHPY%1MRM#D#7#6#7#>RH#=%?R,dQ%ATRT#5#5RR#0#5#S#5#>%?c5cQ1EQT%?T'\%?R%02#DR2#5#5#>'b%AA#5#5,[L%13R3#0!ya$5#>'\PL%0h#S#>PW%8PCa%0I#7RI#QRh#F#>RA,@LPY%8V%72#4R2!s;$V!s;%0M#V#4!s$$A#<%F>R>#4#6RM#A!{_$R!sM$P4!uD%0RT#0#6,[LPY%73#4#S#D#5#<PL%1T!w:&6MPY%=RPL%K>R>#FPY%=APL%1>#4R>#0PY%K2!s['>PY%=V%0B!sr$>RB!te%=B1@LEPW%<F!xT$PY%=8PL%AURU!x\%PU!t=&0DPW%=GPL%K`PW%<?R?PLPaPWP?PL%7CRC#4RaPYP4PL%6CRC!y9&!s-&%D@!~R$C#0R4#AR`!ye$!yR$`!s/'4#6#4#A!sy+#APY%Da!u8$K@#7PP!sN%hRh#0R@#4Ra#KPW!s;%@R@!v7'IRI#4#6!s@&DI#6!sb+0JRJ!tH,J!s/&Qa!sE%P@!sZ&6h!ul'g#D#6#DRg#Q!si&KgPPPL%X5DHDHD3D3!s++BDB!s+$!s8'B!s+&H!s2'FR!s0$!s2&FR3Z3Z3ZCnFRFRFR!sN,DBM<m,`<RL;:LRP1P00Rg/P0RY/P1Rh/P1RWPhP1PYP1PgP0!s$$7PECGPGCGPNCGPOCGRO;:ORNA:0HHRG1;;;RE';R7';R@';Ra,;;RJ';1U08P;PJ1U:9RJP;PaPJPPP@1U=LPNP71UWOPGPE1U0HP;P;PJPJCI!s$/g00TYRJ1PJ:R;g00UeREg00_43MRG7M:#_=:08AWJ:G=::9%Y5R51P5:RGg00X4#YR8g00`93M7W:=::9g00a>g00bD5lfg00cJRf,`<5:=!ul3%kf%jfCG%hfCG%gfCG%ifCG=:WOg00dO9M;ERE9MJ!tS%HAWJ:E!t1&eT9MG89W5!tB$';!s$/do"). Qed.

(* [comment removed for export] *)
Lemma hso_srF : ltac2:(zQ "50!j4!ij2!hv0!ji6!jif@3$1@1$0$2$3$4").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "##+mp;1p;2p;3g002Fj1ATg008^j10Tg003hj11Tg001Gj15Tg004Mj1:!s/$kj19Tg0062j13Tg002fj1>Tg00B4j2@!s\$lj3?Tg00K[j36Tf0R0#0#0p==%0!s0$#0p=2%10#1p=8%50#5p=4g00MDR1f4#3f3#3f2R2#3f1R3#3=61056156136p=7A61309612p=;%3!sD$p=<%A1R0g00T:R3#=#2R2#0#2R4#0R5#0#2#2R6#0R7#0R8#0R9#0R:#0R;#0R<#0R=#0R>#0R?!s\$@g00P2RA#1#8RB#5#4#1#8!s-&!s2%:#9%33%1!sD'5!s&$4!s$$!sF'0@#2R@#3%0@R@!s'$P4P5%:A#9%2@!s@1!s'7P6P7P8P9P:P;P<P=P>P?%0@#=!uE$!sT1%>1D7!s$'3;D73;,<23;'<'@g00fYg00g_5?0do"). Qed.

(* [comment removed for export] *)
Lemma msg_short_img : ltac2:(zQ "b0!jj8!jlb!j4!jm1!io1!io8!ij2!jq3!ju1!ki4!kj7@3$6@1$5@1$2@1$1@1$0#8@4$7$9\0@1$1@1$0#k0@1$3@1$1@1$0#8@2$a@1$0#k0+hjqgaNhf@2$4@1$2@1$1@1$0#8$8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "##0Ep;1p;2p;4p;3g003hj11Tg00hej1@Tg00iCj1=Tg002Fj1BTg003Fj1ITg001Gj10Tg004Mj14!sS$fj29!sS$fj1ATg00@7j2?Tg00B4j2HTg00jYj1GTg00k;j2FTg008^j16!s8$aj4D!t$$lj3CTg00laj3>Tg00K[j3<Tf0R0#1#4p=5%10#1p=;f3R1f2R2f1R3/903>p=3%0!sB$8f4R4A>123;<0p=:A<2309<41p=2%60#6p=E!s-$#6#6p=7g00P2R0#1R4#1R1#1R3#@R2#=R5#BR6#IR7P5P2%0!tT$R8#1R9#1R:#0#0#4R;192;!sG%8R8#0R;#1#5R<192<!s=$;!s=$#4R<P2P<C3R!s=%80R0#8R=#4R>P2P>C3!sT%3R3!s9,R>P5P!sV%0;R;#5!sk21!v8%5R?P2P?!si&0=#4R?192?!s5$5=R=P2P=C3R=P5P>!uC,0!sN18R8P2P8C3R8!t@&#4R;P2P;!t#&50R0P2P0C3R0P5P=!u>%9R9!v#%!sP%R;P5P0!t7&=P5P!ss%1:!sK$:P2P:C3R:!uN&>!sG&;P5P:!t3%9R9P2P9!tB$!sr'2%04#5R41924%A5D:D2!s$4:!s&&!s2%:,?6'Hg00mD%13#@R3#=%G5U%01#0#8#8#;#;#8#0#5,F3g00T:#6#E#7!s$/CDg00nK,?65C7do"). Qed.
Lemma msg_overrun_img : ltac2:(zQ "b0!jj8!jlb!j4!jm1!io1!io8!ij2!jq3!kk2!ki4!kj7@3$6@1$5@1$2@1$1@1$0#8@4$7$9\0@1$1@1$0#k0@1$3@1$1@1$0#8@2$a@1$0#k0+hhko1Nhf@2$4@1$2@1$1@1$0#8$8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "##0Rp;1p;2p;4p;3g003hj11Tg00hej1=Tg00iCj1>Tg002Fj1ITg003Fj1HTg001Gj10Tg004Mj1:!sS$fj29!sS$fj1ATg00@7j2@Tg00B4j2GTg00jYj1FTg00k;j2ETg008^j17!s8$aj4C!t$$lj3BTg00laj3?Tg00K[j3;Tf0R0#1#1p=6%00#:p=4f3R1f2R2f1R3/903?p=2%1!sB$5f4R4A?123;;0p=<A;2309;41p=3%70#7p=D!s-$#7#7p=8g00P2R0#1R4#6R1#=R3#>R2#IR5#HR6P2P3%0!tP$R7#1R8#1#0#4R9P3P9C2R9!sG%7R7#0R:#1#5R;P3P;C2R;!sA$67#4R7P3P7C2R7!su&#1R0#0R<#1R=#:R>P3P>C2!sV%1R>#:R?P3P?C2R?P2P!t2&:R:!tG45:R:P3P:C2R:!sL%8R8#0R@#5RA193AP2P!tC%4@R@P3P@!t5&04R4#0!s$$4R@193@P2P!u$%18#4R8P3P8C2R8P2P:P2P!tV-<#5R<P3P<!sq$8!sZ%0!uG$8!sA,R<P2P<!tI%=!s;0!tw%48!t2'!t+&7!sA+10#5R0P3P0!sC$!sk%5=R=P3P=!u6&54R41934%A2D<D3!s$4<!s&&!s$$,@5'Gg00mD%1>#=R>#>%F2U%01!x<$6!s&$6#6#4,E>g00T:#7#D#8!s$/CCg00oM,@55B6do"). Qed.
Lemma msg_short_len : ltac2:(zQ "60!kl1!k8!ij2!jj8!ju1!jlb@3$2$1@2$0@1$5@1$3#8$4Nhf").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "###up;1p;2g008^j11Tg00B4j22Tf0R0#1#1p=3%1!s0$#1p=0g010Qg00T:#1#3#0!s$/'2o"). Qed.
Lemma msg_overrun_len : ltac2:(zQ "60!kl1!k8!ij2!jj8!kk2!jlb@3$2$1@2$0@1$5@1$3#8$4Nhf").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "###up;1p;2g008^j11Tg00B4j22Tf0R0#1#1p=3%1!s0$#1p=0g010Qg00T:#1#3#0!s$/'2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_regions : ltac2:(zQ "20!j4!kp3@1$0$1") := ltac2:(zQ "b0!h9!kpe!hvf!jb!ih7!pd!va!k2!q2!p6!hpb@3$3@2$2$1$0@4$4$1$0@2$5@1$9N0@1$a$6$6@3$3@2$2$1$0@4$4$1$0@2$5@1$8Z+vsuu8+u8@1$7@2$2$1$0").

Lemma hs_covA : ltac2:(zQ "d0!ih1!j4!ig6!ij8!im3!hvf!kq6!ij2!kqd!krc!il9!ks4!in1@3$7$4@2$8$b@1$9@3$0$3@1$1$2@3$0@2$5$3@1$1$2$a$c$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefHdrErr ()) ["FPX1"] "p;2p;1p;3p10110p4p70R0p10122p4p710p8P0p1012Np4p710p8g00B4j26Tg002Fj15Tg00@Yj21Tg00Bij30Tg012jj14Tg0140j22Tg001lj33Tg00X4R0g0156R1'6g015Vg00TYR2g00PW#5R31123g00Ueg00Vo3030#4'2=301do"). Qed.
Lemma hs_covC : ltac2:(zQ "d0!ih1!j4!ig6!ij8!im3!hvf!kq6!ij2!kqd!krc!il9!ks4!in9@3$7$4@2$8$b@1$9@3$0$3@1$1$2@3$0@2$5$3@1$1$2$a$c$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefHdrErr ()) ["FPX1"] "p;2p;1p;3g00B4j26Tg002Fj15Tg00@Yj21Tg00Bij30Tg012jj14Tg0140j22Tg001lj33Tg00X4R0g0156R1'6g015Vg00TYR2g00PW#5R31123g00Ueg00\j3030#4'2=301do"). Qed.
Lemma ho_covA : ltac2:(zQ "d0!ih1!j4!ig6!ij8!im3!hvf!kq6!ij2!kqd!krc!il9!ks4!iv4@3$7$4@2$8$b@1$9@3$0$3@1$1$2@3$0@2$5$3@1$1$2$a$c$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefHdrErr ()) ["FPX1"] "p;2p;1p;3g00B4j26Tg002Fj15Tg00@Yj21Tg00Bij30Tg012jj14Tg0140j22Tg001lj33Tg00X4R0g0156R1'6g015Vg00TYR2g00PW#5R31123g00Ueg00_43030#4'2=301do"). Qed.
Lemma ho_covC : ltac2:(zQ "d0!ih1!j4!ig6!ij8!im3!hvf!kq6!ij2!kqd!krc!il9!ks4!ivc@3$7$4@2$8$b@1$9@3$0$3@1$1$2@3$0@2$5$3@1$1$2$a$c$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefHdrErr ()) ["FPX1"] "p;2p;1p;3g00B4j26Tg002Fj15Tg00@Yj21Tg00Bij30Tg012jj14Tg0140j22Tg001lj33Tg00X4R0g0156R1'6g015Vg00TYR2g00PW#5R31123g00Ueg00dO3030#4'2=301do"). Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variable model : ltac2:(zQ "10!pl8$0").
  Hypothesis Hh : ltac2:(zQ "60!jj8!jlb!jm1!io8!ij2!pm1@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!jj8!jlb!hvf!j4!k2!ij2!pmd&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd2 : ltac2:(zQ "90!jj8!pna!kj7!io1!io8!ij2!po5!pp2!ppf@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+2@2$3$1@1$6@2$2@1$0#k0+2").
  (* LPS 75d69e00: the stderr write needs the launch's channel reader
     (LibStdioCall.stdio_call_sound_post's premise), constant over the run. *)
  Hypothesis Hrdr : m_channel_reader model = true.

  Definition ENV : ltac2:(zQ "40!j4!jj8!kt0!jlb>4vals@1$0@1$3@1$1#k0$2") := ltac2:(zQ "70!j4!jj8!jlb!k2!lh1!lhd!llc\4vals@1$0@1$2@1$1#k0@2$5@1$6^1@1$4@1$3@1$0@1$2@1$1#8").

  Definition h_regions_w : ltac2:(zQ "50!j4!hvf!jj8!h9!jlb@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "b0!jj8!h9!jlb!hvf!jb!ih7!lq5!kj7!k2!lqe!lr5@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$7@1$0#k0@2$9@2$a@1$0#k0?3sp0$6$6@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$7@1$0#k0+vsuu8+u8@1$8@2$3@1$2@1$0#k0$1").

  Lemma h_regions_denot : ltac2:(zQ "f0!jj8!jlb!j4!hvf!ij2!h9!ltb!lu2!kp3!llc!mj0!mj7!mk6!ml3!lr5>4vals@1$2@1$1@1$0#k0>0@3$4@1$1@1$0#k0@2$9^1N0?3sp0>0@2$d+hggggglg0@2$e@1$0#k0?3sp0@3$4@1$2@2$3@1$1@1$0#k0$5@4$6$8@2$3@1$1@1$0#k0$5@1$7@1$a^3$c$b").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["Sound"] "##/Rh03Hloh12P0h21bh31rh44valsp;1p;2p;3p;4p;6g00hej1KTg00iCj1DTg002Fj1ATg016_j2?Tg001lj38Tg003hj11!s8$Gj10Tg004Mj19Tg017aj27Tg018Kj2BTg00@Yj2;!s8$gj1PTg019Dj2:Tg00k;j24Tg00A9j42!tC$fj1>Tg00K[j33!sS$aj2OTg00B4j2NTg000ij6MTg01:>j1<!sA$ij3JTg01;Aj1ITg01<Hj2FTg01=Oj1GTg00DKj3HTg0062j1ETg00=aj2@!u3$kj1LTg0122j4=Tg01>Uj1CTf0R0#1#1p=6%1!s0$#1p=5g00P2R1#6#5R2#KR3#DR4#Ag00T:R5,?0p,3sp0R6584%62R2#1#5!s$$0#1#0!s0$91736R7'BP4P6g00OTR6,;4R8#AR9P4P61730%92R2#PR:':,43P2C2!sT&S0R;,43,73%01#0R1#0!s$$6!s-&1!s--1#6#9R<!si$%1!s8,1C2%>8R=538538!tA$O72!t6-143<P1C2=38=538R=38X241N9=f2R7/?5f1EMg0110R>P!sg$f3#<g01?VR4?J60R?#I'F,73%G?!tM$AH460C2X3>1;46R0P4P6%E5/@:!tB'%L;/@!tD$%>053033C==89=eP>P8%<7#Cg015VC=g01@^589eW0W1W4o"). Qed.

  Lemma h_regions_flat : ltac2:(zQ "a0!jj8!ml3!jlb!lr5!j4!ij2!ml9!llc!mj0!mk6>4vals@1$4@1$2@1$0#k0>0@3$5@1$2@1$0#k0@2$7^1N0?3sp0>0@2$1+hggggglg0@2$3@1$0#k0?3sp0>0@2$1@2$3@1$0#k0?3sp0+nvvvvvvvvvvf@2$6@1$8^4$9").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["Sound"] "##<Hh01Hh11rh22Hah37__arithh44__ffh58__varmaph65__with74__x1h83Hhih93Hloh:2Hrh;2P0h<6__sat0h=!s/%1h>!s/%3h?!s/%4h@1bhA4valsp;1p;2p;3p;4p;6p;7p;8g003hj11Tg00hej1aTg00iCj1^Tg002Fj1VTg016_j2QTg001lj3I!s/$Gj10Tg004Mj15Tg017aj2DTg018Kj22Tg01Aij3rTg0062j1o!sA$gj1nTg00=aj2PTg00A9j4O!sn$kj1cTg01B@R0j2JTg01:>j1:!s:$Zj36Tg019Dj23Tg01Cej2_Tg01DBj28!s/$^j2]Tg01EFj3\!u5$fj1[!s8$jj2ZTg01FHj1Y!s/$fj1XTg01GQj2WTg00jYj1sTg01H4j2U!s/$Wj2qTg01I:j3F!s/$]j3pTg01J@j4H!s/$kj2mTg00B4j2lTg01KMj2hTg01L9j3g!s/$Xj4fTg000ij6eTg01;Aj1KTg01<Hj2MTg01=Oj1NTg012Nj6LTg01MJj1d!s/$hj2i!t1$ij3jTg00DKj3k!v[$Yj2GTg01Noj7TTg01OSj7bTg01P7j8`Tf0R1#!s$&p==%1!s-$C%01#0p=E!s-$!s$/p=Bg0110R2f1R3;I1p=;g01?VR4g00OTR5;j1p=>Ak451p=9g00S0R6/21p=7f2R71G31'Gp=@1263/G1p=A1U51p=?P7g01P[R8g01Q:R9P9g01QZR:P5P3g01R:P1CHg01RaR;FTp=4P3P8P9P9P:P1P!s9$SP7!s9+3P1Fbp=<f3R;!s;+7P3P1G`p=Rg00P2R8#1R<#1#=R=#aR>#^R?#Vg00T:R@,Q1p,3sp0RA5I?%C=RB#1#=!s$$0#1#0!s0$5RC1D>ARD'2%E8RE#0#ERF#0#B!s$+5RG,2Dg015VRH9r21P0P4P5%o@%5BRB#nRI'PPBCORJ/;3!sA$c6%CF#0#E!t6$!s+%1#C#5RF'P%1E!s5+ECOR4/;3g01SARK'Jf6RL#:%>7%9736P11;J7P2PJf8RM#:RN%>1RO%91RP36X12P?PA1D>1/3IRA%5<R<%5=R='_RQ,8A%7BRR13AB/2Q3@'AX@?1]<=R?186<%7=186Q[[RA%7<RSg01S^RTA\<=3UW2R=%7Q\T^2S!sA$T:RT#[RU%VTRT1Z53%Y5RV%X5RW1W58R8%?G54W%s9R9PW%?C=4W8P91U56R9%?BRX,q59F58R854WP5P8g01TfRY%?<=p5>R<CH,SWA4W9XAF58X=4W<5<W!s%%CRCR1mW:R:P1P7g00X4!z#$56RX'l1h17=I8XdAg563CfRXb4b5b6X75121G12C3137IRI18IQ13IB/2Q7@R'A[[^75P1PDf7RDPMO3b3b>b?1QD@PLEe%:DRD%>JR@#K'M,D>%N@'3RM18MQ%9JRJ#713MJ!v{&eA6D@JeP;P1ELW0P1O11;47/JKP01;4;PKf4R0#>%9056NP11;40P2P4f:#:R0?6OP!x>&P=PSPUPT%d5PV%?F9F59RV94W9P5PVPYP!vI%%?ERY94W9AF5VY!vM0P:P!uy&136FRF18FQ%7E13FE!t{&P1b3b<b=f9#:RF%>4RE!uZ+E'3R>18>Q%94R4#713>4!uZ,FE4ef5!uZ,PK%>L%9L560P1n010!s#%X0KP1O1n20!s9'2110!s3&!s`%!sB51000W:X12%:;/iHeW8W9W;WAo"). Qed.

  (* [comment removed for export] *)
  Ltac scs_nil :=
    lazymatch goal with
    | |- scs_denot _ _ _ ?l => let l' := eval vm_compute in l in change l with l'
    | |- Forall _ ?l => let l' := eval vm_compute in l in change l with l'
    end; apply Forall_nil.

  (* [comment removed for export] *)
  Ltac hf_sound pcA rA cA srA knA sc rC cC srF knF ITIN COVA COVC MSG_IMG MSG_LEN msg :=
    intros vals R M K HL P0 HR HK HKnil HCONT;
    pose proof (know_nth RSEGS _ _ h_kn 1%nat _ HK eq_refl) as Hrg; cbn [kentry_ok edenot ev ENV] in Hrg; rewrite P0 in Hrg;
    pose proof (h_regions_flat vals P0 ltac:(lia) ltac:(lia)) as RF;
    pose proof (h_regions_denot vals P0 ltac:(lia)) as RD;
    (* [comment removed for export] *)
    eapply (rz_run_lf RSEGS FUELH STOPSH scr0 pcA h_sr h_kn 35 (fst (fst rA)) (snd (fst rA)) (snd rA)
              (fst (fst cA)) (snd (fst cA)) (snd cA) (ENV vals) M (seg_rom RSEGS) R model);
      [ vm_cast_no_check (@eq_refl _ rA) | vm_cast_no_check (@eq_refl _ cA)
      | exact HR | exact HK | scs_nil | scs_nil | exact Hh | exact Hlazy | ];
    clear HR HK; intros RA MA HR HK EQA LFA;
    pose proof (log_covered_frame (ENV vals) M h_regions _ COVA RF LFA) as FA; rewrite <- EQA, RD in FA;
    change (s_regs (fst (fst rA))) with srA in HR; change (fst (fst cA)) with knA in HK;
    change (s_pc (fst (fst rA))) with 0xe2ee8%Z;
    (* [comment removed for export] *)
    pose proof ITIN as (_ & _ & _ & SC & _);
    apply (stdio_call_sound_post vals (blobs_ev []) srA knA RA MA model sc [] msg K
             HR HK (eq_trans (f_equal (fun n => stdio_call n srA knA) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn sc edenot ev ENV app];
      rewrite ?MSG_LEN; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ];
    [ unorm; lia
    | unorm; lia
    | unorm; lia
    | unorm; reflexivity
    | lia
    | left; rewrite P0, alu_add, vadd_wZ; unorm; lia
    | left; rewrite P0, alu_add, vadd_wZ; unorm; lia
    | unorm; lia
    | unorm; reflexivity
    | (* [comment removed for export] *)
      lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) 31 = _ =>
        rewrite (kimg_rdn RSEGS (ENV vals) _ knA ltac:(let i := kidx knA (is_kimg_cov a 31) in exact i)
                   _ _ a 31 HK eq_refl) by (cbn; lia) end;
      apply MSG_IMG
    | exact Hfd2
    | exact Hrdr
    | exact Hh
    | exact Hlazy
    | exact HKnil
    | (* [comment removed for export] *)
      clear HR HK; intros Rj MC HR HK HPOST;
      assert (FC0 : frame_mod MA MC h_regions_w);
      [ eapply sw_post_frame_mod; [exact HPOST|]; intros x Hx; unfold h_regions_w, HF_FR in Hx; cbn [outside] in Hx;
        unfold in_rng in Hx; rewrite P0, alu_add, vadd_wZ; revert Hx; unorm; intros (N1 & N2 & _); lia |];
      set (vals' := vals ++ junk_vals Rj) in *;
      assert (HL' : length vals' = 67%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity);
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
      pose proof (h_regions_flat vals' P0' ltac:(lia) ltac:(lia)) as RF';
      pose proof (h_regions_denot vals' P0' ltac:(lia)) as RD';
      change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK;
      eapply (rz_run_lf RSEGS FUELH STOPSH scr0 0xe3780 (sc_sr sc) (sc_kn sc) 67 (fst (fst rC)) (snd (fst rC)) (snd rC)
                (fst (fst cC)) (snd (fst cC)) (snd cC) (ENV vals') MC (seg_rom RSEGS) _ model);
        [ vm_cast_no_check (@eq_refl _ rC) | vm_cast_no_check (@eq_refl _ cC)
        | exact HR | exact HK | scs_nil | scs_nil | exact Hh | exact Hlazy | ];
      clear HR HK; intros RC MF HR HK EQC LFC;
      pose proof (log_covered_frame (ENV vals') MC h_regions _ COVC RF' LFC) as FC; rewrite <- EQC, RD' in FC;
      change (s_regs (fst (fst rC))) with srF in HR; change (fst (fst cC)) with knF in HK;
      change (s_pc (fst (fst rC))) with 0x471d8%Z;
      apply (HCONT Rj RC MF HR HK);
      eapply frame_mod_trans_same; [exact FA|];
      eapply frame_mod_trans_same; [exact FC0 | exact FC] ].

  Theorem hs_sound : ltac2:(zQ "i11!jj8!jlb!ki4!mj0!mof!hg2!io8!ij2!ms4!msd!mt5!nh7!nm3!nmf!ns1!nsc!kj7!kl1!j4!k8!k2!og5!ok6!ol3!olb!om5!ju1!llc!mj7!oma!on2!ona!oo4&>0@1$1@1$0#k0@1$6@1$1@1$0#8>4vals@1$h2@1$1@1$0#k0>1R@2$4@1$0#5@1$1@1$0#k0>1M~0>1K$h7>0@3$7$h3@2$h1@1$1@1$0#k0^4Ni3>0@3$7@1$1@1$0#k0@2$hb^5N0?3sp0>0@3$f@1$3^6$he^5>0@4$e$2@1$3^7^5$hd>0@1^5@1$h4$h5>0>2Rj@2$4@1$0#5@1$1@1$0#k0>2R'@2$4@1$0#5@1$1@1$0#k0>2M'~0>0@3$f@1$3@3$5@1$1@1$0#k0^c@1$d^3$i0^2>0@4$e$2@1$3@3$5@1$1@1$0#k0^d@1$d^4^2$hf>0@3$h6^c^3$hc@4$c$2$b@2$8@5$9?2fx^5@2$h0@1$0#k0+knht8^4@1$a$2?5model^c@4$c$2$b@2$8@5$9?2fx^9@2$h0@1$0#k0+knhpc^8@1$a$2?5model@2$h8@2$h9+2$ha^7").
Proof.
  (* LPS 75d69e00: replay replaced by the tactic it recorded, now with the reader premise. *)
  unfold W.
  hf_sound 0x4719c%Z hs_rA hs_cA hs_srA hs_knA hs_sc hs_rC hs_cC hs_srF hs_knF
           hs_itinerary hs_covA hs_covC msg_short_img msg_short_len msg_short.
Qed.

  Theorem ho_sound : ltac2:(zQ "i11!jj8!jlb!ki4!mj0!mof!hg2!io8!ij2!ms4!msd!mt5!nh7!nm3!nmf!ns1!nsc!kj7!kl1!j4!k8!k2!og5!ok6!ol3!olb!om5!kk2!llc!mj7!oma!on2!ooe!op8&>0@1$1@1$0#k0@1$6@1$1@1$0#8>4vals@1$h2@1$1@1$0#k0>1R@2$4@1$0#5@1$1@1$0#k0>1M~0>1K$h7>0@3$7$h3@2$h1@1$1@1$0#k0^4Ni3>0@3$7@1$1@1$0#k0@2$hb^5N0?3sp0>0@3$f@1$3^6$he^5>0@4$e$2@1$3^7^5$hd>0@1^5@1$h4$h5>0>2Rj@2$4@1$0#5@1$1@1$0#k0>2R'@2$4@1$0#5@1$1@1$0#k0>2M'~0>0@3$f@1$3@3$5@1$1@1$0#k0^c@1$d^3$i0^2>0@4$e$2@1$3@3$5@1$1@1$0#k0^d@1$d^4^2$hf>0@3$h6^c^3$hc@4$c$2$b@2$8@5$9?2fx^5@2$h0@1$0#k0+knht8^4@1$a$2?5model^c@4$c$2$b@2$8@5$9?2fx^9@2$h0@1$0#k0+knhr8^8@1$a$2?5model@2$h8@2$h9+2$ha^7").
Proof.
  unfold W.
  hf_sound 0x471b8%Z ho_rA ho_cA ho_srA ho_knA ho_sc ho_rC ho_cC ho_srF ho_knF
           ho_itinerary ho_covA ho_covC msg_overrun_img msg_overrun_len msg_overrun.
Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable model : ltac2:(zQ "10!pl8$0").
  Hypothesis Hh : ltac2:(zQ "60!jj8!jlb!jm1!io8!ij2!pm1@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!jj8!jlb!hvf!j4!k2!ij2!pmd&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd2 : ltac2:(zQ "90!jj8!pna!kj7!io1!io8!ij2!po5!pp2!ppf@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+2@2$3$1@1$6@2$2@1$0#k0+2").
  Hypothesis Hrdr : m_channel_reader model = true.

  (* [comment removed for export] *)
  Record hfH (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (tid can : Z) : Prop := HFH {
    H2  : getr regs 2 = sp;
    H4  : getr regs 4 = Z_to_bv 64 0x10ebf8;
    Hsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    HspLo : (0x100000500 <= bv_unsigned sp)%Z;
    HspHi : (bv_unsigned sp <= 0x7fffffffffff)%Z;
    Hstk  : stk_ok RSEGS mem sp HF_FR;
    Himg  : forall i, (0x10000 <= i < 0xf4000)%Z -> mem (Z_to_bv 64 i) = None;
    Hcells : cells_ok mem diag_cells;
    Htid  : rdn RSEGS mem (Z_to_bv 64 0x10eb50) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
    Htid32 : (0 <= tid < 2 ^ 32)%Z;
    Hcan  : canary_ok mem can }.

  (* [comment removed for export] *)
  Record hfPost (regs : bvmap 5 word) (mem : word -> option byte) (sp : word)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := HFP {
    P_sp  : getr regs' 2 = sp;
    P_tp  : getr regs' 4 = Z_to_bv 64 0x10ebf8;
    P_a0  : getr regs' 10 = Z_to_bv 64 1;
    P_cs  : forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - HF_FR), HF_FR); (Z_to_bv 64 0xfcee8, 232%Z)];
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0xfcee8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0xfcef0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0xfcef8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0xfcf10) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12f3e0));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0xfcf20) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12f3e0));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0xfcf74) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_stk   : stk_ok RSEGS mem' sp HF_FR }.

  Definition h_vals : ltac2:(zQ "50!jj8!jlb!h9!j4!mof>4regs@2$4@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3tid$2>3can$2@1$3@1$1@1$0#k0") := ltac2:(zQ "90!jj8!jlb!jb!h9!kj7!hg2!k2!mof!nmf\4regs@2$7@1$0#5@1$1@1$0#k0\2sp@1$1@1$0#k0\3tid$3\3can$3@3$5@1$1@1$0#k0@3$2@1$1@1$0#k0^3@3$2@1$1@1$0#k0@2$4@1$0#k0^2@3$2@1$1@1$0#k0@2$4@1$0#k0^1@1$6@1$1@1$0#k0@1$8^4").

  Lemma h_ev_junk : ltac2:(zQ "h00!jj8!jlb!h9!k8!ik4!ij2!or4!osf!ot5!mof!otb!ou3!ou8!pj3!pjd!kj7>4regs@2$9@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3tid$2>3can$2>1i$3>0@2$4@2$7N3^1@2$8^1Ni3@3$5@1$1@1$0#k0@2$b@1$c@4$d^6^5^4^3^2@2$a^6@2$f@1$0#5@1$e@2$6^2N3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["Plain"] "##J`h04__p1h14__p2h24__x1h34__x2h42H3h53Hi0h67__arithh74__ffh84__p3h98__varmaph:5__with;4cstrh<1ih=1nh>1xh?2z3h@1HhA2HihB1bhC3canhD7defaulthE1lhF5lemmahG1mhH4regshI2sphJ3tidhK1yp&0p;1p;2p;3p;<p;6p;4p;=p;9p;5p;Bp;7p;8g003hj1?Tg001Gj1MTg00hej1XTg00iCj1cTg01UMk20JTg008^R0j10Tg034mR1j2YTg02ICR2j2!sG$AYj21Tg035Gj2_!s~$lj32j1ETg01_SR3j13Tg004Mj1ITg019aj26!s/$Dj29Tg01`3k20;!s0$Vk306Tg00B4j28Tg026<l<UTg018KR4j25Tg01DBR5j24!tE$^j6gTg02W6j4iTg01a3j1lTg036Gj2mTg01B@j2F!s8$ij2GTg037Rj3HTg038;j2NTg0079j1n!s8$gk20ITg039Hk30HTg002fj1aTg00K[j3;!s8$Fj1`Tg01Ejk20GTg01MJk10FTg02EKk40DTg01FHk10?!s0$fk10>Tg01GQj2kTg01H4j2A!uY$ak30=Tg01J@j4BTg00jYk10<Tg01I:j3[!sB$kk20:Tg01KMk20!v#$L9k304!s0$Xk402Tg027Dj4eTg00k;j27Tg01V9j2OTg02G?j2WTg03:1k101Tg01Y5j1PTg01Z;j3Q!sB$aj4Cj1zTg03;=j4T!s/$dj1~Tg03<Sj4STg03=Jj3}Tg03>@j1{!s/$oj6|Tg03?Zj2^Tg03@Fl=yTg03A3j2DTg03B4l9x!s/$nj2wTg0122k403Tg03CJj6vTg000ij6bTg03DRk50!u9$6_j2uk108Tg01oFk109Tg022Hj2tTg03E4j2jTg03F7j4sTg01:>j1rTg03G=k20@Tg02YKmB0!w8$Xfl<q!yC$Xk60BTg01Nok70CTg01OSj7p!s`$Zj7oTg01P7k80ETf0R6#0!s$%p=<%06#0p>00g00S0R700@6p=>g00OTR8f1R9;26p==g010QR:P:P:P8P8P8g03H>P3P3P3f6R;g03H^f5R<f4R=f3R>f2R?P9P6NB0Ap=d!s_+0!sZ$>g03IEP!sH$M<qp=V!sE$1P3P4g03IiP<P=P>!sG'Up=f!sG$2P3P5g02`U!sG4RA2867p=]A;?969;=>p=KP9g01P[R5g01Q:R2P2g01QZR4P6J0Bp=\P8P9g02iXP6CBp=ZP9P5P2P2P4P6g01RaK0Cp=:P?!s=+9P6Fpp=@!s92op=hP>!s9+!tf$L0Ep=Lg00P2R5#?R1#M#XR0%?1#?R@#?#?RA#?#XRB#cRC+0Jg00T:RD#0RE#0RF#0RG/Y6%0G#<!s$/RH#0$00RI,J6'11_9GRJ#0RK#0RL#0RM=2:9%39RN%M5#IRO'6#>RP%I5RQ'9RR/9QRS/9QRT/=NP:P8%E:RUP3%E8%36R3,=NA2:9620;96406XK:X>:PMPT196QX>8RTPLPSPTPKPRPTPJPP1696#>XG8X=8RPP9PN188NRTPGPO188ORRFdCVCVCVP9PNPTM<U1YG9RK1J9IRS'115ONRL%M@#M#IRM,4NRV'1RWPKPSPLPVPGPOPR!sc%Ef!s-%PIPM188MRTEREgP6CiPW%l?%3?RW,57%3>RN/6ORV,m7147V%>VRL/=V'115V7%]L'1'F%3=/6ORL#>RVP8p-0RSg01T:RK1G8FRF1G8E1G8DRE5H85H8g03JKRX'NRYPK1G8G%n5-0I8>0H8F=H8E!sO$/NX1NEX%aKRE5;KDK%`KRXP820G8?P9&0F8H0DRF&0?8RZ&0>8R[1\[=1k85R51k81R11A8OR\60=8R]'Z,:[5@[R^P8P]g01R:R]1A87R_CB,:[1Z5_,:[R_5@[5h[&0<2R2P[P8P\P]P1!sJ%\[<R]5@[P21A8QR\9[85=[8\=[8\/Z1,:[CLCL20:[4R4P6P?g00X4R\g0156R`'82056?=2\`dB04879H02R`b7b9b:X28X38X0SW1169OR\,=6,1?Ra15\7%]6R\'1'F15O?/1=19?Q/9!s%$=>[[^28^38^0S^1SP6%3;RQ/4M16QO,47PQP9P?P=O6b6b?b4b;b5CePCP=PC17B>RQ17B?%aCRb5;CDKRc,OC/WJ=2:9RdePdPCP<!sQ$=RdA;CQbDKRQ,OC1_?GRe'WRf=2:?PC%ECRg&01CPCP>PCP;!s[$<A;CdbDKRdf7Rb#P5QCRh17B7RBCCPC1OCd1_>GRd'WRiPhPBCC%`CRjPC^DCRk]ERl^=:RmP:PlPUPjPk%EjPCPCPgPgCTRnCTRoCTRp!sG$oPjPkPn!sF%%~CCSCSCS9}mp%zCP>PiP:PU%{:PiP>P6E|PhPh1^jhPBPB1^CBM=y%3d,70,DbRdPd1^CdM9xWFP6!sz$e%P;RjPBCCRhA2C6dXBCRdPC%3e!s[$;RiPd18CiPCPeP:PC1703,DbX<:R31wDHH03P!uo$P3PePHPB1JeH16WO#>R3%IARA'4PeP3PPP?PW188WRP!}q%FdPHPA188AER1YG?RH1J?IR3!~Y$WRD14WMRd'1RUPHP3PDPd!~Q&?PWPPEf!s-%PIPMP!~M%9CiPU%l>157N1m7L147L1=VL'115L7%]V!~<%</6O#>P8A;KYEPXPFPZP[A@[]_9h[^P2P[1\[;P8P1g01Tf!},$M!|>$!|8$P8P5P11A8A!s:$CLCLP4P!{[3X1SX8S11>\,Fa14?M,1<14?A!{B1^8!{E$bRb,5O16bORO/57147OPb!{K&7!{K/EvEbA2ChiePCPfAQCQj!wC&QPjPBPeI07EbO2b@%P<9QCcRc/u9%3J!x:$<R052Ce&08c%X@#c#`#a$09't/j9=2C0e!#<0&Cs#r!s:'WAX<:XC8XJ8XICWHo"). Qed.

  Lemma h_regs_ok : ltac2:(zQ "a0!jj8!jlb!h9!io8!mof!nsc!ou8!pj3!pk7!on2>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>2sp@1$1@1$0#k0>3tid$2>3can$2>0@5$8^5^4^3^2^1@3$5@1$6@4$7^6^4^3^2$9^6").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["Plain"] "#$ZBp'0h02Hih11ni001nh27__arithh34__ffh48__varmaph55__with61bh71ih82Hah94__p1h:4__x1h;2H3h<2H5h=5Hcan0h>7Hcells0h?3Hi0h@5Himg0hA5Hsp17hB6HspHi0hC6HspLo0hD5Hstk0hE5Htid0hF6Htid33hG2PHhH7__sat34hI!s0&5hJ!s0&6hK3canhL4cstrhM3memhN4regshO2sphP3tidhQ1xi012H2i022H4i034Hcani046!tz%i054Himgi06!tt$6i075!tu$i085!tu$i094Hstki0:4Htidi0;!tu%2p%0p&0p;1p;2p;5p;3p;4p;6p;<p;7p;8g003hj1GTg001Gj1@Tg00hej1]Tg00iCj1aTg01UMk20!sK$3Fj1mTg03K7R0k50:Tg01VYk303Tg004Mj1FTg00k;j2TTg017aj2WTg03L<j2j!t6$lj3LTg018KR1j25!sC$\j4}Tg01DBR2j22Tg00AYj26Tg00jYj1iTg03M]j2wTg002Fj1eTg008^R3j10!t@$aj4sTg03Nej2rTg00@7j2qTg01Cej2pTg03Omj2oTg02ICR4j21Tg00laj3c!u2$kk10ETg03Q6k10CTg03:aj4STg03F7j4bTg034mR5j2!sC$5^j6B!t]$fk10?Tg01MJk10>Tg01FHk10=!s0$fk10<Tg01Jkk209Tg00B4j2_Tg01KMk208Tg01L9k307!s0$Xk406Tg03R;j6?Tg03E4j2hTg01_SR6j1ZTg019Dj2VTg02W6k405Tg01a3k104Tg03SDk202!vp$^k201Tg01EFk300!s0$jj2|Tg02EKj4fTg01H4j2gTg01GQj2{!sr$Xj6yTg03T5j4xTg01:>j1^Tg03A3j2RTg01<Hj2`!v%$Gk20;Tg026<l<l!uc$@j4YTg01Noj7XTg01OSj7uTg027Dj4tTg000ik60@Tg02Xfl<nTg01I:j3\Tg01P7k80BTf3R7f2R8f1R9f0R:Cb#^p=7g03UJR;9c9:p=v1R89=L7:p=d%@:#Gp=P%@:#@p>0F!s/$#@!s3$D%G!sD$[%G:#Fp=Jf4R<Ac89;,R7;L:p=;!sH$#G#Gp=Q!sa+!s$'p=U%@!s`$Ng00S0R=/5:p=Kf5R>P<P7P8Cb#^g00MDR?P9g02a7R@P:CS'`p=4P7P8g03UfRAP9CS,R<=L>:p=31R78%^9/`:5L<p>0A20;9:#Z,T8,R7p=Dg00OTRB/_:p=9g010QRCPBP5P6P1g03IiP!tN&P9P:M<lp=EPCPBP4P6P2g02`U!sG4<1gB:p=8f6R2g01P[R4g01Q:R1P1g01QZR5P>P4P1P1P5PBP<g01R:RDP7CYg01RaREFXP8!sH-9g01TfRFP:CYPEFXFup=A16<!tD&Ctp==f7RGP2P>1_<71h89P:J0@p=>!tm$AP7CS,R2P?P9P!vU$,`85LGp=:1V<7/V8/V9/V:p=HPC!uV$BP3P6!uZ%3IERH!sm$!sA17PH!ul'nM<np=I!u'1PD!t~'p=~A\B<7=\B8=\B9=\B:p=M!sU2!uU+p=zP7!sA+!t1$L0Bp=k%0:#0#0#0p=Og00P2RE#GRF#@RD#]RH%GFR6#GR3#GRI#GRJ#GRK#]RL#aRM+0G%]3#aRN#mRO\M!w{,I0:P0!x4-2!z/&7@03@2P:PMf@R0%FFRF,vHS00f>CdPMfARPPH%F6RQ%@IS01#@#P#P$0FRR#@$0D#[#J,TLD;1WL0%FIRI'j=LB=%[K#Q#QRK#G#Q#P#P#[#Q#J1WLP'5fB,WL%@ES02#@S03#@S04#@S05#@#U!s$+N'5g00mDR0fDS06fCg03W6C}%FK/5:Q04#GS07#P#Q!s$$J,2:'6fGRK1TL9O1%iN5LO[^7BfFROg03X;'w%eNRN#mP0PK%GR!tg&J,TLg00T:RR#0R0#0RS#0RT#0RUCsfE,TL,rU,qN3L%KO%FJRJ,pFS08,2O'6fIRN/oOfKROPNfHPKC7P@PO%0US09#0RK#0S0:#0RN#0RV#0RW#0RX#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk#0Rl#0Rm,1:RnPCPMfORo%aHRpP9AcH=;R;PofMRqfLRrPOP9&0E=RsE4E3^0nP911RmfNRn$0CPMPnPpPRPAP;CSPnPrPOfJCbP?PRP@PsCSI0AeW0PC%0:S0;/1mPMfQR@Pp%09S0<P;P@PoPnPqQ0<P!t2$]0P:110mPMfPR?PHPUPTCDROPMP@PH%FEREP:D;X6MPMPOP?PnPqPrC7S0=PU!s5'PU1CTURr%0mRq#0RO#0RA,1URtQ02#FRu/5QRv%@3S0>#NRw,2QRx'6S0?PrPtPvPxPTPu%9uRxPUPQ%9QRvEEPUPQPvPAPw%9wRvE<EBg01T:Rt$0?Rr%etRt&0>BRy&0=BRz&0<BR{P{%8uR|%8QRQP{PQ%8wRQFA209{5R}P:P8g00X4S0@g0156R~'_Q0@208:8;L~dB07B=9H06R~b3b4b5Q0?P:b2D=E?G>PMP?PpP0P;Q0=P0PsG:!w6$Q0;#0!w8+SR0PpQ0<#0S0=P;P0P@P?PoQ0=!w:/SmPPPMfRRPQ00PPP?PoPnC7Rn/hRCdePMPPPpPSP;PnPS!t81RS!t7%URnPpQ0=!tJ$!sO$0PPP@Q0;!t7/TmPMfTRRPHPK!xK$o!y_$HPu!xH,oPRPPP@P?C7S00PK!s5'PK1CTKS0?11KAS0@Q02#GR?#FR@,5uS0212@wRo'6S0AQ0?Q!sH$PoPTPuPxPKP@%9@RoEEPK!z8$APwP!x7$!xf$yPzP{P{P|%8@RoP{PoPQFAP}P!wA+A!wA0RPpPTP;Q00PT!v/+%0SS00!v-%WRSPp!wR&AP;PSPnPRP0Q0A!v-/UmQ06PMfVRoPpPUP;!ut$0PPPU!sM%!w/&0#0RU!t#%YRPPpQ0A#0S00P;PPPSPoPnQ00!t#,Q09!sS%XR0PHPNPTCDS06!x6$H%FD!w3+Q06P0!}=$RC7S06PN!s5'PN1CTNS0211NAS0@%F3R3,5uRR123wRn!|A$Q02Q0@PRPn!w+&NP3%93RnEEPNP3Pn!w+=3RnP{Pn!w+3!{G1!zz$9P;Q06Q09!w--U!v+'[!z5%0#0S09!z5$PP0PS!sT$!w,,KmPMfZ!z5$V!v&,nPHP@!v%0RP0PSPo!v%%V!s5'PV1CTV!z7$V!v%$@6Ro#FRS!z5'SwR@'6S0B!z5,@!v/&VPS%9SR@EEPVPSP@!v/=SR@P{P@!v/3B!z54K!v-$PK!v,7]RK!vQ$#0S06P;PK!x9$PQ06!y3/:!sS%\R@PHPW!v/%BPMPKPHQ03#F!v2-BP@!}6$0C7S0BPW!s5'PW1CTW!y5$W!v2$GDS0?#FR0!v3$C120wRP'6S0D!y;%Q0CPP!v3&WP0%90RPEEPW!{S$!v3<0RPP{PP!v33D!v30@PpQ0:P;Q0BQ0:!v5/S!ua'_RUPpQ06#0S0BP;PU!~c$nQ0B!y=/NmPMf^RPPHPX!v4%DPMPUPHP3!v1-DPPP@!|@'DPX!s5'PX1CTXS0C11X!y=%DRD#FRR,5uRn12RwR3'6S02Q0CQ0@PnP3!v-&XPR%9RR3EEPXPRP3!v-=RR3P{P3!v-32!v-0PPpPNP;Q0DPN!#7S,:#0RN!v,%aR3PpQ0B#0S0:P;P3PUPPPK!v\$!v,,VmPMf`RnPHPY!v,,3PHPS!v,0nPPPKP@!v,%Y!s5'PY1CTY!y8$Y!y8%?R@#FRK!y7'KwRS'6S0E!y7,S!v/&YPK%9KRSEEPYPKPS!v/=KRSP{PS!v/3E!v/0nPpPV!v/%V!y5-N!v,'cRV!yY$#0S0DP;PVP3PnPUQ0D!v,/WmPMfbRSPHPZ!v,%EPMPVPHP0!v,-EPSPnPUPPC7S0EPZ!s5'PZ1CTZ!y4$Z!y4%?R?#FRP,5uRU12PwR0!y4/UP0!v'&ZPP%9PR0EEPZ!}1$!v'<PR0P{P0!y4ASPpPWP;Q0EPW!v'7eRWPpQ0D#0R0P;PWPVPSP3P0!v%/XmPMfdRUPHP[!v%,WPHPR!v%0U!sa$n!v%%[!s5'P[1CT[!y0$[!#=_$3#GRn#FR3!y2$3123wRR'6S0C!y2'3PR!v,&[!#9Y$REEP[P3PR!#9Y>RP{PR!v,3C!v,0UPpPX!v,%X!v,/S0E!v-%gRNPp%00RXP;PNPWPUPVPX!v+/YmPMffRRPHP\!v+%CPMPNPHPK!v+-CPR!sa$SC7S0CP\!s5'P\1CT\S0311\!v+%4!#9R%RV12SwRK'6S04Q03Q0@PVPK!u~&\!#9P$KEEP\PSPK!#9P>KP{PK!u~34!#9P3YP;Q0CPY!#3;,E#0!v$+iRYPp%0XRKP;PYPNPRPWPK!v$/ZmPMfhRVPHP]!v$,YPHPP!v$0V!sa$U!v$%]!s5'P]1CT]S0411]ARU15uIRW12I!#9?%@Q04PUPW!#9=']PI%9IRPEEP]PI!#9=>I!#9=8@!ux0VPpPZ!ux%Z!ux1RZ!uw%kRPPp%0KRWP;PPPYPV!y#$!uw-[mPMfj!|#$^!|#,P!#981E!xh$N!#98$EP^!s5'P^1CT^S0C11^!xy%>!#96&N!#96+4!#3$%N!#96'^!#96+^!#96W4!{y4[!{y%[!{y-Z!u}'mR[Pp%0WR3P;P[PPPUPYP3!u}/\mPMflRNPHP_!u},[!#901EPN!sa$V!u}%_!s5'P_1CT_!xv$_AS0@%JoRV,5uRY12V!#9'%CQ04Q0@PY!#9&'_PV%9VRSEEP_!|f$!u{<V!#9&8!~v1NPpP\!u{%\!u{7oR\Pp%03RSP;P\P[PNPPPS!u{/]mPMfnRYPHP`!u{,\PHPI!u{0Y!sa$!{s$EP`!s5'P`1CT`!xz$`!u{$NoRo!#8z%o!{x&!xx'U!{y+`Po%9o!{y$`Po!{y?o!{y9!xx1YPpP]!u{%]!u{7qR]Pp%0SRPP;P]P\PY!x~$!u{-^mPMfp!{w$a!u{,]!#8x5YP[PN!u{%a!s5'Pa1CTa!xx$a!{w%?#JRN,5uR[12N!#8s+!xz$[!#8r'aPN%9NRREEPa!|g$!u}<N!#8rJ^!u}%^!u}7sR^Pp%0PRRP;P^P]PUP\PR!u}/_mPMfrR[PHPb!u},^PHPV!u}0[!sa$Y!u}%b!s5'Pb1CTb!xz$b!u}'NRY,5uR\12YwRV!#NL%!x|$\PV!u}&bPY%9YRVEEPb!|g$!u}<YRVP{PV!#NL@[PpP_!u}%_!u}7uR_Pp%0RRVP;P_P^P[P]PV!u}/`mPMftR\PHPc!u},_PHPo!u}0\!sa$!{y&c!s5'Pc1CTcS0?11c!~v%DRU,5uR]12U!#UP%C!#NA$P]!#UO'cPU%9URoEEPcPU!#UO>U!#UO8!xz1\PpP`!u{%`!u{7wR`Pp%0VRoP;P`P_P\P^Po!u{/amPMfvR]PHPd!u{,`PHPN!u{0]!sa$[!u{%d!s5'Pd1CTd!xz$dAR[%NDRD,5uR^12DwRN!#;o%CP[P^PN!uy&dPD%9DRNEEPdPDPN!uy=DRNP{PN!#;o@]PpPa!uy%a!uy7yRaPp%0oRNP;PaP`P]P_PN!uy/bmPMfxR^PHPePTCDR[PMPaPHPY!ux+!u7$]P_P\!uw%e!s5'Pe1CTeS0@11eAR\%J@R_!~o&_wRY!xs&@!yK$Y!uw&eP_%9_RYEEPeP_PY!uw=_RYP{PY!xrA^PpPb!uw%b!uw7{RbPp%0NRYP;PbPaP^P`PY!uw/cmPMfz!~n$f!uw$\PMPbPHPU!uw,\!uy$`P]!uw%f!s5'Pf1CTfR]11fAR`%N@R@!~h&@wRU!uv$P]P`P\PU!uu&f!#^:$UEEPfP@PU!#^:>UP{PU!uuA[PpPc!uu%c!uu7}RcPp%0YRUP;PcPbP[Pa!#]f&!uu%dmPMf|!~f$g!uu$`PMPcPHP!#]0+!u7$[PaP^!uu%g!s5'Pg1CTgR^11gARa%J?R`,5uRD12`wR]!uu%^PaPDP]!uu&gP`%9`R]EEPg!v_$!uu<`R]P{P]!~`Ed!uu%d!uu6p+01@RdPp%0UR]P;PdPcP\PbP]!ux/emPMf~RDPHPh!ux$aPMPdPHP_!ux,aPD!s_$!~a&h!s5'Ph1CThR[11hARb%N?R?,5uRa12?wR_'6R^P[!z5$_!uw&hP?%9?R_EEPhP?P_!uw=?R_P{P_!uw1P^!uv0DPpPe!uv%e!uv:BRePp%0]R^P;PePdPDPcP^!uv/f!sP&AR_PHPi!uy+e!#_z/!u:$DPc!~c'i!s5'Pi1CTiR\11iARc%JnRa,5uR@12awRb'6R[P\PcP@Pb!uy&iPa%9aRbEEPiPaPb!uy=aRbP{Pb!uy2[!uy0_PpPf!uy%f!uy:DRfPp%0^R[P;PfPeP_PdP[!uy/g!sP&CRbPHPj!uy$@PMPfPHP`!uy,@Pb!sb$DC7R@Pj!s4'Pj1CTjRD11jARd%NnRn,5uR`12nwRc'6R\PDPdP`Pc!ux&jPn%9nRcEEPjPnPc!ux=nRcP{Pc!ux2\!ux0bPpPgP;P@Pg!uw:FRgPp%0[R@P;PgPfPbPeP@!uw/h!sP&E!~g$k!uw$cPMPgPHP?!uw,!|L%eP_C7RcPk!s4'Pk1CTkR_11kAReQ07#F!{n%`!{n$d'6RDP_PeP`Pd!uy&k!{n%dEEPkP?Pd!{n?dP{Pd!uy2D!~f4hP;PcPh!uy:HRhPp%0@RcP;PhPgP\PfPc!uy/i!sP&G!~h$l!uy$dPMPhPHPa!uy,d!~Y$fPbC7RdPl!s4'Pl1CTlRb11lARfQ05#F!{n%`!{n$e'6R_PbPfP`Pe!uy&l!{n%eEEPlPaPe!{n?eP{Pe!uy2_!~i4iP;PdPi!uy:JRiPp%0cRdP;PiPhPDPgPd!uy/j!sP&I!~h$m!uy$ePMPiPHPn!uy,e!~Y$gP\C7RePm!s4'Pm1CTmR\11mARg15uJRn12JwR`'6RfP\PgPnP`!us&mPJ%9JR`EEPmPJP`!us=J!#n\6Pf!~c4jP;PePj!us:LRjPp%0dReP;PjPiP_PhPe!us/k!sP&KRfPHPq!us$gPMPj!{i1gPf!sb$DC7S05Pq!s5'Pq1CTqRD11qARhQ01#FRg,5uR?12gwR\'6RbPDPhP?P\!uz&qPg%9gR\EEPq!v_$!uz<gRgP{Pg!uz2b!uz0fPpPkP;Q05Pk!u{:NRkPp%0eRbP;PkPjPfPiPb!u{/l!sP&MRjPHPO!u{+k!{k1g!sb&_C7RgPO!s4'PO1CTOR_11OARiQ0>#JRf!#;V%fwRH'6RkP_PiPaPH!uz&OPf%9fRxEEPOPfPx!uz=fRfP{Pf!uz2k!uz0jPpPlP;PgPl!uy&%0Z/1m%0b!u}$%Z9RlPE!s$%DH!s0i/2JS0>PZ1V:EXQBRZP!s$alO1S05O1S01O1S07O1S0EO1S0CO1S0@O1S0?O1S04O1S03O1RgO1RjO1RkO1RQO1RfO1R|O1RvO1RwO1RAO1RxO1ROO1RuO1RTO1RHO1RaO1RiO1R_O1R\O1RqO1R?O1RhO1RDO1PZPbPDPZPePhPZPdP?PZPcPqPZP@P\PZP[P_PZP^PiPZP]PaPZPUPHPZPYPTPZPNPuPZPoPOPZPVPxPZPRPAPZPPPwPZPSPvPZP3P|PZPWPfPZPKPQPZPXPkPZP0PjPZQ0DPgPZQ0:Q03PZQ0BQ04PZQ06Q0?PZQ09Q0@PZQ00Q0CPZQ0AQ0EPZQ0;Q07PZQ0=Q01PZQ0<Q05PZP9Pl%9lFI!s$A!#4=$E<P:H05Q0>&048%Z8#Kp+01O,WLR`002I%K`%KIp+01QR`,WL/jI#K[[201FJ12=F%KJQ08,2=[[%KFRIg01S^RLB00FJ9UW8Q08#K\L^8Ip-0RI!{S$BPB1|B9P9PyCf!s+&zP{1gB=1{B6R65~{%i1R=P{P6%8ER6P!s$$DMP!s0h=z{nP=P{!$:@'7EyCkCk!|},X:BW9%K:P9!|SvP7[[^:B^9IP:!#44$URIPp%OG#O!s$/RpP;P!wA$Sp+01RP`Pp!#4r$%ZGP<P>O4b2bHbIbJbLb?W0X7CP:O1n0110001020111100X1!s>w0!s>~!s>~!s>~!s>~!s>~!s>~!s>+0!sV~!sV,P:O1!{l$CxW=WFWEW>W@WDWBWCWAW<W;f:f9f8PGP2!$Ij-O;n5!sn$!st%01;110110210610810710910510410:10;103WGXKBXPBXOMWMWNo"). Qed.

  Lemma h_know_ok : ltac2:(zQ "b0!jj8!jlb!h9!io8!mof!ns1!ou8!pj3!pk7!oma!ki4>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>2sp@1$1@1$0#k0>3tid$2>3can$2>0@5$8^5^4^3^2^1@4$5$a@1$6@4$7^6^4^3^2^5$9").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["Plain"] "##\_p'0h07__arithh14__ffh28__varmaph35__with44__x1h51mh61dh72Hah86__sat0h9!s/%1h:7!s/$34h;!s0&5h<!s0&6h=!s0&7h>!s0&8h?1zh@1xhA4__x2hB1bhC4cstrhD2E0hE2E1hF2E2hG2H3hH2H5hI5Hcan0hJ7Hcells0hK2HdhL5Himg0hM2HmhN3HsphO5Hsp17hP6HspHi0hQ6HspLo0hR5Hstk0hS5Htid0hT6Htid33hU2PHhV2Z0hW3canhX1ihY3memhZ1nh[4regsh\2sph]3tidh^1yi002H2i012H4i024Hcani036!tl%i044Himgi05!t\$6i065!t]$i075!t]$i084Hstki094Htidi0:!t]%2p%0p&0p;1p;2p;5p;4p;3p;6p;7p;9p;8p;<p;@p;Bg003hj12Tg001Gj14Tg00hej1VTg00iCj1eTg01UMk20[Tg003Fj1qTg03K7R0k50FTg03F7j4GTg01:>j1ETg01Wgj4aTg004Mj16Tg00laj3oTg03A3j2p!t>$lj3;Tg00k;j2:Tg017aj27Tg03L<j2OTg018KR1j20!s:$\k40;Tg01DBj2<Tg00AYj29Tg00jYj1bTg03M]k203Tg002Fj1tTg008^j1=!t5$aj4hTg03Nej2kTg00@7j2lTg01Cej2vTg03Omj2wTg03YEk10ZTg00B4j2ITg03E4j2UTg0062j1]Tg009=k20WTg00:Fk30V!u$$gk10RTg00=aj2QTg00;Oj2sTg00<Xk20P!v5$kk10OTg00L;j3n!u#$fj1mTg03ZKk10MTg01^Ck30Lk40ATg01MJk10KTg01FHk10I!s0$fk10!w8$H4j2iTg01Jkk20DTg01KMk20CTg01L9k30B!s0$Xk40@Tg000ij6WTg01<Hj2[Tg03[Sk70?Tg03SDj2f!w1$^j2dTg01EFj3^!s/$jj2_Tg01GQj2cTg03\Zk70=Tg03]am90<Tg01I]k30:Tg03^ik809Tg019DR2j23Tg01_SR3j1KTg03_nj4STg01a3k106Tg02EKk405Tg03`nk507!wL$Nk404Tg03bBk208Tg01;Ak102Tg01=Ok101Tg01BZk30>Tg03cFk20!yP$4mR4j2gTg027Dj4YTg025^j1~!s8$oj4}Tg026<l<jTg03dSm@0HTg03eYj6{Tg01j3k20JTg03fdj3zTg03h3j6yTg00K[k30N!w@$@j4uTg01Noj7rTg01OSj7xTg01P7k80!u]$I:k30TTg02Xfm<0UTg02YKmB0YTg03i>k60XTf0R5#4#4p=P%45#2p=\%4!s8$#4p>0Q%2!s;$Mg00OTR6g00S0R77;5p=T!sB$!s$/p=H!s:+p=D%25#4p=>!sw+!s$'p=J1075p=1g00NKR8f1R9<0N5p=@1i65p=8P6P9g01TfP5Cup=X!s4$P[R:g01Q:R;P;g01QZR<P5g01RaR=Frp=Zg00X4R>g0156R?!tu$Nf2R@1095'9p=?P@P:P;P;P<!t0&R:P5CuP!se$5!sD-9P5Fxp=Ff3R=!s;+@P9P5L0Sp=LB0T695p=AP6P7P=!sA%EWp=R1I65p=Cg010QR:P6P4P3P1g03Iif5R4f4RA!sV'M<jp=`P:P6!s$$3P3P4P!sD+N<0Up>0G!sD&!s$%2P5P9P@P2P=PAP4f6S00f7R2f8R3f9RBNB0Yp=|P8!sn,J0Xp=Bg00P2RC#2RD#4#VRE%2DRF#2RG#2RH#2RI#2RJ#VRK#eRL+0[%VG#eRM#qRN\L!st,I0FP0!tu,g00mDR0Q00!s8%CG#EP4g02b;S01CaP5f@RO%6DRPg03UJRQ5oE'pf>5;LfARR%6FRS=oEQ'p%PH#\#\#PRQ$0Q#\#M#6,:K5;L17KO%6HRH'O#T%MJRO#HRE#D#>#>#H#6RT17KR'0fBRU,7K%4CRV#PRW#PRX#4#J!s$+6RY'0P0fDfCg03W6RZH0;%6ERE/05%>W#M#D!sw$W,<5'9fGR[1:K9O1%bM5;N[^X6fFRNg03X;R\+03%tMRM#qS02P0P[%>Q#>#D#6RQ,:Kg00T:R[#=R]#=R^#=#=R_ChfE,:K,k_,lM3;%1N%6IRI,vPR`,<N'9fIRa/wN&0Za17KaRN#1%6JRJ,vPRb!sH%JRN,ILfLRcPNPafHCG#E/U[=;LN1:KNRd,ILRefMRffKRgPNPa!sH%]=;LdPefNRePcPgPN!s=%^=;Ld1I671:K7Rd,7KRN#TfPRgPePfPcCG#ERafORh%][Ri00WHRjB0ViTYRk&0RZ,Qi/sZS0320PEWS04&0O7Rl%MX!vl&X'QRm%>V!v;$H#6RV'sRn1QlQ%]]S057n_S06g03i_,Ql%=_#=!vL$o%]^3nS07%m8S08'@S09'@S0:'@S0;'@S0<'@Rp'@Rq'@&0M\B0L0ahR\PjPqP0PaPhPiPHg01T:Rq#mRj%tqRq&0K6Rr&0I6Rs&0E6Rt1i67Ru%8H'X'Z20Dt<R<P5P@1I>?20C5@#NdB0B679H0@R?b1b2b31<7HP5b0PLPe17K5R>/OH#TXBLf=1Ua[S0=P=EW1[ai,7KR[!sD$eK0?P\PkPp!tn+TPY!si$0T>??>YXBL17KeR>/fHS0>%1>%1HRp17Kg/OH#1[[S0?1dPIRk1<7PRv%1I1<7`[[Rw%1PRxg01S^RyA^PI9UW7RI%1`\y^7xR`1dPJRz%1J1<7bR{[\vRvA^PJ9VyX7xRJ%1b!sP%xPjPq1_69RyPsPt1c6CR|%8Y55tR}%b;R;Pt%8T=5t|R~P;AFt~}CLCLP<P!v<&X46105Y10T910T@??@Y[[^46P5fTR},7KS0@PRPUO3b0b:b;b<b=b>Q!vR&0T[??[YeK0=P\Q03Q0<!vN+ePZP=f:RiQ0>Q0?PkPwPIP`PzPvPJP!u0$P!u+$P~P;%6ORO#8R~95tuA5t~|5Ft!tv4T5%1O??O9!tp%Q0@PUO2!tg/107Z??Z>eN90<P\Q04Q0;!ta&EPW!tC$rPs%8E95tu!t,,%1E!y:$!tk/!sN$W%8P>0:6KRP55t!sW,10WbP5b0b8b9PBL09P\PnQ0:135XRW#11<Wb%1VRE13WV;?b'9'9%19RW%K9,3@/0VR>P0P}13AX/3=,:KP@CS#N[[^5:^66'9X?6137XRZ#11<Zb13ZV=?E!so$RUP0fSRO13Z=RT!sb+\>\W!sd%!u>5XR~,AuR[95tu1X[P,Zt%8VRY!s6$A[Y=5tP5Ft!s%%!u],PU!u[+OPTP@&06@S0:%K@#1RT17KORU/fHRR%1UfU,7K!{b$\p[Rp!x_=A5tu|P;1A[|!t_$~!xW2%1513Z9RZ,0X!xX%PiP3!xW1bCQ0:PTPRP!t7961_6@P9PrH05!|%&DRD,A|=5tY!tJ$D%PF#M!#5B'F#855!z13XA61359/0V13Z@/0F[^46^A6P5%KBPiP2!{}1bCI07XM>XKWX5:X66H04PN!wS3A5tuu1XuP,Z!w311077/9{!w8'-087CR&02mR{,[a,7K&01mRF'3!y&7P0POP}fRfQPgCG#ER}/[{,7K/3F!yv/!y:,'9eB0>amVP0PO200}m!sN<!|O&nH0AeP\Q06Q09!s:&lPdPQP_Q051:Kf1ILdP@1g]_%6CRC/0SRdP]PC%CCP_PS%CSR]E`!zT,C%8SRC!|g0PdP5b0CY1g_o%6GRG,!sk$_PSP]PoPG%CG!sh/G95tC!sd635QRd#1X?6!sR,Q,AuRG!~W1137QRQ#1!~\$NP5CR%K_R7,3d/0b!}9$Q7Ru/0bRo13QSRf/0bRlP6P6P1P5X@6RnP11095#~X^6X@6PuPfPn!s$$6P6g02j?1395C}#CX56XZ6PQPQ%CQP7PSPnPn%K5#CX@:!uX%J0GM:|PbPb%CbM<j!yR31AGC=5tP!uh-l!yF'CYPoe!u:%Q02P0Pg1:KdP_Ch1:Ke!#@Y&X?6P2!sL%N@0HP\Q07Q08!x;$^PcP9P4E{20J8\DB!s$/Azah3Ey!xe%Q01CaebVbFbEbDbNWIWTWSWJWLWRWPWQWOWHWGPiPBP3P2Q0!#E`,P5O;n5000001!s+$01;110010110510710610810410310910:102WUXW6X]6X\LWYW[o"). Qed.

  Ltac hf_plain SOUND :=
    intros regs mem sp tid can K PH HKnil HCONT;
    pose proof (h_regs_ok regs mem sp tid can PH) as HR; pose proof (h_know_ok regs mem sp tid can PH) as HK;
    destruct PH; pose proof (u64_range sp) as Hsp;
    apply (SOUND sp model Hh Hlazy Hfd2 Hrdr (h_vals regs sp tid can) regs mem K);
      [ unfold h_vals; rewrite length_app, junk_vals_length; reflexivity | reflexivity | exact HR | exact HK | exact HKnil |];
    clear HR HK; intros Rj R' M' HR HK FM;
    try rewrite hso_srF in HR;
    set (vals' := h_vals regs sp tid can ++ junk_vals Rj) in *;
    assert (P0 : vals_ev vals' 0 = sp) by reflexivity;
    assert (PJ : forall i, (3 <= i < 35)%nat -> vals_ev vals' i = getr regs (Z_to_bv 5 (Z.of_nat (i - 3))));
    [ intros i Hi; subst vals'; rewrite vals_ev_app_l by (unfold h_vals; rewrite length_app, junk_vals_length; cbn; lia);
      apply (h_ev_junk regs sp tid can i Hi) |];
    apply HCONT; split;
    [ regv HR (2 : reg); exact P0
    | regv HR (4 : reg); reflexivity
    | regv HR (10 : reg); reflexivity
    | intros r Hr; cbn [In] in Hr;
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]];
        lazymatch goal with |- getr R' ?rr = _ => regv HR rr end; cbn [edenot ev ENV]; rewrite PJ by lia; f_equal; apply bv_eq; reflexivity
    | exact FM
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | intros a n Ha Hn; eapply frame_mod_store_ok; [exact FM|];
      match goal with Hs : stk_ok _ mem sp _ |- _ => apply Hs; assumption end ].

  Theorem hdr_short_fwrite : ltac2:(zQ "h41!jj8!jlb!ki4!io8!h9!ms4!mof!msd!mt5!nh7!nm3!kj7!k2!og5!ol3!olb!om5!ju1!pk7!pke&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4regs@2$6@1$0#5@1$1@1$0#k0>3mem~0>2sp@1$1@1$0#k0>3tid$4>3can$4>1K$e>0@5$h2^6^5^4^3^2>0@1^2@1$c$d>0>5regs'@2$6@1$0#5@1$1@1$0#k0>4mem'~0>0@5$h3^a^9^8^2^1@4$a$2$9@2$5@5$7?2fx^3@2$b@1$0#k0+knht8^2@1$8$2?5model^6@4$a$2$9@2$5@5$7?2fx^9@2$b@1$0#k0+knhpc^8@1$8$2?5model@2$f@2$h0+2$h1^4").
Proof.
  hf_plain hs_sound.
Qed.

  Theorem hdr_overrun_fwrite : ltac2:(zQ "h41!jj8!jlb!ki4!io8!h9!ms4!mof!msd!mt5!nh7!nm3!kj7!k2!og5!ol3!olb!om5!kk2!pk7!pke&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4regs@2$6@1$0#5@1$1@1$0#k0>3mem~0>2sp@1$1@1$0#k0>3tid$4>3can$4>1K$e>0@5$h2^6^5^4^3^2>0@1^2@1$c$d>0>5regs'@2$6@1$0#5@1$1@1$0#k0>4mem'~0>0@5$h3^a^9^8^2^1@4$a$2$9@2$5@5$7?2fx^3@2$b@1$0#k0+knht8^2@1$8$2?5model^6@4$a$2$9@2$5@5$7?2fx^9@2$b@1$0#k0+knhr8^8@1$8$2?5model@2$f@2$h0+2$h1^4").
Proof.
  hf_plain ho_sound.
Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
