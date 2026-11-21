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
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail
  LazyRestrict LazySR LazyFdNodes LazySym Spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib AsPrintfFirst.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsHdrErr () := KReplay.lz_vm "#%A/C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics?!s<22Fs4path!st,4Init5Logic8eq_ind_rC46Stdlib5Lists4!s+#6nth_okK!tU,Numbers7BinNums8positive01!sKG2I!tQ72eq00!s@29Datatypes4list00K!sFA1!sf<6option!sh/!to31Z02K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr01C13~~~!smc2!smi3!sm&!v3;3nat!uj_6kentry05!t}c!so'6!sok7!sok4!soc5sadd!y/Y2Bs;AsStdioCall9s!s0#_res!st+!{TC!{v=4prod!|^?!sF$1!}`83an!sa5!}{,1K!s[<1C!zI<fstC!{U]s_pc!v2%!t0=sndC!wE^:!wE%call!t8&!ss^6sc_ret!soe4sc_f!sme5!sm#d!t]is!smil!{J3!#7V53!#8^A!#52e!|y&I!#71a0!smc!t^'!so'!v5?0!#<tF3!tZ]8sideco!~d#!uMV!#5,<0!xaF1K!#@~95Riscv5Instr5aluop!#483!#;@11!ux]9sym_state!xHe7script!uu+c!vkR8AsHdrErr5hs_rA!y63!|#3bool00!t3`cA!txb6hs_sr!slgknA!vTfsc!wAgC!skfc!skeo_rA!skf!xSfo!xSho!xSho!xSgo!xSgo!xS+!#5?=N02I45stdpp9bitvector;definitions2bv00C!sI@DZ_to_bv_obliga!s:#_1!#DbC2!s{A7!s{&C7!#5FNPropExec3rdn!ur'!uTC1!t1/!t&96images9AsanUbsan1M?loaded_segment!#?s&!t|O4Spec9msg_short!sh[;!sh#overru!uj&I!#:,?0!t1P6SymAux7sregio!t/&!#F{+!#Tm$7!s+#Def3map!#UN76!#UN$!#HH\5s_log!vAV!u6&;log_c!vD#ed!{{3!#:X71!}0\9h_!vJ%s!t}ZRun7vals_ev!w5'!{&?;bv_unsignedC5!#YM%6ZArith6BinInt1Z2le!sB<3opp!sC=ad!s|=3sub!#HNR=AsPrintfFirst3ENV!u[&!y2\6a_base!smdedenot!smc5a_off!zh]6r!tU[!v{46ASP_LO!~s&!}2^!#VY#!#Deb;!{~+_w!{>'!#a;42In!#`E8o!tP#!tJO=!u:'Sound4SX2S4fla!vx'!{:<pow!|U>t!sB<>pow_pos_nonneg!sN<:!sN#!sJ%K!uw'9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PE!#a?#!sIE1!sIE6!sIE3!sIE7K!uPL1C!sQ55Tauto8B!sJ&!sH6:Z!sp+=Z!sT$CheckerC!w7<4find!sqAC!sq0_s!z3#!xN@1!~|W<!|Q'!{0,K!uz<G!vF'4!sJF5!sJF8!w6<5eKind!#Ot<unit!zG8!se%4kind!yy8!xh13Op2!#Z+>!t5$1!#64eHI!#B%7!#4:$5False!#m\3!sC%4True!}U8!yC-;!~r%!tj$!v58!um65C!#W8?7Prelude5bv!#Bd4!#HM,length!#6Hb7regs_ok!#:EU!st7know!st,!#spI5State5m_fds!sZQ9fd_lookupK!s^P7FdE!#`<$!s^K3Run6config01I!~OPLazySR4lzok!#<j&!#38O<!sg#Restrict8r!s/&!soV!#Ml'7seg_rom!sjWSymDrive9junk_val!#GD&!#Kr;app!t1P5Frame9f!s+#_mod!vQcEs!so#but_materialize!s|W!x8&8hid_!sz#!#A3<9nth_error!t/P9!v{'X8!|W$nth!}Ni9!#g3$!}P,!#@b:6of_na!#AR34Znat5Nat2Z7inj_iff!#P,77iff_sym!sf>9is!#Ak<!#:F23!#E{[>!#E{+!#<P+!st\?!st,!#IK,!#3zP5event02!|}RhapeAlg6t_emi!tG'!#Iy[!#hV,1!yqV!#Jm0carry!z_jsc!vy0!svc8sc!wp1!#X686Forall!#?PQ!#P|0s!y1#s!u}jmem!u}plog!{f-!#F#VA!#Yg,_!#7:#!srV!#9+'8blob!#X_-!#3K6f_equal!$3?;trans!tNP7StepTac6u_Z2bv!|Tc3env!|NX!#|45wb!snjp!vq>8iff_refl!#In5;ZifyClasses5mkrel!#OAD4!snB;rew_!tB%v!sQB3inj!#G7@3Sem5alu64!#@|X5v_ad!#>-V7LibTail7vadd_wZ!{_W!#BQ'alu!tU,K!#Xh:1!xucsp!ttV!#?^-img_!#k;'!#BS\I!#BS7!#IX#!t$$!#~@R<Ref!u_$Defs7s!#Z?#t!#GuW!#E5$7outside!wV'!zb4!#U6+3!#Q=`A!t{&_!#FO2!xr13Nat!#ez#!x#Y@!#H]'_!#P#%!t3&!#Es4:!sG%_ap!#lR3Peano2lt!tSZ=!#id%!t%#_l!#5-hsr!snikn!yB\D!x$+!#9q$!#Is-!|/\K!|/9!#:z$!t&U!#Kb%>!#Kb&!so0!z~`>rz_run_lf_lazy!wTe7sc_bufp!spe8!sp%sz!sqeE!$<\+!#a%$!}j$!wOV!#wq#1W!s`V!#8z'4mk!tI'I!#BDP!#JK%8re!ye$!$2A'!#<rA7!#=E%!#G+\8sym_exec!t>H5mk!#4'#!sK@6!sK$2!#@^73not!#PME7I!#N`I>!#?O#!sE+=machine!$6p'!xoQcfg=hunspe!yc#cf!#{5%!$+1\FUELH!skb6STOPSH!~pg4scr!#sKb=!$%e'_le!#7A&!#V4<6inj_lt!t=\4h!#9?'!sj_k!$&w'!#UPOModel!y]R!~'+4TS!$I/&I!#ckX0I!#WOV0!$6A]s_srF!zoc!$<\#!slc<hs_itinera!#WR&!$G:]s!$G:/!tc\7hs_cov!$9[%!#mLH!#uy68ZifyInst7Inj_Z_Z!}Egimg!uUi!$:Xb?!$4~,!#3'+!yf^o!zTho!zTho!zT3!w4^o!yc-!w4i!xrgo!xr-I!#K-8e00!#Lt6sub!#>ZA9and_morph!#i@;8max_spec!|mD5Psatz!$%q7!sO8!$%T6!#xa:!$&n>3Pol!#{qE!tD&4!$k\,!u|&?Rel!$BD#!s6&=eq_Tran!$Sw$!$=2;n!$kZ-!sr'9M!vl#isms:re!vU#tful!tAE<eq_Reflex!t@0!s|5Jr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^??eq!tM#per!tT;!sR,@!u$0per!#J+Yget!#Rb&!t<>M!#QQ$co_!$BA#v_impl!|2%ism!x{<seq!#?}Q!#UC%;nth_map_!sh#!tl&!#Vj4=app_nth2_plus!#J~\2!#gX&!#7_]!#zK-!$8C;max!#JwE6!sg+5!sf$8!#5##Na!#4n+!#FI<;inj_sub_max!sM>8!sM%cc!#G<Ce!#4>M1i!v^[3hfH!#P]'!#y5;modulo!#W`P!$Fh$6stk!$,^X!#Kf38cells!$,]S!#Ok1@word_to_le_byte!#n0Req!z|#9!}t#_zero!|32!wr,9SatDivModCZ!#\S#!#{e$!$>}&!v%`>!$1U%_by_idx!|Rb9h_ev_jun!vx&!#i=7!$5N$!$6za9all!u1#32!u%b5HF_FR!skb8hf_!yj$!x2&!#7nW9u64_range!{Jhkn!ta\!#f/+;!$6n%!#g2#!soU!}q&<kalign_int!{M+!smX!v<$!smc=kwr_of_!#3V/!snV:!#oq#!t[b;k!#3L#!sl/!#4<X8store!uG#!z;PAgentLib7!z;#li!$P\Y;RefExitBase=!tW'_data!svV!$$556esta!$^7'!#?,57f!$'-#!$Vba:!#8f$!{Z#!t9'!#4n55proj2!$+`B2!#56a!tY#_wf_!#~<%i!#@e\fP!#u`,!#8%^!$CP/!so_!$CK0!znO!#p~$B!#p~+!{\+!sr$k!vDc1!uSb8hs!#m4$!~p]7reg_va!#utV!#\z1r_ge!$CMW!#8M&5kread!}+2!#kS9eq!#m7#!t6X9!t6$!$#<,!uk]a!$53-!#;:Y!sj%_lit0!x}do!x}/".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nilhc3nat37Corelib4Init7Decimalke2D0ke2D8ke3Nil37Corelib4Init3Natn4bof_num_uint37Corelib4Init6Numberp4bUIntDecimalhc4prodhc4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~s56kentrys54EVars52SA89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsHdrErr4FPX1~~~~~~hh95HF_FRs54ELits54KImgs53KWrhc3apphh98hf_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~hob6ASP_HIhob6ASP_LOhob8kn_cellss56KAligns56KRanges55KWord46Stdlib6ZArith6BinInt1Zih63opp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsStdioCall~~~~~~ij59stdio_resij54SCR_s54exprs58sidecondhc3fst37Corelib4Init5Logiciq32eqs59sym_stateiq33andhh95hs_schc3snds57scriptshc4boolhh95hs_rAhh95hs_rCs54s_pchc4Somehc6optionhh95hs_cAhh95hs_cChh96hs_knAhh96hs_srAij54sc_fij55sc_fdij54sc_lij56sc_retij54sc_sij5astdio_callhh95ho_schh95ho_rAhh95ho_rChh95ho_cAhh95ho_cChh96ho_knAhh96ho_srA04Npos35stdpp9bitvectorbdefinitionsjrf2bvhc4None69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ju93rdn69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~kib9msg_short69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~kmffloaded_segmentsjrf7Z_to_bvkibbmsg_overrunhc6length69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~ktf7sregions55saddrhc4truehh99h_regionsktfblog_covereds55s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsHdrErr~~~~~~ll65HF_FRih63subjrfbbv_unsigned37Corelib5Lists7ListDeflr33map89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsHdrErr5Sound~~~~~~lt1bh_regions_wll69h_regionshob3ENVktf6rdenot69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~mk27vals_evih62lektfcregions_flat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsmpcdmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runmu45mkCfg3h5LinuxProcessSemantics5Riscv7Preludenh95bvmap3h5LinuxProcessSemanticsfLinuxProcessSem5Statenk87FdEntrynk85Model69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~noa8restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~nt54lzokju94mkstju97seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~oi9dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~on18realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~or89junk_vals79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~pg07know_okpg07regs_oknk89FdChannelnk85eventnk89fd_lookupnk85m_fdsll64h_knll64h_srll66hs_knFll66hs_srF69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~pqb9frame_modnoah5same_but_materializednt58hid_sameon14TSeton16t_emitkib1Wll66ho_knFll66ho_srFn43sub37Corelib4Init5Peanoqk72leqk72lt89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsHdrErr5Plain~~~~~~qm76h_valsju94getrs52evih66of_natqm73hfHqm76hfPost" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition HF_FR : Z := 2400%Z.
Definition STOPSH : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0+hporm0@3$1$0+ruqr0@1$2$0").
Definition FUELH : nat := 8000.

(* [comment removed for export] *)
Definition h_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition hf_cells : ltac2:(zQ "40!r7!h9!j4!k8@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!r7!k8!re!jb!k2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrkht0N8+hppmq0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrthn8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrtul8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmti0N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtk0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtm8N8+hporm0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtn8N8+nhhrj0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmto0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtp8N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtq8N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrmtqcN4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvsmt8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvsmu0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvqtt8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvqtu0N8Z@1$5@2$1@2$1$0$2$0").

Definition h_kn : ltac2:(zQ "20!j4!hg4@1$0$1") := ltac2:(zQ "h20!hg4!jb!hgd!hh4!hlc!hm5!hmc!hn3!hn9!k2!hnf!htc!hu6!hv0!hvc!ig5!ige!iie@3$8$0@3$1$0@2$e@1$2N0+h0@3$1$0@3$f@1$2N0$c$b@3$1$0@2$7@2$3@1$2N0@1$h1$4$4@3$1$0@2$6+hggg0+mngg0@3$1$0@2$6+hqqgg0+hrkgg0@3$1$0@3$h0@2$3@1$5Z+nhhjl8N8@1$2N1@3$1$0@2$7@2$3@1$5Z+hrmti0+u8@1$9$0@1$d$a").

Definition sc_dummy : ltac2:(zQ "10!in6$0") := ltac2:(zQ "50!hm5!k2!io3!iob!hg4@c$2ZZZ@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$1$3@1$1$4").

(* [comment removed for export] *)
Definition hs_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x0bea74 h_sr [] h_kn 34) []).
Definition hs_cA := Eval vm_compute in (carry (s_log (fst (fst hs_rA))) h_kn []).
Definition hs_srA : list expr := Eval vm_compute in (s_regs (fst (fst hs_rA))).
Definition hs_knA : list kentry := Eval vm_compute in (fst (fst hs_cA)).
Definition hs_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 hs_srA hs_knA with Some r => r | None => sc_dummy end).
Definition hs_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x199728 (sc_sr hs_sc) [] (sc_kn hs_sc) 66) []).
Definition hs_cC := Eval vm_compute in (carry (s_log (fst (fst hs_rC))) (sc_kn hs_sc) []).
Definition hs_srF : list expr := Eval vm_compute in (s_regs (fst (fst hs_rC))).
Definition hs_knF : list kentry := Eval vm_compute in (fst (fst hs_cC)).

Lemma hs_itinerary : ltac2:(zQ "i10!h9!j4!r7!ip2!ipd!re!ir7!iob!ird!is9!it0!k2!it9!hg4!itf!iu9!iv0!iv9!in6!hm5!jg2!jg9!jh0!jh9!ji2!jib!jj5!jjf!jk7!jl0!jl8!jm2!jma@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h0+hporm0@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h0@1$b$3@2$9@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$h7@1$b$3@2$9@3$6@1$h6$h2@3$i0Ni2$ha$h9@2$h5$h2$a@2$9@3$6@2$2@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0@1$he$a@1$hb$a@1$hc$a@1$hf$a@1$hd$a@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0+hppni8+hrmti0+2@1$h3+ijmtc@1$h3+hf@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h1+ruqr0@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h1@1$b$3@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$h8@1$b$3").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "##Amp;1p;3p;2p;<p;4p-1R0p10000R1p4p710p9P0P!s2$2!s3/3110p9!sQ$Np4p7!s\$1>!sZ%R1p8!s6$\!s6%P1p8g0027j11Tg002\j10Tg003Aj38!s/$[j1XTg004;j1V!s/$[j1cTg005=j1A!s/$[j1CTg006bj1=Tg007ij3eTg0090j12!s/$Oj2dTg00:Xj3bTg00;aj2\Tg00<jj2[Tg00>3j2ETg00?;l<mTg00@Ij2_!s/$kj2MTg00AKj4D!s/$kj29Tg00BFj2Q!s/$`j4HTg00C;j3J!s/$Xj1^Tg00D]j3TTg00E:j3lTg00FGj1kTg00GPj1jTg00HWj1iTg00I_j1fTg00Jfj1hTg00Kmj1YTg00LKj3;!s/$kj3LTf0R1#1#1p=6%01#0p=3%01#1#0#1p=I%1!s0$#1p=B!sF$#0#Ap=<!sJ$p=5!sF$p=:!sB'0p=4%A1#Cp=>!sb%!s:$P%01#Yp=g%21#2p=S!s-$#2#2p=Gg00N4R0f2R2#=f1R3#==;013;p=?A;0319;02p=O%=3=;01p=]%1!u&$!s$,p=N!s:+p=R!u8%!th$W!th+!s$'p=K%Y1,E3p=af3R4/E2?L31p=Z!sQ%A!sA$`g00O;R5f4R6%A4'E?L23;;1p=F%14!sr&A,E6?L23=;51p=@f6f5;L6AL4!s9%5;5p=nA;5319;52p=U%Y4!sY07g00PDR1g00PbR3#1R2#0R6#0R4#6R7#3R8#I#B#3#<R9;89g00QGR:#XR;%V:R:;8:R<g00RRR=#cR>%16R6#1R?#5R@#B#5RA#0RB#5RC#0RD#0#<RE%03RF#ARG%B8R8#:#I#<RH%12!tK$I#3RJ#1#3#5RK!tI$6#4#>RLPLPLg00S`#CRM%0FRN#0RO#1RP#1#5#B#5#6#3#>RQ%62R2#>RRg00T>g00TjRS#=RT%3PRP#P#g#C3eRU%2SRS#2#SRV#2RW#2RX#SRY#SRZ#2R[#2#G#GR\#2R]#2R^#2R_#2R`#2Ra#2Rb#2Rc#2Rd#2Re#2#GRf%CH%2f#GRg%2g!s''>3R3%GgRg#=!s<-!s'7CERh%2g#S!tF$!sE1%V03?3?9?de9?bc9?`a9O335OR3?3?3?5OR7OR']3?9?WX7OU']PM%1BRB#0RU#0RX#4PYPLPMPX!s-%%1U!s/'C!sB$MPMPD!s-%%:ARA#1#5!wz$3PV%62#NRC#1RU#1RX#1#6#R#NRW!s0+a#1#N#N#>PT%0!w,$PYP3PT%4!s/'0ORP#1R`#1Rc#1Rb!sH$hPT%4bPYPQPT%0cRc!s<$RPT%4cPYPTPT%5`#PPY%32#I#6!y$$>PTPJPY%=_PT%04R4#0PY%=^PT%1FRF!u%$Y%=]!tY%]PY%=\PTP4PY%=[PTPPPY%=ZPTPOPY%RF#5#I#W#<RO#C%AP,dT%0C!uM$:#4#K#K#<%Aa5bT%1N#W#4RN,aT%AN'\%K]#<%:7#K#<'[%I6#3!sT$0@#4R@#3#4#<'[PM%0K#W#B#<PY%=SCZ1EMERK%1I#<'\PM%6@#:#:!sE$08!s1$4#>CZPM%6?#5R?#3#I#6PY%0URU!s}$K#>!sD%:#IPSP3PKPV%>F!x`&#:,`MPY%C9!xs$!xV&0ARA#0!xZ'%1APV%CGPM%1D!xR$>WPM%3X#5#BRX#5!xy'X!sX+BU#5#6RU!sB,U!sB%%V5DFD@!s&/FnD@D@3U!s$%D7!s$>!s\'@DFM<m,_=RM;8MRY1M11RU/M1RX/M0RW/M0RVPWP0PXP0PUP1!s$$HPECDPGCDPQCDPRCDRR;8RRQA81OORG19<<RE'9RH'9RD'9RA,9<RL'91Q19P<PL1Q;:RLP<PAPLPYPD1Q>MPQPH1QVRPGPE1Q1OP<P<PLPLCH!s$/g00UIRL1ML;R<g00VUREg00W_3JRG7J;#^=819ATL;G=8;:%X5R51M5;RGg00Xd#XR9g00YD3J7T;=8;:g00ZIg00[O5lfg00\URf,_=58>!ul3%kf%jfCD%ifCD%ffCD%hfCD=8VRg00]Z9J<ERE9JL!tS%OATL;E!t1&^_9JG99T5!tB$'9!s$/do"). Qed.

(* [comment removed for export] *)
Definition ho_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x0bea90 h_sr [] h_kn 34) []).
Definition ho_cA := Eval vm_compute in (carry (s_log (fst (fst ho_rA))) h_kn []).
Definition ho_srA : list expr := Eval vm_compute in (s_regs (fst (fst ho_rA))).
Definition ho_knA : list kentry := Eval vm_compute in (fst (fst ho_cA)).
Definition ho_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 ho_srA ho_knA with Some r => r | None => sc_dummy end).
Definition ho_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x199728 (sc_sr ho_sc) [] (sc_kn ho_sc) 66) []).
Definition ho_cC := Eval vm_compute in (carry (s_log (fst (fst ho_rC))) (sc_kn ho_sc) []).
Definition ho_srF : list expr := Eval vm_compute in (s_regs (fst (fst ho_rC))).
Definition ho_knF : list kentry := Eval vm_compute in (fst (fst ho_cC)).

Lemma ho_itinerary : ltac2:(zQ "i10!h9!j4!r7!ip2!ipd!re!ir7!iob!ird!is9!jn8!k2!it9!hg4!itf!iu9!jo1!joa!in6!hm5!jg2!jg9!jh0!jp3!jpc!jq5!jqf!jjf!jk7!jl0!jl8!jm2!jma@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h0+hporm0@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h0@1$b$3@2$9@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$h7@1$b$3@2$9@3$6@1$h6$h2@3$i0Ni2$ha$h9@2$h5$h2$a@2$9@3$6@2$2@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0@1$he$a@1$hb$a@1$hc$a@1$hf$a@1$hd$a@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0+hppni8+hrmti0+2@1$h3+hmuv9@1$h3+hf@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h1+ruqr0@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h1@1$b$3@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$h8@1$b$3").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "##@np;1p;3p;2p;<p;4g0027j11Tg002\j10Tg003Aj39!s/$[j1XTg004;j1V!s/$[j1cTg005=j1A!s/$[j1BTg006bj1<Tg007ij3eTg0090j12!s/$Oj2dTg00:Xj3bTg00;aj2\Tg00<jj2[Tg00>3j2ETg00?;l<mTg00@Ij2_!s/$kj2MTg00AKj4C!s/$kj28Tg00BFj2Q!s/$`j4HTg00C;j3J!s/$Xj1^Tg00D]j3STg00E:j3lTg00FGj1kTg00GPj1jTg00HWj1iTg00I_j1hTg00Jfj1gTg00Kmj1YTg00LKj3=!s/$kj3LTf0R0#1#1p=5%00#0p=3%00#1#0#1p=I%10#!sF&D!sF$#0#Ap=;!sJ$p=:!sF$p=6!sB'0p=4%A0#Bp=?%1!s`$#1p=T!sn%!sF$P%00#Yp=f%20#2p=R!s-$#2#2p=Gg00N4R1f2R2#<f1R3#<==103=p=>A=1309=12p=O%<3==10p=]!t4+!s$'p=N!u8%1#0p=W!th+!s$'p=K%Y0,E3p=af3R4/E2?L30p=Z!sQ%A!sA$`g00O;R5f4R6%A4'E?L23;=0p=F%14!sr&A,E6?L23==50p=@f6f5;L6AL4!s9%5=5p=nA=5309=52p=U%Y4!sY07g00PDR0g00PbR3#1R2#0R6#0R4#5R7#3R8#I#D#3#;R9;99g00QGR:#XR;%V:R:;9:R<g00RRR=#cR>%16R6#1R?#:R@#D#:RA#0RB#:RC#0RD#0#;RE%03RF#ARG%D8R8#6#I#;RH%12!tK$I#3RJ#1#3#:RK!tI$5#4#?RLPLPLg00S`#BRM%1FRN#1RO#0#5#6#T#6#:#?RP%52R2#?RQg00T>g00TjRR#<RS%0FRF#0RT#1#3RU#P#f#B3eRV%2RRR#2#RRW#2RX#2RY#RRZ#RR[#2R\#2#G#GR]#2R^#2R_#2R`#2Ra#2Rb#2Rc#2Rd#2Re#2Rf#2#GRg%BH%2g#GRh%2h!s''?3R3%GhRh#<!s<-!s'7BERi%2h#R!tF$!sE1%V13>3>9>ef9>cd9>ab9O335OQ3>3>3>5OQ7OQ']3>9>XY7OV']PM%1BRB#0RV#0RY#4PZPLPMPY!s-%%1V!s/'C!sB$MPMPD!s-%%6ARA#1#:!x$$3PW%52#NRC#1RV#1RY#1#5#T#NRX!s0+b#1#N#N#?PS%0URU#PPZP3PS%4U!s/&0TRU#1Ra#1Rd#1Rc!sH$iPS%4cPZPPPS%0dRd!s<$QPS%4dPZPSPS%:a#PPZ%32#I#5!y-$?PSPJPZ%<`PS%04R4#0PZ%<_PS%0N#3PZ%<^!tU%^PZ%<]PSP4PZ%<\PSPUPZ%<[PSPTPZ%1O#5#:#I#W#;RO#B%AU,dS%0C!uK$6#4#K#K#;%Ab5bS%1F#W#4RF,aS%AF'\%K^#;%67#K#;'[%I6#3!sT$0@#4R@#3#4#;'[PM%0K#W#D#;PZ%<RCZ1EMERK%1I#;'\PM%5@#6#6!sE$08!s1$4#?CZPM%5?#:R?#3#I#5PZ%0VRV!s}$K#?!sD%6#IPRP3PKPW%?N!x^&#6,`MPZ%B9!xq$!xT&0ARA#0!xX'%1APW%BGPM%1D!xP$?XPM%3Y#:#DRY#:!xw'Y!sX+DV#:#5RV!sB,V!sB%%V5DFD@!s&/FnD@D@3U!s$%D7!s$>!s\'@DFM<m,_=RM;9MRZ1M00RV/M0RY/M1RX/M1RWPXP1PYP1PVP0!s$$HPECCPGCCPPCCPQCCRQ;9QRPA90OORG18<<RE'8RH'8RD'8RA,8<RL'81Q09P<PL1Q;:RLP<PAPLPZPD1Q>MPPPH1QWQPGPE1Q0OP<P<PLPLCH!s$/g00UIRL1ML;R<g00VUREg00_d3JRG7J;#^=909ASL;G=9;:%X5R51M5;RGg00Xd#XR9g00`i3J7S;=9;:g00ang00c45lgg00d:Rg,_=59>!ul3%kg%jgCC%igCC%hgCC%ggCC=9WQg00e?9J<ERE9JL!tS%OASL;E!t1&fD9JG99S5!tB$'8!s$/do"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msg_short_img : ltac2:(zQ "b0!jr9!jtc!j4!ju2!jg9!jh0!ir7!ki4!km2!kq9!krc@3$6@1$5@1$2@1$1@1$0#8@4$7$9\0@1$1@1$0#k0@1$3@1$1@1$0#8@2$a@1$0#k0+ijmtcNhf@2$4@1$2@1$1@1$0#8$8").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "##0Ap;1p;2p;4p;3g002\j11Tg00gIj1>!s/$gj1<Tg003[j1ATg004[j1HTg0027j10Tg005=j14Tg00hJj29!sJ$;j1@Tg00@Ij2?Tg00BFj2GTg00i=j1F!s/$_j2ETg0090j17Tg00jEj4C!t:$Aj3BTg00kEj3=Tg00LKj3;Tf0R0#1#4p=5f3R1f2R2f1R3/903=p=3%00#1p=6f4R4A=123;;0p=:A;2309;41p=2%70#7p=D!s-$#7#7p=8g00PbR0#1R4#1#1R1#>R3#<R2#AR5#HR6P2P3%0!tJ$R7#1R8#1R9#0#0#4R:193:!sG%7R7#0R:#1#5R;193;!s=$17!s\$0#4R;P3P;C3R!s?%60R0#6R<#4R=P3P=C3!sV%1#1R=#4R>P3P>C3R>P2P!sX%0:R:#5!sm21!v2%5R?P3P?!sk&0<#4R?193?!s5$5<R<P3P<C3R<P2P>!uG,0!sN17R7P3P7C3R7!t@&#4R:P3P:!t#&50R0P3P0C3R0P2P<!u@%8R8!v'%!sP%R:P2P0!t7&<P2P!ss%19!sK$9P3P9C3R9!uN&>!sG&:P2P9!t3%8R8P3P8!tB$!sr'3%04#5R41934%@2D:D2!s$4:D!s>,:D:,?5'Gg00kh%1=#>R=#<%F2U%01#6#0!s&+0#6#5,E=g00Tj#7#D#8!s$/CCg00m3,?55B6do"). Qed.
Lemma msg_overrun_img : ltac2:(zQ "b0!jr9!jtc!j4!ju2!jg9!jh0!ir7!ki4!ks7!kq9!krc@3$6@1$5@1$2@1$1@1$0#8@4$7$9\0@1$1@1$0#k0@1$3@1$1@1$0#8@2$a@1$0#k0+hmuv9Nhf@2$4@1$2@1$1@1$0#8$8").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "##0Zp;1p;2p;4p;3g002\j10Tg00gIj1@!s/$gj1=Tg003[j1BTg004[j1ITg0027j11Tg005=j1:Tg00hJj28!sJ$;j1ATg00@Ij2?Tg00BFj2HTg00i=j1G!s/$_j2FTg0090j16Tg00jEj4D!t:$Aj3CTg00kEj3>Tg00LKj3;Tf0R0#1#:p=4f3R1f2R2f1R3/803>p=2%00#:p=5%10#1p=9f4R4A>123;;0p=<A;2309;41p=3%60#6p=E!s-$#6#6p=7g00PbR0#0R4#0#0R1#@R3#=R2#BR5#IR6P2P3%10!sI$7#0R8#0#1#4R9P3P9C2R9!sG%7R7#1R:#0#5R;P3P;C2R;!sA$07#0#4R7P3P7C2R7!sw&#!uM$R<#0R=#:R>P3P>C2!sX%1!tW$!s;+R>P2P!t6&:R:!tK45:R:P3P:C2R:!sL%8R8#1R?#5R@183@P2P!tE%4?R?P3P?!t7&14R4!sN$9#4!sP+!u+&8#4R8P3P8C2R8P2P:P2P!tV-<#5R<P3P<!sq$8!sZ%!uI%8!sA,R<P2P<!tI%=!s;0!tw%48!t2'!t+&7!sA+00#5R0P3P0!sC$!sk%5=R=P3P=!u6&54R41834%A2D<D3!s$4<!s&&!s$$,?5'Hg00kh%01#@R1#=%G2U%0?#1#9!xD$9!s-$0#4,F1g00Tj#6#E#7!s$/CDg00n5,?55C6do"). Qed.
Lemma msg_short_len : ltac2:(zQ "60!kt6!k8!ir7!jr9!km2!jtc@3$2$1@2$0@1$5@1$3#8$4Nhf").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "###up;1p;2g0090j11Tg00BFj22Tf0R0#1#1p=3%1!s0$#1p=0g00o9g00Tj#1#3#0!s$/'2o"). Qed.
Lemma msg_overrun_len : ltac2:(zQ "60!kt6!k8!ir7!jr9!ks7!jtc@3$2$1@2$0@1$5@1$3#8$4Nhf").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "###up;1p;2g0090j11Tg00BFj22Tf0R0#1#1p=3%1!s0$#1p=0g00o9g00Tj#1#3#0!s$/'2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_regions : ltac2:(zQ "20!j4!lh8@1$0$1") := ltac2:(zQ "b0!h9!li3!r7!jb!re!hlc!hh4!k2!hm5!hgd!iie@3$3@2$2$1$0@4$4$1$0@2$6@1$9N0@1$a$5$5@3$3@2$2$1$0@4$4$1$0@2$6@1$8Z+hrmti0+u8@1$7@2$2$1$0").

Lemma hs_covA : ltac2:(zQ "d0!ipd!j4!ip2!ird!iu9!r7!lib!ir7!lj2!iv0!ljf!lke!itf@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsHdrErr ()) ["FPX1"] "p;2p;1p;3p100oXp4p70R0p1010Zp4p710p8P0p10116p4p710p8g00BFj26Tg003[j15Tg00@kj21Tg00C;j30Tg011Rj14Tg012Xj22Tg003Aj33Tg00XdR0g013^R1'6g014>g00UIR2g00QG#5R31123g00VUg00W_3030#4'2=301do"). Qed.
Lemma hs_covC : ltac2:(zQ "d0!ipd!j4!ip2!ird!iu9!r7!lib!ir7!lj2!iv9!ljf!lke!itf@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsHdrErr ()) ["FPX1"] "p;2p;1p;3g00BFj26Tg003[j15Tg00@kj21Tg00C;j30Tg011Rj14Tg012Xj22Tg003Aj33Tg00XdR0g013^R1'6g014>g00UIR2g00QG#5R31123g00VUg00]Z3030#4'2=301do"). Qed.
Lemma ho_covA : ltac2:(zQ "d0!ipd!j4!ip2!ird!iu9!r7!lib!ir7!lj2!jo1!ljf!lke!itf@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsHdrErr ()) ["FPX1"] "p;2p;1p;3g00BFj26Tg003[j15Tg00@kj21Tg00C;j30Tg011Rj14Tg012Xj22Tg003Aj33Tg00XdR0g013^R1'6g014>g00UIR2g00QG#5R31123g00VUg00_d3030#4'2=301do"). Qed.
Lemma ho_covC : ltac2:(zQ "d0!ipd!j4!ip2!ird!iu9!r7!lib!ir7!lj2!joa!ljf!lke!itf@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsHdrErr ()) ["FPX1"] "p;2p;1p;3g00BFj26Tg003[j15Tg00@kj21Tg00C;j30Tg011Rj14Tg012Xj22Tg003Aj33Tg00XdR0g013^R1'6g014>g00UIR2g00QG#5R31123g00VUg00e?3030#4'2=301do"). Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variables (L S Zr : list (word * word)).

  Definition h_regions_w : ltac2:(zQ "50!j4!r7!jr9!h9!jtc@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "b0!jr9!h9!jtc!r7!jb!re!lp4!krc!k2!lpd!lq4@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$7@1$0#k0@2$9@2$a@1$0#k0?3sp0$6$6@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$7@1$0#k0+hrmti0+u8@1$8@2$3@1$2@1$0#k0$1").

  Lemma h_regions_denot : ltac2:(zQ "h00!jr9!jtc!j4!r7!ir7!h9!lsa!mh5!mi4!hu6!mj1!mj8!lh8!mnb!mo6!lq4>4vals@1$2@1$1@1$0#k0>0@3$4@1$1@1$0#k0@2$d^1N0?3sp0>0@2$e$9@2$f@1$0#k0?3sp0@3$4@1$2@2$3@1$1@1$0#k0$5@4$6$c@2$3@1$1@1$0#k0$5@1$b@1$a^3$8$7").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["Sound"] "##/<h03Hloh12P0h21bh31rh44valsp;1p;2p;3p;4p;6g00gIj1PTg00ggj1KTg003[j1;Tg015Gj2A!s8$Aj37Tg016Ij26Tg0173j2JTg00@kj2<Tg0027j12Tg005=j19!sJ$Oj1B!s/$lj2:Tg00i_j24Tg00AKj43!s\$\j18Tg004;j1?Tg00LKj35Tg018Ij2OTg00BFj2NTg001>j6M!sA$fj1=Tg00C;j3ITg019nj1HTg01;5j2ETg01<<j1FTg00D]j3GTg006bj1DTg00>3j2@!ty$[j1LTg010Zj4>Tg01=Bj1CTf0R0#8#8p=0%20#8p=1g00PbR1#0R2#0#0#PR3#KR4#;g00TjR5,A0p,3sp0R6574g01>C1636R7'JP4P6g00PDR6,<4R8#;R9P4P61630%12#2#1!sy$9R2#BR:':,43P2C3!s^&S`R;,43,63%21R1#8!sW$!s&,0!se+<!sa$%11!s8$9R1C3%?8R=558558!tA$O72!t+-143<P1C3=58=558R=37X241N9=f2R7/A5f1EMg00oXR>P!sg$f3#=g01?NR4?I60R?#H'E,63%F?!tK$AG460C3X3>1<46R0P4P6%D5/@:!tB'%L;/@!tD$%?055035C>=79=eP>P8%=7#Cg014>C>g01@V579eW0W1W4o"). Qed.

  Lemma h_regions_flat : ltac2:(zQ "c0!jr9!mo6!jtc!lq4!j4!ir7!mi4!htc!hu6!mj1!moc!mnb>4vals@1$4@1$2@1$0#k0>0@3$5@1$2@1$0#k0@2$b^1N0?3sp0>0@2$1$8@2$3@1$0#k0?3sp0>0@2$1@2$3@1$0#k0?3sp0$7@2$a@1$9^4$6").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["Sound"] "##<sh01Hh11rh22Hah37__arithh44__ffh56__sat1h68__varmaph75__with84__x1h93Hhih:3Hloh;2Hrh<2P0h=!s_%0h>!s/%2h?1bh@4valsp;1p;2p;3p;4p;6p;7p;8g002\j11Tg00gIj1g!s/$gj1bTg003[j1WTg015Gj2N!s8$Aj3ITg016Ij2CTg0173j22Tg01Aaj3dTg006bj1aTg0027j10Tg005=j1;!sS$Oj1uTg00>3j2VTg00AKj4M!sJ$[j1kTg01B8R0j2XTg018fj1:!s:$Rj36!sg$lj23Tg01C]j2cTg01D:j29!s/$Vj2`Tg01E>j3_Tg004;j1^!s8$bj2]Tg01F@j1\!s/$^j1[Tg01GIj2ZTg00i=j1v!s8$lj2KTg01HOj2tTg01I2j3E!s/$Uj3sTg01J8j4G!s/$cj2rTg00BFj2qTg01KEj2pTg01L1j3o!s/$Pj4nTg001>j6jTg019nj1RTg01;5j2QTg01<<j1PTg0116j6LTg01MBj1i!s/$`j2hTg00C;j3lTg00D]j3m!v[$kj2HTg01Ngj7OTg01OKj7f!s/$oj8eTf0R1#!s$&p=4%11#0p=D%0!s6$Fg00oXR2f1R3;I1p==%0!sG$J%1!sG$Sg01?NR4g00PDR5;l1p=7Am451p=8g00S`R6/21p=<f2R71H31'Hp=@1263/H1p=A!sv$#0#0p=Y!s2+!s$'p=B1K51p=>P7g01PSR8g01Q2R9P9g01QRR:P5P3g01R2P1CGg01RYR;FOp=5P3P8P9P9P:P1P!s9$UP7!s9+3P1Ffp=?f3R;!s;+7P3P1Gep=Tg00PbR8#1R<#1R=#4R>#gR?#bR@#Wg00TjRA,N1p,3sp0RB5I@g01>C1C?BRC'2g01S9,2Cg014>RD9d21P0P4P5%aA%0=#D#F#4#;R=#uRE'VP=CMRF/=3!sI$k6%08R4#1#J!sO$J#D#S!sW&G'V%04!sC$F#S#;RHCMRI/=3g01TDRJ'Xf6RK#:%77%8736P11=F7P2PFf8RL#:RM%71RN%81RO36X12P@PB1C?1/3ERB%;<R<%;>R>'cRP,9B%<=RQ13B=/2P3@'AX?@1`<>R@196<%<>196P[[RB%<<RRg01TaRSA_<>3UW2R>%<P\S^2R!sA$U=RS#^RT%WSRS1]53%\5RU%[5RV1Z58R8%Y4#BR4#B!s$&;RW#>55V%v9R9PV%D4#J#Y#4!s$-;R4#>=5V8P91K56R9%>=RX,t59E58R855VP5P8g01UiRY%><=s5?R<CG,UVA5V9XAE58X=5V<5?V!s%%CTCT1rV:R:P1P7g00Xd!z1$3^RX'q1p17=I8XdAo563CnRXb4b6b7X85121W1243137ERE19EP13E=/2P7@Q'A[[^85P1PCf7RCPLO3b3b5b>1NCAPKEj%:CRC%7FRA#R'Q,C?%PA'3RL19LP%8FRF#<13LF!wK&eA6CAFeP;P1ELW0P1O11=I7/XJP01=I;PJf4R0#7%8056MP11=I0P2PIf:#:R0?6NO!xf&P>PRPTPS%i5PU%>G9E59RU95V9P5PUPYP!vI%%>HRY95V9AE5UY!vM0P:P!uy&136GRG19GP%<H13GH!t{&P1b3b=b5f9#:RG%7IRH!uZ+H'3R?19?P%8IRI#<13?I!uZ,GHIef5RI!u\,PJ%7K%8K560P1n010!s#%X0JP1O1n20!s9'2110!s3&!s`%!sB51000%:I%73%8336eW;X12%:;/hDeW9W:W<W@o"). Qed.

  (* [comment removed for export] *)
  Ltac hf_sound pcA rA cA srA knA sc rC cC srF knF ITIN COVA COVC MSG_IMG MSG_LEN msg :=
    intros vals R M msF mo K HL P0 HR HK Hfd2 Hrd2 OK RS HKnil HCONT;
    pose proof (know_nth RSEGS _ _ h_kn 1%nat _ HK eq_refl) as Hrg; cbn [kentry_ok edenot ev ENV] in Hrg; rewrite P0 in Hrg;
    unfold ASP_LO, ASP_HI in Hrg;
    pose proof (h_regions_flat vals P0 ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF;
    pose proof (h_regions_denot vals P0 ltac:(unfold ASP_LO; lia)) as RD;
    pose proof ITIN as (PCA & SCA & CCA & SC & _ & PCC & SCC & CCC);
    (* [comment removed for export] *)
    eapply (rz_run_lf_lazy RSEGS L S Zr FUELH STOPSH scr0 pcA h_sr h_kn 34 (fst (fst rA)) (snd (fst rA)) (snd rA)
              (fst (fst cA)) (snd (fst cA)) (snd cA) (ENV vals) M (seg_rom RSEGS) R msF mo);
      [ vm_cast_no_check (@eq_refl _ rA) | vm_cast_no_check (@eq_refl _ cA)
      | exact HR | exact HK | rewrite SCA; constructor | rewrite CCA; constructor | exact OK | exact RS | ];
    clear HR HK; intros RA MA msFA moA HR HK EQA LFA OKA SBA HSA RSA;
    pose proof (log_covered_frame (ENV vals) M h_regions _ COVA RF LFA) as FA; rewrite <- EQA, RD in FA;
    change (s_regs (fst (fst rA))) with srA in HR; change (fst (fst cA)) with knA in HK;
    rewrite PCA in RSA;
    (* [comment removed for export] *)
    apply (stdio_call_sound_post vals (blobs_ev []) srA knA RA MA L S Zr msFA moA sc [] msg K
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
    | rewrite (same_but_materialized_fds _ _ SBA); exact Hfd2
    (* LPS 75d69e00: the reader premise, transported through the same materialization as the
       fd one -- donor Both/As/AsHdrErr.v:196. *)
    | rewrite (same_but_materialized_reader _ _ SBA); exact Hrd2
    | exact OKA
    | exact RSA
    | exact HKnil
    | (* [comment removed for export] *)
      clear HR HK; intros Rj MC msFC moC HR HK HPOST OKC SBC HSC RSC;
      assert (FC0 : frame_mod MA MC h_regions_w);
      [ eapply sw_post_frame_mod; [exact HPOST|]; intros x Hx; unfold h_regions_w, HF_FR in Hx; cbn [outside] in Hx;
        unfold in_rng in Hx; rewrite P0, alu_add, vadd_wZ; revert Hx; unorm; intros (N1 & N2 & _); lia |];
      set (vals' := vals ++ junk_vals Rj) in *;
      assert (HL' : length vals' = 66%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity);
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0);
      pose proof (h_regions_flat vals' P0' ltac:(unfold ASP_LO; lia) ltac:(unfold ASP_HI; lia)) as RF';
      pose proof (h_regions_denot vals' P0' ltac:(unfold ASP_LO; lia)) as RD';
      change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK;
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELH STOPSH scr0 0x199728 (sc_sr sc) (sc_kn sc) 66 (fst (fst rC)) (snd (fst rC)) (snd rC)
                (fst (fst cC)) (snd (fst cC)) (snd cC) (ENV vals') MC (seg_rom RSEGS) _ msFC moC);
        [ vm_cast_no_check (@eq_refl _ rC) | vm_cast_no_check (@eq_refl _ cC)
        | exact HR | exact HK | rewrite SCC; constructor | rewrite CCC; constructor | exact OKC | exact RSC | ];
      clear HR HK; intros RC MF msFF moF HR HK EQC LFC OKF SBF HSF RSF;
      pose proof (log_covered_frame (ENV vals') MC h_regions _ COVC RF' LFC) as FC; rewrite <- EQC, RD' in FC;
      change (s_regs (fst (fst rC))) with srF in HR; change (fst (fst cC)) with knF in HK;
      rewrite PCC in RSF;
      apply (HCONT Rj RC MF msFF moF HR HK);
      [ eapply frame_mod_trans_same; [exact FA|]; eapply frame_mod_trans_same; [exact FC0 | exact FC]
      | exact OKF
      | eapply same_but_materialized_trans; [exact SBA|]; eapply same_but_materialized_trans; [exact SBC | exact SBF]
      | eapply hid_same_trans; [exact HSA|]; eapply hid_same_trans; [exact HSC | exact HSF]
      | exact RSF ] ].

  (* LPS 75d69e00, the channel-reader premise.  stdio_call_sound_post gained
     [m_channel_reader mo = true] in Bs/AsStdioCall, so this file's replayed
     applications of it are one argument short.  Measured before the edit, cold single-target
     run from a verdict-grade staging (SOURCE: a clean tree, image 2c6b6db8):
       VOS-FAIL Bs/AsHdrErr.v - Illegal application: "@stdio_call_sound_post" at line 212
     FOUR sites here, two chains: hs_ (short) and ho_ (overrun), each with a Sound theorem and
     a Plain wrapper.  This tree ALREADY CARRIES the hf_sound and hf_plain Ltacs in plain text
     (only the serialised Qed proofs replayed), so the repair is: thread Hrd2 through those two
     tactics - one extra intro and one extra bullet each - and write the four statements out
     with the premise.  NOTHING IS RE-ENCODED; the file's other replays are untouched.
     Statement faithfulness is MEASURED, not asserted: `About` on the OLD statements (scratch
     copy, the four proofs stubbed so the file reaches .vos, printed under -vok) against the
     NEW, whitespace-normalised - NEW minus the premise == OLD, with the negative control
     NEW == OLD failing.  OLD text saved at g3notes/bjrb-ashdrerr-statements.txt.
     DONOR, statement and proof, with its branch (rule 23c):
       a donor tree:projects/openssl/echconfiglist_parser/
       proofs/lib/Both/As/AsHdrErr.v:159-271 (the two Ltacs) and :225-265, :384-409. *)
  Theorem hs_sound : forall vals R M msF mo (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0xbea74) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) hs_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' hs_knF ->
       frame_mod M M' h_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0xbeab0) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_short) K).
  Proof.
    unfold W.
    hf_sound 0xbea74%Z hs_rA hs_cA hs_srA hs_knA hs_sc hs_rC hs_cC hs_srF hs_knF
             hs_itinerary hs_covA hs_covC msg_short_img msg_short_len msg_short.
  Qed.

  Theorem ho_sound : forall vals R M msF mo (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0xbea90) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) ho_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' ho_knF ->
       frame_mod M M' h_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0xbeab0) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
  Proof.
    unfold W.
    hf_sound 0xbea90%Z ho_rA ho_cA ho_srA ho_knA ho_sc ho_rC ho_cC ho_srF ho_knF
             ho_itinerary ho_covA ho_covC msg_overrun_img msg_overrun_len msg_overrun.
  Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variables (L S Zr : list (word * word)).

  (* [comment removed for export] *)
  Record hfH (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z) : Prop := HFH {
    H2  : getr regs 2 = sp;
    Hsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    HspLo : (ASP_LO <= bv_unsigned sp)%Z;
    HspHi : (bv_unsigned sp <= ASP_HI)%Z;
    Hstk  : stk_ok RSEGS mem sp HF_FR;
    Himg  : forall i, (0x10000 <= i < 0x67000)%Z -> mem (Z_to_bv 64 i) = None;
    Hgot  : forall i, (0x1aa000 <= i < 0x1b4000)%Z -> mem (Z_to_bv 64 i) = None;
    Hcells : cells_ok mem hf_cells;
    Hcan  : rdn RSEGS mem (Z_to_bv 64 0x711358) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Hcan64 : (0 <= can < 2 ^ 64)%Z }.

  (* [comment removed for export] *)
  Record hfPost (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := HFP {
    P_sp  : getr regs' 2 = sp;
    P_a0  : getr regs' 10 = Z_to_bv 64 1;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - HF_FR), HF_FR); (Z_to_bv 64 0x1b6d20, 232%Z)];
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0x1b6d20) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0x1b6d28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0x1b6d30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0x1b6d40) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x711b30));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0x1b6d48) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x711b30));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0x1b6d58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x711b30));
    P_mode  : rdn RSEGS mem' (Z_to_bv 64 0x1b6da8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0x1b6dac) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0x711358) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp HF_FR }.

  Definition h_vals : ltac2:(zQ "50!jr9!jtc!j4!h9!njf>4regs@2$4@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3can$3@1$2@1$1@1$0#k0") := ltac2:(zQ "90!jr9!jtc!jb!hn9!k2!h9!njf!ov3!krc\4regs@2$6@1$0#5@1$1@1$0#k0\2sp@1$1@1$0#k0\3can$5@3$3@1$1@1$0#k0@3$2@1$1@1$0#k0^2@3$2@1$1@1$0#k0@2$8@1$0#k0^1@1$4@1$1@1$0#k0@1$7^3").

  Lemma h_ev_junk : ltac2:(zQ "h00!jr9!jtc!k8!is9!ir7!qk1!qlb!qm1!h9!njf!qqb!mj1!qr5!qrd!qs2!krc>4regs@2$9@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3can$8>1i$2>0@2$3@2$6N2^1@2$7^1Ni2@3$4@1$1@1$0#k0@2$d@1$b@3$a^5^4^3^2@2$c^5@2$f@1$0#5@1$e@2$5^2N2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["Plain"] "##Iih04__p1h14__p2h24__x1h34__x2h42H0h53Hi0h67__arithh74__ffh84__p3h98__varmaph:5__with;4cstrh<1ih=1nh>1xh?2z0h@1HhA2HihB1bhC3canhD7defaulthE1lhF5lemmahG1mhH4regshI2sphJ1yp&0p;1p;2p;3p;<p;6p;4p;=p;9p;5p;Bp;7p;8g002\j1<Tg0027j1lTg00gIj1O!s/$gj1`Tg01VPk20ITg0090R0j12Tg03BBR1j2WTg02PZR2j2!sG$Akj20!sE$\j2[Tg003Aj31j1JTg01hRR3j13Tg005=j1KTg018Ij27Tg017lj2ATg01i2k20;!s0$Uk305Tg00BFj2;Tg02@Kl<P!sU$3R4j26Tg01D:R5j24Tg03C3j6dTg02`Bj4gTg01j2j1j!sA$\j2kTg01B8j2HTg03D>j2F!s/$gj3GTg03EPj2LTg00Kmj1mTg03F<k20!sT$F]k30GTg004;j1]Tg00LKj3!tm$3[j1\Tg01Ebk20FTg01MBk10ETg02Lbk40DTg01F@k10C!s0$^k10>Tg01GIj2i!s/$lj2CTg02A0k30=Tg01J8j4@Tg00i=k10<Tg01I2j3e!sB$ck20:Tg01KEk20!va$L1k304!s0$Pk402!st$Sj4_!sj$_j28Tg01W<j2VTg02NVj2TTg03GFk100Tg01`_j1UTg01aej3NTg03H6j4?j1z!s2$Rj4QTg03I9j1~!s/$hj4RTg03J_j3{Tg03KUj1yTg03LDj6}!s/$oj2MTg03M[l=xTg03NHj2DTg03OIm901Tg03PCj2wTg010Zj4v!s8$_k60!yB$1>j6^Tg03Qgj5uTg015Gk206j1tTg029Uk108Tg02<Wk209Tg03RIj2hTg03SLj3s!y~$fj1rTg03TRj2qTg02bWmB0?!s0$2m<0@!yD$Wj6pTg01Ngk70!zM$OKk70B!s`$oj7o!s9$oj8nTf0R6#2!s$%p=9%26#2p=|g00S`R7/q6p==g00PDR8f1R9;16p=>g00o9R:P:P:P8P8P8g03USP3P3P3f6R;g03V3f5R<f4R=f3R>f2R?P9P6NB0?p=b!s_+0!sZ$>g03VZP!sH%<0@p=a!sF$1P3P4g03W>P<P=P>!sH%M<Pp=c!sG$2P3P5g02jh!sG4SA1867p=ZP9g01PSR5g01Q2R2P2g01QRR4P6Epp=YP8P9g036_P6C@p=XP9P5P2P2P4P6g01RYK0Ap=:P?!s=+9P6K0Bp=B!s:1Fop=fP>!s9+!tZ$Gnp=Eg00PbR5#<R1#l#OR0%<1#<R@#<#<RA#<#ORB#`RC+0Ig00TjRD#2RE#2RF/W6%2FRG#2#9!s$/RH#|RI,I6'01[9FRJ#2RK#2RL=1:9%39RM%K1RN'7#=RO%K5RP'ARQ/APRR/>MP:P8%J:RSP3%J8%36R3,>MA1:9620;96405XJ:X>:PLPR1A6PX>8RRPKPQPRPJPO1796#=XG8X=8ROP9PM1;8MRRPFPN1;8NRQFbCaCaP9PMPRM<P1WF9RK1I9IRL'016NMRT%l@#<#KRU,4MRV'0RWPKPLPTPVPFPNPQ!sc%Ec!s-%PIPU1;8URRESEdP6CgPW%j?%3?RW,67%3>RM/7NRV,k7147V%=VRT/>V'016V7%ZT'0'H%3=/7NRT#=RVP8p-0RLg01U=RK1F8FRX1F8E1F8DRE5G85G8g03W`RY'LRZ1F8G%m5-0H8>0G8X=G8E!sM$/LY1LEY%]KRE55K55K35%\KRYP820F8?P9&0E8H0DRX&0C8RG&0>8R[1Y[=1i85R51i81R11C8NR\60=8R]'X,:[5B[R^P8P]g01R2R]1C87R_C@,:[1X5_,:[R_5B[5f[&0<2R2P[P8P\P]P1!sJ%Y[<R]5B[P21C8PR\9e85=e8\/X1,:[CECE20:[4R4P6P?g00XdR\g013^R`';2076?=1\`dB04879H02R`b7b9b:X28X38X0LW1179NR\,>6,0?Ra16\7%Z6R\'0'H16N?/0=1A?P/AP/>>[[^28^38^0L^1LP6%3;RP/4U17PN,47PPP9P?P=O6b6b?b4b;b5C_18B?%]CRP55C95C>Rb,VC/TJ=1:9RcePc18B>=5CP95C=Rc,VC1[?FRd'TRe=1:?PC%JCRf&00CPCP>18B=!sT&<RP%U;5NCRg18B7RBC?PC1VCP1[>FRP'TRhPgPBC?%\CRiPC^DCRj]ERk^=:RlP:PkPSPiPj%JiPCPCPfPfCQRmCQRnCQRo!sG$nPiPjPm!sF%%~CCRCRCR9{lo%zCP>PhP:PS%y:PhP>P6E}PgPg1MigPBPB1MCBM=x%3P,80,D;RPPP1MCPN901WFP6!s{$d%U<RiPBC?RgA1C6PXBCRPPC%3d!s\$<RhPP1;ChPCPdP:PC1803,D;X<:R31wDHCvP!uo$P3PdPHPB1IdH17WN#=R3%KARA'4PdP3POP?PW1;8WRO!}R%FbPHPA1;8AES1WF?RH1I?IR3!~:$WRD14WURP'0RSPHP3PDPP!~2&?PWPOEc!s-%PIPUP!~-%9CgPS%j>167M1k7T147T1>VT'016T7%ZV!}u%</7N#=P8A5KZEPYPXPGP[AB[]_9f[^P2P[1Y[;P8P1g01Ui!|e$U!{v$!{p$P8P5P11C8A!s:$CECEP4P!{?3X1LX8L10>\,Ha14?U,0<14?A!{%1^8LP6f7#3R6,6N176NRN/67147NP6!{3&7!{3/J03E^A1CghePCPeANCci!wE&cPiPBPdDuE^O2b@%U=9NCbRb0069%3J!x;$=R051Ce%tb%O@#`#\#]$08+09/h9=1C0eAs=>?#r!s5'WAX<:XC8XICWHo"). Qed.

  Lemma h_regs_ok : ltac2:(zQ "a0!jr9!jtc!jh0!h9!njf!qqb!qsc!pof!mj1!pl0>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2sp@1$1@1$0#k0>3can$3>0@4$6^4^3^2^1@3$9@1$8@3$5^5^3^2$7^5").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["Plain"] "#$W_p'0h02Hih17__arithh24__ffh38__varmaph45__with51ni001nh61bh71ih82Hah94__p1h:4__x1h;2H3h<5Hcan0h=6Hcan65h>7Hcells0h?5Hgot0h@3Hi0hA5Himg0hB5Hsp17hC6HspHi0hD6HspLo0hE5Hstk0hF2PHhG7__sat66hH!s0&7hI!s0&8hJ3canhK4cstrhL3memhM4regshN2sphO1xi012H2i024Hcani03!tn%4i046!to%i054Hgoti064Himgi07!ti$6i085!tj$i095!tj$i0:4Hstkp%0p&0p;1p;2p;4p;3p;6p;<p;7p;5p;8g002\j1FTg0027j1ETg00gIj1[!s/$gj1_Tg01VPk20BTg004[j1jTg03XLR0k405Tg01W\j3xTg005=j1<Tg016Ij2RTg03YQj2kTg003Aj3KTg0173R1j24Tg03Z1k40@Tg01D:R2j23Tg00Akj22Tg00i_j2U!s/$=j1eTg03[2j2w!ss$[j1fTg0090R3j10Tg00jEj4tTg03\?j2rTg00@Ij2qTg01C]j2nTg02PZR4j21Tg00kEj3Z!u&$[j1mTg03]Gj1lTg03H6j4PTg03SLj3`Tg03BBR5j2CTg03C3j6A!v$$;k10?Tg01MBk10>Tg01F@k10!uw$F^k10;Tg01Jck207Tg00BFj2^Tg01KEk206Tg01L1k304!s0$Pk403Tg03RIj2hTg01hRR6j1V!vS$lj2STg02`Bk402Tg01j2k101Tg03^Lk200!ve$Vj2~Tg01E>j3}!s/$bj2{Tg02Lbj4dTg01Glj2c!s/$Ij2y!sp$Wj6|Tg03_=j4uTg018fj1\Tg03NHj2OTg01;5j2]!v%$\j2sTg02@Kl<i!uW$8j4YTg01Ngj7WTg01OKk708Tg02ASk409Tg03`Pk50:Tg001>j6oTg02b2l<bTg01I2j3X!s_$ok80=Tf2R7f1R8f0R93`#\p=9g03aYR:9Z89p=pf3R;1O78;K9p=a%F9#F#F#Fp=J%F9#<p=I%E9#Fp=Q!sB$p=Tg00S`R</49p=Lf4R=?`;7#\g00N4R>P8g02kJR?P9CP']p=6f5R@P;P7g03b5RAP8CP,O=!t>$51O;7%\8/]95K=p>0A1s89#V,U7,O;p=@AZ78:,O;=K=9p=Dg00PDRB/^9p=8g00o9RCPBP5P6P1g03W>P@P=P;P7P8P9M<ip=BPCPBP4P6P2g02jh!sG4;1cB9p=7f6R2g01PSR4g01Q2R1P1g01QRR5P@P4P1P1P5PBP=g01R2RDP;CYg01RYREFWP7!sH-8g01UiRFP9CYPEFWK08p=>f7RGP2!tM/H09I0:p=?P!s?$1^=;1h78P9Eop==!sP$AP;CP,O2P>P8P!vp$,]75KGp=:1S=;/S7/S8/S9p=GPC!u`$BP3P6!ud%3VZRH!sm$!sA1;PH!uv'bM<bp=H!u51PD!u0'p=zAXB=;=XB7=XB8=XB9p=M!sU2!u_+p=vP;!sA+!t1$L0=p=g%09#0#0#0p=Ng00PbRE#FRF#ERD#[RH%FFS00#FR6#FS01#FS02#FR3#[RI#_RJ+0B%[6#_RK#jRL\J!v_,5P0!vn'A9@;7?x?@P9PJf>R0%<FRF,pHS03f<Caf=,RIQ01#<RM'k=KB<g01>C1RI0'4f?,RIg01S9'4g00khR0fAf@S04g03cCH0@%F3#J#J#I/49%EERN#FRO#FS05#ES06#E#Q#T!sH%,39'2fDRP1UI8RQO1%eKRR5KL[^7B%EOS07#FS08#Q#E!sX$!s|%Q07#ES09#F#Q!s='!sq%ERSPQO1=KLR[^7Bg03dH,wP%fKRK#jP0PS%ENS0:#FS0;#FS0<!sj$T#E!s&$Q!t7$E#T#I,UIg00TjR0#0RR#0RL#0RQ#0RT#0RU#0RV#0RW#0RXCtfC,UI,rX,qK3K%LP%<3R3,nFS0=,3P'2fHRPfF;9SP?PP%0XRS#0RK#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk#0Rl#0Rm#0Rn,19RoPCPJfLRp%_HRqP8AZH<:R:PpfJRrfIRsP8%m<RtD6E5^0oP8110nfKRo#lPJPoPqP0PAP:CPA`osPP>P0P?PtCPI0AeW0PC%09S0>/1nPJfNR?Pq%08S0?P:P?PpPoQ0?P!t&$]0P911RnPJfMR>PHPQPLC@RsPJP?PH%<EREP9DDX6JPJPsA9>orS0@PQP>PoPrPQ1CLQRr%0nRo#0Rs,1QRP'2%<NRN,4FRA%E6S0A#IRu,3NRv'2S0BPrPPPAPvPLPF%8FRvPQPN%8NRAEBPQPNPAPsPu%8uRAE;EAg01U=RP$0?Rr%fPRP&0>BRw&0<BRx&0;BRyPy%7FRz%7NR{PyP{%7uR{F>207y5R|P9P7g00XdR}g013^R~'^20697=K}~dB04B<8H03R~b2b3b4Q0BP9b1G?G=PJP>PqPRP:Q0@PRPtG:!v|$Q0>#0!v~+PRRPqQ0?#0S0@P:PRP?P>Q0@!w$/LnQ04PJfOR}Q03A9}>pR>/h0CaePJP}PqPLP:P>PL!t21R!t1&RR0PqQ0@!tD$P:P0PRP}Q0>!t1/QnPJfQRpPHPUPLC@S03PJP0PHPN!x1+!tJ$p}?S03PUPpP}P?PU1CLUS0411UsS0B'2%<DR?,4FR}13?uRN'2S0CQ0!v7$}PNPLPFPvPUP?%8?RNEBPUP?PNPsPuP!ww$!xN$wPxPyPyPz%7?RNPyPNP{F>P|P!w++C!w+-pPqPQP:Q03PQ!ux+%0>!uv'TRQPq!w<&3P:PQP0PpQ03!uv/TnPJfSRNPHPV!{'$}PJPQPHQ00#<!{',}A9NpRS0CPVPNPpPRPV1CLVS0B11VsS04'2%<ORR,4FRp13RuR}'2S0DQ0BQ04!vR$!uw%VPR%8RR}EBPVPRP}!uw=RR}PyP}!uw3D!uw-NPqPTP:Q0CPT!uw7VRTPqQ03#0S0CP:PTPQPNQ0C!uw/UnPJfUR}PHPW!uw$pPJPTPHP?!ut,pA9}N0S0DPW!x:$0PW1CLW!xm$WsR0'2Q0:#<!}t%p13NuR?!}k$Q04P0PpP?!ut&W!}i%?EBPWPNP?!ut=NR?PyP?!ut3!|s/}PqPUP:Q0DPU!ut7XRUPqQ0C#0R?P:PUPT!zx$!ur-VnPJfW!{c$X!ur$0PJPUPHPR!ur,0A9p}QS0DPX!x5$QPX1CLXRQ11XsR}'2%<6R6,4FR0136uRR!uo$PQP}!|~$!un%XP6%86RREBPXP6PR!un=6RRPyPR!un?pPqPV!un%V!un7ZRVPq%0?RRP:PV!}h$R!ul/WnPJfYR0PHPS!{Y+V!~P0P}A90pTS0DPS!x/$TPS1CLS!{V$SsRT'2Q00#ERp#<R},4FRN13}uRQ'2S00Q0BPTPNPQ!ut&SP}%8}RQEBPS!v`$!ut<}RQPyPQ!ut30!ut-0PqPW!ut%W!ut7\RWPq%0RRQP:PWPVP0PQ!ut/XnPJf[!~O$K!ut$TPJPWPHP6!ut,TA9N0US0DPK!{T$UPK1CLKS0011K!#5E%FDRU#<R0,4FRT130uR6'2S04Q!uv'6!ut&KP0%80R6EBPKP0P6!ut=0R6PyP6!ut34!~P2X!ut%X!ut7^RXPq%0QR6P:PX!|s$6!ut/SnPJf]RTPHPY!#8=$DPJPXPHP}!#8=,DA9TNVS0DPY!x7$VPY1CLY!~N$Y!uv&EDRD#<RV!xk&V!#5H%0!#8A%N!#5H'YPV%8VR}EBPYPV!#5H>V!#5H8!xl/TPqPS!uv%S!uv7`RSPq%06R}P:PSPX!~R$!uv-KnPJf_!xl$Z!uv,SPHP0!uv1NTWS0DPZPNPTPWPZ1CLZ!xn$Z!uv%Q05#<RW!xl&WuR0!xl10!ut&ZPW%8WR0EBPZPWP0!ut=WR0PyP0!xlCK!ut%K!ut7bRKPq%0}R0P:PKPS!z{$!ut-YnPJfa!xl$[!ut,KPHPV!xl3XS0DP[!xl$XP[1CL[!xl$[!ut'7#<RX!xj&XuRV'2S07!xj+V!ut&[PX%8XRVEBP[PXPV!ut=XRVPyPV!ut37!xj2Y!ut%Y!ut7dRYPq%00RVP:PYPKPTPV!ut/ZnPJfc!xj$\!ut,YPHPW!xj3SS0DP\!xj$SP\1CL\S0711\!ut';#<RS!xj&SuRW!xj&7!xj%W!ut&\PS%8SRWEBP\PSPW!ut=SRWPyPW!xjCZ!ut%Z!ut7fRZPq%0VRWP:PZPYPNPW!ut/[nPJfe!xj$]!ut,ZPHPX!xj3KS0DP]!xj$KP]1CL]!xj$]!ut':#ERK!#>,%S0:13NuRX!xo-Q0:PX!uz&]!#>0$XEBP]!yb$!#>0=XPyPX!xpC[!uz%[!uz/S0D!u{%hR>Pq%0WR[P:P>PZPTP[!u{/\nPJfgRXPHP^!u{%7PJP>PHPS!u{-7A9XTYS07P^PXPTPYP^1CL^S0:11^sRY'214FMRT13MuRS!#@w%:PY!yD$!um%^PM%8MRSEBP^PMPS!um=MRSPyPS!#>/>XPqP\P:Q07P\!#I`,D#0R\!un%j!#5M$[RTP:PSP>!u,$!un-]nPJfiRYPHP_!#5M0N!xk1YXZS0DP_PYPXPZP_1CL_!{a$_!xk'A#<RZ,4FRX13Z!#I^%A!{a&X!#I^'_PZ%8ZRNEBP_PZ!#I^>Z!#I^8A!uv-YPqP]!xe%]!xe-\!ut'lR]Pq%0TRNP:P]PS!{c$!ut-^nPJfk!xd$`!ut,]PHPM!ut1XY>S0DP`PXPYP>P`1CL`S0A11`!ut%%IpR>!{[$713>uRY'2S0:Q0A!{[$7PY!ut&`P>%8>RYEBP`P>PY!ut=>RYPyPY!ut3:!xl2^!ut%^!ut/!{[+nR\Pq%0NR^P:P\P]PXP^!uu/_nPJfm!xk$a!uu%:PJP\PHPZ!uu-:A9YXSS0:Pa!xk$SPa1CLa!xk$asRS'2%Ep#<Rp!xj&puRZ!{a&7PS!yD$!us%aPp%8pRZEBPaPpPZ!us=pRZPyPZ!{a?YPqP_P:Q0:P_!{a2_!ut%p!#5N$^RXP:PZP\!u3$!ut-`nPJfoRSPHPb!#5N0>!xk1SY]S0DPb!yV$]Pb1CLb!~Q$b!xk'UR],4FRY13]uR>!#5G%:Q0B!yD$!ut%bP]%8]R>EBPbP]P>!ut=]R>PyP>!#5F>SPqP`!xi%`!xi-_!ur'rR`Pq%0XR>P:P`PZ!~Y$!ur-anPJfq!xh$c!ur,`PHPp!~U2S\S0DPcPYPSP\Pc1CLc!xh$csR\'2%EU#<RU,4FRS13UuRp!xh+\PSPp!ur&cPU%8URpEBPcPUPp!ur=URpPyPp!xhCa!ur%a!ur7tRaPq%0>RpP:PaP`PYPp!ur/bnPJfs!xf$dPLC@R\PJPaPHP]!uq+P\A9SYZS0DPd!xd$ZPd1CLdS0B11dsRZ'2%IDRY,4FR\13YuR]!xc&B!z$$]!un&dPY%8YR]EBPd!yR$!un<YR]PyP]!xbCb!un%b!un7vRbPq%0pR]P:PbPaPSP]!un/cnPJfuR\PHPe!un$ZPJPbPHPU!un,ZA9\S`S0DPe!x/$`Pe1CLeR`11e!~I&D#<RD,4FRZ13DuRU!uo$P`PSPZPU!un&ePD%8DRUEBPePDPU!un=DRUPyPU!un?\PqPc!un%c!un7xRcPq%0]RUP:PcPbP\PU!un/dnPJfwRZPHPf!un$SPJPcPHPY!un,SA9Z\aS0DPf!x/$aPf1CLfRa11f!{O$Q05#I!#C`$Y13SuR`'2S05PaP\PYP`!un&f!#C^$`EBPf!v\$!#C^=`PyP`!un35!un-ZPqPd!un%d!un7zRdPq%0UR`P:PdPcPZP`!un/enPJfy!~B$g!{N+dPHPD!{N0YZbS0DPg!{L$bPg1CLgRb11g!{M$Q06#<R\,4FRD13\uRa'2S06PbPZPDPa!un&gP\%8\RaEBPg!v\$!un<\RaPyPa!un36!~>2e!un%e!un7|RePq%0`RaP:Pe!|g$a!un/fnPJf{RDPHPh!{N+e!#CP/PZA9DYcS0DPhPDPYPcPh1CLhRc11hsRY'2Q08!#@]&S13ZuRb'2S08!#5_%b!un&h!#@[$bEBPh!v\$!#@[=bPyPb!un38!un-DPqPf!un%f!un7~RfPq%0aRbP:Pf!|g$b!un/gnPJf}RSPHPi!un$YPJPfPHP\!un,YA9SDdS0DPiPSPDPdPi1CLiRd11isRD'2Q09#<!#5/-c'2S09PdPDP\Pc!un&i!#5-$cEBPi!v\$!#5-=cPyPc!un39!#5-1g!un%g!un6p+01ARgPq%0bRcP:Pg!|j$c!uq/h!sN&@R\PHPj!ut$DPJPg!#@Y/PDA9\SeS0DPjP\PSPePj1CLjRe11jsRS'2Q0<!#540d'2S0<PePSPZPd!ut&j!#54$dEBPj!vb$!#54=dPyPd!ut3<!#541h!ut%h!ut:CRhPq%0cRdP:Ph!|p$d!ut/i!sN&BRZPHPk!#5:'h!#5:5fS0DPkPZP\PfPk1CLkRf11k!#5:%;#E!#Qv&!#5<$e'2S0;PfP\PYPe!uv&k!#5<$eEBPk!vd$!#5<=ePyPe!uv3;!#5<1i!uv%i!uv:ERiPq%0dReP:Pi!|x$e!uv/j!sN&DRYPHPl!#5B'i!#5B5gS0DPlPYPZPgPl1CLlRg11l!#=i%K!#5@-f!ur%gPZPDPf!ur&l!#5@$fEBPl!vb$!#5@=fPyPf!ur?YPqPj!ur%j!ur:GRjPq%0eRfP:Pj!||$f!ur/k!sN&FRDPHPm!#5F'j!#5F5hS0DPmPDPYPhPm1CLmRh11msRY'2%EK#<RK!{`&KuRS'2RgPh!vH$!#Qr&mPK%8KRSEBPmPK!#Qr>K!#Qr6Pg!#5D1k!ur%k!ur:IRkPq%0fRgP:Pk!|z$g!ur/l!sN&HRSPHPn!ur+k!#5J0ZA9SDiS0DPnPSPDPiPn1CLnRi11n!#5J%2!#8:&\13ZuRY'2RhPiPD!{]$!ur%n!#89$YEBPnPZ!#Nx>ZR\PyP\!ur2h!#5H1l!ur%l!ur:KRlPq%0gRhP:Pl!|v$h!ur/m!sN&JRkPHPo!#5H'lPHPK!#5H/kSjRDPo!si$jPo1CLoRj11o!#5G%1!~Q$!xg$H!xg$l'2RiPjPS!|Z%!us$o!xg%vEBPoPKPv!xg?KPyPK!us2i!us-kPqPmP:PDPm!ur&%0_/1n%0h!uv$%V8RmPE!s$%DG!s0i/3ZS01P_1S9EXOBR_P!s$amO1S0DO1S02O1S0;O1S0<O1S09O1S08O1S06O1S05O1S07O1S0BO1S0:O1S0AO1S04O1S00O1S0EO1RDO1RkO1RiO1R{O1RKO1RzO1RAO1RuO1RsO1RvO1RoO1RLO1RlO1RHO1RSO1RjO1P_PhPjP_PgPSP_PfPHP_PePlP_PdPLP_PcPoP_PbPvP_PaPsP_P`PuP_PUPAP_P]PzP_PpPKP_P>P{P_PXPiP_P^PkP_PNPDP_PTQ0EP_P[Q00P_PWQ04P_PVQ0AP_P0!#T3$}Q0BP_P6Q07P_PQQ05P_PRQ06P_P?Q08P_Q0CQ09P_Q03Q0<P_Q0>Q0;P_Q0@Q02P_Q0?Q0DP_P8Pm%8mFH!s$A!}?%E;P9H02Q01&017%V7#Lp+01L,RIRY000M%LY%LMp+01N,RI/kM#L[[1~F313<F%L3Q0=,3<[[%LFRMg01TaRIA}F38UW8Q0=#L\I^8Mp-0RM!{T$BPBPwP81{B8CdP8PwCdPxPy1cB<1yBORO5zy%e1R<PyPO%7EROP!s$$DMP!s0h=vy\P<Py!$8]';E|CgCg!|~,X:BW9%L9P8!|VvP;[[^:B^9MP9!#42$RRMPq%NG#N!s$/RqP:P!w=$Pp+01OPq!#4n$%VGP=P@O4b1bGbHbIbKb@W0X7CP9O1n0110001020111100X5!s>_0!s>~!s>~!s>~!s>~!s>~!s>~!s>t0!sVXP9O1!{l$CuW=W<W>W?WAWEWCWDWBW;f9f8P!$Fd1O:n40!{c$!s#$1:110110710910810:106105104102103WFXJBXNJWLWMo"). Qed.

  Lemma h_know_ok : ltac2:(zQ "b0!jr9!jtc!jh0!h9!njf!qqb!qsc!po7!mj1!pk5!kq9>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2sp@1$1@1$0#k0>3can$3>0@4$6^4^3^2^1@4$9$a@1$8@3$5^5^3^2^4$7").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["Plain"] "##cYp'0h07__arithh14__ffh28__varmaph35__with44__x1h51mh66__sat0h7!s/%1h81dh91zh:7!s7$66h;!s0&7h<!s0&8h=4__x2h>1xh?2Hah@4__p1hA4__x3hB1bhC4cstrhD1ihE2E0hF2E1hG2H3hH5Hcan0hI6Hcan65hJ7Hcells0hK2HdhL5Hgot0hM5Himg0hN2HmhO3HsphP5Hsp17hQ6HspHi0hR6HspLo0hS5Hstk0hT2PHhU2Z0hV3canhW3memhX1nhY4regshZ2sph[1yi002H2i014Hcani02!t\%4i036!t]%i044Hgoti054Himgi06!tM$6i075!tN$i085!tN$i094Hstkp%0p&0p;1p;2p;4p;3p;5p;6p;7p;9p;8p;<p;@p;Bg002\j10Tg0027j11Tg00gIj1d!s/$gk102Tg01VPk20YTg004[j1tTg03XLR0k40GTg03SLj3NTg018fj1ITg01Xjj4_Tg005=j1CTg00kEk306Tg03NHk20iTg003Aj3?Tg016Ij27Tg03YQj2QTg0173R1j25Tg03Z1k40!t,$D:j2;Tg00i_j2:!s/$=j1oTg03[2k20>!s{$[j1kTg0090j1ETg00jEj4pTg03\?j2~Tg00@Ij2rTg01C]k205Tg00Akj2!tm$ePk103Tg00BFj2OTg03RIj2hTg006bj1}!t&$Ok20]Tg00:Xk30[!u%$Ok10ZTg00>3j2gTg00;aj2{Tg00<jj2z!v-$[k10XTg00Lkk30W!vr$;j1yTg03fVk10VTg01aek30UTg03gck50!v1$gBk30Pk40gTg01MBk10MTg01F@k10L!s0$^k10KTg01Glj2sTg01Jck20!wY$KEk20HTg01L1k30F!s0$Pk40!vB$1>j6!tH$;5j2cTg03hlk70DTg03^Lj2q!wF$Vk20BTg01E>k30A!s0$bj2a!tA$Ij2]Tg03j3k70@Tg03k:m90!xO$IUk30=Tg03lBj8mTg03BBR2j2lTg02ASj4b!va$lR3j23Tg01hRR4j1JTg02?mk10<Tg02B>k40;Tg02@Kl<iTg03mGm@09Tg03nMj4TTg01B8j2XTg01j2k108Tg02Lbj4f!s9$Wk60!z%$Tok70JTg03D>j2e!s/$gj3xTg03EPk20O!wl$Kj3uTg03oMj2vTg040Qk404!y6$`j4wTg019nk10RTg01<<k10S!tS$Rk30TTg041ak20hTg024Bk20f!z?$kk200Tg042nk30eTg043Jk50_Tg044Yk40^!x,$8j4|Tg01Ngk701Tg01OKk70\!s0$ok80`!v}$2k30aTg02b2m<0b!s0$WmB0cTg0454k60dTf0R5#0#0p=>g00PDR6g00S`R77?5p=\%0!sD$!s$+Cp==%15#1p=A%15#0p=9!sJ+p=[f2R8f1R9'5/65p=^%0!sR$D!sJ'Cp=P1575p=4g00O;R:?u95p=Gg00khR;P8P9P5C_p=M1s65p=8P6P9g01UiP5C|p=Z!s4$PSR<g01Q2R=P=g01QRR>P5g01RYR?K01p=Yg00XdR@g013^RA!uD$Kf3RB/581595'6p=<!u@$#1#1p=`!s2+!s$'p=RP8P<P=P=P>!tT&R2P5C|P!t1%2!v;30p=n!sY-9P5K0\p=FPB!s:+!uU$L0`p=@1595,68p=W1O65p=Lg00o9R?P6P2P4P1g03W>f5R2f4RCPB!sa%M<ip=jB0a695p=BP6P7!sA'EVp=U1389/55p=SP?P6!s$$4P4P2P!sh+N<0bp>0:!sD&!s$%3P5P9P8P3PBPCP2f6R3f7R4f8RDf9S00NB0cp>0CP:!so,J0dp=Hg00PbRE#0RF#1#dRG%0FRH#0RI#0RJ#>RK#dRL$02RM+0Y%dI$02RN#tRO\M!sp'H0GP0!t#+;AN2B8#IPCg02lNS01C_P5f>R0%CFRPg03aY606G+0if<RG5?Mf=,7L%CJRJ'Q#\g01>CRQ17L0'5f?RR,7Lg01S9RS'5P;fAf@g03cCRTH0N%0K#>#=RU%1ERV#0RW#0#A#9#[#=RX,;57^5fDRY1:L9RZO1%oNR[5?O[^D6%1WR\#D#D#>!sU$]%1\S02#DR\#0!s:&^!si&ER_PZO1=?O[[^D6g03dHR[-0>Y%kNRN#tS03P;P_%1VR_#0RO#0#D#>S04#0#9#D#9#9#A#PRZ,:Lg00TjR`#ERa#E#ES05#ES06#E!s$%RbCpfC,:L,~b,rN3?%4Y%CKRK-05PRc,;Y'6fFRd$0317LdRe#41;ec'6fGRe,OMfIRf?Ned#I/h`=?Me1:LeRd,OMfJRgfH;Ne#I/ha=?Md1O671:L7Rd,7LRe#\fLRh?Ngf#IRifKRj%}`Rk00]JRlB0[kQSRm&0ZT,gk/{TS071zUXS081z]^S09&0X7Rn/gZ%}aS0:80WbS0;%9\#AS0<!v%&>#PR\,gnRo%1O#PRO'{S0=%y:S0>'GS0?'GS0@'GS0A'GS0B'GRp'GRq'GRr&0V[Rs60U:Rt3MfMS0C?Njg#IRu?MhrAMuhs'6[AMijrRvAMijsRw'6AMuht[P;PiPjPrPsI0QPvPwB0P;ijRwPlPq!sC&kPJg01U=Rq#yRl%kqRv&0M6Rs&0L6Rr&0K6Ru1s67Rt%8J'Z'Y20Iu>RxP5P81O@AS0D20H58#KdB0F679H0ERAb1b2b31;7JP5b0PMPg17L5R@/QJ#\XBMPG1hi`S0EP8EV1cik,7LRG!sD$eK0DPwPmPp!tq+QPSPMPgPQP@P@PSC<XBM17LgR@/qJS0F%4@%4JS0G17Lh/QJ#4[[S0H20BPKRp1;7P%4K1;7cS0I[[Rm%4PRyg01TaRzB0APK9UW?RK%4c\z^?yRyPlPv1a69S0JPrPu1]6ERz%`_#RR_#R!s$&CR{#852uR|%o=R}Pu%0_#A#`#9#n#n#=R_#8S0K=2uzR~P}AFu~|C@C@PxP!v>&X46155{15_9P_P8P8P{C<[[^46P5fNR{,7LR|P0PRO3b0b:b;b<!uz,eQ!v\%PQPGPG!s8$K0@PwQ07Q0B!vZ+gPTP8Q00Q0FQ0HPpPmPKP!uW$Q!uS%P~P}%9H#A!zg$H#8R~92utA2u~z5Fu!t~4_5%4H?WH9!tv%P|PRO2!tm+7PTPTP@C<eN90?PwQ08Q0A!t\&UPXPlPvPsPr%8U92ut!t&,%4U!yA$!to-!sN%X%8P>0=6LRP52u!sW,15XcP5b0b6b7PDGmPwQ09Q0@!t:&]P^!sj,]!t:3]!t:9^=2uP!t1/^!t1,4!t1%;Q0?!t1&nPdPZPbQ0:1:Lf1OMdP91lab%CERE%CIRI'5RdPaPE%LEPbPI%LIRaEj!t>,E%8IRE!uM0PdP5b0Cb1lbb15IIRdPbPIPa!s+%!sc,A2uEE!s]635ZRd#4X96!t5,Z,BtRf!uz1137ZRZ#4!v#$eP5CU%JbRn=SdcX9613ZnR^/5cR]13ZIRX/5cRUP6P6P1P5X>6R@P11595$0<X[6X>6P^PX!zY$@P6P6g037F1395H0;#LX56XX6PZPZ%LZPnPIP@P@%J5#LX>?!uO%J0:N:0CPcPc%LcM<i!wc31BfE!wd1PU!wb'CbP]e!u;%Q03P;Ph1:LdPbCp1:Lg!#9M&X96P2!sL%N@09PwQ0=Q0>135\RN#41;Nc%4ORb13NO;Wc'6'6%49RN%J9=S8ORgP;fPRd13C\/3B,:LP8CT#K[[^5?^86'6!vV$7\Rh#41;hc13hO=Wb!so$R]P;fORU13hBRf,:LRE!sd%\g\N!sf%!zL5\Ra,BtRI92ut1ZIP,Yu%8OR@!s6$BI@=2uP5Fu!s%%!v6-]!zr+UPEP8P6PfP\P5%JB,35R]Q0<#1#9#=RnC<Q02#9RZ#0#D!~`$=RXP5P]%1ZRZ!s9$9#=R^C<%AZ#9#`#9#>#PRZP5P]Q04!sn$[#=R]C<'X'XX96&088R1%J8#4RT17LURR/qJR|%4RQ0GfQ,7L!#7H%RJ!ui'p-0RR!un$61a68RHP9PsCf!#6y%FRF,Bz=2u@P}PuA2utzR~P}Pu!#E|&1BIz!vD$a1BIF%8n52!v0$!sG+PCJ07K0J!#6|3X=6W@AS59O13h8R>AS>Bn5^\/XC\N[^46^=6^@RP5PX13hDRX%J4RR,3XR\P^C<PZPXP\P!us$PRPDP2P3O5!#5b&bC17LEP1PTP|P!ub+Q06,e6Q05,e61e6`5x65x6g03W`+0O=uq!u}$P6PsPB1a6BCfP9PH!v'+WRW!}~$}Pu1BzW!v4'P!v/$Q0K1]6V52uP}A2utI!yL&5FuC@!s$%!uu3XA6%48RIAS9BO15_C13hC!{$''6[\I[!u~'A6P5PRfS,7LPDPCP2P3PYO7!ue,,vfEVH04XNgXKNX5?X86CwPe!{@3A2utt1Zt!ti&!ta,Q0I9^77!z}',v7CU&0RoR7,ci,7L&0SoRA'3Rx#41;xc13x!|p+P;PUQ0C9Nd{#IRd/c7,7L/3A!}a/!|{,'6eB0TioOP;PU20hdo!sN<!#8;$Q0=H0ge20f:wDH!s$/PiPjP[Q0D2006?0006g045U<0e[#KdP3I0_CwH0^!sn'1C_RjePjebUbFbEbOWIWHWJWLWMWSWQWRWPWGQ00PDP4P3!#Ly-O:n4000010!s#$1:1100106108107109105104103101102WTXV6XZMWWWYo"). Qed.

  Ltac hf_plain SOUND :=
    intros regs mem msF mo sp can K PH OK RS Hfd2 Hrd2 HKnil HCONT;
    pose proof (h_regs_ok regs mem sp can PH) as HR; pose proof (h_know_ok regs mem sp can PH) as HK;
    destruct PH; pose proof (u64_range sp) as Hsp; unfold ASP_LO, ASP_HI in *;
    apply (SOUND sp L S Zr (h_vals regs sp can) regs mem msF mo K);
      [ unfold h_vals; rewrite length_app, junk_vals_length; reflexivity | reflexivity | exact HR | exact HK
      | exact Hfd2 | exact Hrd2 | exact OK | exact RS | exact HKnil |];
    clear HR HK; intros Rj R' M' msF' mo' HR HK FM OK' SB' HS' RS';
    set (vals' := h_vals regs sp can ++ junk_vals Rj) in *;
    assert (P0 : vals_ev vals' 0 = sp) by reflexivity;
    assert (P1 : vals_ev vals' 1 = Z_to_bv 64 can) by reflexivity;
    assert (PJ : forall i, (2 <= i < 34)%nat -> vals_ev vals' i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2))));
    [ intros i Hi; subst vals'; rewrite vals_ev_app_l by (unfold h_vals; rewrite length_app, junk_vals_length; cbn; lia);
      apply (h_ev_junk regs sp can i Hi) |];
    apply (HCONT R' M' msF' mo'); [| exact OK' | exact SB' | exact HS' | exact RS']; split;
    [ regv HR (2 : reg); exact P0
    | regv HR (10 : reg); reflexivity
    | intros r Hr; cbn [In] in Hr;
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
        lazymatch goal with |- getr R' ?rr = _ => regv HR rr end; cbn [edenot ev ENV]; rewrite PJ by lia; f_equal; apply bv_eq; reflexivity
    | exact FM
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | krd_solve HK
    | let Hc := fresh "Hc" in krd HK 0x711358%Z 8%nat Hc; rewrite Hc; cbn [ev ENV]; rewrite P1; reflexivity
    | intros a n Ha Hn; eapply frame_mod_store_ok; [exact FM|];
      match goal with Hs : stk_ok _ mem sp _ |- _ => apply Hs; assumption end ].

  Theorem as_hdr_short_fwrite : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0xbea74) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0xbeab0) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_short) K).
  Proof. hf_plain hs_sound. Qed.

  Theorem as_hdr_overrun_fwrite : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0xbea90) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0xbeab0) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
  Proof. hf_plain ho_sound. Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
