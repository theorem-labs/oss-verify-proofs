(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefPrintfLib LibTail
  LazyRestrict LazySR LazyFdNodes LazySym Spec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite AsStdioCall AsScLib AsPrintfFirst.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsHdrErr () := KReplay.lz_vm "#%A&C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics?!s<22Fs4path!st,4Init5Logic8eq_ind_rC46Stdlib5Lists4!s+#6nth_okK!tU,Numbers7BinNums8positive01!sKG2I!tQ72eq00!s@29Datatypes4list00K!sFA1!sf<6option!sh/!to31Z02K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr01C13~~~!smc2!smi3!sm&!v3;3nat!uj_6kentry05!t}c!so'6!sok7!sok4!soc5sadd!y/Y2As;AsStdioCall9s!s0#_res!st+!{TC!{v=4prod!|^?!sF$1!}`83an!sa5!}{,1K!s[<1C!zI<fstC!{U]s_pc!v2%!t0=sndC!wE^:!wE%call!t8&!ss^6sc_ret!soe4sc_f!sme5!sm#d!t]is!smil!{J3!#7V53!#8^A!#52e!|y&I!#71a0!smc!t^'!so'!v5?0!#<tF3!tZ]8sideco!~d#!uMV!#5,<0!xaF1K!#@~95Riscv5Instr5aluop!#483!#;@11!ux]9sym_state!xHe7script!uu+c!vkR8AsHdrErr5hs_rA!y63!|#3bool00!t3`cA!txb6hs_sr!slgknA!vTfsc!wAgC!skfc!skeo_rA!skf!xSfo!xSho!xSho!xSgo!xSgo!xS+!#5?=N02I45stdpp9bitvector;definitions2bv00C!sI@DZ_to_bv_obliga!s:#_1!#DbC2!s{A7!s{&C7!#5FNPropExec3rdn!ur'!uTC1!t1/!t&96images4Asan1M?loaded_segment!#?n&!twO4Spec9msg_short!sh[;!sh#overru!ue&I!#:$?0!t1P6SymAux7sregio!t/&!#Fv+!#Th$7!s+#Def3map!#UI76!#UI$!#HC\5s_log!vAV!u6&;log_c!vD#ed!{v3!#:S71!}'\9h_!vJ%s!t}ZRun7vals_ev!w5'!z}?;bv_unsignedC5!#YH%6ZArith6BinInt1Z2le!sB<3opp!sC=ad!s|=3sub!#HIR=AsPrintfFirst3ENV!u[&!y2\6a_base!smdedenot!smc5a_off!zh]6r!tU[!v{46ASP_LO!~s&!}2^!#VT#!#D`b;!{~+_w!{>'!#a642In!#`@8o!tP#!tJO=!u:'Sound4SX2S4fla!vx'!{:<pow!|U>t!sB<>pow_pos_nonneg!sN<:!sN#!sJ%K!uw'9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PE!#a:#!sIE1!sIE6!sIE3!sIE7K!uPL1C!sQ55Tauto8B!sJ&!sH6:Z!sp+=Z!sT$CheckerC!w7<4find!sqAC!sq0_s!z3#!xN@1!~|W<!|Q'!{0,K!uz<G!vF'4!sJF5!sJF8!w6<5eKind!#Oo<unit!zG8!se%4kind!yy8!xh13Op2!#Z#>!t5$1!#64eHI!#B%7!#4:$5False!#mW3!sC%4True!}U8!yC-;!~r%!tj$!v58!um65C!#W3?7Prelude5bv!#Bd4!#HH,length!#6Hb7regs_ok!#:EU!st7know!st,!#skI5State5m_fds!sZQ9fd_lookupK!s^P7FdE!#`7$!s^K3Run6config01I!~OPLazySR4lzok!#<j&!#38O<!sg#Restrict8r!s/&!soV!#Mg'7seg_rom!sjWSymDrive9junk_val!#GD&!#Kr;app!t1P5Frame9f!s+#_mod!vQcEs!so#but_materialize!s|W!x8&8hid_!sz#!#A3<9nth_error!t/P9!v{'X8!|W$nth!}Ni9!#g-$!}P,!#@b:6of_na!#AR34Znat5Nat2Z7inj_iff!#P,77iff_sym!sf>9is!#Ak<!#:F23!#E{[>!#E{+!#<P+!st\?!st,!#IK,!#3zP5event02!|}RhapeAlg6t_emi!tG'!#Iy[!#hQ,1!yqV!#Jm0carry!z_jsc!vy0!svc8sc!wp1!#X686Forall!#?PQ!#P|0s!y1#s!u}jmem!u}plog!{f-!#F#VA!#Yg,_!#7:#!srV!#9+'8blob!#X_-!#3K6f_equal!$3:;trans!tNP7StepTac6u_Z2bv!|Tc3env!|NX!#|/5wb!snjp!vq>8iff_refl!#In5;ZifyClasses5mkrel!#OAD4!snB;rew_!tB%v!sQB3inj!#G7@3Sem5alu64!#@|X5v_ad!#>-V7LibTail7vadd_wZ!{_W!#BQ'alu!tU,K!#Xh:1!xucsp!ttV!#?^-img_!#k6'!#BS\I!#BS7!#IX#!t$$!#~;R<Ref!u_$Defs7s!#Z?#t!#GuW!#E5$7outside!wV'!zb4!#U6+3!#Q=`A!t{&_!#FO2!xr13Nat!#ez#!x#Y@!#H]'_!#P#%!t3&!#Es4:!sG%_ap!#lR3Peano2lt!tSZ=!#id%!t%#_l!#5-hsr!snikn!yB\D!x$+!#9q$!#Is-!|/\K!|/9!#:z$!t&U!#Kb%>!#Kb&!so0!z~`>rz_run_lf_lazy!wTe7sc_bufp!spe8!sp%sz!sqeE!$<W+!#a%$!}j$!wOV!#wq#1W!s`V!#8z'4mk!tI'I!#BDP!#JK%8re!ye$!$2<'!#<rA7!#=E%!#G+\8sym_exec!t>H5mk!#4'#!sK@6!sK$2!#@^73not!#PME7I!#N`I>!#?O#!sE+=machine!$6k'!xoQcfg=hunspe!yc#cf!#{5%!$++\FUELH!skb6STOPSH!~pg4scr!#sKb=!$%e'_le!#7A&!#V4<6inj_lt!t=\4h!#9?'!sj_k!$&w'!#UPOModel!y]R!~'+4TS!$I&&I!#ckX0I!#WOV0!$6<]s_srF!zoc!$<W#!slc<hs_itinera!#WR&!$G5]s!$G5/!tc\7hs_cov!$9V%!#mLH!#uy68ZifyInst7Inj_Z_Z!}Egimg!uUi!$:Sb?!$4~,!#3'+!yf^o!zTho!zTho!zT3!w4^o!yc-!w4i!xrgo!xr-I!#K-8e00!#Lt6sub!#>ZA9and_morph!#i@;8max_spec!|mD5Psatz!$%q7!sO8!$%T6!#xa:!$&n>3Pol!#{qE!tD&4!$kW,!u|&?Rel!$B?#!s6&=eq_Tran!$Sr$!$=2;n!$kU-!sr'9M!vl#isms:re!vU#tful!tAE<eq_Reflex!t@0!s|5Jr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^??eq!tM#per!tT;!sR,@!u$0per!#J+Yget!#Rb&!t<>M!#QQ$co_!$BA#v_impl!|2%ism!x{<seq!#?}Q!#UC%;nth_map_!sh#!tl&!#Vj4=app_nth2_plus!#J~\2!#gX&!#7_]!#zK-!$8C;max!#JwE6!sg+5!sf$8!#5##Na!#4n+!#FI<;inj_sub_max!sM>8!sM%cc!#G<Ce!#4>M1i!v^[3hfH!#P]'!#y5;modulo!#W`P!$Fh$6stk!$,^X!#Kf38cells!$,]S!#Ok1@word_to_le_byte!#n0Req!z|#9!}t#_zero!|32!wr,9SatDivModCZ!#\S#!#{e$!$>}&!v%`>!$1U%_by_idx!|Rb9h_ev_jun!vx&!#i=7!$5N$!$6za9all!u1#32!u%b5HF_FR!skb8hf_!yj$!x2&!#7nW9u64_range!{Jhkn!ta\!#f/+;!$6n%!#g2#!soU!}q&<kalign_int!{M+!smX!v<$!smc=kwr_of_!#3V/!snV:!#oq#!t[b;k!#3L#!sl/!#4<X8store!uG#!z;PAgentLib7!z;#li!$P\Y;RefExitBase=!tW'_data!svV!$$556esta!$^7'!#?,57f!$'-#!$Vba:!#8f$!{Z#!t9'!#4n55proj2!$+`B2!#56a!tY#_wf_!#~<%i!#@e\fP!#u`,!#8%^!$CP/!so_!$CK0!znO!#p~$B!#p~+!{\+!sr$k!vDc1!uSb8hs!#m4$!~p]7reg_va!#utV!#\z1r_ge!$CMW!#8M&5kread!}+2!#kS9eq!#m7#!t6X9!t6$!$#<,!uk]a!$53-!#;:Y!sj%_lit0!x}do!x}/".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nilhc3nat37Corelib4Init7Decimalke2D0ke2D8ke3Nil37Corelib4Init3Natn4bof_num_uint37Corelib4Init6Numberp4bUIntDecimalhc4prodhc4pair79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~s56kentrys54EVars52SA89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsHdrErr4FPX1~~~~~~hh95HF_FRs54ELits54KImgs53KWrhc3apphh98hf_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~hob6ASP_HIhob6ASP_LOhob8kn_cellss56KAligns56KRanges55KWord46Stdlib6ZArith6BinInt1Zih63opp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsbAsStdioCall~~~~~~ij59stdio_resij54SCR_s54exprs58sidecondhc3fst37Corelib4Init5Logiciq32eqs59sym_stateiq33andhh95hs_schc3snds57scriptshc4boolhh95hs_rAhh95hs_rCs54s_pchc4Somehc6optionhh95hs_cAhh95hs_cChh96hs_knAhh96hs_srAij54sc_fij55sc_fdij54sc_lij56sc_retij54sc_sij5astdio_callhh95ho_schh95ho_rAhh95ho_rChh95ho_cAhh95ho_cChh96ho_knAhh96ho_srA04Npos35stdpp9bitvectorbdefinitionsjrf2bvhc4None69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ju93rdn69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~kib9msg_short69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~kmffloaded_segmentsjrf7Z_to_bvkibbmsg_overrunhc6length69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~kta7sregions55saddrhc4truehh99h_regionsktablog_covereds55s_log79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsHdrErr~~~~~~ll15HF_FRih63subjrfbbv_unsigned37Corelib5Lists7ListDeflqe3map89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsHdrErr5Sound~~~~~~lscbh_regions_wll19h_regionshob3ENVkta6rdenot69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~mjd7vals_evih62lektacregions_flat3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsmp7dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runmtf5mkCfg3h5LinuxProcessSemantics5Riscv7Preludenh45bvmap3h5LinuxProcessSemanticsfLinuxProcessSem5Statenk37FdEntrynk35Model69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~no58restrict69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6LazySR~~~~~~nt04lzokju94mkstju97seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~oi4dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~omc8realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~or39junk_vals79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~ovb7know_okovb7regs_oknk39FdChannelnk35eventnk39fd_lookupnk35m_fdsll14h_knll14h_srll16hs_knFll16hs_srF69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~pq69frame_modno5h5same_but_materializednt08hid_sameomc4TSetomc6t_emitkib1Wll16ho_knFll16ho_srFn43sub37Corelib4Init5Peanoqk22leqk22lt89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsHdrErr5Plain~~~~~~qm26h_valsju94getrs52evih66of_natqm23hfHqm26hfPost" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition HF_FR : Z := 2400%Z.
Definition STOPSH : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0+hprtu8@3$1$0+rurh4@1$2$0").
Definition FUELH : nat := 8000.

(* [comment removed for export] *)
Definition h_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
Definition hf_cells : ltac2:(zQ "40!r7!h9!j4!k8@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "60!h9!r7!k8!re!jb!k2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrnjv0N8+hpspi8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgij8N8+nvvvogg0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hsgvh8N1+1@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvg8N4+5@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvi8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvl0N8+hprtu8@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvm0N8+nhkrv0@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvm8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvo0N4+2@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp0N4Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+hrpvp4N4+vvvvvvvf@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvsms8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvsmt0N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvqtr8N8Z@3$4@2$1@2$1$0$2$0@4$3@2$1$0$2$0@4$3$0$2+nvvvqts0N8Z@1$5@2$1@2$1$0$2$0").

Definition h_kn : ltac2:(zQ "20!j4!hg4@1$0$1") := ltac2:(zQ "h20!hg4!jb!hgd!hh4!hlc!hm5!hmc!hn3!hn9!k2!hnf!htc!hu6!hv0!hvc!ig5!ige!iie@3$8$0@3$1$0@2$e@1$2N0+h0@3$1$0@3$f@1$2N0$c$b@3$1$0@2$7@2$3@1$2N0@1$h1$4$4@3$1$0@2$6+hggg0+mngg0@3$1$0@2$6+hqtgg0+hrngg0@3$1$0@3$h0@2$3@1$5Z+nhkkh8N8@1$2N1@3$1$0@2$7@2$3@1$5Z+hrpvg8+u8@1$9$0@1$d$a").

Definition sc_dummy : ltac2:(zQ "10!in6$0") := ltac2:(zQ "50!hm5!k2!io3!iob!hg4@c$2ZZZ@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$1$3@1$1$4").

(* [comment removed for export] *)
Definition hs_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x0bead8 h_sr [] h_kn 34) []).
Definition hs_cA := Eval vm_compute in (carry (s_log (fst (fst hs_rA))) h_kn []).
Definition hs_srA : list expr := Eval vm_compute in (s_regs (fst (fst hs_rA))).
Definition hs_knA : list kentry := Eval vm_compute in (fst (fst hs_cA)).
Definition hs_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 hs_srA hs_knA with Some r => r | None => sc_dummy end).
Definition hs_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x19c9b0 (sc_sr hs_sc) [] (sc_kn hs_sc) 66) []).
Definition hs_cC := Eval vm_compute in (carry (s_log (fst (fst hs_rC))) (sc_kn hs_sc) []).
Definition hs_srF : list expr := Eval vm_compute in (s_regs (fst (fst hs_rC))).
Definition hs_knF : list kentry := Eval vm_compute in (fst (fst hs_cC)).

Lemma hs_itinerary : ltac2:(zQ "i10!h9!j4!r7!ip2!ipd!re!ir7!iob!ird!is9!it0!k2!it9!hg4!itf!iu9!iv0!iv9!in6!hm5!jg2!jg9!jh0!jh9!ji2!jib!jj5!jjf!jk7!jl0!jl8!jm2!jma@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h0+hprtu8@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h0@1$b$3@2$9@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$h7@1$b$3@2$9@3$6@1$h6$h2@3$i0Ni2$ha$h9@2$h5$h2$a@2$9@3$6@2$2@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0@1$he$a@1$hb$a@1$hc$a@1$hf$a@1$hd$a@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0+hpspr0+hrpvg8+2@1$h3+ijmna@1$h3+hf@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h1+rurh4@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h1@1$b$3@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$h8@1$b$3").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "##Ahp;1p;3p;2p;<p;4p-1R0p10000R1p4p710p9P0P!s2$2!s3/3110p9!sQ$Np4p7!s\$1>!sZ%R1p8!s6$\!s6%P1p8g0027j11Tg002\j10Tg003Aj3:!s/$[j1WTg004;j1V!s/$[j1cTg005=j1C!s/$[j1ETg006bj1<Tg007ij3eTg0090j12!s/$Oj2bTg00:Xj3aTg00;aj2[Tg00<jj2ZTg00>3j2KTg00?;l<mTg00@Ij2^!s/$kj2LTg00AKj4D!s/$kj2;Tg00BFj2R!s/$`j4FTg00C;j3I!s/$Xj1]Tg00D]j3TTg00E:j3lTg00FGj1kTg00GPj1jTg00HWj1iTg00I_j1hTg00Jfj1gTg00Kmj1XTg00LKj3>!s/$kj3QTf0R1#1#1p=4%0!s-$9%11#0p=7%1!s@$#1p=B%01#0#0#Cp==!sF$#0p=M!sX$#!sT$H!sH$p=?!sP'0p=3%C1#Ep=A!sX&#0p=6%01#Xp=f%21#2p=S!s-$#2#2p=Gg00N4R0f2R2#<f1R3#<=>013>p=@A>0319>02p=P%<3=>01p=\!t<&p=J!t|+!s$'p=O%01#Cp=d!tb+!s$'p=N%X1,K3p=`f3R4/K2?Q31p=Y!sQ%C!sA$_g00O;R5f4R6%C4'K?Q23;>1p=5f6f5;Q6AQ423=>515>5p=nA>5319>52p=U%X4,K6?Q!sF%p=8g00PDR1g00PbR3#1R2#0R6#0R4#4R7#9#4#7#B#9#=R8;:8g00QGR9#WR:%V9R9;:9R;g00RRR<#cR=%16R6#1R>#7#9#BR?#0R@#0RA#0R!sl%C%03RD#CRE%M7R7#7#9RF#1#H#=RG%12!tO$H#?RI#1#9#?RJ#7#4#B#3#ARKPKPKg00S`#ERL%0DRM#0RN#1RO!si$!t}%7#ARP%42R2#ARQg00T>g00TjRR#<RS%?ORO#6#f#E3eRT%2RRR#2#SRU#2RV#2RW#SRX#SRY#2RZ#2#G#GR[#2R\#2R]#2R^#2R_#2R`#2Ra#2Rb#2Rc#2Rd#2#GRe%EG%2e#GRf%2f!s''A3R3%GfRf#<!s<-!s'7ECRg%2f#S!tF$!sE1%V03@3@9@cd9@ab9@_`9P335PQ3@3@3@5PQ7PQ'\3@9@VW7PT'\PL%1ARA#0#6PXPK!s5$#3!s1'@!wc'!s9,BRB!sQ$LPL%3B!s/&M?R?#7RB#JPU%42#ORT#1RW#1RV#1!wd$OR`!s0+_#1#O#O#APS%0!w3$PXP3PS%3O!s/&0NRO#1Rb#1Ra#1Rd!sH$gPS%3dPXPPPS%0aRa!s<$QPS%3aPXPSPS%9b#6PX%?2!xZ$?#4#?#APSPIPX%<^PS%04R4#0PX%<]PS%1DRD#JPX%<\!tY%\PX%<[PSP4PX%<ZPSPOPX%<YPSPNPX%BD#9#9#6!yZ$dRN#E%CO,bS%0T!uQ$7#3#N#N#=%C_5aS%1M#H#3RM,`S%CM'[%N\#=%J7#3#='Z%H6#7!sT$9>#4#?R>#J!s@%PL%0J!st$4#=PX%<RCY1KLCRJ%1H#='[PL%1>!t?$=PX%?F#7#6#ACYPL%JIRI#?#6#4!v%$0WRW#?!tf$APL%BI#?#9#6PRP3PJPU%AD%MA,_LPX%E8PL%7@R@!x[+6@!xN&0?#3PU%EEPL%MBPU%A`PL%JV#4#HRV!yS&LPL%1V!sc$!s1$W#H#4RW#0!tY%!y?%W!sF%%V5D!s$2FnD5D53U!s$%D8!s$>!s\-M<m,^<RL;:LRX1L11RW/L1RV/L0R`/L0RUP`P0PVP0PWP1!s$$GPCCDPECDPPCDPQCDRQ;:QRPA:1NNRE1;;;RC';RG';RB';R?,;;R@';1R18P;P@1R:9R@P;P?P@PXPB1R=LPPPG1RUQPEPC1R1NP;P;P@P@CF!s$/g00UIR@1L@:R;g00VURCg00W_3IRE7I:#]=:18AT@:E=::9%W5R51L5:REg00Xd#WR8g00YD3I7T:=::9g00ZIg00[O5leg00\URe,^<5:=!ul3%ke%jeCD%ieCD%heCD%geCD=:UQg00]Z9I;CRC9I@!tS%NAT@:C!t1&^_9IE89T5!tB$';!s$/do"). Qed.

(* [comment removed for export] *)
Definition ho_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x0beaf4 h_sr [] h_kn 34) []).
Definition ho_cA := Eval vm_compute in (carry (s_log (fst (fst ho_rA))) h_kn []).
Definition ho_srA : list expr := Eval vm_compute in (s_regs (fst (fst ho_rA))).
Definition ho_knA : list kentry := Eval vm_compute in (fst (fst ho_cA)).
Definition ho_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 ho_srA ho_knA with Some r => r | None => sc_dummy end).
Definition ho_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x19c9b0 (sc_sr ho_sc) [] (sc_kn ho_sc) 66) []).
Definition ho_cC := Eval vm_compute in (carry (s_log (fst (fst ho_rC))) (sc_kn ho_sc) []).
Definition ho_srF : list expr := Eval vm_compute in (s_regs (fst (fst ho_rC))).
Definition ho_knF : list kentry := Eval vm_compute in (fst (fst ho_cC)).

Lemma ho_itinerary : ltac2:(zQ "i10!h9!j4!r7!ip2!ipd!re!ir7!iob!ird!is9!jn8!k2!it9!hg4!itf!iu9!jo1!joa!in6!hm5!jg2!jg9!jh0!jp3!jpc!jq5!jqf!jjf!jk7!jl0!jl8!jm2!jma@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h0+hprtu8@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h0@1$b$3@2$9@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$h7@1$b$3@2$9@3$6@1$h6$h2@3$i0Ni2$ha$h9@2$h5$h2$a@2$9@3$6@2$2@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0@1$he$a@1$hb$a@1$hc$a@1$hf$a@1$hd$a@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0+hpspr0+hrpvg8+2@1$h3+hmtud@1$h3+hf@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h1+rurh4@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h1@1$b$3@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$h8@1$b$3").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "##@ip;1p;3p;2p;<p;4g0027j11Tg002\j10Tg003Aj3:!s/$[j1WTg004;j1V!s/$[j1cTg005=j1B!s/$[j1ETg006bj1<Tg007ij3eTg0090j12!s/$Oj2bTg00:Xj3aTg00;aj2[Tg00<jj2ZTg00>3j2HTg00?;l<mTg00@Ij2^!s/$kj2LTg00AKj4D!s/$kj2;Tg00BFj2R!s/$`j4FTg00C;j3I!s/$Xj1]Tg00D]j3TTg00E:j3lTg00FGj1kTg00GPj1jTg00HWj1iTg00I_j1hTg00Jfj1gTg00Kmj1XTg00LKj3>!s/$kj3QTf0R0#1#1p=3%00#1p=7%10#0p=8%1!s@$#1p=C%00#0#0#Bp==!sF$#0p=K!sX$#1#0p=M!sH$p=A!sP'0p=4%B0#Ep=@!sX&#0p=6%00#Xp=f%20#2p=S!s-$#2#2p=Gg00N4R1f2R2#<f1R3#<=>103>p=?A>1309>12p=P%<3=>10p=\!t<&p=J!t|+!s$'p=O%0!u$$d!tb+!s$'p=N%X0,H3p=`f3R4/H2?Q30p=Y!sQ%B!sA$_g00O;R5f4R6%B4'H?Q23;>0p=5f6f5;Q6AQ423=>505>5p=nA>5309>52p=U%X4,H6?Q!sF%p=9g00PDR0g00PbR3#1R2#0R6#0R4#3R7#7#3#8#C#7#=R8;:8g00QGR9#WR:%V9R9;:9R;g00RRR<#cR=%16R6#1R>#8#7#CR?#0R@#0RA#0RB!sl$C%03RD#BRE%K7R7#8#7RF#1#M#=RG%12!tO$H#ARI#1#7#ARJ#8#3#C#4#@RKPKPKg00S`#ERL%1DRM#1RN#0#3!ty&3#7#@RO%32R2#@RPg00T>g00TjRQ#<RR%0DRD#0RS#KRT#6#f#E3eRU%2QRQ#2#SRV#2RW#2RX#SRY#SRZ#2R[#2#G#GR\#2R]#2R^#2R_#2R`#2Ra#2Rb#2Rc#2Rd#2Re#2#GRf%EG%2f#GRg%2g!s''@3R3%GgRg#<!s<-!s'7ECRh%2g#S!tF$!sE1%V13?3?9?de9?bc9?`a9P335PP3?3?3?5PP7PP'\3?9?WX7PU'\PL%1ARA#0#6PYPK!s5$#4!s1'@!wi'!s9,BRB!sQ$LPL%4B!s/&K?R?#8RB#JPV%32#ORU#1RX#1RW#1!wj$ORa!s0+`#1#O#O#@PR%0TRT!sv$3PR%4T!s/&0SRT#1Rc#1Rb#1Re!sH$hPR%4ePYPOPR%0bRb!s<$PPR%4bPYPRPR%7c#6PY%A2#M#7#A#3#A#@PRPIPY%<_PR%04R4#0PY%<^PR%JMPY%<]!tU%]PY%<\PRP4PY%<[PRPTPY%<ZPRPSPY%1N!yX$7#6#8#8#dRN#E%BT,bR%0U!uO$8#4#N#N#=%B`5aR%1D#M#4RD,`R%BD'[%N]#=%J7#4#='Z%M6#8!sT$7>#3#AR>#J!s@%PL%0J!st$3#=PY%<QCY1HLCRJ%1H#='[PL%1>!t?$=PY%AF#8#6#@CYPL%JIRI#A#6#3!v#$0XRX#A!tf$@PL%CI#A#7#6PQP3PJPV%@M%KA,_LPY%E8PL%8@R@!xY+6@!xL&0?#4PV%EEPL%KBPV%@aPL%JW#3#MRW!yQ&LPL%1W!sc$!s1$X#M#3RX!}7$!sF'KX!sF%%V5D!s$2FnD5D53U!s$%D9!s$>!s\-M<m,^<RL;:LRY1L00RX/L0RW/L1Ra/L1RVPaP1PWP1PXP0!s$$GPCCDPECDPOCDPPCDRP;:PROA:0NNRE1;;;RC';RG';RB';R?,;;R@';1R08P;P@1R:9R@P;P?P@PYPB1R=LPOPG1RVPPEPC1R0NP;P;P@P@CF!s$/g00UIR@1L@:R;g00VURCg00_d3IRE7I:#]=:08AT@:E=::9%W5R51L5:REg00Xd#WR8g00`i3I7T:=::9g00ang00c45lfg00d:Rf,^<5:=!ul3%kf%jfCD%ifCD%hfCD%gfCD=:VPg00e?9I;CRC9I@!tS%NAT@:C!t1&fD9IE89T5!tB$';!s$/do"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma msg_short_img : ltac2:(zQ "b0!jr9!jtc!j4!ju2!jg9!jh0!ir7!ki4!km2!kq4!kr7@3$6@1$5@1$2@1$1@1$0#8@4$7$9\0@1$1@1$0#k0@1$3@1$1@1$0#8@2$a@1$0#k0+ijmnaNhf@2$4@1$2@1$1@1$0#8$8").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "##0Cp;1p;2p;4p;3g002\j11Tg00gIj1>!s/$gj1<Tg003[j1ATg004[j1HTg0027j10Tg005=j14Tg00hJj29!sJ$;j1@Tg00@Ij2?Tg00BFj2GTg00i=j1F!s/$_j2ETg0090j16Tg00jEj4C!t:$Aj3BTg00kEj3=Tg00LKj3;Tf0R0#1#4p=5f3R1f2R2f1R3/903=p=3%00#1p=8f4R4A=123;;0p=:A;2309;41p=2%60#6p=D!s-$#6#6p=7g00PbR0#1R4#1#1R1#>R3#<R2#AR5#HR6P2P3%0!tJ$R7#1R8#1R9#0#0#4R:193:!sG%7R7#0R:#1#5R;193;!s=$17!s\$0#4R;P3P;C3R!s?%80R0#8R<#4R=P3P=C3!sV%1#1R=#4R>P3P>C3R>P2P!sX%0:R:#5!sm21!v2%5R?P3P?!sk&0<#4R?193?!s5$5<R<P3P<C3R<P2P>!uG,0!sN17R7P3P7C3R7!t@&#4R:P3P:!t#&50R0P3P0C3R0P2P<!u@%8R8!v'%!sP%R:P2P0!t7&<P2P!ss%19!sK$9P3P9C3R9!uN&>!sG&:P2P9!t3%8R8P3P8!tB$!sr'3%04#5R41934%@2D:D2!s$4:D!s>,:D:,?5'Gg00kh%1=#>R=#<%F2U%01#8#0#8#1!x3$0!s4$5,E=g00Tj#6#D#7!s$/CCg00ln,?55B6do"). Qed.
Lemma msg_overrun_img : ltac2:(zQ "b0!jr9!jtc!j4!ju2!jg9!jh0!ir7!ki4!ks2!kq4!kr7@3$6@1$5@1$2@1$1@1$0#8@4$7$9\0@1$1@1$0#k0@1$3@1$1@1$0#8@2$a@1$0#k0+hmtudNhf@2$4@1$2@1$1@1$0#8$8").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "##0Xp;1p;2p;4p;3g002\j10Tg00gIj1@!s/$gj1=Tg003[j1BTg004[j1ITg0027j11Tg005=j1:Tg00hJj29!sJ$;j1ATg00@Ij2?Tg00BFj2HTg00i=j1G!s/$_j2FTg0090j16Tg00jEj4D!t:$Aj3CTg00kEj3>Tg00LKj3;Tf0R0#1#:p=4f3R1f2R2f1R3/903>p=2%00#:p=5%10#1p=8f4R4A>123;;0p=<A;2309;41p=3%60#6p=E!s-$#6#6p=7g00PbR0#0R4#0#0R1#@R3#=R2#BR5#IR6P2P3%10!sI$7#0R8#0#1#4R9P3P9C2R9!sG%7R7#1R:#0#5R;P3P;C2R;!sA$07#0#4R7P3P7C2R7!sw&#!uM$R<#0R=#:R>P3P>C2!sX%1!tW$!s;+R>P2P!t6&:R:!tK45:R:P3P:C2R:!sL%8R8#1R?#5R@193@P2P!tE%4?R?P3P?!t7&14R4!sN$8#4!sP+!u+&8#4R8P3P8C2R8P2P:P2P!tV-<#5R<P3P<!sq$8!sZ%!uI%8!sA,R<P2P<!tI%=!s;0!tw%48!t2'!t+&7!sA+00#5R0P3P0!sC$!sk%5=R=P3P=!u6&54R41934%A2D<D3!s$4<!s&&!s$$,?5'Hg00kh%01#@R1#=%G2U%0?#8#0#8!s+&0#4,F1g00Tj#6#E#7!s$/CDg00n0,?55C6do"). Qed.
Lemma msg_short_len : ltac2:(zQ "60!kt1!k8!ir7!jr9!km2!jtc@3$2$1@2$0@1$5@1$3#8$4Nhf").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "###up;1p;2g0090j11Tg00BFj22Tf0R0#1#1p=3%1!s0$#1p=0g00o4g00Tj#1#3#0!s$/'2o"). Qed.
Lemma msg_overrun_len : ltac2:(zQ "60!kt1!k8!ir7!jr9!ks2!jtc@3$2$1@2$0@1$5@1$3#8$4Nhf").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["FPX1"] "###up;1p;2g0090j11Tg00BFj22Tf0R0#1#1p=3%1!s0$#1p=0g00o4g00Tj#1#3#0!s$/'2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_regions : ltac2:(zQ "20!j4!lh3@1$0$1") := ltac2:(zQ "b0!h9!lhe!r7!jb!re!hlc!hh4!k2!hm5!hgd!iie@3$3@2$2$1$0@4$4$1$0@2$6@1$9N0@1$a$5$5@3$3@2$2$1$0@4$4$1$0@2$6@1$8Z+hrpvg8+u8@1$7@2$2$1$0").

Lemma hs_covA : ltac2:(zQ "d0!ipd!j4!ip2!ird!iu9!r7!li6!ir7!lid!iv0!lja!lk9!itf@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsHdrErr ()) ["FPX1"] "p;2p;1p;3p100oSp4p70R0p1010Up4p710p8P0p10111p4p710p8g00BFj26Tg003[j15Tg00@kj21Tg00C;j30Tg011Mj14Tg012Sj22Tg003Aj33Tg00XdR0g013YR1'6g0149g00UIR2g00QG#5R31123g00VUg00W_3030#4'2=301do"). Qed.
Lemma hs_covC : ltac2:(zQ "d0!ipd!j4!ip2!ird!iu9!r7!li6!ir7!lid!iv9!lja!lk9!itf@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsHdrErr ()) ["FPX1"] "p;2p;1p;3g00BFj26Tg003[j15Tg00@kj21Tg00C;j30Tg011Mj14Tg012Sj22Tg003Aj33Tg00XdR0g013YR1'6g0149g00UIR2g00QG#5R31123g00VUg00]Z3030#4'2=301do"). Qed.
Lemma ho_covA : ltac2:(zQ "d0!ipd!j4!ip2!ird!iu9!r7!li6!ir7!lid!jo1!lja!lk9!itf@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsHdrErr ()) ["FPX1"] "p;2p;1p;3g00BFj26Tg003[j15Tg00@kj21Tg00C;j30Tg011Mj14Tg012Sj22Tg003Aj33Tg00XdR0g013YR1'6g0149g00UIR2g00QG#5R31123g00VUg00_d3030#4'2=301do"). Qed.
Lemma ho_covC : ltac2:(zQ "d0!ipd!j4!ip2!ird!iu9!r7!li6!ir7!lid!joa!lja!lk9!itf@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_AsHdrErr ()) ["FPX1"] "p;2p;1p;3g00BFj26Tg003[j15Tg00@kj21Tg00C;j30Tg011Mj14Tg012Sj22Tg003Aj33Tg00XdR0g013YR1'6g0149g00UIR2g00QG#5R31123g00VUg00e?3030#4'2=301do"). Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variables (L S Zr : list (word * word)).

  Definition h_regions_w : ltac2:(zQ "50!j4!r7!jr9!h9!jtc@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "b0!jr9!h9!jtc!r7!jb!re!lof!kr7!k2!lp8!lpf@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$7@1$0#k0@2$9@2$a@1$0#k0?3sp0$6$6@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$7@1$0#k0+hrpvg8+u8@1$8@2$3@1$2@1$0#k0$1").

  Lemma h_regions_denot : ltac2:(zQ "h00!jr9!jtc!j4!r7!ir7!h9!ls5!mh0!mhf!hu6!mic!mj3!lh3!mn6!mo1!lpf>4vals@1$2@1$1@1$0#k0>0@3$4@1$1@1$0#k0@2$d^1N0?3sp0>0@2$e$9@2$f@1$0#k0?3sp0@3$4@1$2@2$3@1$1@1$0#k0$5@4$6$c@2$3@1$1@1$0#k0$5@1$b@1$a^3$8$7").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["Sound"] "##/Bh03Hloh12P0h21bh31rh44valsp;1p;2p;3p;4p;6g00gIj1OTg00ggj1KTg003[j1:Tg015Bj2@!s8$Aj37Tg016Dj26!s/$nj2JTg00@kj2<Tg0027j10!s/$\j12Tg005=j18Tg017Jj1A!s/$gj29Tg00i_j25Tg00AKj43Tg004;j1?Tg00LKj34Tg018Dj2NTg00BFj2MTg001>j6L!sA$aj1>Tg00C;j3ITg019ij1HTg01;0j2ETg01<7j1DTg00D]j3FTg006bj1GTg00>3j2=!tp$[j1CTg010Uj4;Tg01==j1BTf0R0#2#2p=1g00PbR1#1R2#1#1#OR3#KR4#:g00TjR5,@0p,3sp0R6574g01>>1636R7'JP4P6g00PDR6,<4R8#:R9P4P61630%02#2#0#0#!s}%8R2#AR:'9,53P2C3!sb&S`R;,53,63%01R1!sY&0#1!s-&!s2%1!sm&8R<!sg$%0!sP%!s:%1C3%?8R=548548!tO$N72!t6-153<P1C3=48=548R=37X241M9=f2R7/@5f1ELg00oSR>P!sg$f3#>g01?IR4?I60R?#H'E,63%D?!tO$AF460C3X3>1<46R0P4P6%G5/=:!tB'%C;/=!tD$%?054034C;=79=eP>P8%>7#Bg0149C;g01@Q579eW0W1W4o"). Qed.

  Lemma h_regions_flat : ltac2:(zQ "c0!jr9!mo1!jtc!lpf!j4!ir7!mhf!htc!hu6!mic!mo7!mn6>4vals@1$4@1$2@1$0#k0>0@3$5@1$2@1$0#k0@2$b^1N0?3sp0>0@2$1$8@2$3@1$0#k0?3sp0>0@2$1@2$3@1$0#k0?3sp0$7@2$a@1$9^4$6").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["Sound"] "##<kh01Hh11rh22Hah37__arithh44__ffh56__sat1h68__varmaph75__with84__x1h93Hhih:3Hloh;2Hrh<2P0h=!s_%0h>!s/%2h?1bh@4valsp;1p;2p;3p;4p;6p;7p;8g002\j11Tg00gIj1e!s/$gj1`Tg003[j1WTg015Bj2T!s8$Aj3JTg016Dj2C!s/$nj22Tg01A\j3aTg006bj1_Tg0027j10Tg005=j1;Tg017Jj1sTg00>3j2UTg00AKj4L!sJ$[j1lTg01B3R0j2NTg018aj1<!s:$Mj35!sg$gj23Tg01CXj2bTg01D5j27!s/$Qj2^Tg01E9j3]Tg004;j1\!s8$]j2[Tg01F;j1Z!s/$Yj1YTg01GDj2XTg00i=j1t!s8$gj2VTg01HJj2r!s/$mj3DTg01IPj3qTg01J3j4F!s/$^j2pTg00BFj2oTg01K@j2n!s/$lj3mTg01LKj4kTg001>j6iTg019ij1QTg01;0j2PTg01<7j1MTg0111j6OTg01M=j1h!s/$[j2gTg00C;j3jTg00D]j3f!v[$kj2GTg01Nbj7RTg01OFj7d!s/$jj8cTf0R1#!s$&p=4%01#0p=Eg00oSR2f1R3;J1p==%1!sG$H!sG$#0#0p=Ig01?IR4g00PDR5;j1p=:Af451p=9g00S`R6/21p=8f2R71G31'Gp=@1263/G1p=A!sr+!s$'p=B1V51p=?P7g01PNR8g01PmR9P9g01QMR:P5P3g01QmP1CFg01RTR;FRp=6P3P8P9P9P:P1P!s9$KP7!s9+3P1Fdp=>f3R;!s;+7P3P1Gcp=Sg00PbR8#1R<#1R=#4R>#eR?#`R@#Wg00TjRA,T1p,3sp0RB5J@g01>>1C?BRC'2g01S4,2Cg0149RD9a21P0P4P5%_A%0=#1#E#1#4#;R=#sRE'UP=CLRF/=3!sK$l6%08R4#1#0#E#H#0#I#4#0#1#H#;RG'U%04!sE&!s9%HCLRI/=3g01T?RJ'Nf6RK#<%:7%9735P11=F7P2PFf8RL#<RM%:1RN%91RO35X12P@PB1C?1/3ERB%;<R<%;>R>'bRP,7B%8=RQ13B=/2P3@'AX?@1^<>R@176<%8>176P[[RB%8<RRg01T\RSA]<>3UW2R>%8P\S^2R!sA$U8RS#\RT%WSRS1[53%Z5RU%Y5RV1X58R8%I4#BR4#B!s$&;RW#?56V%t9R9PV%14!v2$I#4!s$-;R4#?=6V8P91V56R9%?=RX,r59D58R856VP5P8g01UdRY%?<=q5?R<CF,KVA6V9XAD58X=6V<5>V!s%%CSCS1pV:R:P1P7g00Xd!z9$3YRX'o1n17=J8XdAm563CkRXb4b6b7X85121W1243137ERE17EP13E=/2P7@Q'A[[^85P1PCf7RCPLO3b3b5b>1TCAPKEi%<CRC%:FRA#Q'P,C?%MA'3RL17LP%9FRF#813LF!wM&eA5CAFeP;P1EOW0P1O11=I7/NJP01=I;PJf4R0#:%9055MP11=I0P2PIf:#<R0?5NO!xh&P>PRPTPS%h5PU%?G9D59RU96V9P5PUPYP!vI%%?HRY96V9AD5UY!vM0P:P!uy&136GRG17GP%8H13GH!t{&P1b3b=b5f9#<RG%:IRH!uZ+H'3R?17?P%9IRI#813?I!uZ,GHIef5RI!u\,PJ%:K%9K550P1n010!s#%X0JP1O1n20!s9'2110!s3&!s`%!sB51000%<I%:3%9335eW;X12%<;/gDeW9W:W<W@o"). Qed.

  (* [comment removed for export] *)
  Ltac hf_sound pcA rA cA srA knA sc rC cC srF knF ITIN COVA COVC MSG_IMG MSG_LEN msg :=
    (* LPS 75d69e00: + Hrd2, the channel-reader premise, immediately after Hfd2 *)
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
    (* LPS 75d69e00: the reader fact, transported the same way the fds fact is *)
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
      eapply (rz_run_lf_lazy RSEGS L S Zr FUELH STOPSH scr0 0x19c9b0 (sc_sr sc) (sc_kn sc) 66 (fst (fst rC)) (snd (fst rC)) (snd rC)
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

  (* LPS 75d69e00: + [m_channel_reader mo = true] after the fd_lookup premise.  The replayed
     Qed proof was one argument short once stdio_call_sound_post gained it; the
     TACTIC was already plain text here ([Ltac hf_sound] above), so the repair is one intro and
     one bullet there plus this statement written out, not a decode-to-source.
     Statement: this file's own [About] output with that one line added. *)
  Theorem hs_sound : forall vals R M msF mo (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0xbead8) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) hs_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' hs_knF ->
       frame_mod M M' h_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0xbeb14) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_short) K).
Proof.
    unfold W.
    hf_sound 0xbead8%Z hs_rA hs_cA hs_srA hs_knA hs_sc hs_rC hs_cC hs_srF hs_knF
             hs_itinerary hs_covA hs_covC msg_short_img msg_short_len msg_short.
Qed.

  (* LPS 75d69e00: + [m_channel_reader mo = true] after the fd_lookup premise.  The replayed
     Qed proof was one argument short once stdio_call_sound_post gained it; the
     TACTIC was already plain text here ([Ltac hf_sound] above), so the repair is one intro and
     one bullet there plus this statement written out, not a decode-to-source.
     Statement: this file's own [About] output with that one line added. *)
  Theorem ho_sound : forall vals R M msF mo (K : TSet),
    length vals = 34%nat -> vals_ev vals 0 = sp0 ->
    regs_ok (ENV vals) h_sr R -> know_ok RSEGS (ENV vals) M h_kn ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0xbeaf4) M (seg_rom RSEGS) ->
    K [] ->
    (forall Rj R' M' msF' mo',
       regs_ok (ENV (vals ++ junk_vals Rj)) ho_srF R' ->
       know_ok RSEGS (ENV (vals ++ junk_vals Rj)) M' ho_knF ->
       frame_mod M M' h_regions_w ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst R' (Z_to_bv 64 0xbeb14) M' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
Proof.
    unfold W.
    hf_sound 0xbeaf4%Z ho_rA ho_cA ho_srA ho_knA ho_sc ho_rC ho_cC ho_srF ho_knF
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
    Hgot  : forall i, (0x1ad000 <= i < 0x1b7000)%Z -> mem (Z_to_bv 64 i) = None;
    Hcells : cells_ok mem hf_cells;
    Hcan  : rdn RSEGS mem (Z_to_bv 64 0x714418) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Hcan64 : (0 <= can < 2 ^ 64)%Z }.

  (* [comment removed for export] *)
  Record hfPost (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := HFP {
    P_sp  : getr regs' 2 = sp;
    P_a0  : getr regs' 10 = Z_to_bv 64 1;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - HF_FR), HF_FR); (Z_to_bv 64 0x1b9f08, 232%Z)];
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0x1b9f08) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0x1b9f10) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0x1b9f18) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0x1b9f28) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x714bf0));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0x1b9f30) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x714bf0));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0x1b9f40) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x714bf0));
    P_mode  : rdn RSEGS mem' (Z_to_bv 64 0x1b9f90) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0x1b9f94) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0x714418) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp HF_FR }.

  Definition h_vals : ltac2:(zQ "50!jr9!jtc!j4!h9!nja>4regs@2$4@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3can$3@1$2@1$1@1$0#k0") := ltac2:(zQ "90!jr9!jtc!jb!hn9!k2!h9!nja!oue!kr7\4regs@2$6@1$0#5@1$1@1$0#k0\2sp@1$1@1$0#k0\3can$5@3$3@1$1@1$0#k0@3$2@1$1@1$0#k0^2@3$2@1$1@1$0#k0@2$8@1$0#k0^1@1$4@1$1@1$0#k0@1$7^3").

  Lemma h_ev_junk : ltac2:(zQ "h00!jr9!jtc!k8!is9!ir7!qjc!ql6!qlc!h9!nja!qq6!mic!qr0!qr8!qrd!kr7>4regs@2$9@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3can$8>1i$2>0@2$3@2$6N2^1@2$7^1Ni2@3$4@1$1@1$0#k0@2$d@1$b@3$a^5^4^3^2@2$c^5@2$f@1$0#5@1$e@2$5^2N2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["Plain"] "##Iih04__p1h14__p2h24__x1h34__x2h42H0h53Hi0h67__arithh74__ffh84__p3h98__varmaph:5__with;4cstrh<1ih=1nh>1xh?2z0h@1HhA2HihB1bhC3canhD7defaulthE1lhF5lemmahG1mhH4regshI2sphJ1yp&0p;1p;2p;3p;<p;6p;4p;=p;9p;5p;Bp;7p;8g002\j1<Tg0027j1lTg00gIj1O!s/$gj1`Tg01VKk20ITg0090R0j12Tg03B=R1j2WTg02PUR2j2!sG$Akj20!sE$Wj2[Tg003Aj31j1JTg01hMR3j13Tg005=j1KTg018Dj27Tg017gj2A!sL$mk20;Tg01iPk305Tg00BFj2;Tg02@Fl<PTg016nR4j26Tg01D5R5j24!tE$nj6dTg02`=j4g!sj$mj1jTg03CWj2kTg01B3j2HTg03D9j2F!s/$bj3GTg03EKj2LTg00Kmj1mTg03F7k20!sT$FXk30GTg004;j1]Tg00LKj3!tm$3[j1\Tg01E]k20FTg01M=k10ETg02L]k40DTg01F;k10C!s0$Yk10>Tg01GDj2i!s/$gj2C!uY$kk30=Tg01J3j4@Tg00i=k10<Tg01Hmj3e!sB$^k20:Tg01K@k20!va$Klk304Tg01LKk402Tg02ANj4_!sj$_j28Tg01W7j2VTg02NQj2TTg03GAk100Tg01`Zj1UTg01a`j3NTg03H1j4?j1z!s2$Mj4QTg03I4j1~!s/$cj4RTg03JZj3{Tg03KPj1yTg03L?j6}!s/$jj2MTg03MVl=xTg03NCj2DTg03ODm901Tg03P>j2wTg010Uj4v!s8$Zk60!yB$1>j6^Tg03Qbj5uTg015Bk206j1tTg029Pk108Tg02<Rk209Tg03RDj2hTg03SGj3s!y~$aj1rTg03TMj2qTg02bRmB0?Tg02amm<0@Tg01jRj6pTg01Nbk70!zM$OFk70B!s`$jj7o!s9$jj8nTf0R6#2!s$%p=9%26#2p=|g00S`R7/q6p==g00PDR8f1R9;16p=>g00o4R:P:P:P8P8P8g03UNP3P3P3f6R;g03Unf5R<f4R=f3R>f2R?P9P6NB0?p=b!s_+0!sZ$>g03VUP!sH%<0@p=a!sF$1P3P4g03W9P<P=P>!sH%M<Pp=c!sG$2P3P5g02jc!sG4SA1867p=ZP9g01PNR5g01PmR2P2g01QMR4P6Epp=YP8P9g036ZP6C@p=XP9P5P2P2P4P6g01RTK0Ap=:P?!s=+9P6K0Bp=B!s:1Fop=fP>!s9+!tZ$Gnp=Eg00PbR5#<R1#l#OR0%<1#<R@#<#<RA#<#ORB#`RC+0Ig00TjRD#2RE#2RF/W6%2FRG#2#9!s$/RH#|RI,I6'01[9FRJ#2RK#2RL=1:9%39RM%K1RN'7#=RO%K5RP'ARQ/APRR/>MP:P8%J:RSP3%J8%36R3,>MA1:9620;96405XJ:X>:PLPR1A6PX>8RRPKPQPRPJPO1796#=XG8X=8ROP9PM1;8MRRPFPN1;8NRQFbCaCaP9PMPRM<P1WF9RK1I9IRL'016NMRT%l@#<#KRU,4MRV'0RWPKPLPTPVPFPNPQ!sc%Ec!s-%PIPU1;8URRESEdP6CgPW%j?%3?RW,67%3>RM/7NRV,k7147V%=VRT/>V'016V7%ZT'0'H%3=/7NRT#=RVP8p-0RLg01U8RK1F8FRX1F8E1F8DRE5G85G8g03W[RY'LRZ1F8G%m5-0H8>0G8X=G8E!sM$/LY1LEY%]KRE55K55K35%\KRYP820F8?P9&0E8H0DRX&0C8RG&0>8R[1Y[=1i85R51i81R11C8NR\60=8R]'X,:[5B[R^P8P]g01QmR]1C87R_C@,:[1X5_,:[R_5B[5f[&0<2R2P[P8P\P]P1!sJ%Y[<R]5B[P21C8PR\9e85=e8\/X1,:[CECE20:[4R4P6P?g00XdR\g013YR`';2076?=1\`dB04879H02R`b7b9b:X28X38X0LW1179NR\,>6,0?Ra16\7%Z6R\'0'H16N?/0=1A?P/AP/>>[[^28^38^0L^1LP6%3;RP/4U17PN,47PPP9P?P=O6b6b?b4b;b5C_18B?%]CRP55C95C>Rb,VC/TJ=1:9RcePc18B>=5CP95C=Rc,VC1[?FRd'TRe=1:?PC%JCRf&00CPCP>18B=!sT&<RP%U;5NCRg18B7RBC?PC1VCP1[>FRP'TRhPgPBC?%\CRiPC^DCRj]ERk^=:RlP:PkPSPiPj%JiPCPCPfPfCQRmCQRnCQRo!sG$nPiPjPm!sF%%~CCRCRCR9{lo%zCP>PhP:PS%y:PhP>P6E}PgPg1MigPBPB1MCBM=x%3P,80,D;RPPP1MCPN901WFP6!s{$d%U<RiPBC?RgA1C6PXBCRPPC%3d!s\$<RhPP1;ChPCPdP:PC1803,D;X<:R31wDHCvP!uo$P3PdPHPB1IdH17WN#=R3%KARA'4PdP3POP?PW1;8WRO!}R%FbPHPA1;8AES1WF?RH1I?IR3!~:$WRD14WURP'0RSPHP3PDPP!~2&?PWPOEc!s-%PIPUP!~-%9CgPS%j>167M1k7T147T1>VT'016T7%ZV!}u%</7N#=P8A5KZEPYPXPGP[AB[]_9f[^P2P[1Y[;P8P1g01Ud!|e$U!{v$!{p$P8P5P11C8A!s:$CECEP4P!{?3X1LX8L10>\,Ha14?U,0<14?A!{%1^8LP6f7#3R6,6N176NRN/67147NP6!{3&7!{3/J03E^A1CghePCPeANCci!wE&cPiPBPdDuE^O2b@%U=9NCbRb0069%3J!x;$=R051Ce%tb%O@#`#\#]$08+09/h9=1C0eAs=>?#r!s5'WAX<:XC8XICWHo"). Qed.

  Lemma h_regs_ok : ltac2:(zQ "a0!jr9!jtc!jh0!h9!nja!qq6!qs7!poa!mic!pkb>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2sp@1$1@1$0#k0>3can$3>0@4$6^4^3^2^1@3$9@1$8@3$5^5^3^2$7^5").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["Plain"] "#$Wap'0h02Hih17__arithh24__ffh38__varmaph45__with51ni001nh61bh71ih82Hah94__p1h:4__x1h;2H3h<5Hcan0h=6Hcan65h>7Hcells0h?5Hgot0h@3Hi0hA5Himg0hB5Hsp17hC6HspHi0hD6HspLo0hE5Hstk0hF2PHhG7__sat66hH!s0&7hI!s0&8hJ3canhK4cstrhL3memhM4regshN2sphO1xi012H2i024Hcani03!tn%4i046!to%i054Hgoti064Himgi07!ti$6i085!tj$i095!tj$i0:4Hstkp%0p&0p;1p;2p;4p;3p;6p;<p;7p;5p;8g002\j1FTg0027j1ETg00gIj1[!s/$gj1_Tg01VKk20BTg004[j1jTg03XGR0k405Tg01WWj3xTg005=j1<Tg016Dj2RTg03YLj2kTg003Aj3J!sA$nR1j24!sC$lk40@Tg01D5R2j23Tg00Akj22Tg00i_j2U!s/$=j1eTg03Zmj2w!ss$[j1fTg0090R3j10Tg00jEj4tTg03\:j2rTg00@Ij2qTg01CXj2nTg02PUR4j21Tg00kEj3Z!u&$[j1mTg03]Bj1lTg03H1j4QTg03SGj3`Tg03B=R5j2?!s1$nj6!v$%;k10?Tg01M=k10>Tg01F;k10!uw$FYk10;Tg01J^k207Tg00BFj2^Tg01K@k206!s0$lk304Tg01LKk403Tg03RDj2hTg01hMR6j1VTg017gj2TTg02`=k402Tg01imk101Tg03^Gk200!ve$Qj2~Tg01E9j3}!s/$]j2{Tg02L]j4dTg01Ggj2c!s/$Dj2yTg01jRj6|Tg03_8j4uTg018aj1\Tg03NCj2PTg01;0j2]!uv$Wj2sTg02@Fl<i!uW$3j4YTg01Nbj7WTg01OFk708Tg02ANk409Tg03`Kk50:Tg001>j6oTg02aml<bTg01Hmj3X!s_$jk80=Tf2R7f1R8f0R93`#\p=9g03aTR:9Z89p=pf3R;1P78;J9p=a%F9#F#F#Fp=K%F9#<p=I%E9#Fp=O!sB$p=Sg00S`R</49p=Lf4R=?`;7#\g00N4R>P8g02kER?P9CQ']p=7f5R@P;P7g03b0RAP8CQ,P=!t>$61P;7%\8/]95J=p>0A1s89#V,U7,P;p=AAZ78:,P;=J=9p=Dg00PDRB/^9p=8g00o4RCPBP5P6P1g03W9P@P=P;P7P8P9M<ip=CPCPBP4P6P2g02jc!sG4:1cB9p=5f6R2g01PNR4g01PmR1P1g01QMR5P@P4P1P1P5PBP=g01QmRDP;CYg01RTREFWP7!sH-8g01UdRFP9CYPEFWK08p=>f7RGP2!tM/H09I0:p=@P!s?$1^=;1h78P9Eop==!sP$AP;CQ,P2P>P8P!vp$,]75JGp=;1T=;/T7/T8/T9p=GP!u`%BP3P6!ud%3VURH!sm$!sA1;PH!uv'bM<bp=H!u51PD!u0'p=zAXB=;=XB7=XB8=XB9p=M!sU2!u_+p=vP;!sA+!t1$L0=p=g%09#0#0#0p=Ng00PbRE#FRF#ERD#[RH%FFS00#FR6#FS01#FS02#FR3#[RI#_RJ+0B%[6#_RK#jRL\J!v_,5P0!vn'A9@;7?x?@P9PJf>R0%<FRF,pHS03f<Caf=,RIQ01#<RM'k=JB<g01>>1RI0'4f?,RIg01S4'4g00khR0fAf@S04g03c>H0@%F3#K#K#I/49%EERN#FRO#FS05#ES06#E#O#S!sH%,39'2fDRP1UI8RQO1%eKRR5JL[^7B%EOS07#FS08!sZ$!s\+/49Q07#ES09#F#E!sw5ERSPQO1=JLR[^7Bg03dC,wP%fKRK#jP0PS%ENS0:#FS0;#FS0<#F!t/&O#K!sx$S#I,UIg00TjR0#0RR#0RL#0RQ#0RT#0RU#0RV#0RW#0RXCtfC,UI,rX,qK3J%LP%<3R3,nFS0=,3P'2fHRPfF;9SP?PP%0XRS#0RK#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk#0Rl#0Rm#0Rn,19RoPCPJfLRp%_HRqP8AZH<:R:PpfJRrfIRsP8%m<RtD7E6^0oP8110nfKRo#lPJPoPqP0PAP:CQA`osPP>P0P?PtCQI0AeW0PC%09S0>/1nPJfNR?Pq%08S0?P:P?PpPoQ0?P!t&$]0P911RnPJfMR>PHPQPLCARsPJP?PH%<EREP9DDX6JPJPsA9>orS0@PQP>PoPrPQ1?LQRr%0nRo#0Rs,1QRP'2%<NRN,4FRA%E6S0A#IRu,3NRv'2S0BPrPPPAPvPLPF%8FRvPQPN%8NRAECPQPNPAPsPu%8uRAE:EBg01U8RP$0?Rr%fPRP&0>BRw&0<BRx&0;BRyPy%5FRz%5NR{PyP{%5uR{F>207y5R|P9P7g00XdR}g013YR~'^20697=J}~dB04B<8H03R~b2b3b4Q0BP9b1G@G=PJP>PqPRP:Q0@PRPtG;!v|$Q0>#0!v~+PRRPqQ0?#0S0@P:PRP?P>Q0@!w$/LnQ04PJfOR}Q03A9}>pR>/h0CaePJP}PqPLP:P>PL!t21R!t1&RR0PqQ0@!tD$P:P0PRP}Q0>!t1/QnPJfQRpPHPUPLCAS03PJP0PHPN!x1+!tJ$p}?S03PUPpP}P?PU1?LUS0411UsS0B'2%<DR?,4FR}13?uRN'2S0CQ0!v7$}PNPLPFPvPUP?%8?RNECPUP?PNPsPuP!ww$!xN$wPxPyPyPz%5?RNPyPNP{F>P|P!w++C!w+-pPqPQP:Q03PQ!ux+%0>!uv'TRQPq!w<&3P:PQP0PpQ03!uv/TnPJfSRNPHPV!{'$}PJPQPHQ00#<!{',}A9NpRS0CPVPNPpPRPV1?LVS0B11VsS04'2%<ORR,4FRp13RuR}'2S0DQ0BQ04!vR$!uw%VPR%8RR}ECPVPRP}!uw=RR}PyP}!uw3D!uw-NPqPTP:Q0CPT!uw7VRTPqQ03#0S0CP:PTPQPNQ0C!uw/UnPJfUR}PHPW!uw$pPJPTPHP?!ut,pA9}N0S0DPW!x:$0PW1?LW!xm$WsR0'2Q0:#<!}t%p13NuR?!}k$Q04P0PpP?!ut&W!}i%?ECPWPNP?!ut=NR?PyP?!ut3!|s/}PqPUP:Q0DPU!ut7XRUPqQ0C#0R?P:PUPT!zx$!ur-VnPJfW!{c$X!ur$0PJPUPHPR!ur,0A9p}QS0DPX!x5$QPX1?LXRQ11XsR}'2%<6R6,4FR0136uRR!uo$PQP}!|~$!un%XP6%86RRECPXP6PR!un=6RRPyPR!un?pPqPV!un%V!un7ZRVPq%0?RRP:PV!}h$R!ul/WnPJfYR0PHPS!{Y+V!~P0P}A90pTS0DPS!x/$TPS1?LS!{V$SsRT'2Q00#ERp#<R},4FRN13}uRQ'2S00Q0BPTPNPQ!ut&SP}%8}RQECPS!v`$!ut<}RQPyPQ!ut30!ut-0PqPW!ut%W!ut7\RWPq%0RRQP:PWPVP0PQ!ut/XnPJf[!~O$K!ut$TPJPWPHP6!ut,TA9N0US0DPK!{T$UPK1?LKS0011K!#5E%FDRU#<R0,4FRT130uR6'2S04Q!uv'6!ut&KP0%80R6ECPKP0P6!ut=0R6PyP6!ut34!~P2X!ut%X!ut7^RXPq%0QR6P:PX!|s$6!ut/SnPJf]RTPHPY!#8=$DPJPXPHP}!#8=,DA9TNVS0DPY!x7$VPY1?LY!~N$Y!uv&EDRD#<RV!xk&V!#5H%0!#8A%N!#5H'YPV%8VR}ECPYPV!#5H>V!#5H8!xl/TPqPS!uv%S!uv7`RSPq%06R}P:PSPX!~R$!uv-KnPJf_!xl$Z!uv,SPHP0!uv1NTWS0DPZPNPTPWPZ1?LZ!xn$Z!uv%Q05#<RW!xl&WuR0!xl10!ut&ZPW%8WR0ECPZPWP0!ut=WR0PyP0!xlCK!ut%K!ut7bRKPq%0}R0P:PKPS!z{$!ut-YnPJfa!xl$[!ut,KPHPV!xl3XS0DP[!xl$XP[1?L[!xl$[!ut'7#<RX!xj&XuRV'2S07!xj+V!ut&[PX%8XRVECP[PXPV!ut=XRVPyPV!ut37!xj2Y!ut%Y!ut7dRYPq%00RVP:PYPKPTPV!ut/ZnPJfc!xj$\!ut,YPHPW!xj3SS0DP\!xj$SP\1?L\S0711\!ut';#<RS!xj&SuRW!xj&7!xj%W!ut&\PS%8SRWECP\PSPW!ut=SRWPyPW!xjCZ!ut%Z!ut7fRZPq%0VRWP:PZPYPNPW!ut/[nPJfe!xj$]!ut,ZPHPX!xj3KS0DP]!xj$KP]1?L]!xj$]!ut':#ERK!#>,%S0:13NuRX!xo-Q0:PX!uz&]!#>0$XECP]!yb$!#>0=XPyPX!xpC[!uz%[!uz/S0D!u{%hR>Pq%0WR[P:P>PZPTP[!u{/\nPJfgRXPHP^!u{%7PJP>PHPS!u{-7A9XTYS07P^PXPTPYP^1?L^S0:11^sRY'214FMRT13MuRS!#@w%:PY!yD$!um%^PM%8MRSECP^PMPS!um=MRSPyPS!#>/>XPqP\P:Q07P\!#I`,D#0R\!un%j!#5M$[RTP:PSP>!u,$!un-]nPJfiRYPHP_!#5M0N!xk1YXZS0DP_PYPXPZP_1?L_!{a$_!xk'A#<RZ,4FRX13Z!#I^%A!{a&X!#I^'_PZ%8ZRNECP_PZ!#I^>Z!#I^8A!uv-YPqP]!xe%]!xe-\!ut'lR]Pq%0TRNP:P]PS!{c$!ut-^nPJfk!xd$`!ut,]PHPM!ut1XY>S0DP`PXPYP>P`1?L`S0A11`!ut%%IpR>!{[$713>uRY'2S0:Q0A!{[$7PY!ut&`P>%8>RYECP`P>PY!ut=>RYPyPY!ut3:!xl2^!ut%^!ut/!{[+nR\Pq%0NR^P:P\P]PXP^!uu/_nPJfm!xk$a!uu%:PJP\PHPZ!uu-:A9YXSS0:Pa!xk$SPa1?La!xk$asRS'2%Ep#<Rp!xj&puRZ!{a&7PS!yD$!us%aPp%8pRZECPaPpPZ!us=pRZPyPZ!{a?YPqP_P:Q0:P_!{a2_!ut%p!#5N$^RXP:PZP\!u3$!ut-`nPJfoRSPHPb!#5N0>!xk1SY]S0DPb!yV$]Pb1?Lb!~Q$b!xk'UR],4FRY13]uR>!#5G%:Q0B!yD$!ut%bP]%8]R>ECPbP]P>!ut=]R>PyP>!#5F>SPqP`!xi%`!xi-_!ur'rR`Pq%0XR>P:P`PZ!~Y$!ur-anPJfq!xh$c!ur,`PHPp!~U2S\S0DPcPYPSP\Pc1?Lc!xh$csR\'2%EU#<RU,4FRS13UuRp!xh+\PSPp!ur&cPU%8URpECPcPUPp!ur=URpPyPp!xhCa!ur%a!ur7tRaPq%0>RpP:PaP`PYPp!ur/bnPJfs!xf$dPLCAR\PJPaPHP]!uq+P\A9SYZS0DPd!xd$ZPd1?LdS0B11dsRZ'2%IDRY,4FR\13YuR]!xc&B!z$$]!un&dPY%8YR]ECPd!yR$!un<YR]PyP]!xbCb!un%b!un7vRbPq%0pR]P:PbPaPSP]!un/cnPJfuR\PHPe!un$ZPJPbPHPU!un,ZA9\S`S0DPe!x/$`Pe1?LeR`11e!~I&D#<RD,4FRZ13DuRU!uo$P`PSPZPU!un&ePD%8DRUECPePDPU!un=DRUPyPU!un?\PqPc!un%c!un7xRcPq%0]RUP:PcPbP\PU!un/dnPJfwRZPHPf!un$SPJPcPHPY!un,SA9Z\aS0DPf!x/$aPf1?LfRa11f!{O$Q05#I!#C`$Y13SuR`'2S05PaP\PYP`!un&f!#C^$`ECPf!v\$!#C^=`PyP`!un35!un-ZPqPd!un%d!un7zRdPq%0UR`P:PdPcPZP`!un/enPJfy!~B$g!{N+dPHPD!{N0YZbS0DPg!{L$bPg1?LgRb11g!{M$Q06#<R\,4FRD13\uRa'2S06PbPZPDPa!un&gP\%8\RaECPg!v\$!un<\RaPyPa!un36!~>2e!un%e!un7|RePq%0`RaP:Pe!|g$a!un/fnPJf{RDPHPh!{N+e!#CP/PZA9DYcS0DPhPDPYPcPh1?LhRc11hsRY'2Q08!#@]&S13ZuRb'2S08!#5_%b!un&h!#@[$bECPh!v\$!#@[=bPyPb!un38!un-DPqPf!un%f!un7~RfPq%0aRbP:Pf!|g$b!un/gnPJf}RSPHPi!un$YPJPfPHP\!un,YA9SDdS0DPiPSPDPdPi1?LiRd11isRD'2Q09#<!#5/-c'2S09PdPDP\Pc!un&i!#5-$cECPi!v\$!#5-=cPyPc!un39!#5-1g!un%g!un6p+01ARgPq%0bRcP:Pg!|j$c!uq/h!sN&@R\PHPj!ut$DPJPg!#@Y/PDA9\SeS0DPjP\PSPePj1?LjRe11jsRS'2Q0<!#540d'2S0<PePSPZPd!ut&j!#54$dECPj!vb$!#54=dPyPd!ut3<!#541h!ut%h!ut:CRhPq%0cRdP:Ph!|p$d!ut/i!sN&BRZPHPk!#5:'h!#5:5fS0DPkPZP\PfPk1?LkRf11k!#5:%;#E!#Qv&!#5<$e'2S0;PfP\PYPe!uv&k!#5<$eECPk!vd$!#5<=ePyPe!uv3;!#5<1i!uv%i!uv:ERiPq%0dReP:Pi!|x$e!uv/j!sN&DRYPHPl!#5B'i!#5B5gS0DPlPYPZPgPl1?LlRg11l!#=i%K!#5@-f!ur%gPZPDPf!ur&l!#5@$fECPl!vb$!#5@=fPyPf!ur?YPqPj!ur%j!ur:GRjPq%0eRfP:Pj!||$f!ur/k!sN&FRDPHPm!#5F'j!#5F5hS0DPmPDPYPhPm1?LmRh11msRY'2%EK#<RK!{`&KuRS'2RgPh!vH$!#Qr&mPK%8KRSECPmPK!#Qr>K!#Qr6Pg!#5D1k!ur%k!ur:IRkPq%0fRgP:Pk!|z$g!ur/l!sN&HRSPHPn!ur+k!#5J0ZA9SDiS0DPnPSPDPiPn1?LnRi11n!#5J%2!#8:&\13ZuRY'2RhPiPD!{]$!ur%n!#89$YECPnPZ!#Nx>ZR\PyP\!ur2h!#5H1l!ur%l!ur:KRlPq%0gRhP:Pl!|v$h!ur/m!sN&JRkPHPo!#5H'lPHPK!#5H/kSjRDPo!si$jPo1?LoRj11o!#5G%1!~Q$!xg$H!xg$l'2RiPjPS!|Z%!us$o!xg%vECPoPKPv!xg?KPyPK!us2i!us-kPqPmP:PDPm!ur&%0_/1n%0h!uv$%V8RmPE!s$%DG!s0i/3ZS01P_1T9EXOBR_P!s$amO1S0DO1S02O1S0;O1S0<O1S09O1S08O1S06O1S05O1S07O1S0BO1S0:O1S0AO1S04O1S00O1S0EO1RDO1RkO1RiO1R{O1RKO1RzO1RAO1RuO1RsO1RvO1RoO1RLO1RlO1RHO1RSO1RjO1P_PhPjP_PgPSP_PfPHP_PePlP_PdPLP_PcPoP_PbPvP_PaPsP_P`PuP_PUPAP_P]PzP_PpPKP_P>P{P_PXPiP_P^PkP_PNPDP_PTQ0EP_P[Q00P_PWQ04P_PVQ0AP_P0!#T3$}Q0BP_P6Q07P_PQQ05P_PRQ06P_P?Q08P_Q0CQ09P_Q03Q0<P_Q0>Q0;P_Q0@Q02P_Q0?Q0DP_P8Pm%8mFH!s$A!}?%E:P9H02Q01&017%V7#Lp+01L,RIRY000M%LY%LMp+01N,RI/kM#L[[1~F313<F%L3Q0=,3<[[%LFRMg01T\RIA}F38UW8Q0=#L\I^8Mp-0RM!{T$BPBPwP81{B8CdP8PwCdPxPy1cB<1yBORO5zy%e1R<PyPO%5EROP!s$$DMP!s0h=vy\P<Py!$8_';E|CgCg!|~,X:BW9%L9P8!|VvP;[[^:B^9MP9!#42$RRMPq%NG#N!s$/RqP:P!w=$Pp+01OPq!#4n$%VGP=P@O4b1bGbHbIbKb@W0X7CP9O1n0110001020111100X5!s>_0!s>~!s>~!s>~!s>~!s>~!s>~!s>t0!sVXP9O1!{l$CuW=W<W>W?WAWEWCWDWBW;f9f8P!$Ff1O:n40!{c$!s#$1:110110710910810:106105104102103WFXJBXNJWLWMo"). Qed.

  Lemma h_know_ok : ltac2:(zQ "b0!jr9!jtc!jh0!h9!nja!qq6!qs7!po2!mic!pk0!kq4>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2sp@1$1@1$0#k0>3can$3>0@4$6^4^3^2^1@4$9$a@1$8@3$5^5^3^2^4$7").
Proof.
ltac2:(KReplay.run1z (kr_t_AsHdrErr ()) ["Plain"] "##cYp'0h07__arithh14__ffh28__varmaph35__with44__x1h51mh66__sat0h7!s/%1h81dh91zh:7!s7$66h;!s0&7h<!s0&8h=4__x2h>1xh?2Hah@4__p1hA4__x3hB1bhC4cstrhD1ihE2E0hF2E1hG2H3hH5Hcan0hI6Hcan65hJ7Hcells0hK2HdhL5Hgot0hM5Himg0hN2HmhO3HsphP5Hsp17hQ6HspHi0hR6HspLo0hS5Hstk0hT2PHhU2Z0hV3canhW3memhX1nhY4regshZ2sph[1yi002H2i014Hcani02!t\%4i036!t]%i044Hgoti054Himgi06!tM$6i075!tN$i085!tN$i094Hstkp%0p&0p;1p;2p;4p;3p;5p;6p;7p;9p;8p;<p;@p;Bg002\j10Tg0027j11Tg00gIj1b!s/$gk102Tg01VKk20YTg004[j1vTg03XGR0k40HTg03SGj3OTg018aj1ITg01Xej4_Tg005=j1CTg00kEk306Tg03NCk20iTg003Aj3=Tg016Dj27Tg03YLj2R!s8$nR1j25!s:$lk40PTg01D5j2:Tg00i_j29!s/$=j1oTg03Zmk20>!s{$[j1kTg0090j1ETg00jEj4qTg03\:j2rTg00@Ij2sTg01CXk205Tg00Akj2!tm$eKk103Tg00BFj2PTg03RDj2hTg006bj1~!t&$Ok20]Tg00:Xk30[Tg017Jk10ZTg00>3j2gTg00;aj2|Tg00<jj2{!v-$[k10XTg00Lkk30W!vr$;j1zTg03fQk10VTg01a`k30RTg03g^k50QTg01g=k30Ok40gTg01M=k10NTg01F;k10L!s0$Yk10JTg01Ggj2tTg01J^k20!wY$K@k20G!s0$lk30FTg01LKk40!vB$1>j6WTg01;0j2aTg03hgk70DTg03^Gj2p!wF$Qk20BTg01E9k30A!s0$]j2`!tA$Dj2ZTg03ink70@Tg03k5m90?Tg01IPk30=Tg03l=j8mTg03B=R2j2lTg02ANj4d!va$gR3j23Tg01hMR4j1JTg02?hk10<Tg02B9k40;Tg02@Fl<iTg03mBm@09Tg03nHj4^Tg01B3j2UTg01imk108Tg02L]j4cTg01jRk60!z%$Tjk70KTg03D9j2e!s/$bj3uTg03EKk20M!wl$Kj3xTg03oHj2wTg040Lk404!y6$`j4yTg019ik10STg01<7k10T!tS$Mk30UTg041\k20hTg024=k20f!z?$kk200Tg042ik30eTg043Ek50_Tg044Tk40!uA$J3j4}Tg01Nbk701Tg01OFk70\!s0$jk80!wB$Hmk30aTg02amm<0bTg02bRmB0c!su$ok60dTf0R5#0#0p=>g00PDR6g00S`R77=5p=\%0!sD$!s$+Cp=<%15#1p=L%15#0p=B!sJ+p=Af2R8f1R9'5/65p=]%0!sR$F!sJ'Cp=Q1575p=4!sm$#1#1p=fg00O;R:?x95p=Hg00khR;P8P9P5C_p=M1t65p=8P6P9g01UdP5C}p=[!s4$PNR<g01PmR=P=g01QMR>P5g01RTR?K01p=Yg00XdR@g013YRA!uP$Nf3RB/581595'6p=;!t]+!s$'p=SP8P<P=P=P>!tH&QmP5C}P!s}%2!v;30p=n!sY-9P5K0\p=@PB!s:+!uI$L0`p=?1595,68p=X1P65p=Kg00o4R?P6P2P4P1g03W9f5R2f4RCPB!sa%M<ip=jB0a695p=DP6P7!sA'EWp=V1389/55p=TP?P6!s$$4P4P2P!sh+N<0bp>0:!sD&!s$%3P5P9P8P3PBPCP2f6R3f7R4f8RDf9S00NB0cp>0CP:!so,J0dp=Gg00PbRE#0RF#1#bRG%0FRH#0RI#0RJ#>RK#bRL$02RM+0Y%bI$02RN#vRO\M!sp'H0HP0!t#+;AO2B8#IPCg02lIS01C_P5f>R0%CFRPg03aT606G+0if<RG5=Mf=,7L%CJRJ'R#\g01>>RQ17L0'5f?RR,7Lg01S4RS'5P;fAf@g03c>RTH0P%0K#>#<RU%1ERV#0RW#0#L#B#A#<RX,:57]5fDRY19L9RZO1%oNR[5=O[^D6%1WR\#F#B!sU&]%1\R\!sf-^!sf&ER_PZO1==O[[^D6g03dCR[-0>Y%kNRN#vS02P;P_%1VR_#0RO#0#F#FS03#0#>!ss$L#QRZ,9Lg00TjR`#ERa#E#ES04#ES05#E!s$%RbCqfC,9L,rb,sN3=%4Y%CKRK-05PRc,:Y'6fFRd$0317LdRe#41:ec'6fGRe,PMfIRf?Oed#I/h`==Me19LeRd,PMfJRgfH;Oe#I/ha==Md1P6719L7Rd,7LRe#\fLRh?Ogf#IRifKRj%~`Rk00]JRlB0[kQSRm&0ZT,gk/|TS061{UXS071{]^S08&0X7Rn/gZ%~aS0980WbS0:%1\S0;#0S0<#0#f#B#>#F#QR\,gnRo%1O#QRO'|S0=%z:S0>'HS0?'HS0@'HS0A'HS0B'HRp'HRq'HRr&0V[Rs60R:Rt3MfMS0C?Ojg#IRu?MhrAMuhs'6[AMijrRvAMijsRw'6AMuht[P;PiPjPrPsI0QPvPwB0O;ijRwPlPq!sC&kPJg01U8Rq#zRl%kqRv&0N6Rs&0L6Rr&0J6Ru1t67Rt%8J'['Y20Iu>RxP5P81P@AS0D20G58#NdB0F679H0ERAb1b2b31:7JP5b0PMPg17L5R@/RJ#\XBMPG1hi`S0EP8EW1aik,7LRG!sD$eK0DPwPmPp!tq+QPSPMPgPQP@P@PSC;XBM17LgR@/pJS0F%4@%4JS0G17Lh/RJ#4[[S0H20BPKRp1:7P%4K1:7cS0I[[Rm%4PRyg01T\RzB0APK9UW?RK%4c\z^?yRyPlPv1`69S0JPrPu1Z6ERz%f_#SR_#S!s$&CR{#852uR|%o=R}Pu%0_#L!xc$n#n#<R_#8S0K=2uzR~P}A@u~|C?C?PxP!v>&X46155{15_9P_P8P8P{C;[[^46P5fNR{,7LR|P0PRO3b0b:b;b<!uz,eQ!v\%PQPGPG!s8$K0@PwQ06Q0B!vZ+gPTP8Q00Q0FQ0HPpPmPKP!uW$Q!uS%P~P}%BH#L#>#QRH#8R~92utA2u~z5@u!t~4_5%4H?XH9!tv%P|PRO2!tm+7PTPTP@C;eN90?PwQ07Q0A!t\&UPXPlPvPsPr%8U92ut!t&,%4U!yA$!to-!sN%X%8P>0=6LRP52u!sW,15XcP5b0b6b7PDGmPwQ08Q0@!t:&]P^!sj,]!t:3]!t:9^=2uP!t1/^!t1,4!t1%:Q0?!t1&nPdPZPbQ0919Lf1PMdP91lab%CERE%CIRI'5RdPaPE%KEPbPI%KIRaEj!t>,E%8IRE!uM0PdP5b0Cd1lbb15IIRdPbPIPa!s+%!sc,A2uEE!s]635ZRd#4X96!t5,Z,DtRf!uz1137ZRZ#4!v#$eP5CV%JbRn=TdcX9613ZnR^/5cR]13ZIRX/5cRUP6P6P1P5X>6R@P11595$0<X[6X>6P^PX!zY$@P6P6g037A1395H0;#KX56XX6PZPZ%KZPnPIP@P@%J5#KX>?!uO%J0:N:0CPcPc%KcM<i!wc31DfE!wd1PU!wb'CdP]e!u;%Q02P;Ph19LdPbCq19Lg!#9R&X96P2!sL%N@09PwQ0=Q0>135\RN#41:Nc%4ORb13NO;Xc'6'6%49RN%J9=T8ORgP;fPRd13C\/3B,9LP8C^#N[[^5?^86'6!vV$7\Rh#41:hc13hO=Xb!so$R]P;fORU13hBRf,9LRE!sd%\g\N!sf%!zL5\Ra,DtRI92ut1[IP,Yu%8OR@!s6$DI@=2uP5@u!s%%!v6-]!zr+UPEP8P6PfP\P5%JB,35R]Q0<#1#A#F#L#F#QRnC;Q0;#1RZ#>RX#0!#>J$P5P]%1Z#>!s5$ZC;%1X#F#>#F#<RXP5P]Q03#1!sF&]C;'U'UX96&088R1%J8#4RT17LURR/pJR|%4RQ0GfQ,7L!#7H%RJ!ui'p-0RR!un$61`68RHP9PsCc!#6y%FRF,Dz=2u@P}PuA2utzR~P}Pu!#E|&1DIz!vD$a1DIF%8n52!v0$!sG+PCJ07K0K!#6|3X=6W@AT59O13h8R>AT>Bn5]\/UC\N[^46^=6^@RP5P^13hDR^%J4RR,3^R\PZC;PXP^P\P!us$PRPDP2P3O5!#5b&bC17LEP1PTP|P!ub+Q05,e6Q04,e61e6`5u65u6g03W[+0M=xq!u}$P6PsPB1`6BCcP9PH!v'+WRW!}~$}Pu1DzW!v4'P!v/$Q0K1Z6V52uP}A2utI!yL&5@uC?!s$%!uu3XA6%48RIAT9BO15_C13hC!{$''6[\I[!u~'A6P5PRfS,7LPDPCP2P3PYO7!ue,,wfEWH04XNgXKNX5?X86CyPe!{@3A2utt1[t!ti&!ta,Q0I9]77!z}',w7CV&0SoR7,ai,7L&0ToRA'3Rx#41:xc13x!|p+P;PUQ0C9Od{#IRd/a7,7L/3A!}a/!|{,'6eB0UioOP;PU20hdo!sN<!#8;$Q0=H0ge20f:wDG!s$/PiPjP[Q0D2006?0006g045P<0e[#NdP3I0_CyH0^!sn'1C_RjePjebUbFbEbOWIWHWJWLWMWSWQWRWPWGQ00PDP4P3!#Ly-O:n4000010!s#$1:1100106108107109105104103101102WTXV6XZMWWWYo"). Qed.

  Ltac hf_plain SOUND :=
    (* LPS 75d69e00: + Hrd2, immediately after Hfd2 *)
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
    | let Hc := fresh "Hc" in krd HK 0x714418%Z 8%nat Hc; rewrite Hc; cbn [ev ENV]; rewrite P1; reflexivity
    | intros a n Ha Hn; eapply frame_mod_store_ok; [exact FM|];
      match goal with Hs : stk_ok _ mem sp _ |- _ => apply Hs; assumption end ].

  (* LPS 75d69e00: + [m_channel_reader mo = true] after the fd_lookup premise, passed straight
     to hs_sound by [Ltac hf_plain] above.  Statement from this file's own [About] with that
     one line added. *)
  Theorem as_hdr_short_fwrite : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0xbead8) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0xbeb14) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_short) K).
Proof. hf_plain hs_sound. Qed.

  (* LPS 75d69e00: + [m_channel_reader mo = true] after the fd_lookup premise, passed straight
     to ho_sound by [Ltac hf_plain] above.  Statement from this file's own [About] with that
     one line added. *)
  Theorem as_hdr_overrun_fwrite : forall regs mem msF mo (sp : word) (can : Z) (K : TSet),
    hfH regs mem sp can ->
    lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst regs (Z_to_bv 64 0xbeaf4) mem (seg_rom RSEGS) ->
    fd_lookup (m_fds mo) (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
    m_channel_reader mo = true ->
    K [] ->
    (forall regs' mem' msF' mo', hfPost regs mem sp can regs' mem' ->
       lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
       restrict L S msF' = mkst regs' (Z_to_bv 64 0xbeb14) mem' (seg_rom RSEGS) ->
       realizes RSEGS (mkCfg msF' mo') K) ->
    realizes RSEGS (mkCfg msF mo) (t_emit (W 2 msg_overrun) K).
Proof. hf_plain ho_sound. Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
