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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux Hoare RefNodes LibTail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefExitBase RefStdioDefs RefStdioWrite LibStdioCall RefPrintfBufBase LibDiagKn.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefPrintfFirst () := KReplay.lz_vm "#%?xC47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd9ex_elimF1C13~~~C46Stdlib5Lists4!s+#6nth_ok!tw,4Init5Logic8eq_ind_rK!u=,Numbers7BinNums8positive01!sKG2I!t619Datatypes4list00K!sFA1I!tv72eq00!t$<6option!t&/!to31Z02K!w#O8SymExec23SX24expr0!w&&!smc2!sm&!uD;3nat!t{_5sadd!t|,!v1?3!t4]6kentry05!v3c!so'6!sok7!sok4!soV1U<LibStdioCall9s!s0#_res!wV5!{':!{g93and!|J4!|&,1K!s[<1!}G=prod00C!zG<fstC!{S]s_pc!#4D&!t0;sndC!v}^:!v}%call!}Ri3!wkB!#4R$2!yre!x|&I!}T?0K!#94?5Instr5aluop01I!upb0!t_&!uPd0!#3~B!#8z+3!t<]8sideco!{{#!u/V!}\=0!#7CF1!#6S?!wQ^9sym_state!wVe7script!uI+c!v?Q>RefPrintfFirst5p1_rA!zs3!|+3bool00!t8ecA!u&lB!spkc!sph6p1_sr!sqlkn!uVlsc!w:lC!w:lC!#3SB1N02I45stdpp9bitvector;definitions2bv00K!}Ig!#H2&!#4c]ym_exec!#3kA!#=/$1!t7]5s_log!t}c5carry!slV=!sl'Sound4SX2S7regs_ok!stjknow!stl9scs_denot!sv&!#<e9?!s<25S!y,#8m_halted!#C`C2!t#Q9m_vm_lazy!x1]6s_!w?#!vFjmem!vF0!svb8log_flat!{u'!v<I3Run6config01I7!v9PhapeAlg8realiz!#>-+!smP6CatSim6mstep!si+C!siPSymRun;!|p$_after!slV!uF+9rz_!t\%!w`V!#VI%:and!#VJ$3!uG]9run_s!xP#!|Y'!#7A>7Z_to_bv!ukQProp!y`#4mks!yQ&I!yQJ<MemImageType7Segment!#VW=!#Ct#0!#Bb\3env!yy+!~[P5Model00!x~Y4TSe!|d+!#C3?!#F']6s!#Ig/!txP4Scfg=hunspell_scfg!z3ZAux7sregion!z1'!ug'!#^B$7!s+#Def3map!#^B76!#^B$!tHW;log_covere!{W&!#A&`:p1_!uB%!~#&!#LDRRef!#LD#Defs7sw_post!wgX5Frame7outside!sg&5!#b;%6ZArith6BinInt1Z3sub!~HA;bv_unsigned!sm<2le!sB>t!u6V9f!s+#_mod!u8Cad!xoQ7StoreOk!#;Z#grows!#7fV!#4y&3rdn!sf_5v_!u7#!{f&!#3nH>!#VC#!sE+@word_to_le_bytes!|:83no!wN0!tj96images5Ubsan1M?loaded_s!#6n$s!#9U\7vals_ev!|zg3ENV!tX&!#5Y\a_base!smde!#B4Z!#H~0a_off!#6F\6r!tU-!#8f\!#hN%!#Vug<!#5g+_w!{F'!#oI42In!#mM8o!tV#!#E}a4!#Ey+!#3F<pow!sC<>po!#70#_nonneg!sN<:!sN#!sJ%K!u['9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PE!#nk#!sIE1!sIE7C!sI55Tauto8B!t[&!sH6:Z!u%+=Z!sT$CheckerC!uv<4find!sqAC!sq0!#F'$!w5@1!|ZW<!zt'!#LN-!w^K!vp7!vM&G!sJ'4!w<E3!smF5!sJF8!x+<5eKind!#aF<unit!y|8!se%4kind!ud8!v713Op2!uD#!t5@!smJ5!#3/75False!#J$3!sC%4True!|f8!ym-;!~'%!y5$!#pb=6length!#IMQymDrive9junk_val!#<1&!#K~;app!#?0X7seg_rom!#6j<9nth_error!t0P9!u;'X8!#Z[#nth!#;6U!#W<6!#n6$!#[T+!#6]:6of_nat!sF34Znat5Nat2Z7inj_iff!#A177iff_sym!sf>9is!#7f<!|d33!#;``?!#;`,!#3j+!sza@!sz-!#>I,K!#QpPevent02!#QpX6t_emi!#\Ojsc!u>1!#P$86Forall!#87XA!#Oi,_!#K5#!vSW7FdE!#xf%!#M^?D!#Y$%_obliga!s:#_1K!#ivC1!#J3Y:fetch_word!#bb^r_g!#W5&!#4DX4getr!#FWYRun7reg_val!#5'&!#e\Oerrno_ret!u1Y6regup!#^MG5bv_eq!#8iX;!#j~#set_a0!t:G4BvWf!xB]4ridx!}[V!y/4!v9,!umX8blob!#Ox+!#7_8f_equal!$:_;trans!#s$\!#`s#!#rzV!$#l15sc_wb!snjp!v/>8iff_refl!#C^5;ZifyClasses5mkrel!#E>D4!snB;rew_!tB%v!uO_4sc_!}z+!t@@3inj!$Aq@3!~?#alu64!z7P7StepTac6u_Z2bv!zyV7LibTail7vadd_wZ!#5m^7alu!#[?+K!#R`:1!ydcsp!zTe!x'#s!~I_5krea!ua&!#Hu2Peano2le00!y/B!#fj#ff!sLB9and_morp!#HvZ!ty$_!#`c+!#5y\a!#[`-!#H>X;!sj%_lit!#8i'!#CWOm_fds!yZcfd!tJW9fd_lookup!#TQ?3!tlP!#uG3!$C/%!#Gc`A!#k5%_!#hB2!zj13Nat!#h<S!x;,@!#Oi'_!#PX%!#5f0!#Ng,:!sG%_ap!#o^3!|>&t!tSZ=!#e]%!t%#!#78'!#3jbr!snik!#jgV!#mD$D!x$+!#>Q$_s!#ID'!y1a9rz_run_lf!#6Fh!smf7sc_buf!#8#e8!sp%sz!sqe6sc!#H7#!sodE!$IN+!#`o$!}P$!s~V!#3138!ytV!#J&+!#q]#i!siW!}2':!si%_pc4!smWRefNodes>rz_ioctl_win!x%+!#;\@7!#CM%!#DdD!#3x#!#<v@!sK$2!#XuE7!$>DaFUEL1!}{g6STOPS!sqh4scr!#<y&!#\<<6inj_!#{Y4!sH4t!t[a7!$E$#A'!vBh!$E%#!$HKk!#8b&!spe!#8d&I!#]aV0!v3esrF!v~m!sqh!xe#covA!#3LU!#>G+6ECALLW!sj`?is_e!#7P#!ss/!w9g!uR&K!#lB<1!#EdP6ENOTTY!$Yk=N!yCc!w]&B!u1'!#5v3!#o951!#6k58ZifyInst7Inj_Z_ZI!#bnX!uEi!$O7g<p1_itinera!$Jt'!#H&5sub!#lq;8max_spec!vwD5Psatz!#{E7!sO86!sO6!#r|:!#|B>3Pol!#tyE!tD&4!$sD,!#<H%?Rel!#g>#!s6&=eq_Tran!$^q$!$:{;nth!sr59Morphisms:re!vU#tful!tAE<eq_Reflex!t@0!s|5Jr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^??eq!tM#per!tT;!sR,@!u$0per!sS?M!#KM$co_!$?I#v_impl!#W?$ism!x:<s!#gk[nth_map_!sh#!|o&!#Pf4=app_nth2_plus!#X&\2!$7-h7p1!#{Y-!$0p;max!#EEE6!sg+5!sf$8!#S1#Na!#3b;!#Bm,;inj_sub_max!sM>8!sM%cc!#39M1i!vB`3p1H00!v@B6modulo!yQP!#po%6stk!$YEX1U9LibDiagKn8cell!$[',!#eoPeq!yp#9getr_zero!{#2!w&,9SatDivModCZ!#UC#!#}I$!$6\&!u4Q@!w/+BufBase>!$]?%_by_!#p2'!{Ha:p1_ev_jun!w$Y!tr49all!tu#32!tmg8p1_!x$$!w}V!#Ry'9u64_range!y[ckn!t\\!{4&<kalign_int!y]+!smX!uF$!smc=kwr_of_!|q0!snV:kimg!t[c;k!$I]#!sl/!$#@X8store!uG#!{2b=data_!st+!zAVAgentLib7!zA#l!$,Rj6estart!#441!#<5,7f!$,L#b!{P\:!#6,$know!|Bb;!$j,%!#gQ#!sq$!$/QB2!t:\9!u+#_wf_!#{0%!#:w`6p1P!$WI,!#6fd!$m}/!sue!$m~0!#haTB!#ha+!{I1k!vUh!#]dg8p1!$f1-".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil03nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~kb7scripts04boolkb3SCRkb4expr04prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9LibDiagKn~~~~~~qd9pf1_cellskb6kentrykb4EVarkb2SAkb4ELitkb3KWr03appkb6KAlignkb4KImgkb6KRangekb5KWordqd8kn_cells89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U0e1R1e1f1P1r1i1n1t1f1F1i1r1s1t4FPX1~~~~~~hka8p1_cellskb8sidecond03fstkb9sym_state37Corelib4Init5Logichs92eqhs93and03sndkb4s_pc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcLibStdioCall~~~~~~hv69stdio_reshka5p1_rAhka5p1_rBhka5p1_rC04Some06optionhv6astdio_callhka5p1_cAhka5p1_cBhka5p1_cChka6p1_knBhka5p1_schka6p1_srBhe4Npos35stdpp9bitvectorbdefinitionsira2bv04pairkb5s_log3h5LinuxProcessSemanticsfLinuxProcessSem3Runiub5mkCfg3h5LinuxProcessSemantics5Riscv7Preludeji05bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jkf4mkst69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jp2dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~jta8realizes79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~ki17know_okki17regs_okki19scs_denotira7Z_to_bv04None04true3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypekq07Segment3h5LinuxProcessSemanticsfLinuxProcessSem5Stateku05Modelku08m_haltedku09m_vm_lazyjta4TSetkb2SSkb5carrykb3envkb6s_regskb6sentrykb8sym_execki18log_flatki19mem_denot69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~lo17sregionkb5saddrlo1blog_coveredhkaap1_regionsirabbv_unsigned46Stdlib6ZArith6BinInt1Zlv93addhs93notlv92lelv92lt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~mib9frame_modmib7outside79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcRefStdioDefs~~~~~~mnb7sw_postlv93sub69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~mse8blobs_evkb3Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~nhb7vals_ev37Corelib5Lists7ListDefnlf3maplo16rdenot89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U0e1R1e1f1P1r1i1n1t1f1F1i1r1s1t5First~~~~~~no73ENVno7cp1_regions_w79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U0e1R1e1f1P1r1i1n1t1f1F1i1r1s1t~~~~~~nv6ap1_regionslo1cregions_flat69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~om6floaded_segmentsku05eventku07WriteEvjkf7seg_rommse9junk_vals06lengthjta6t_emitnv65p1_knnv66p1_knFnv65p1_srnv66p1_srF37Corelib4Init3Natph33sub37Corelib4Init5Peanopic2lepic2ltjkf4getrkb2evnv63ENV89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U0e1R1e1f1P1r1i1n1t1f1F1i1r1s1t5Plain~~~~~~pm07p1_valslv96of_natpm03p1Hpm06p1Postku07FdEntryku09FdChannelku09fd_lookupku05m_fds" s.   (* [comment removed for export] *)
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
Definition STOPS1 : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+uiuu8@3$1$0+knjp0@1$2$0").
Definition FUEL1 : nat := 5000.
Definition scr0 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "40!k1!p4!pa!q0@3$2@1$0$1@1$0$3@1$0$1").

(* [comment removed for export] *)
Definition p1_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 1 => ELit 0x47390%Z | 2 => EVar 0 | 11 => ELit 0%Z
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p1_cells : ltac2:(zQ "40!q7!j7!h8!k6@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "10!ub$0").

Definition p1_kn : ltac2:(zQ "20!h8!v7@1$0$1") := ltac2:(zQ "e0!v7!jb!hg0!hg7!hgc!hh3!hh9!k1!hhe!hi7!hie!hj7!hjf!hq1@3$6$0@3$1$0@2$8@1$2N0+h0@3$1$0@3$a@1$2N0+hggggglg0+nvvvvvvvvvvf@3$1$0@2$5@2$3@1$2N0-kt0+kt0@3$1$0@2$9+hggg0+vkgg0@3$1$0@3$b@2$3@1$4Z+hiusj8N8@1$2N1@3$1$0@2$5@2$3@1$4Z+vsgg0+jlgg0@1$7$0@1$c$d").

(* [comment removed for export] *)
Definition p1_rA := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0x4743c p1_sr [] p1_kn 34) []).
Definition p1_cA := Eval vm_compute in (carry (s_log (fst (fst p1_rA))) p1_kn []).
Definition p1_srA : list expr := Eval vm_compute in (s_regs (fst (fst p1_rA))).
Definition p1_knA : list kentry := Eval vm_compute in (fst (fst p1_cA)).
(* [comment removed for export] *)
Definition p1_srA' : list expr := Eval vm_compute in (sr_upd p1_srA (ridx 10) (ELit (2^64 - 25)%Z)).
(* [comment removed for export] *)
Definition p1_rB := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0xe3910 p1_srA' [] p1_knA 34) []).
Definition p1_cB := Eval vm_compute in (carry (s_log (fst (fst p1_rB))) p1_knA []).
Definition p1_srB : list expr := Eval vm_compute in (s_regs (fst (fst p1_rB))).
Definition p1_knB : list kentry := Eval vm_compute in (fst (fst p1_cB)).
(* [comment removed for export] *)
Definition p1_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 p1_srB p1_knB with Some r => r
   | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end).
(* [comment removed for export] *)
Definition p1_rC := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0xe3930 (sc_sr p1_sc) [] (sc_kn p1_sc) 66) []).
Definition p1_cC := Eval vm_compute in (carry (s_log (fst (fst p1_rC))) (sc_kn p1_sc) []).
Definition p1_srF : list expr := Eval vm_compute in (s_regs (fst (fst p1_rC))).
Definition p1_knF : list kentry := Eval vm_compute in (fst (fst p1_cC)).

(* [comment removed for export] *)
Lemma p1_itinerary : ltac2:(zQ "hb0!h8!hqd!hr8!hrd!htd!q7!hu3!k1!hua!v7!oa!p4!j7!huf!ij7!ik4!ikd!il6!ilf!im5!imd!inb!io4!iod!ip6!iq0!iq9@2$6@3$4$c@1$d@3$2$3@1$0$1@3$2@2$5$3@1$0$1$a$f+ujpgc@2$6@3$4@1$0$1@3$8$3@1$0$1@3$2@2$5$3@1$0$1$a$f@1$7$1@2$6@3$4@1$0$1@3$8@1$0$9@1$0$1@3$2@2$5@1$0$9@1$0$1@1$0$b$h5@1$7$1@2$6@3$4$c@1$d@3$2$3@1$0$1@3$2@2$5$3@1$0$1$a$h0+uiuu8@2$6@3$4@1$0$1@3$8$3@1$0$1@3$2@2$5$3@1$0$1$a$h0@1$7$1@2$6@3$4@1$0$1@3$8@1$0$9@1$0$1@3$2@2$5@1$0$9@1$0$1@1$0$b$h6@1$7$1@2$6@3$4@1$h3$e@3$h4Ni2$ha$h8@2$h2$e$h9@2$6@3$4$c@1$d@3$2$3@1$0$1@3$2@2$5$3@1$0$1$a$h1+knjp0@2$6@3$4@1$0$1@3$8$3@1$0$1@3$2@2$5$3@1$0$1$a$h1@1$7$1@3$4@1$0$1@3$8@1$0$9@1$0$1@3$2@2$5@1$0$9@1$0$1@1$0$b$h7@1$7$1").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["FPX1"] "##KWp%0p;1p;3p;2p;<p;4p-1R0p10000R1p4p710p9P0P!s2$2!s3/3110p9!sQ$N!sC'1001:!s\&8p1002>!s4&1002Y!s@'g0037j11Tg003\j10Tg004Aj1]!s/$aj1\Tg005Aj3H!s/$[j1iTg006=j1G!s/$[j19Tg007bj1CTg008ij12Tg009Hj26Tg00:Pj1?!s/$nj2jTg00<7j3hTg00=@j2aTg00>Ij2gTg00?Rl<nTg00@`j2eTg00ABj2D!s/$]j2VTg00B7j4Z!s/$Rj2dTg00C2j3J!s/$Oj1^Tg00DTj3TTg00E1j3mTg00F>j3lTg00GEj38!s/$ej3FTf0R1#0#1p=3%01#0p=4%1!s-$5%01#Gp=fg00HnR0f1R2;H1p=S%11#1p=>!sW$#0#Gp=K!s:$#!s>$U%G1#9p=:%01#?p=_g00IL?l21p=R%21#2p=;!t3$#0#0p=Ig00J8R3f2R4#C%C2=83138p=PA83219834p=M!s>&p=c!tE'0p=7!tE+!s$'p=O!sF&p=<!sD%!s2$N!s<%?,62p=[!s3%!sU$L!tt$!s=$k%?1!s/$b!sF%G!s3$rf3R5/64?F21p=qg00K?R6f4R7%G5'6?F42;81p=AA86219864p=`AF542=861p=p%?5,67?F!s7'@!s7%%C27F4!s9%=f6R8f5R9;F7!sa+586p=W%C29F5!sN&o!sa&G2#9!sc+Q%05#?!t10B%15!vB%!s?2EP8P9P7P5P4P2P1CZCZp=X1D21,D4p=Yg00LHR4#1R2#1R1#0R5#0R7#0R9#1R8#1R:#1R;#0R<#3#4R=#0#3#5#fR>/S>g00LmR?#]R@%\?R?;H?RA%08R8#1#>#3!s&$KRB/SBS00g00N8RC#iRD%11R1#1RE#1RF#0RG#0RH#>#URI#0#>#KRJ%G4RK%1=#5#KR=%04R4#0RL#1RM#0RN#1RO#>RP#5RQ#3#U!tl$R#fRS#9RT%1R#:PT%0LRL#0RR#0RU#0RV#0S01#4RW#0RX#:S02%1LRY#0RZ#4S03#0R[#5#3#>R\#1R]#0#:R^%9KRKg00OFR_#CR`%0[R[#_#9'RRa%2_R_#2#;Rb#2Rc#2Rd#;Re#;Rf#2S04#2#;S05#2S06#2S07#2S08#2S09#2Rg#2S0:#2S0;#2Rh#2Ri#2Rj#2Rk#2Rl#2Rm#2Rn#2Ro#2#;#;Rp%9=%2p!s2$=%2=!s''3P#I!w8$KRP#9Rq%;=#;R=#C!sJ-!s'6g00Oe#9Rr%1]#:R]%2=#;!s$'!sT2%\33P3P9MKK9MKr9MK^3M9M^K3P3P3P5MK7MK'c3P9Pcd7Ma'cPr%1IRI#1#IPe%1Q#U#5#I#:Pr%5G#7!xf$Q#0Ra#0#7PePTPr%1a!s1,GRG#5Ra#IPb%1FRF!ym$U#O#ORd#1Rc#1R^#>R3#1#U#OR=#1#O#O#:RsPr%1QRQ!s~%%9BP`%1RRt#1RuPe%C_RvP`%<u!s4$9JRwP`%0tRtPe%3:#5!s$$I#:P`%1UR:PeP]P`%0:R:#4R]PePwP`PVPePKP`PXPe%0dP`%<FPePcP`%0HRH#0RcPePOP`%0E!{O&<Pe%1;#3!|Q$3#416rSP_%02R2#0RS#0!|x$d#:RV%NSRS,[`P_PVP`%0!|>%VPePr!s5'0R_#4Rx!tT%%<VRV#0Ry!sH&<EREPe%1:#4#L#3#:P`P1!sB&12R2#>R1#<!uQ$r%09Rz#4R{#?R|,6`Pe%?dR}#9,R`%15R5#1R~#5,[`Pe%L3#L!s$-!t$$%<~R~Pe%0=!wE%!t:%%NS#N!s$&!vh$7R7#<RSPe%<O#I!uy$!s>$YRY!xa$vP`P{PePqP`%48!t{%P!x,$|,R`P`%05R5Pe%14R4#1R|#<R7#0R8#_!ty$P`%<!sG&|#4#_R|!s=&PZPe%CoP`P[PePnP`PuPePmP`%<tPePlP`P]PePkP`PWPePjP`PHPe%:4RHP`PE!tW&!x]'x!tp%P~Pe%4\P`P5!x~&SPe%><!#5L%4Pr%0IRI#I!se$r%7!s/'0aRa#<PbPs16rJPbPH!#53$4!yJ$J,k`!t?&4!s-&!v$$16`|!wr$5MRM!wP$!sB$:Pe%?9R9!u`$R:P`%4NRN!vj%Q03PePiP`Q01PePhP`P_PeQ0;P`PzPeQ0:P`!z:%4PeQ04P`PdPe%Cf!w<&5YRY#1#4!uH$IP`PJPeP:P`PUPeQ07!vD%Q0616`}PeQ0516`9!tz$b`LPe%CgP`PRPeQ09P`P;PeQ08P`PNPe%3Y#N#5#KRY#9%GR,j`%4X#7RX#0#7!}3$7#K%G=5h`%1M#7RM,b`%GM'a%GX%<y#7#K'g16rPPePv%7c#7,rr%52#7!sA$aPr%>F#I#U#KPePqCq!~n'!#3a&IQPeQ02Pr%3G#7PbPK!#4%$4Pb%:^%\6DA!s$%3`Cp3`3`D@D=D=FWCoD=D=D@DQDB!s0$!s$%BD@FWD@DEFW!s`&Q!sJ$@!s$&!sP,EDBDEDED@DB!s&$EDBFW!s-%!s6%FWDQ!s$&!sR'BDE!t^'DAM<n,eCR^;H^Rb1SYYRa1DAARr'DRK'DRG,DARe,DARQ'DRT,DARq'D1V0>PAPq1V@?RqPAPTPqQ00PQ1V0BPA!{;$APGPqPbPK1VD^PaPr1V0YPAPAPqPqCZFX!s$%g00PCRq1dq@RAg00QOR0g00RY3JRr7J@#^/S>ATq@r=H@?%]6R61d6@Rrg00Sc#]R>g00TC3J7T@=H@?g00UM9JA0Ra9Jq!se$BATq@a!sC&VW9Jr>9T6!sT'Wag00Xl5mpg00Z7,eC5HDg00[A!sl$0!sl'YATq@0!s[&\K!sl/'D3Y!s$%do"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem rz_run_lf : ltac2:(zQ "ia2!h8!ir3!it7!hqd!q7!im5!htd!v7!p4!k1!itd!oa!hrd!iu3!k6!j7!jh7!jk6!joa!js9!kh5!km6!kn1!knc!ko9!kp4!kpa!kt5!lge!lh7!li3!lj0!lj8!ljd!lk5!q0!huf!lkb!ll4!lld!lm8!ln4&>0@1$2@1$1#k0@1$5@1$2@1$1#8&@2$4@1$2@1$1#k0@1$2@1$1#k0>4segs@1$0$hb>4fuel$e>5stops@1$0$f>3scr$b>2pc$f>2sr@1$0$i3>2kn@1$0$7>2nx$e>3ss'$c>3scs@1$0$3>4scr'$b>3kn'@1$0$7>4scs2@1$0$3>3hs2@1$0$8>1E$i2>1M~0>3rom~0>1R@2$h1@1$1#5@1$2@1$1#k0>5model$hc>1T$hf>0@3$6@2$4@2$4$c@1$0$3$b@7$i7^h4^h3$ha^h2^h1@5$i0^h0^f@1$9$i6^e^d@1$9$3@4$a@2$4$c@1$0$3$b@4$a$c@1$0$3^c^b^a>0@3$6@2$4@2$4@1$0$7@1$0$3@1$0$8@3$i1@1$d^d^f@1$9$8@4$a@2$4@1$0$7@1$0$3@1$0$8@4$a@1$0$7@1$0$3^a^9^8>0@3$h6^8^h1^5>0@4$h5^h7^9^8^h1>0@4$h7^h8^9^a^f>0@4$h7^h9^a^b^d>0@3$6@1$5@1$2@1$1#k0@1$hd^8@1$h9@1$2@1$1#k0>0@3$6@1$0~1@1$he^9@1$9~1>0>2R'@2$h1@1$1#5@1$2@1$1#k0>2M'~0>0@3$h6^h0@1$i5^h6^2>0@4$h5^hf^h1^2^h4>0@3$6~0^3@3$i9^h2^h1@1$d^h8>0@2$i8^h3@1$d^h9@4$h4^i2$h3@2$h0@5$h2?2fx^6@2$h8@1$1#k0@1$i4^ha^5^h2^h0^f@4$h4^hd$h3@2$h0@5$h2?2fx^c@2$h8@1$1#k0^h9^e^d^b^a").
Proof.
ltac2:(KReplay.run1 (kr_t_RefPrintfFirst ()) ["FPX1"] "h01Rh12R'h21Eh32HKh42HRh53HR'h62Hch75Hconth83Hexh92Hhh:5Hlazyh;3Hlfh<3Hmsh=3Hsch>4Hsc2h?1Mh@2M'hA1ThB4fuelhC3hs2hD2knhE3kn'hF5modelhG2nxhH2pchI3romhJ3scrhK4scr'hL3scshM4scs2hN4segshO2srhP3ss'hQ5stopsp;1p;2p;5p;7p;4p;3p;=p;:p;Dg004Aj11Tg003\j12Tg00]Uj1=Tg00^3j1?Tg005[j1DTg0037j1TTg000Nj2RTg00BRj24Tg004aj17Tg00^Vj5JTg00_bj7HTg00`kj48Tg005Aj33Tg00aKj15Tg00bQj3UTg00cWj3>Tg00dej4BTg00f3j4ATg00gCj1STg00h:j1QTg00h\j1NTg00iTj1KTg00j[j3<Tg00kkj2;Tg00COj16Tg00m:j2:Tg00moj49Tg00o6j3CTg00ABj2@Tg0109l=ITg00A]j2GTg011?l:LTg012Ej5MTg013JlDFTg001:j5OTg014Nj2PTg0154j5ETf5R0f4R1f3R2f2R3'Pf1R4f0R5DEp=0g0165#1g0174R6g00HnR7#1g00QOR8g00J8#1g00K?#1R9g00PCR:g00LmR;#1R<g00ScR=#1R>g017Sg00LH#2R?#2#2R@#2#2#2#=RA#?RB%=@#?#D[R@%T?#=/RBR?g018Yg019O14:<RC/48fCRDfBREg01:PfARFf@RGf?RHf>RIg01;0#7f=RJf<RKDJ%7;FHPCP8P:P<f;R:f:RCC8f9R;C833149<RL/4>%5K%7=R=7UIPLP>P9P<P;f8R>C8f7RLC833A>LG1fFRMP>PLPGCBfGRNP>P;PICAfHROP;PCPKCA%DB%SL%QB3314BBRB#1%N>%7B33fERB#KRP=>H4fNPGP4PDCB%5N9<FGRQ93@3%5ORR,;EfQg01<9RSp,2fxRTP0PAfIRU#6P1PFE0/:HPIC9[[[[^@@^1?P?A>HP5RP%5BRV,;HRWfMRXPTPKPAPUPIPJE0RYPTP5PA%6BA<HIVPJE03CRV'@'@X0?fLRZPSPTP:PAPOPJPKE0/:CP;C9PPPWPVPXPS1:Y:PCC9%5M,;GfOPTPIPAfKRCPGPHE0PTP3PA%6NPQPHE03CfPRQPSPTPHPAPZPFPGE0PTP2PA%6OA<EFRRAPGE0PIPJf6RGP0P5P1P2PAP3PQPEPFPRfJRRP=PBfDR=PDP:P4P;PLM=I1G@AP4O6M:LW<W;X5PDMX1?PTPZPCPRPUPOPNPMPBP=PDPEPIPJPKP:P>PGP0P1MDFDOW7W:W9W>W=W3W4W6W8WAWFW0XI@W?W2WCXM<XE9XK8WLWPXG6WDWOXH7WJWQWBWNo"). Qed.

(* [comment removed for export] *)
Definition p1_regions : ltac2:(zQ "20!h8!lra@1$0$1") := ltac2:(zQ "90!j7!ls5!q7!jb!itd!hg7!hgc!k1!hg0@3$3@2$2$1$0@4$4$1$0@2$5@1$8N0-kt0+kt0@3$3@2$2$1$0@4$4$1$0@2$5@1$6Z+vsvt8+u8@3$3@2$2$1$0@4$4$1$0@2$5@1$6Z+hivju8+1@1$7@2$2$1$0").

Lemma p1_covA : ltac2:(zQ "d0!hr8!h8!hqd!hrd!p4!q7!kpa!htd!lsd!iu3!oa!ik4!ltc@3$7$4@2$8$c@1$9@3$0$3@1$1$2@3$0@2$5$3@1$1$2$a$b$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefPrintfFirst ()) ["FPX1"] "p;2p;1p;3p101=?p4p70R0p101>Ap4p710p8P0p101>]p4p710p8g00A]j26Tg004Aj15Tg00BRj21Tg00C2j30Tg00aKj14Tg01?9j22Tg005Aj33Tg00ScR0g01:PR1'6g01@?g00PCR2g00Lm#5R31123g00QOg00RY3030#4'2=301do"). Qed.
Lemma p1_covB : ltac2:(zQ "d0!hr8!h8!hqd!hrd!p4!q7!kpa!htd!lsd!iu3!oa!ikd!ltc@3$7$4@2$8$c@1$9@3$0$3@1$1$2@3$0@2$5$3@1$1$2$a$b$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefPrintfFirst ()) ["FPX1"] "p;2p;1p;3g00A]j26Tg004Aj15Tg00BRj21Tg00C2j30Tg00aKj14Tg01?9j22Tg005Aj33Tg00ScR0g01:PR1'6g01@?g00PCR2g00Lm#5R31123g00QOg00UM3030#4'2=301do"). Qed.
Lemma p1_covC : ltac2:(zQ "d0!hr8!h8!hqd!hrd!p4!q7!kpa!htd!lsd!iu3!oa!il6!ltc@3$7$4@2$8$c@1$9@3$0$3@1$1$2@3$0@2$5$3@1$1$2$a$b$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefPrintfFirst ()) ["FPX1"] "p;2p;1p;3g00A]j26Tg004Aj15Tg00BRj21Tg00C2j30Tg00aKj14Tg01?9j22Tg005Aj33Tg00ScR0g01:PR1'6g01@?g00PCR2g00Lm#5R31123g00QOg00[A3030#4'2=301do"). Qed.

Lemma sw_post_frame_mod : ltac2:(zQ "h01!ir3!it7!lua!hu3!mh1!mh8!j7!mhf!mi5!im5!h8!q7!mm3!mn0!mrc!ms7&>0@1$1@1$0#k0@1$9@1$1@1$0#8>3mem~0>2su$6>1f$6>4bufp@1$1@1$0#k0>5bufsz@1$1@1$0#k0>4mem'~0>2rs@1$a@2$b@1$1@1$0#k0$6>0@6$e^7^6^5^4^3^2>0>1x@1$1@1$0#k0>0@2$d^1^3@2$3@1$5@2$3@2$7@2$f^9+n0@2$2@1$0#k0^2@2$8@2$2@1$0#k0^2^9@2$3@1$5@2$3@2$7@2$4^8+i0@2$2@1$0#k0^2@2$8@2$2@1$0#k0^2@2$4^8+j0@1$5@2$3@2$7@2$4^8+j8@2$2@1$0#k0^2@2$8@2$2@1$0#k0^2@2$4^8+k0@3$c^9^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["FPX1"] "##4ap'0h01xh11ah21Hh32Hah43Hagh53Hgrh63Hrsh72N1h82N2h92N3h:2_Hh;3_H0h<3_H1h=4bufph>5bufszh?1fh@3memhA4mem'hB2rshC2sui009swp_agreei01!s3$growsi02!s3$wbasei038!s3$endi04!s2%posp;1p;2p;6p;3p;4g003\j12Tg00]Uj1FTg00^3j1DTg005[j1HTg00BRj2OTg004Aj1GTg01ANR0j6KTg01BZj2ATg0037j1CTg006=j17Tg01C[j2;Tg01D8j2:!s/$bj28Tg01E>j24Tg00ABj23!s8$Zj3NTg01F]j25!tN$Aj39Tg01G:j2ETg014Nj2@Tg008ij11Tg01H?j4?Tg01I?j2JTg01JAj2>Tg00@`j2BTg012Ej6I!u>$7j4LTg01KIj1=Tf0R1#2#2p=6f1R2/31#=p=<f5R3f4R4'5f3R5'8f2R61521'4'3#=p=01521,46,35#=p=Mg00LHR7#2R8#6R9#6R:#2R;#FR<#DR=%F9#DR9#HR>[R?g00HnR@1O=@#Gf6RAP3P4P5P6P2EKP0f7P!s8+1A15f9R3%C7R7#C#2#6RA#2#7R0';1:<2RB'814B3'<f8RC%7:R:PBPBPC%67#6#7R7E0PC%7ARA!s>&7;R;E0'3'3[^0=AN345[P1f<RD/;01:<1RE'814ED'<15D:RE/8BPBPDP7CMf=RFPA1:<6RGPGPFP;E0f;RHP5O1f@P5O159>[[[^0=1EFC%G9!uk$Cg01KbRIP31@<Eg00OF#1!s$1REC?f:R3,JH,>E,B939PIP3%C8#2#6#7,5F,@<PEC?1>ED,B959CPIPHf>/5A!s@,F!s@%1A1DfB!uH$/8B14BD'<fARCP!v;&P!v4$P!v1&P!v--1A1FRCf?P2O1fDR9P2!uJ$R>[^1=1EDFfCRF!s}+F'<R0PD!s}&D!s}$D!s}&DP;E0P>PFP:P!vK%7E0P9!v]$5R<P<P9!sH$3P4P6P2P1O4W9W8X70!s5&2EIX3CX1=P4CLW6W<W;W:W5W4!yC'P1O5n60!s#$1!s,&51100101103104102W2WBXA?X>=X==X?@WCW@o"). Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section First.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variable model : ltac2:(zQ "10!lge$0").
  Hypothesis Hh : ltac2:(zQ "60!ir3!it7!kp4!im5!htd!lh7@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!ir3!it7!q7!h8!k1!htd!li3&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd1 : ltac2:(zQ "90!ir3!pte!ko9!ilf!im5!htd!pu9!pv6!qg3@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+1@2$3$1@1$6@2$2@1$0#k0+1").
  (* LPS 75d69e00: the stdout write needs the launch's channel reader
     (LibStdioCall.stdio_call_sound_post's premise), constant over the run. *)
  Hypothesis Hrdr : m_channel_reader model = true.

  Definition ENV : ltac2:(zQ "40!h8!ir3!lk5!it7>4vals@1$0@1$3@1$1#k0$2") := ltac2:(zQ "70!h8!ir3!it7!k1!ng9!nh5!nl4\4vals@1$0@1$2@1$1#k0@2$5@1$6^1@1$4@1$3@1$0@1$2@1$1#8").

  (* [comment removed for export] *)
  Definition p1_regions_w : ltac2:(zQ "50!h8!q7!ir3!j7!it7@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "a0!ir3!j7!it7!q7!jb!itd!ko9!k1!ms7!lua@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0@2$8@2$9@1$0#k0?3sp0+kt0+kt0@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0+vsvt8+u8@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0+hivju8+1@1$7@2$3@1$2@1$0#k0$1").

  Lemma p1_regions_denot : ltac2:(zQ "f0!ir3!it7!h8!q7!htd!j7!nn6!nnd!lra!nl4!ntf!nu6!ok8!mhf!lua>4vals@1$2@1$1@1$0#k0>0@3$4@1$1@1$0#k0@2$9^1N0?3sp0>0@2$d+hggggglg0@2$e@1$0#k0?3sp0@3$4@1$2@2$3@1$1@1$0#k0$5@4$6$8@2$3@1$1@1$0#k0$5@1$7@1$a^3$c$b").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["First"] "##0Hh03Hloh12P0h21bh31rh44valsp;1p;2p;3p;6p;4g00]Uj1TTg00^3j1ITg004Aj1FTg01Lij2ETg005Aj3;Tg006=j18Tg01D8j29!s/$bj2HTg00BRj2BTg0037j14Tg00:Pj1UTg01F]j2=Tg014Nj23!sJ$\j10!t:$aj1DTg00GEj32Tg01C[j2STg00A]j2RTg002Yj6QTg01Mkj1ATg00C2j3OTg01O3j1NTg01P:j2MTg01QAj1LTg00DTj3JTg007bj1KTg009Hj2?!u<$[j1GTg01>Aj4CTg01RGj1PTg00`kj4@Tf0R0#0#0p=5%0!s0$#0p=7%00#4p=:f2R1g00HnR2f1R3P0C@p=6%4!sD$1%4!sT$<g01SHR4P2P!sH&>g00LHR5#5R6#7R7#TR8#IR9#Fg00OFR:,E0p,3sp0R;5;9%57#!s$%:#:!s-$8198;R7'HP9P;1B92R;#FR<1980%46R6#4#:#7R=#UR>'=,38%8=R=569g00OeR?,38,98R@%15RA#4#1#5#1!s$$:#<#5#8RB!s]%0A!s6&A569%06!sJ$!sR%<!s@&6,=@!t0$5R5569%D;R@52;!s%%1S7=,38=69=138B=69A1386=695=2;!sN&R@3;X291R<@1E1:P3EQg01=?R3P;f3#AAO420R7#N'M,98%L7!tj$AJ420569X331B42R4%K:/?>/>=%G?R?/?B/>A1??6/>5%D452452432CC=;<@eP3P;%A1#Pg01@?CCg01TP5;<eW0W1W4o"). Qed.

  Lemma p1_regions_flat : ltac2:(zQ "a0!ir3!mhf!it7!lua!h8!htd!ol6!nl4!ntf!ok8>4vals@1$4@1$2@1$0#k0>0@3$5@1$2@1$0#k0@2$7^1N0?3sp0>0@2$1+hggggglg0@2$3@1$0#k0?3sp0>0@2$1@2$3@1$0#k0?3sp0+nvvvvvvvvvvf@2$6@1$8^4$9").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["First"] "##@<h01Hh11rh27__arithh34__ffh48__varmaph55__with62Hah76__sat0h8!s/%1h94__x1h:3Hhih;3Hloh<2Hrh=2P0h>!sL%2h?!s/%3h@1bhA4valsp;1p;2p;3p;4p;6p;7p;8g003\j13Tg00]Uj1dTg00^3j1`Tg004Aj1ZTg01Lij2XTg005Aj3TTg006=j17Tg01D8j2F!s/$bj22Tg0037j10Tg01Uaj3uTg007bj1rTg00:Pj1qTg009Hj2R!sn$[j1eTg01V8R0j2BTg01Mkj1<!s:$Rj35Tg01F]j21Tg01W]j2aTg01E>j2:Tg01X:j2_!s/$bj3^!u+$aj1]Tg01YFj2\!s/$dj1[Tg01ZBj1x!s/$mj2wTg00h:j1vTg01[Pj2YTg01\3j3t!s/$Vj2pTg00A]j2oTg01]8j2n!s/$dj3jTg01^Cj4iTg002Yj6hTg01O3j1LTg01P:j2PTg01QAj1OTg01>]j6NTg01_5j1g!s/$Sj2fTg00`kj4kTg00C2j3lTg00DTj3m!tL$Bj2MTg01`Zj4STg01aEj7V!s/$ij3cTg01bLj7bTg01c0j8sTf0R1#3!s$%p=@%31#3p=C%31#0p=H%0!s-$J!s-$!s$/p=Eg01SHR2g00HnR3f1R4P1Ckp=Qg01=?R5?T41p=4!sa+p=U%0!t,$IAl231p==Am!s-$;g00OeR2/21p=8f2R61M41'Mp=?1224/M1p=>1Y31p=9P6g01cTR7g01d3R8P8g01dSR9P3P4g01e3R:P1CSg01eZR;FVp=GAc341p=AP3P4P!sD$p=D!sV&f!s6&Kf3R:P7P8P8P9P6!s0+4P;FVP1Fbp=6P!sG/4P1Gsp=Wg00LHR7#3R;#3R<#@R=#dR>#`R?#Zg00OFR@,X1p,3sp0RA5T?%C=#@!s$$H#H!s-$7RB1F>ARC'2%J7RD#0#JRE#0#E!s$+7RF,2Cg01@?RG9u51P0%r@%0<R<#0#H#@RH#qRI'R%7HRH'QRJ/44%e2RK%CE#J#U#H#I#C#7RE'R%3D!s3&D'QRL/44%3<#U#C#U#I!s@&<,RK%77RK'QRM/4!vJ$aRN'B'Bf6RO#<%=6%;635P114J6P5PJf8RP#<RQ%=1RR%;1RS35X15P?PA1F>1/1IRA%7;R;%7=R='aRT,:A%8HRU11AH/2T3?'>X@?1_;=R?1:2;%8=1:2T[[RA%8;RVg01g>RWA^;=4UW6R=%8T\W^6V!sA%ZRW#]RX%ZWRW1\34%[3RY%x3RZ1w37R7%9F5GZ%v8R8PZ%9B=GZ7P8PZPZ1Y32R8%9I,A7R7'DPZPZ%9;=t3>R;,K7!s6%HR[,D81A7[=GZ;C6!s$$WCW1pZ9R9P1P6g00ScR[g01:PR7'o1n16=T[7dAj324CiR7b3b4b5X93121F12B4116IRI1:IT11IH/2T7?U'>[[^93P1PCf7RCPPO3b2b>b?1XC@POEh%<CR@%=JRU#L'P,F>%OU'1!sm%%;JRJ#811IJ!vr&eA5@UJeP:P1ENW0P1O114L614M6/BN'BP014L:14M:/BNf4R6#=%;655QP!sN$P5PLf:#<RQ?5RS!x@&P=PVPXPW%g3R3PY!v?%E,A8RJ,D!vr%KJ;!s=%DRU!vV$JU!vV,P9P!v&&112ERE1:ET%8D11ED!u+&P1b2b7b8f9#<RE%=LRD!uc+D'1RU1:UT%;LRL#811UL!uc,EDLef5RL!ue/!ua$P014MLPN%=O%;O!uW&MOP5PMf<#<RO!uW6P!uT+<,A8RY!uT+Y!uT&KR3!uT$Y3!uT:<R<1:<T%8K11<K!uT3;#<R<%=MRK!uT+K'1R>1:>T%;MRM#811>M!uT,<KMePC!uR,PN%=P%;P55OP1n010!s#%X0NP1O1n20!s9'2110!s3&!s`%!sB51!sBC<X15%<:/fGeW:W;W=WAo"). Qed.

  Theorem p1_sound : ltac2:(zQ "i11!ir3!it7!opc!ko9!oqf!ntf!jk6!hh9!jb!k1!im5!htd!jh7!or8!joa!os3!js9!kh5!ose!km6!kn1!otb!h8!k6!mm3!lj0!ou3!nl4!nu6!oud!ov6!pg0!pg9&>0@1$1@1$0#k0@1$a@1$1@1$0#8>4vals@1$h6@1$1@1$0#k0>1R@2$6@1$0#5@1$1@1$0#k0>1M~0>1K$h9>0@3$b$h7@2$h5@1$1@1$0#k0^4Ni2>0@3$b@1$1@1$0#k0@2$hb^5N0?3sp0>0@3$h4@1$5^6$hf^5>0@4$h3$2@1$5^7^5$hd>0@1^5@1$9$4>0>2Rj@2$6@1$0#5@1$1@1$0#k0>2R'@2$6@1$0#5@1$1@1$0#k0>2M'~0>0@3$h4@1$5@3$7@1$1@1$0#k0^c@1$h2^3$i0^2>0@4$h3$2@1$5@3$7@1$1@1$0#k0^d@1$h2^4^2$he>0@3$h8^c^3$hc@4$h1$2$h0@2$c@5$e?2fx^5@2$3@1$0#k0+knjp0^4@1$f$2?5model^c@4$h1$2$h0@2$c@5$e?2fx^9@2$3@1$0#k0+knkjc^8@1$f$2?5model@2$ha@3$8$4@2$d@2$3@1$0#k0+1@2$3@1$0#8+j0@3$8$4@2$d@2$3@1$0#k0+1@2$3@1$0#8+a@1$9$4^7").
Proof.
    (* LPS 75d69e00: replay replaced (it applied stdio_call_sound_post at the old
       arity). Shape from boost-beast http_request RefPrintfFirst.v p1_sound; pcs are
       boost-json's own (0x4743c entry, 0xe390c ioctl, 0xe2ee8 write, 0xe3930 resume,
       0x47390 exit, all from p1_itinerary / the sym_exec seeds above). *)
    intros vals R M K HL P0 HR HK HKnil HCONT.
    pose proof (know_nth RSEGS _ _ p1_kn 1%nat _ HK eq_refl) as Hrg. cbn [kentry_ok edenot ev ENV] in Hrg. rewrite P0 in Hrg.
    pose proof (p1_regions_flat vals P0 ltac:(lia) ltac:(lia)) as RF.
    pose proof (p1_regions_denot vals P0 ltac:(lia)) as RD.
    eapply (rz_run_lf RSEGS FUEL1 STOPS1 scr0 0x4743c p1_sr p1_kn 34 (fst (fst p1_rA)) (snd (fst p1_rA)) (snd p1_rA)
              (fst (fst p1_cA)) (snd (fst p1_cA)) (snd p1_cA) (ENV vals) M (seg_rom RSEGS) R model);
      [ vm_cast_no_check (@eq_refl _ p1_rA) | vm_cast_no_check (@eq_refl _ p1_cA)
      | exact HR | exact HK | constructor | constructor | exact Hh | exact Hlazy | ].
    clear HR HK. intros RA MA HR HK EQA LFA.
    pose proof (log_covered_frame (ENV vals) M p1_regions _ p1_covA RF LFA) as FA. rewrite <- EQA, RD in FA.
    change (s_regs (fst (fst p1_rA))) with p1_srA in HR. change (fst (fst p1_cA)) with p1_knA in HK.
    change (s_pc (fst (fst p1_rA))) with 0xe390c%Z.
    eapply (rz_ioctl_winsz RSEGS _ _ _ model ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | exact Hh | exact Hlazy
      | regv HR (17 : reg); reflexivity | regv HR (10 : reg); reflexivity
      | change (bv_unsigned (Z_to_bv 64 1)) with 1%Z; lia | exact Hfd1
      | regv HR (11 : reg); reflexivity | ].
    rewrite v_addi_pc4 by lia. change (0xe390c + 4)%Z with 0xe3910%Z.
    pose proof (regs_set_a0 (ENV vals) _ _ (errno_ret ENOTTY) (ELit (2^64 - 25)%Z) HR
                  ltac:(cbn [edenot]; apply bv_eq; reflexivity)) as HR'.
    clear HR. change (sr_upd p1_srA (ridx 10) (ELit (2 ^ 64 - 25)%Z)) with p1_srA' in HR'.
    eapply (rz_run_lf RSEGS FUEL1 STOPS1 scr0 0xe3910 p1_srA' p1_knA 34 (fst (fst p1_rB)) (snd (fst p1_rB)) (snd p1_rB)
              (fst (fst p1_cB)) (snd (fst p1_cB)) (snd p1_cB) (ENV vals) MA (seg_rom RSEGS) _ model);
      [ vm_cast_no_check (@eq_refl _ p1_rB) | vm_cast_no_check (@eq_refl _ p1_cB)
      | exact HR' | exact HK | constructor | constructor | exact Hh | exact Hlazy | ].
    clear HR' HK. intros RB MB HR HK EQB LFB.
    pose proof (log_covered_frame (ENV vals) MA p1_regions _ p1_covB RF LFB) as FB. rewrite <- EQB, RD in FB.
    change (s_regs (fst (fst p1_rB))) with p1_srB in HR. change (fst (fst p1_cB)) with p1_knB in HK.
    change (s_pc (fst (fst p1_rB))) with 0xe2ee8%Z.
    pose proof p1_itinerary as (_ & _ & _ & _ & _ & _ & SC & _).
    apply (stdio_call_sound_post vals (blobs_ev []) p1_srB p1_knB RB MB model p1_sc [Z_to_bv 8 48] [Z_to_bv 8 10] K
             HR HK (eq_trans (f_equal (fun n => stdio_call n p1_srB p1_knB) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn p1_sc length edenot ev ENV Z.of_nat Pos.of_succ_nat Pos.succ].
    - unorm. lia.
    - unorm. lia.
    - unorm. lia.
    - first [reflexivity | unorm; reflexivity].
    - lia.
    - left. unorm. rewrite P0, alu_add, vadd_wZ. unorm. lia.
    - left. unorm. rewrite P0, alu_add, vadd_wZ. unorm. lia.
    - unorm. lia.
    - first [krd_solve HK | unorm; krd_solve HK].
    - first [krd_solve HK | unorm; krd_solve HK].
    - exact Hfd1.
    - exact Hrdr.
    - exact Hh.
    - exact Hlazy.
    - exact HKnil.
    - clear HR HK. intros Rj MC HR HK HPOST.
      assert (FC0 : frame_mod MB MC p1_regions_w).
      { eapply sw_post_frame_mod; [exact HPOST|]. intros x Hx. unfold p1_regions_w in Hx. cbn [outside] in Hx.
        unfold in_rng in Hx. rewrite P0, alu_add, vadd_wZ. revert Hx. unorm. intros (N1 & N2 & N3 & _). lia. }
      set (vals' := vals ++ junk_vals Rj) in *.
      assert (HL' : length vals' = 66%nat) by (subst vals'; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (P0' : vals_ev vals' 0 = sp0) by (subst vals'; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      pose proof (p1_regions_flat vals' P0' ltac:(lia) ltac:(lia)) as RF'.
      pose proof (p1_regions_denot vals' P0' ltac:(lia)) as RD'.
      change (Env (vals_ev vals') (blobs_ev [])) with (ENV vals') in HR, HK.
      eapply (rz_run_lf RSEGS FUEL1 STOPS1 scr0 0xe3930 (sc_sr p1_sc) (sc_kn p1_sc) 66 (fst (fst p1_rC)) (snd (fst p1_rC)) (snd p1_rC)
                (fst (fst p1_cC)) (snd (fst p1_cC)) (snd p1_cC) (ENV vals') MC (seg_rom RSEGS) _ model);
        [ vm_cast_no_check (@eq_refl _ p1_rC) | vm_cast_no_check (@eq_refl _ p1_cC)
        | exact HR | exact HK | constructor | constructor | exact Hh | exact Hlazy | ].
      clear HR HK. intros RC MF HR HK EQC LFC.
      pose proof (log_covered_frame (ENV vals') MC p1_regions _ p1_covC RF' LFC) as FC. rewrite <- EQC, RD' in FC.
      change (s_regs (fst (fst p1_rC))) with p1_srF in HR. change (fst (fst p1_cC)) with p1_knF in HK.
      change (s_pc (fst (fst p1_rC))) with 0x47390%Z.
      apply (HCONT Rj RC MF HR HK).
      eapply frame_mod_trans_same; [exact FA|]. eapply frame_mod_trans_same; [exact FB|].
      eapply frame_mod_trans_same; [exact FC0 | exact FC].
Qed.
End First.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable model : ltac2:(zQ "10!lge$0").
  Hypothesis Hh : ltac2:(zQ "60!ir3!it7!kp4!im5!htd!lh7@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!ir3!it7!q7!h8!k1!htd!li3&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd1 : ltac2:(zQ "90!ir3!pte!ko9!ilf!im5!htd!pu9!pv6!qg3@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+1@2$3$1@1$6@2$2@1$0#k0+1").
  Hypothesis Hrdr : m_channel_reader model = true.

  (* [comment removed for export] *)
  Record p1H (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z) : Prop := P1H {
    Q1  : getr regs 1 = Z_to_bv 64 0x47390;
    Q2  : getr regs 2 = sp;
    Q11 : getr regs 11 = Z_to_bv 64 0;
    Qsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    QspLo : (0x100000500 <= bv_unsigned sp)%Z;
    QspHi : (bv_unsigned sp <= 0x7fffffffffff)%Z;
    Qstk  : stk_ok RSEGS mem sp 1232;
    Qimg  : forall i, (0x10000 <= i < 0xf4000)%Z -> mem (Z_to_bv 64 i) = None;
    Qcells : cells_ok mem p1_cells;
    Qcan  : rdn RSEGS mem (Z_to_bv 64 0x12ec38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Qcan64 : (0 <= can < 2 ^ 64)%Z }.

  (* [comment removed for export] *)
  Record p1Post (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := P1P {
    P_sp  : getr regs' 2 = sp;
    P_ra  : getr regs' 1 = Z_to_bv 64 0x47390;
    P_a0  : getr regs' 10 = Z_to_bv 64 2;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    (* [comment removed for export] *)
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1232), 1232%Z); (Z_to_bv 64 0xfcfd8, 232%Z); (Z_to_bv 64 0x12f3e8, 1%Z)];
    (* [comment removed for export] *)
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0xfcfd8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0xfcfe0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0xfcfe8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0xfcff8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12f7e8));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0xfd000) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12f3e8));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0xfd010) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12f3e8));
    P_write : rdn RSEGS mem' (Z_to_bv 64 0xfd020) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xe2ee8));
    P_buf   : rdn RSEGS mem' (Z_to_bv 64 0xfd030) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12f3e8));
    P_bsz   : rdn RSEGS mem' (Z_to_bv 64 0xfd038) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
    P_fd    : rdn RSEGS mem' (Z_to_bv 64 0xfd050) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
    P_mode  : rdn RSEGS mem' (Z_to_bv 64 0xfd060) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0xfd064) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lbf   : rdn RSEGS mem' (Z_to_bv 64 0xfd068) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0x12ec38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp 1232 }.

  Definition p1_vals : ltac2:(zQ "50!ir3!it7!h8!j7!jk6>4regs@2$4@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3can$3@1$2@1$1@1$0#k0") := ltac2:(zQ "90!ir3!it7!jb!hh9!k1!j7!jk6!ose!ko9\4regs@2$6@1$0#5@1$1@1$0#k0\2sp@1$1@1$0#k0\3can$5@3$3@1$1@1$0#k0@3$2@1$1@1$0#k0^2@3$2@1$1@1$0#k0@2$8@1$0#k0^1@1$4@1$1@1$0#k0@1$7^3").

  Lemma p1_ev_junk : ltac2:(zQ "h00!ir3!it7!k6!hu3!htd!pi5!pk0!pk6!j7!jk6!pkc!pl4!pl9!pr8!ps3!ko9>4regs@2$9@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3can$8>1i$2>0@2$3@2$6N2^1@2$7^1Ni2@3$4@1$1@1$0#k0@2$b@1$c@3$d^5^4^3^2@2$a^5@2$f@1$0#5@1$e@2$5^2N2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["Plain"] "##Iih04__p1h14__p2h24__x1h34__x2h42H2h53Hi0h67__arithh74__ffh84__p3h98__varmaph:5__with;4cstrh<1ih=1nh>1xh?2z2h@1HhA2HihB1bhC3canhD7defaulthE1lhF5lemmahG1mhH4regshI2sphJ1yp&0p;1p;2p;3p;<p;6p;4p;=p;9p;5p;Bp;7p;8g003\j1<Tg0037j1lTg00]Uj1OTg00^3j1`Tg000Nk20ITg008iR0j12Tg02UeR1j2WTg02bUR2j2!sG$ABj20Tg03Mmj2[Tg005Aj31j1JTg01nAR3j13Tg006=j1KTg01C[j27Tg01F]j2A!sL$ak20;Tg01oDk305!s~$]j2;Tg02Jll<PTg01DbR4j26Tg01E>R5j24Tg02Vej6dTg033;j4g!sj$aj1jTg03NDj2kTg01V8j2H!s8$fj2FTg03OOj3GTg03P8j2LTg00:Pj1m!s8$dk20!sT$QEk30GTg004aj1]Tg00GEj3!tm$4Aj1\Tg01YFk20FTg01_5k10ETg02]Xk40D!sD$dk10CTg01ZBk10>!s0$mj2iTg01[Pj2CTg02KQk30=Tg01`Zj4@Tg00h:k10<Tg01aij3eTg01\Vk20:Tg01]8k20!va$]dk304Tg01^Ck40!wn$L4j4_Tg014Nj28Tg01hFj2VTg02`Qj2T!uQ$nk100!sB$fj1UTg01ilj3NTg03R^j4?j1zTg03S:j4Q!s/$aj1~Tg03TPj4RTg03UGj3{Tg03V=j1y!s/$lj6}Tg03WWj2MTg03XCl=xTg02<_j2DTg03Y0m901!s0$jj2wTg01>Aj4vTg03ZFk60!yB$2Yj6^Tg03[Nj5uTg01Lik206j1tTg02E8k108Tg02G8k209Tg03\0j2hTg03]3j3sTg01Mkj1rTg03^?j2qTg034GmB0?!yC$bm<0@Tg020Fj6p!w-$Ek70!zM$bLk70B!s`$\j7oTg01c0j8nTf0R6#2!s$%p=9%26#2p=|g00OeR7/q6p==g00HnR8f1R9;16p=>g0174R:P:P:P8P8P8g03_@P3P3P3f6R;g03_`f5R<f4R=f3R>f2R?P9P6NB0?p=b!s_+0!sZ$>g03`GP!sH%<0@p=a!sF$1P3P4g038oP<P=P>!sH%M<Pp=c!sG$2P3P5g039Q!sG4SA1867p=ZP9g01cTR5g01d3R2P2g01dSR4P6Epp=YP8P9g03IMP6C@p=XP9P5P2P2P4P6g01eZK0Ap=:P?!s=+9P6K0Bp=B!s:1Fop=fP>!s9+!tZ$Gnp=Eg00LHR5#<R1#l#OR0%<1#<R@#<#<RA#<#ORB#`RC+0Ig00OFRD#2RE#2RF/W6%2FRG#2#9!s$/RH#|RI,I6'01[9FRJ#2RK#2RL=1:9%39RM%K1RN'7#=RO%K5RP'ARQ/APRR/>MP:P8%J:RSP3%J8%36R3,>MA1:9620;96405XJ:X>:PLPR1A6PX>8RRPKPQPRPJPO1796#=XG8X=8ROP9PM1;8MRRPFPN1;8NRQFbCaCaP9PMPRM<P1WF9RK1I9IRL'016NMRT%l@#<#KRU,4MRV'0RWPKPLPTPVPFPNPQ!sc%Ec!s-%PIPU1;8URRESEdP6CgPW%j?%3?RW,67%3>RM/7NRV,k7147V%=VRT/>V'016V7%ZT'0'H%3=/7NRT#=RVP8p-0RLg01gZRK1F8FRX1F8E1F8DRE5G85G8g03`kRY'LRZ1F8G%m5-0H8>0G8X=G8E!sM$/LY1LEY%]KRE55K55K35%\KRYP820F8?P9&0E8H0DRX&0C8RG&0>8R[1Y[=1i85R51i81R11C8NR\60=8R]'X,:[5B[R^P8P]g01e3R]1C87R_C@,:[1X5_,:[R_5B[5f[&0<2R2P[P8P\P]P1!sJ%Y[<R]5B[P21C8PR\9e85=e8\/X1,:[CECE20:[4R4P6P?g00ScR\g01:PR`';2076?=1\`dB04879H02R`b7b9b:X28X38X0LW1179NR\,>6,0?Ra16\7%Z6R\'0'H16N?/0=1A?P/AP/>>[[^28^38^0L^1LP6%3;RP/4U17PN,47PPP9P?P=O6b6b?b4b;b5C_18B?%]CRP55C95C>Rb,VC/TJ=1:9RcePc18B>=5CP95C=Rc,VC1[?FRd'TRe=1:?PC%JCRf&00CPCP>18B=!sT&<RP%U;5NCRg18B7RBC?PC1VCP1[>FRP'TRhPgPBC?%\CRiPC^DCRj]ERk^=:RlP:PkPSPiPj%JiPCPCPfPfCQRmCQRnCQRo!sG$nPiPjPm!sF%%~CCRCRCR9{lo%zCP>PhP:PS%y:PhP>P6E}PgPg1MigPBPB1MCBM=x%3P,80,D;RPPP1MCPN901WFP6!s{$d%U<RiPBC?RgA1C6PXBCRPPC%3d!s\$<RhPP1;ChPCPdP:PC1803,D;X<:R31wDHCvP!uo$P3PdPHPB1IdH17WN#=R3%KARA'4PdP3POP?PW1;8WRO!}R%FbPHPA1;8AES1WF?RH1I?IR3!~:$WRD14WURP'0RSPHP3PDPP!~2&?PWPOEc!s-%PIPUP!~-%9CgPS%j>167M1k7T147T1>VT'016T7%ZV!}u%</7N#=P8A5KZEPYPXPGP[AB[]_9f[^P2P[1Y[;P8P1g01f:!|e$U!{v$!{p$P8P5P11C8A!s:$CECEP4P!{?3X1LX8L10>\,Ha14?U,0<14?A!{%1^8LP6f7#3R6,6N176NRN/67147NP6!{3&7!{3/J03E^A1CghePCPeANCci!wE&cPiPBPdDuE^O2b@%U=9NCbRb0069%3J!x;$=R051Ce%tb%O@#`#\#]$08+09/h9=1C0eAs=>?#r!s5'WAX<:XC8XICWHo"). Qed.

  Lemma p1_regs_ok : ltac2:(zQ "a0!ir3!it7!im5!j7!jk6!kn1!pl9!psd!pr8!pg0>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2sp@1$1@1$0#k0>3can$3>0@4$7^4^3^2^1@3$5@1$6@3$8^5^3^2$9^5").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["Plain"] "#$Top'0h02Hih11ni001nh27__arithh34__ffh48__varmaph55__with61bh71ih82Hah94__p1h:4__x1h;3Hi0h<2PHh=3Q12h>2Q3h?2Q4h@5Qcan0hA6Qcan65hB7Qcells0hC5Qimg0hD5Qsp17hE6QspHi0hF6QspLo0hG5Qstk0hH7__sat66hI!s0&7hJ!s0&8hK3canhL4cstrhM3memhN4regshO2sphP1xi012Q1i023Q11i032Q2i044Qcani05!th%4i066!ti%i074Qimgi08!ti$6i095!tj$i0:5!tj$i0;4Qstkp%0p&0p;1p;2p;4p;3p;6p;<p;7p;5p;8g003\j1FTg0037j1=Tg00]Uj1]Tg00^3j1`Tg000Nk20DTg005[j1lTg03aWR0k40:Tg00cWj3|Tg006=j17Tg014Nj2STg01D8j2WTg03baj2i!sh$Aj3K!sA$bR1j26Tg03cAk402Tg01E>R2j25Tg00ABj22Tg00h:j1fTg03dBj2xTg004Aj1cTg008iR3j10Tg01H?j4tTg01JAj2qTg00@`j2pTg01W]j2oTg02bUR4j21Tg02:3j3\!u&$[j1nTg03eJk10CTg03R^j4TTg03]3j3bTg03\0j2mTg02UeR5j2ATg02Vej6@!t\$ak10?Tg01_5k10>Tg01Ydk10<Tg01ZBk10;Tg01\Vk209!uQ$]j2^Tg01]8k208!s0$dk30!vZ$^Ck406Tg01nAR6j1XTg01F]j2VTg033;k405Tg01oak104Tg03fOk203Tg01X:k201!s0$bk30!v7$YFj2~Tg02]Xj4eTg01[Pj2d!tj$mj2{Tg020Fj6yTg03g@j4wTg01Mkj1aTg02<_j2QTg01P:j2_Tg03Mmj2vTg02Jll<hTg01`Zj4YTg01aEj7ZTg01bLj7uTg02L4j4sTg03hUj5rTg002Yk60=!uB$bl<j!s]$ij3[Tg01c0k80ATf2R7f1R8f0R93b#ap=8%=9#=p=R%F9#Fp=O%=!s-$P%F9#7p=If4R:f3R;g03FRR<9\78'Q;K9p=;A\89<p>0@1Q78=K;9p=k!sm$#F#Fp=L!t%$!s$/p=Ug00OeR=/69p=JAb:;7#ag00J8R>P8g03<JR?P9CT'_p=3f5R@P;P7g03idRAP8CT,Q:!tK$41Q;7%a8/_95K:p>0Bf7RBf6RCP@P:PAP;CT'QP>P8P!sv$,_73Kp=<1v89#X,S7,Q;p=Dg00HnRD/^9p=:g0174REPDP5P6P1g038o!st$;P7P8P9M<hp=CPEPDP4P6P2g039Q!sG4>1dD9p=9PCg01cTR2g01d3R4P4g01dSR1P@P2P4P4P1PDP:g01e3R5P;CYg01eZRFFZP7!sH-8g01f:RGP9CYPFFZFup=BPBPC!tH/CsDrp=E!s=%1^:;1m78P9J0=p=?1V:;/V7/V8/V9p=GPE!u:$DP3P6P6PCg03`GRH!sv$!sA1;PH!uP'jM<jp=H!ti1P5!td'p=zA[D:;=[D7=[D8=[D9p=N!sU2!u;+p=}P;!sA+!t1$L0Ap=g%09#0#0#0p=Mg00LHRF#FRG#=R5#]RH%FGR6#FR3#FS00#FS01#FRI#]RJ#`RK+0D%]3#`RL#lRM\K!v='H0:P0!vL'A8@;7?|?@P9PKf?R0PH%7FRN%=3S02#R#O#=!s+$P#O#I,SJD;PKf@RO%7GRG-0@HRPf>CkPKfARQPH%=5S03#7RR1SJ=D;1WJOQ00#7RS'i=KD=%OI#L#LRT#F#L#P!s~$L#I1WJQ'6fB,WJ%=FRF#=S04#=S05#=S06#R#U!s$+7'6g01KbRQfDfC%=6S07#=S08#F!tu%H02%7T/69Q05#FS09#P#L!s$$I,59'2fGRT1SJ8O1%fL5KM[^7DfFRMg03k4'x%cLRL#lPQPTQ07#FS0:#R#P#R#L!v'&I,SJg00OFRQ#0RU#0RV#0RW#0RX#0RY#0RZ#0R[#0R\CtfE,SJ,q\,pL3K%JM%7IRI,oGS0;,5M'2fJRMfH;8TP?PM%0\RT#0RL#0R]#0R^#0S0<#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk#0Rl#0Rm#0Rn#0Ro#0Rp#0Rq,19RrPEPKfNRs%`HRtP8A\H=<R<PsfLRufKRvP8%n=RwD3E4^0rP811QqfMRr$0CPKPrPtPQPAP<CTAbrvMP>PQP?PwCTI0BeW0PE%09R?/1qPKfPR>Pt%08S0=P<P>PsPrQ0=P!t&$]0P911UqP0PKfOR0PtPUP<P0PrPuPU!sJ%!sv&?!sv'RRUPtQ0=#0S0>P<PUP>P0Q0>!sx/VqPOPKfQROPPA8O0sR0/mQCkePKPOPtPV!t3$VPwG<!t,'S0!t-&TR?PtQ0>#0S0@P<P?PUPOQ0@!t-/WqPKfSR0PHPYPVCDRQPKP?!|I$P9D;X6KPKPQA80O>S0APYP0POP>PY1AVYR>%0q!yN$s,1YRP'2%75Ru,6GRrQ02#IRv,5uRM'2S0BP>PPPrPMPVPG%:GRMPYPu%:uRrECPYPuPrPsPv%:vRrE>E@g01gZRP$0?R>%cPRP&0>DRA&0<DRx&0;DRyPy%9GRz%9uR{PyP{%9vR{FB209y1R|P9P7g00ScR}g01:PR~'^20897=K}~dB07D=8H06R~b3b4b5Q0BP9b2GEG?PKP0PtPWP<Q0APW!vy+Q0?#0!v{+VRWPtQ0@#0S0AP<PWP?P0Q0A!v{/XqPKfUR}PHPZPVCDS0BPKPWPH%76!v|+Q0BA8}0US0BPZP}P0PUPZ1AVZS0C11ZsS0D'2%FFRF#7RU,6GS0E15UvR0'2S0FQ0CQ0DQ0E!xu$GPMPZPU%:UR0ECPZPUP0PsPvP!vs$!wJ$APxPyPyPz%9UR0PyP0P{FBP|P!v$+F!v$-}PtPXP<Q0BPX!v$:XRXPtQ0A#0S0BP<PXPWP}Q0B!v$/YqPKfW!y}$[!v$%FPKPXPHPu!v#-FA80}?S0FP[P0P}P?P[1AV[S0E11[!v#%Q04#7R?,6GR}15?vRu'2S0CQ0EQ0DP}Pu!u{&[P?%:?RuECP[P?Pu!u{=?RuPyPu!u{3C!x}2YP<Q0FPY!u{:ZRYPtQ0B#0RuP<PYPXP0Pu!uy/ZqPKfY!x{$\!uy,YPHPU!uy1}0WS0FP\!xz$WP\1AV\!xz$\sRW'2%73R3,6GR0153vRU'2S0DQ0CPW!yQ$!uu%\P3%:3RUECP\P3PU!uu=3RUPyPU!uu3D!xr2Z!uu%Z!uu1RZ!ut%\RUPt%0uR0P<PUPY!u1$!ur-[qPKf[RWPHPT!ur%?PKPUPHP?!ur-?A8W}XS0?PTPWP}PXPT1AVTS0F11T!xm'7#7RX!xm&XvR?'2S07Q0F!xm%?!uv&TPX%:XR?ECPTPXP?!uv=XR?PyP?!uv37!uv-WPtP[P<Q0?P[!#6g,Z!ut'^R[Pt%00R?P<P[PU!~j$!ut-\qPKf]!xh$L!ut,[PHP3!ut1}WYS0?PLP}PWPYPL1AVLS0711L!~d'5R5#7RY,6GRW15YvR3!~c&7Q0DPWP3!uv&LPY%:YR3ECPLPYP3!uv=YR3PyP3!~bC\!uv%\!uv7`R\Pt%0?R3P<P\P[P}P3!uv/TqPKf_!xl$]!uv,\PHPX!xl3US0?P]!xl$UP]1AV]!xl$]sRU'216GRR}15RvRX!{\&FPU!y?$!ul%]PR%:RRXECP]PRPX!ul=RRRPyPR!{\?WPtPT!ul%T!ul7bRTPt%03RRP<PTP\PWPR!ul/LqPKfaRXPHP^PVCDR}PKPTPHPY!uk+P}A8XW[S0?P^PXPWP[P^1AV^S0D11^sR[!#8G$W#7R},6GRY15}!~P&!{V$[PY!~P+^P}%:}!~P$^!v\$!ur<}!~P9!x`/XPtPL!ur%L!ur7dRLPt%0RRUP<PL!|q$U!ur/]!#@D$cROPtP]P<POPXP\P]!#A>/!st+fR]Pt%0UR\P<P]PLPOP\!st/^qPKfe!vh$_!vh$YPKP]PHP}!vh,YA8XOTS0?P_PXPOPTP_1AV_!yT$_sRT!#90$FRO!|M'}!|M$['2S04Q0FPTP}P[!vj&_!|L%[ECP_PYP[!|L?[PyP[!vj34!vj2^!vj%^!vj7hR^Pt%0\R[P<P^P]PXP[!ut,Q0<!sM%gR}PHP`!uv$TPKP^PH!#J}$7!u{,TA8}XLS0?P`!{|$LP`1AV`S0411`sS0F'2Q05#7RL,6GRX15LvRT'2S05Q!u{%XPT!uy&`PL%:LRTECP`!xP$!uy<LRTPyPT!uy35!#3G0Q0<!uz$Q0<!u{/S!uU'jRZPt%0[RTP<PZ!{%$T!xr/_qPKfi!xr$a!#3J+Z!|]0Q0?A8X}]S0?PaPXP}P]Pa1AVaS0511asR]'216GSR}15SvRY!|V&5P]P}PY!uo&aPS%:SRYECPaPSPY!uo=SRYPyPY!|VC_!xj%_!#<$,<#0R_!un%lRYPt%0TR}P<PYPZ!u,$!un-`qPKfkR]PHPb!un%<!#>t%L!un-<A8]X^S0<Pb!yW$^Pb1AVbS0?11b!xg'2#7R^!xg&^vRL'2S02!wY$F!yB$!uv%bP^%:^RLECPbP^PL!uv=^RLPyPL!uv32!uv-]PtP`P<Q0<P`!xe-_!ut'nR`Pt%0}RLP<P`PY!~\$!ut-aqPKfm!xd$c!ut,`PHPS!ut1X]ZS0<PcPXP]PZPc1AVcS0211c!ut':#7RZ,6GS0:15ZvR]'2S0?Q02Q0FQ0:P]!uv&cPZ%:ZR]ECPcPZP]!uv=ZR]PyP]!uv3?!xn2a!uv%a!uv/!{]+pR_Pt%0LRaP<P_P`PXPa!uw/bqPKfo!xm$d!{],_PHP^!{]1]XYS0?Pd!xm$YPd1AVdS0:11d!uw'8!#5P&X15YvR^'2S08Q0:!xm%^!uu&d!#5Q$^ECPdPYP^!#5Q>^PyP^!uu38!xm2b!{e%b!{e1!uw+rRbPt%0aR^P<PbP_P]P^!uw/cqPKfq!xp$e!uw,bPHPZ!~V2]`S0?Pe!xp$`Pe1AVeS0811e!uw%%I5R`,6GR]15`vRZ'2S0:Q08Q0F!yI$!uu%eP`%:`RZECPeP`PZ!uu=`RZPyPZ!uu3:!xl2c!uu%c!uu:tRcPt%0^RZP<PcPbPXPZ!uu/dqPKfs!xn$f!uu,c!#5M4]X_S0?Pf!xn$_Pf1AVf!xn$fsR_'2%=5#7R5!xm&5!#5S+:P_!yG$!uu%fP5%:5RYECPfP5!#5S>5!#5SD]PtPd!uu%d!uu1Rd!ut%v!#5S$ZRXP<PYPc!u3$!ut-eqPKfuR_PHPg!#5S0`!~]1_]bS0<Pg!yV$bPg1AVgS0?11g!{d'3#IRb!xm&bvR`!xm&?!xm%`!uv&gPb%:bR`ECPgPbP`!uv=bR`PyP`!xm?_PtPe!~[%e!~[-d!ut'xRePt%0XR`P<PePY!~^$!ut-fqPKfw!xj$h!ut,ePHP5!ut1]_cS0<PhP]P_PcPh1AVh!xj$h!ut,=#7Rc,6GR_15cvR5'2S03!~\&_P5!uv&hPc%:cR5ECPhPcP5!uv=cR5PyP5!uv33!xn2f!uv%f!uv7zRfPt%0`R5P<PfPeP]P5!uv/gqPKfy!xl$i!uv,fPHPb!xl3YS0<Pi!xl$YPi1AViS0311i!~Y'W!#5P$]15YvRb!xj&3!xj%b!ur&i!#5P$bECPiPYPb!#5P>bPyPb!xjCg!ur%g!ur7|RgPt%05RbP<PgPfP_Pb!ur/hqPKf{!xj$j!ur,gPHPc!xj3eS0<Pj!xj$ePj1AVj!xj$jsRe'2%=W#7RW!xg&WvRc!~V+e!yC$!ur%jPW%:WRcECPjPWPc!ur=WRcPyPc!~VCh!ur%h!ur7~RhPt%0bRcP<PhPgP]Pc!ur/iqPKf}!xf$kPVCDRePKPh!#MO0eA8_]fS0<Pk!xd$fPk1AVkS0F11ksRf'2%IFR],6GRe15]!#5F%!{T$f!|z$!un%kP]%:]RYECPk!yR$!un<]!#5F8!xb3i!un%i!un6p+01ARiPt%0cRYP<PiPhP_PY!uq/j!sN&@RePHPl!ut$fPKPiPHPW!ut,fA8e_gS0<Pl!x5$gPl1AVlRg11l!#8=%F#7RF,6GRf15FvRW!uu$PgP_PfPW!ut&lPF%:FRWECPlPFPW!ut=FRWPyPW!ut?ePtPj!ut%j!ut:CRjPt%0YRWP<PjPiPePW!ut/k!sN&BRfPHPm!ut$_PKPjPHP]!ut,_A8fehS0<Pm!x;$hPm1AVmRh11m!{[%IOR_!~N&_vRg!ur%hPeP]Pg!ur&mP_%:_RgECPm!v`$!ur<_RgPyPg!ur?fPtPk!ur%k!ur:ERkPt%0WRgP<PkPjPfPg!ur/l!sN&D!~R$n!{^+kPHPF!{^0]fiS0<Pn!{\$iPn1AVnRi11n!{]%=O#7RO!{_&OvRF'2RhPi!vH$F!us&nPO%:ORFECPnPOPF!us=ORFPyPF!us1Ph!~L2l!ur%l!ur:GRlPt%0gRhP<Pl!|x$h!ur/m!sN&FRFPHPo!ur+lPHP_!ur0F]jS0<PoPFP]PjPo1AVoRj11osR]'2Q09#7Re!#5C%evRf'2Ri!#5r%f!ur&oPe%:eRfECPoPePf!ur=eRfPyPf!ur2i!ur-FPtPm!ur%m!ur:IRmPt%0hRiP<Pm!|v$i!ur/n!sN&H!{Z$p!{Z+mPHPO!{Z1FkS0<PpPfPFPkPp1AVpRk11psRF'2Q06#7!{\%O!{\$]'2RjPkPFPO!#LJ'p!{[%]ECPpP_!#LJ>_!#LJ6Pj!{Z2n!ur%n!ur:KRnPt%0iRjP<Pn!}d$j!ur/o!sN&J!{Z$q!ur$OPKPnPHPe!ur,OA8]flS0<Pq!{Z$lPq1AVqRl11q!{Z$Q01!{Z5kPl!{Z0q!{Z,q!{ZCePyPe!ur2k!{Z2o!ur%o!ur:MRoPt%0jRkP<Po!}d$k!ur/p!sN&LRnPHPQ!#88'o!{Z1fA8n]mRfPQ!si$mPQ1AVQRm11Q!{Y&0#=!xg'H!xg$o'2RlPmP]!|Z%!us$Q!xg%MECPQP_PM!xg?_PyP_!us2l!us-nPtPpP<PfPp!ur&%0d/1q%0k!uv$%X8RpPN!s$%DG!s0i/5OS00Pd1V9NXPDRdP!s$apO1S0<O1S01O1S06O1S09O1S0:O1S0FO1S03O1S0?O1S08O1S02O1S05O1S04O1S0DO1S07O1S0CO1RfO1RnO1RlO1R{O1R_O1RzO1RrO1RvO1RsO1RMO1RQO1RVO1RoO1RHO1R]O1RmO1PdPkPmPdPjP]PdPiPHPdPhPoPdPgPVPdPWPQPdPYPMPdPcPsPdPbPvPdP5PrPdP`PzPdPXP_PdPZP{PdP^PlPdPaPnPdPLPfPdP}Q0CPdPTQ07PdP[Q0DPdP\Q04PdPUQ05PdPRQ02PdP3Q08PdP?!#Nv$0Q03PdPuQ0FPdQ0BQ0:PdQ0AQ09PdQ0@Q06PdQ0>Q01PdQ0=Q0<PdP8Pp%:pFH!s$A!}?%E>P9H05Q00&047%X7#Jp+01N,WJRF003S%JF%JSp+01P,WJ/iS#J[[201GI15=G%JIQ0;,5=[[%JGRSg01g>RJB00GI8UW8Q0;#J\J^8Sp-0RS!{V$DPD1~D8P8PACe!s+&xPy1dD=1{D6R65zy%f4R=PyP6%9NR6P!s$$DNP!s0h=}yeP=Py!$5@';EyCgCg!}$,X:DW9%J9P8!|XvP;[[^:D^9SP9!#44$TRSPt%MB#M!s$/RtP<P!w?$Rp+01QPt!#4p$%XBP:P@O4b2bHbIbJbLb;W0X7EP9O1n0110001020111100X1!s>_0!s>~!s>~!s>~!s>~!s>R0!t-~!s>~!uN\!s>AP9O1!{l$CwWAW@WBWCWGWEWFWDW=W?W>f:f9f8!$C&2O;n40!{g$!s#$1;110110310210810:10910;107106104105W<XKDXOKWMWNo"). Qed.

  Lemma p1_know_ok : ltac2:(zQ "b0!ir3!it7!im5!j7!jk6!km6!pl9!psd!pr8!oud!opc>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2sp@1$1@1$0#k0>3can$3>0@4$7^4^3^2^1@4$5$a@1$6@3$8^5^3^2^4$9").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["Plain"] "##Y~p'0h07__arithh14__ffh28__varmaph35__with44__x1h51mh61dh76__sat0h8!s/%1h97!s/$66h:!s0&7h;!s0&8h<1zh=1xh>2Hah?4__x2h@1bhA4cstrhB2E0hC2E1hD2HdhE2HmhF3HsphG2PHhH3Q12hI2Q3hJ2Q4hK5Qcan0hL6Qcan65hM7Qcells0hN5Qimg0hO5Qsp17hP6QspHi0hQ6QspLo0hR5Qstk0hS2Z0hT3canhU1ihV3memhW1nhX4regshY2sphZ1yi002Q1i013Q11i022Q2i034Qcani04!tP%4i056!tQ%i064Qimgi07!tQ$6i085!tR$i095!tR$i0:4Qstkp%0p&0p;1p;2p;4p;3p;6p;7p;9p;8p;<p;@p;5p;Bg003\j11Tg0037j15Tg00]Uj1TTg00^3j1rTg000Nk20OTg005[j1hTg03aWR0k40=Tg03]3j3KTg01Mkj1MTg00dej4fTg006=j17Tg02:3j3YTg02<_j2\Tg014Nj29!sz$Aj3;Tg01D8j28Tg03baj2O!s8$bR1j20Tg03cAk405Tg01E>j2<Tg00ABj24Tg00h:j1dTg03dBk200Tg004Aj1_Tg008ij1>Tg01H?j4gTg01JAj2lTg00@`j2jTg01W]j2vTg03lAj1t!t%$]j2ETg03\0j2]Tg007bj1qTg00:nk20YTg00<7k30X!s:$Pk10WTg009Hj2[Tg00=@j2oTg00>Ik20V!v'$[k10UTg00Gek30N!tv$aj1mTg03mGk10MTg01m1k30Lk40FTg01_5k10ITg01Ydk10HTg01ZBk10GTg01[Pj2iTg01\Vk20ETg01]8k20D!s0$dk30ATg01^Ck40@Tg002Yj6ZTg01P:j2VTg03nOk70<Tg03fOj2eTg01X:k20!wY$Xbk30:!tL$Fj2^!tK$mj2bTg03oVk707Tg040]m906!tU$3k304Tg041ek803Tg02UeR2j2aTg02L4j4UTg01F]R3j22Tg01nAR4j1JTg02JNk102Tg02Mfk401!s:$ll<cTg042jl@~Tg0440j4STg01oaj1}Tg02]Xj4|Tg0450k50>Tg00B7k40?Tg046Dj2{Tg01O3k10BTg01QAk10CTg01VRj3zTg047Hj2yTg026[j2x!sh$Rj2kTg048Uj3wTg0491k50JTg04:;k60K!x8$Ej3uTg01`Zj4pTg01aEj7nTg01bLk70PTg01c0k80Q!sC$ik30RTg033bl<sTg034GmB0STg04;Fk60TTf0R5#1#1p=I%55#5p=A%55#1p=P%1!s6$?%1!sH$#1p==g00HnR6g00OeR77;5p=Q!sF+!s$'p=D!sr$!s$/p=L1075p=3g00K?R8f1R9;u5p=B1i65p=:P6P9g01f:P5Cpp=W!s4$cTR:g01d3R;P;g01dSR<P5g01eZR=Fnp=Xg00ScR>g01:PR?!t`$Hf2R@P:P;P;P<!s}&e3P5CpP!sZ$6P!sD,9P5K0Pp=Gf3R=!s<+@P9P5L0Qp=N1E65p=Cg0174R:P6P2P4P1g038of5R2f4RAP=!sW%M<cp=`B0R695p=@P6P7!sA'EZp=RP:P6!s$$4P4P2P!s^-sp>08!sC&!s$%3P5P9P@P3P=PAP2f6R3f7R4f8RBf9S00NB0Sp>09P8!sn,J0Tp=Fg00LHRC#1RD#5RE#TRF%1DRG#1RH#1RI#IRJ#TRK#rRL+0O%TH#rRM#hRN\L!sp'H0=P0!t#'g01KbR0AK2=@#MPAg03=TS01CfP5f?%7CROg03FRRP5YF'\%5H#A#I#A#P#?#=#7,9K5;Lf@RQ%7DRR=YFP'\f>RS5;LfART%5E#7!s<%19K7RP5;L18KQ%7IRI'O#Q%IJ#DRQ#=#?#?#D#7RF18KT'0fB,8K%5CRT#ARE#ARU#5#L!s$+7RV'0P0fDfC%5GRG#PRW#5#=RX#7RYH05%7QRQ/05%?E#I#=!t%$E,<5'4fGRZ19K9O1%dM5;N[^U6fFRNg03k4R[+00%_M!vT$\P0PZ%1G!uf$A#=!s-$I#7RG,9Kg00OFRZ#>R]#>!s$/R^CgfE,9K,l^,jM3;%3N%7JRJ,vRR_,<N'4fHRN#t18KNR`#31<`_'4fIR`,ELfKRa?K`N#M/]Z=;L`19K`RN,ELfLRbfJ;K`#M/]]=;LN1E6718KPRN#QfNR`?Kba#MRcfMRd%qZRe00YIRfB0XeFVRg&0WX,[e/oYRX20VQERh&0U7Ri/[G%q]S0280N^S03%IU!vP&U,[iRj%?T!x]$D#7RT'oRk%m8S04'BRl'BRm'BRn'BRo'BRp'B&0M[B0L0cdRqPfPpP0PcPdPePIg01gZRp#mRf%_pRp&0I6Rr&0H6Rs&0G6Rt1i67Ru%:I'W'X20Et<R<P5P@1E>?S0520D5@#HdB0A679H0@R?b1b2b31<7IP5b0PLPb18K5R>/OI#QX@Lf;1]cZRZP@EZ1Vce,8KRv!sC$eK0<PqPgPo!tp+FPV!sh$0F>10>V'4X@L18KbR>/eIRo%3>%3IR>18K`/OI#3[[Rg20;RJRw1<7R%3J1<7_Rx[[Ry%3RRzg01g>R{B0:RJ9UW>RJ%3_\{^>zRzPfPp1^69R{PsPt1b6CRC%:V56tR|%d;R;Pt%:F=6tCR}P;AGt}|CNCNP<P!uk&X46105V10F910F@10@V'4[[^46P5fPR|,8KR~f=PSO3b0b9b:b;P!u~%0Fv10vV'4eK07PqPXPn!uz+bPYP@PBPoPgPwPyPJP!tx$P!tt$P}P;%:YR}96tuA6t}C5Gt!tb4F5%3Y10Y9'4!t\%P~PSO2!tS'N906PqPhPm!tC&QPE!t1$rPs%:Q96tu!sw,%3Q!xG$!tY/!sN$E%:R>046KRR56t!sW,10E_P5b0b7b8P4L03PqQ03Pl!t:&iPPPGP^Q0219Ka1ELPP91a]^%7HRH,0ORPP]PO%COP^PH%CHR]E`!tC,O%:HRO!t>0PPP5b0CU1a^^10HHRPP^PHP]!s+%!sc,A6tOO!s]625GRP#3X<6!t5,G,@uRa!v#1127GRG#3!v+$NP5CR%J^Ri,2P/0_X<612GiRl/0_RE12GHRQ/0_RmP6P6P1P5X=6RhP11095$02XZ6X=6PlPQPh!s$$6P6g03J41295H01#CX56XW6PGPG%CGPiPHPhPh%J5#CX=:!uQ%J08N:09P_P_%C_M<c!wj31@aO=6tR!uk-m!w`'CUPEe!u=%P0P`19KPP^Cg19Kb!#64$5;\X<6P2!sJ%M@~PqPkQ04125UR\#31<\_%3TRM12\T/0_'4'4'4%39R\%J9,2@/0TR^P0fRRb12AU/2=,9KP@CS#H[[^5:^66'4!vV$7URP#31<P_12PT/0_,4M'4'4R`P0fQRE12P=Rm!sd+\^\\!sf%!zS5URa,@uRO96tu1WOR,Xt%:TR]!s6$@O]=6tR5Gt!s%%!v6-`!zp+EPmP@%}@Rm%J@#3R`18KERH/eIRh%3HfS,8K/OI#3\>[R>!}X5A6tuCP;1@OC!tU$a!}T2%3512P9RP,0U!}S&BP3!}S,bAPmP`PhP!t&161^6@P9PrC|!#4\%DRD,@C=6t]!t<$D%1W!#8r'W#:56!~v3X?61259/0T12P@/0W[^46^?6P5%J4PBP2!#4U+bAI0>XE^XD\X5:X66H0?PN!w53A6tuu1WuR,X!vm11077/4x!vr',{7CR&0BjR7,Vc,8K&0CjRx'2R?#31<?_12?!xe-P0PEfO9Kb|#MRb/V7,8K/2x!yW/!xq,'4eAzcjTP0PE1ybj!sL<!#4,%kH0Fe1x8qDF!s$,!s@$[Q051k6:/k6g04;g;w[#HdP3I0JJ0K!se%Q01CfebSbCbBbFWLWKWMWNWRWPWQWOWHWJWIf:Q00PBP4P3!#E^-O;n4000010!s#$1;110010210110710910810:106105103104WGXT6XYLWVWXo"). Qed.

  Theorem printf0_first : ltac2:(zQ "h41!ir3!it7!ko9!oqf!opc!jb!k1!im5!jh7!or8!jk6!joa!os3!js9!kh5!j7!lj0!ou3!psd!pt4&>0@1$1@1$0#k0@1$7@1$1@1$0#8>4regs@2$a@1$0#5@1$1@1$0#k0>3mem~0>2sp@1$1@1$0#k0>3can$f>1K$h0>0@4$h2^5^4^3^2>0@1^2@1$6$3>0>5regs'@2$a@1$0#5@1$1@1$0#k0>4mem'~0>0@6$h3^9^8^7^6^2^1@4$e$4$d@2$8@5$b?2fx^3@2$2@1$0#k0+knjp0^2@1$c$4?5model^6@4$e$4$d@2$8@5$b?2fx^8@2$2@1$0#k0+knkjc^7@1$c$4?5model@2$h1@3$5$3@2$9@2$2@1$0#k0+1@2$2@1$0#8+j0@3$5$3@2$9@2$2@1$0#k0+1@2$2@1$0#8+a@1$6$3^4").
Proof.
    (* LPS 75d69e00: replay replaced (p1_sound gained the reader premise). Shape from
       boost-beast http_request RefPrintfFirst.v printf0_first; the canary cell is
       boost-json's 0x12ec38. *)
    intros regs mem sp can K PH HKnil HCONT.
    pose proof (p1_regs_ok regs mem sp can PH) as HR. pose proof (p1_know_ok regs mem sp can PH) as HK.
    destruct PH. pose proof (u64_range sp) as Hsp.
    apply (p1_sound sp model Hh Hlazy Hfd1 Hrdr (p1_vals regs sp can) regs mem K);
      [ unfold p1_vals; rewrite length_app, junk_vals_length; reflexivity | reflexivity | exact HR | exact HK | exact HKnil |].
    clear HR HK. intros Rj R' M' HR HK FM.
    set (vals' := p1_vals regs sp can ++ junk_vals Rj) in *.
    assert (P0 : vals_ev vals' 0 = sp) by reflexivity.
    assert (P1 : vals_ev vals' 1 = Z_to_bv 64 can) by reflexivity.
    assert (PJ : forall i, (2 <= i < 34)%nat -> vals_ev vals' i = getr regs (Z_to_bv 5 (Z.of_nat (i - 2)))).
    { intros i Hi. subst vals'. rewrite vals_ev_app_l by (unfold p1_vals; rewrite length_app, junk_vals_length; cbn; lia).
      apply (p1_ev_junk regs sp can i Hi). }
    apply HCONT. split.
    - regv HR (2 : reg). exact P0.
    - regv HR (1 : reg). reflexivity.
    - regv HR (10 : reg). reflexivity.
    - intros r Hr. cbn [In] in Hr.
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
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd_solve HK.
    - krd HK 0x12ec38%Z 8%nat Hc. rewrite Hc. cbn [ev ENV]. rewrite P1. reflexivity.
    - intros a n Ha Hn. eapply frame_mod_store_ok; [exact FM|]. apply Qstk0; assumption.
Qed.
End Plain.
(* [comment removed for export] *)
