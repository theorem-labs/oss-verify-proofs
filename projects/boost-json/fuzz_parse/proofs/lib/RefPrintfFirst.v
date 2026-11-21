(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts Frame StreamSim FileSim
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame SymAux
  Hoare RefExitBase RefStdioDefs RefStdioWrite LibStdioCall RefNodes RefPrintfBufBase LibTail LibDiagKn.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefPrintfFirst () := KReplay.lz_vm "#%>\C47Corelib7Program6Basics4flipC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC89OSSVerify6Proofs:boost_json:fuzz_parse3lib3Lib2Nd9ex_elimF1C13~~~C46Stdlib5Lists4!s+#6nth_ok!tw,4Init5Logic8eq_ind_rK!u=,Numbers7BinNums8positive01!sKG2I!t619Datatypes4list00K!sFA1I!tv72eq00!t$<6option!t&/!to31Z02K!w#O8SymExec23SX24expr0!w&&!smc2!sm&!uD;3nat!t{_5sadd!t|,!v1?3!t4]6kentry05!v3c!so'6!sok7!sok4!so&7!soN<LibStdioCall9s!s0#_res!wT5!{%:!{e93and!|H4!|$,1K!s[<1!}E=prod00C!zE<fstC!{Q]s_pc!#4B&!t0;sndC!v{\:!v{%call!}Ni3!wiB!#4N$2!yne!xz&I!}P?0K!#90?5Instr5aluop01I!upb0!t_&!uPd0!#3zB!#8v+3!t<]8sideco!{y#!u/&!}Xg0!#7=F1!#6M?!wO^9sym_state!wTe7script!uI+c!v=O>RefPrintfFirst5p1_rA!zo3!|$3bool00!t6ccA!t~jB!snic!snf6p1_sr!sojkn!uPjsc!w0jC!w0jC!#3?B1N02I45stdpp9bitvector;definitions2bv00K!}7g!#Gr&!#4O]ym_exec!#3YA!#<q$1C!#Cq]_log!t}c5carry!slV=!sl'Sound4SX2S7regs_ok!stjknow!stl9scs_denot!sv&!#<Q9?!s<25S!y,#8m_halted!#CJC2!t#Q9m_vm_lazy!x1]6s_!w?#!vFjmem!vF0!svb8log_flat!{u'!v<I3Run6config01!#=yO8ShapeAlg8realiz!#=t+!smP6CatSim6mstep!si+!#F0O6SymRun;!|p$_after!slV!uF+9rz_!t\%!w`V!#V1%:and!#V2$3!uG]9run_s!xP#!|Y'!#7A>7Z_to_bv!ukQProp!y`#4mks!yQ&I!yQJ<MemImageType7Segment!#V?=!#Cb#0!#BP\3env!yy+!~[P5Model00!x~Y4TSe!|d+!#B{?!#Eq]6s!#IS/!txP4Scfg=hunspell_scfg!z3ZAux7sregion!z1'!ug'!#^&$7!s+#Def3map!#^&76!#^&$!tHW;log_covere!{W&!#A$^:p1_!u@%s!#4DU<Ref!#L-#Defs7sw_post!wcX5Frame7outside!sg&5!#aw%6ZArith6BinInt1Z3sub!~DA;bv_unsigned!sm<2le!sB>t!u6V9f!s+#_mod!u8Cad!xkQ7StoreOk!#;V#grows!#7bV!#4u&3rdn!sf_5v_!u7#!{b&!#3jH>!#V'#!sE+@word_to_le_bytes!|683no!wN0!tj96images5Plain1M?loaded_s!#6j$s!#9Q\7vals_ev!|ve3ENV!tV&!#5S\a_base!smde!#B-Z!#Hx0a_off!#6@\6r!tU-I!#K=]!#h0#!#V]e<!#5a+_w!{B'!#o%42In!#m,8o!tT#!#Eua4!#Eq+!#3B<pow!sC<>po!#7+#_nonneg!sN<:!sN#!sJ%K!u['9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PE!#nK#!sIE1!sIE7C!sI55Tauto8B!t[&!sH6:Z!u%+=Z!sT$CheckerC!uv<4find!sqAC!sq0!#E{$!w5@1!|XW<!zt'!#LF-!w^K!vp7!vM&G!sJ'4!w<E3!smF5!sJF8!x+<5eKind!#a-<unit!y|8!se%4kind!ud8!v713Op2!uD#!t5@!smJ5!#3/75False!#Ix3!sC%4True!|f8!ym-;!~'%!y5$!#pD=6length!#IEQymDrive9junk_val!#<,&!#Kv;app!#?+X7seg_rom!#6j<9nth_error!t0P9!u;'X8!#ZS#nth!#;4U!#W46!#mr$!#[L+!#6]:6of_nat!sF34Znat5Nat2Z7inj_iff!#A,77iff_sym!sf>9is!#7f<!|d33!#;^^?!#;^,!#3h+!sx_@!sx-!#>C,K!#QdPevent02!#QdX6t_emi!#\Cjsc!u>1!#Ot86Forall!#83XA!#O],_!#K,#!vSW7FdE!#xF%!#MV?D!#Xt%_obliga!s:#_1K!#ijC1!#J'Y:fetch_word!#bV^r_g!#W%&!#4@X4getr!#FQYRun7reg_val!#5#&!#ePOerrno_ret!u1Y6regup!#^AG5bv_eq!#8eX;!#jr#set_a0!t:G4BvWf!xB]4ridx!}[V!y/4!v9,!umX8blob!#Op+!#7[8f_equal!$:;;transK!#`g`1!u<V!$#L/5sc_wb!slhp!v'>8iff_refl!#CV5;ZifyClasses5mkrel!#E6D4!snB;rew_!tB%v!uM]4sc_!}t+!t>@3inj!$AG@3!~9#alu64!#t$cu_sm!$2y'!uTP7LibTail7vadd_wZ!#5s^7alu!#[=+K!#Rb:1!ylasp!zZc!x3#s!~K_5krea!u]&!#Hs2Peano2le00!y7B!#f`#ff!sLB9and_morp!#HtZ!ty$_!#`]+!#\K]!#[\-!t[O!#H<+;!sj%_lit!#8k'!#CYOm_fds!yVafd!tHW9fd_lookup!#TM?3!#u;`!$Bc%!#Ga^A!#k'%_!#h82!zf13Nat!#h2S!x7,@!#Oc'_!#PR%!#5j0!#Na,:!sG%_ap!#oP3!|:&t!tSZ=!#eS%!t%#_l!#:Pfsr!slgk!#jYV!#m6$D!w|+!#>K$_s!#I>'!y'_9rz_run_lf!#6:f!skd7sc_buf!#7oc8!sn%sz!soc6sc!#H##!smbE!$Ht+!#`Y$!}@$!#6wU!~w48!tiV!#Ip+!#qC#i!siW!|z':!si%_pc4!smWRefNodes>rz_ioctl_win!w}+!#;H@7!#C?%!#DVD!#3h#!#<b@!sK$2!#X_E7!$=|_FUEL1!}me6STOPS!sof4scr!#<_&!#[x<6inj_!#{94!sH4t!tY_7!$DR#A'!v<f!$DS#!$Gmi!#8H&!snc!#8J&I!#]AV0!v,csrF!vvk!sof!xY#covA!#38U!#={+6ECALLW!sj`?is_e!#7<#!ss/!w3e!uP&K!#kn<1!#E<P6ENOTTY!$X{=N!y;a!wY&B!u/'!#5^3!#nc51!#6S58ZifyInst7Inj_Z_ZI!#bDX!uCg!$NUe<p1_itinera!$J:'!#GV5sub!#l?;8max_spec!vsD5Psatz!#zk7!sO86!sO6!#rJ:!#{h>3Pol!#tGE!tD&4!$rJ,!#<+%?Rel!#fh#!s6&=eq_Tran!$]{$!$:A;nth!sr59Morphisms:re!vU#tful!tAE<eq_Reflex!t@0!s|5Jr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^??eq!tM#per!tT;!sR,@!u$0per!sS?M!#J}$co_!$>g#v_impl!#Vg$ism!x:<s!#g=[nth_map_!sh#!|o&!#P:4=app_nth2_plus!#WR\2!$6Pf7p1!#z}-!$0<;max!#E#E6!sg+5!sf$8!#R[#Na!#3`;!#BU,;inj_sub_max!sM>8!sM%cc!#37M1i!v@^3p1H00!v>B6modulo!yMP!#p=%6stk!#|9+!#>:OLibDiagKn8cells!slY7Seq!yj#9getr_zero!zy2!v~,9SatDivModCZ!#Tm#!#|i$!$5|&!tDO@!w'+BufBase>!$\U%_by_!#oT'!{@_:p1_ev_jun!v4W!tn49all!tq#32!tie8p1_!wx$!tgV!#RO'9u64_range!yQakn!tZ\!{$&<kalign_int!yS+!smX!uD$!smc=kwr_of_!|e\!sn&:kimg!t[c;k!$Ho#!sl/!#~ZX8store!uG#!{+`=data_!sr+!z=VAgentLib7!z=#l!$+jj6estart!#4$1!#;{,7f!$+d#b!{LZ:!#5w$know!|<`;!$i5%!#fg#!so$!$-eB2!t8Z9!u$#_wf_!#zD%!#:a^6p1P!$VQ,!#6Tb!$m#/!ssc!$l~0!ssO!#gs$B!#gs+!{=1k!vOf!#]+e8p1!$e,-".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list37Corelib7Numbers7BinNumshe1Z04cons03nil03nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~kb7scripts04boolkb3SCRkb4expr04prod69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~qd9pf1_cellskb6kentrykb4EVarkb2SAkb4ELitkb3KWr03appqd8kn_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib0e1R1e1f1P1r1i1n1t1f1F1i1r1s1t4FPX1~~~~~~hi78p1_cellskb6KAlignkb4KImgkb6KRangekb5KWordkb8sidecond03fstkb9sym_state37Corelib4Init5Logichs52eqhs53and03sndkb4s_pc69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLibStdioCall~~~~~~hv29stdio_reshi75p1_rAhi75p1_rBhi75p1_rC04Some06optionhv2astdio_callhi75p1_cAhi75p1_cBhi75p1_cChi76p1_knBhi75p1_schi76p1_srBhe4Npos35stdpp9bitvectorbdefinitionsir42bv04pairkb5s_log3h5LinuxProcessSemanticsfLinuxProcessSem3Runiu55mkCfg3h5LinuxProcessSemantics5Riscv7Preludejha5bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jk94mkst69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jocdhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~jt48realizes79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~khb7know_okkhb7regs_okkhb9scs_denotir47Z_to_bv04None04true3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypekpa7Segment3h5LinuxProcessSemanticsfLinuxProcessSem5Statekta5Modelkta8m_haltedkta9m_vm_lazyjt44TSetkb2SSkb5carrykb3envkb6s_regskb6sentrykb8sym_execkhb8log_flatkhb9mem_denot69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~lnb7sregionkb5saddrhi7ap1_regionslnbblog_coveredir4bbv_unsigned46Stdlib6ZArith6BinInt1Zlv33addhs53notlv32lelv32lt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~mi59frame_modmi57outside69OSSVerify6Proofsaboost_jsonafuzz_parse3libcRefStdioDefs~~~~~~mn57sw_postlv33sub69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~ms68blobs_evkb3Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~nh37vals_ev37Corelib5Lists7ListDefnl73map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib0e1R1e1f1P1r1i1n1t1f1F1i1r1s1t5First~~~~~~nn53ENVnn5cp1_regions_w69OSSVerify6Proofsaboost_jsonafuzz_parse3lib0e1R1e1f1P1r1i1n1t1f1F1i1r1s1t~~~~~~nu2ap1_regionslnb6rdenotlnbcregions_flat69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~olafloaded_segmentskta5eventkta7WriteEvjk97seg_romms69junk_vals06lengthnu25p1_knnu26p1_knFnu25p1_srnu26p1_srFjt46t_emit37Corelib4Init3Natpg73sub37Corelib4Init5Peanopi02lepi02ltjk94getrnu23ENV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib0e1R1e1f1P1r1i1n1t1f1F1i1r1s1t5Plain~~~~~~pkf7p1_valskb2evlv36of_natpkf3p1Hpkf6p1Postkta7FdEntrykta9FdChannelkta9fd_lookupkta5m_fds" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition STOPS1 : ltac2:(zQ "20!h8!j7@1$0$1") := ltac2:(zQ "30!j7!jb!k1@3$1$0+tvqk0@3$1$0+knnnc@1$2$0").
Definition FUEL1 : nat := 5000.
Definition scr0 : ltac2:(zQ "10!oa$0") := ltac2:(zQ "40!k1!p4!pa!q0@3$2@1$0$1@1$0$3@1$0$1").

(* [comment removed for export] *)
Definition p1_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 1 => ELit 0x4777c%Z | 2 => EVar 0 | 11 => ELit 0%Z
                          | _ => EVar (2 + i) end)%nat (seq 0 32)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition p1_cells : ltac2:(zQ "40!q7!j7!h8!k6@1$2@2$0@2$0$1$3$1") := ltac2:(zQ "10!u9$0").

Definition p1_kn : ltac2:(zQ "20!h8!v5@1$0$1") := ltac2:(zQ "e0!v5!jb!ve!hg5!hga!hh1!hh7!k1!hhc!hnc!ho8!hp1!hp8!hq1@3$6$0@3$1$0@2$a@1$2N0+h0@3$1$0@3$c@1$2N0+hggggglg0+nvvvvvvvvvvf@3$1$0@2$5@2$3@1$2N0-kt0+kt0@3$1$0@2$b+hggg0+vhgg0@3$1$0@3$d@2$3@1$4Z+hirmv8N8@1$2N1@3$1$0@2$5@2$3@1$4Z+vpgg0+jkgg0@1$7$0@1$8$9").

(* [comment removed for export] *)
Definition p1_rA := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0x47828 p1_sr [] p1_kn 34) []).
Definition p1_cA := Eval vm_compute in (carry (s_log (fst (fst p1_rA))) p1_kn []).
Definition p1_srA : list expr := Eval vm_compute in (s_regs (fst (fst p1_rA))).
Definition p1_knA : list kentry := Eval vm_compute in (fst (fst p1_cA)).
(* [comment removed for export] *)
Definition p1_srA' : list expr := Eval vm_compute in (sr_upd p1_srA (ridx 10) (ELit (2^64 - 25)%Z)).
(* [comment removed for export] *)
Definition p1_rB := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0xe0468 p1_srA' [] p1_knA 34) []).
Definition p1_cB := Eval vm_compute in (carry (s_log (fst (fst p1_rB))) p1_knA []).
Definition p1_srB : list expr := Eval vm_compute in (s_regs (fst (fst p1_rB))).
Definition p1_knB : list kentry := Eval vm_compute in (fst (fst p1_cB)).
(* [comment removed for export] *)
Definition p1_sc : stdio_res := Eval vm_compute in
  (match stdio_call 34 p1_srB p1_knB with Some r => r
   | None => SCR_ 0 0 0 (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) (ELit 0) [] [] end).
(* [comment removed for export] *)
Definition p1_rC := Eval vm_compute in (sym_exec RSEGS FUEL1 true STOPS1 scr0 (SS 0xe0488 (sc_sr p1_sc) [] (sc_kn p1_sc) 66) []).
Definition p1_cC := Eval vm_compute in (carry (s_log (fst (fst p1_rC))) (sc_kn p1_sc) []).
Definition p1_srF : list expr := Eval vm_compute in (s_regs (fst (fst p1_rC))).
Definition p1_knF : list kentry := Eval vm_compute in (fst (fst p1_cC)).

(* [comment removed for export] *)
Lemma p1_itinerary : ltac2:(zQ "hb0!h8!hq9!hr4!hr9!ht9!q7!htf!k1!hu6!v5!oa!p4!j7!hub!ij1!ije!ik7!il0!il9!ilf!im7!in5!ine!io7!ip0!ipa!iq3@2$6@3$4$c@1$d@3$2$3@1$0$1@3$2@2$5$3@1$0$1$a$f+ugkm4@2$6@3$4@1$0$1@3$8$3@1$0$1@3$2@2$5$3@1$0$1$a$f@1$7$1@2$6@3$4@1$0$1@3$8@1$0$9@1$0$1@3$2@2$5@1$0$9@1$0$1@1$0$b$h5@1$7$1@2$6@3$4$c@1$d@3$2$3@1$0$1@3$2@2$5$3@1$0$1$a$h0+tvqk0@2$6@3$4@1$0$1@3$8$3@1$0$1@3$2@2$5$3@1$0$1$a$h0@1$7$1@2$6@3$4@1$0$1@3$8@1$0$9@1$0$1@3$2@2$5@1$0$9@1$0$1@1$0$b$h6@1$7$1@2$6@3$4@1$h3$e@3$h4Ni2$ha$h8@2$h2$e$h9@2$6@3$4$c@1$d@3$2$3@1$0$1@3$2@2$5$3@1$0$1$a$h1+knnnc@2$6@3$4@1$0$1@3$8$3@1$0$1@3$2@2$5$3@1$0$1$a$h1@1$7$1@3$4@1$0$1@3$8@1$0$9@1$0$1@3$2@2$5@1$0$9@1$0$1@1$0$b$h7@1$7$1").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["FPX1"] "##KMp%0p;1p;3p;2p;<p;4p-1R0p10000R1p4p710p9P0P!s2$2!s3/3110p9!sQ$N!sC'1001:!s\&8p1002>!s4&1002Y!s@'g0037j11Tg003\j10Tg004Aj1]!s/$aj1\Tg005Aj3I!s/$[j1pTg006=j1E!s/$[j18Tg007bj1DTg008ij12Tg009Hj25Tg00:Pj1A!s/$nj2iTg00<7j3hTg00=@j2cTg00>Ij2sTg00?Rl<mTg00@^j2gTg00A@j2C!s/$[j2UTg00B5j4_!s/$Pj2fTg00C0j3K!s/$Mj1^Tg00DRj3S!s/$oj3lTg00F:j3kTg00GAj36!s/$aj3GTf0R1#0#0p=;%11#!s2&H%11#0p=4%01#Ep=`g00HjR0f1R2;I1p=Q!sS$p==%0!s-$9!sW$!sc%J%0!s2%Ep=N!s>&p=V%E1#8p=7!sD'0p=3%01#Ap=ag00IH?k21p=R%21#2p=:!t]%!t+$Xg00J4R3f2R4#D%D2=63136p=PA63219634p=M!s>&p=e!sa+!s$'p=O!tE&p=>!s0%A,52p=[!s3%!sI$L!t\$!s=$j%A1!s/$d!sF%E!s3$rf3R5/54?G21p=qg00K;R6f4R7%E5'5?G42;61p=BA66219664p=bAG542=661p=o%A5,57?G!s7'F!s7%%D27G4!s9%<f6R8f5R9;G7!sa+566p=W%D29G5!sN&n!sa&E2#8!sc+T%05#A!t10?%15!w5%!s?2@P8P9P7P5P4P2P1C_C_p=Y1C21,C4p=Zg00LDR4#1R2#1R1#0R5#0R7#0R9#0S00#0R8#0R:#1R;#;R<#0#H#4#`R=/Q=g00LiR>#]R?%\>R>;I>R@%02!sr$A#=RB#1RC#=#9#;#J#NRD/QDS01g00N4RE#pRF%11R1#1RG#0RH#0RI#1RJ#1#9RK#9RL#0RM#0#=#NRN%E4RO%V<#9#NR<%04R4#0RP#1RQ#0RR#1RS#0RT#=RU#1!tC$9#9#;RV#`RW#8RX%1V#7PX%0PRP#0RV#0RY#0RZ#0S02#;R[#0R\#7S03%1PR]#0R^#;S04#0R_#1#3R`#1Ra#9#7Rb%8OROg00O@Rc#DRd%0_R_#a#8'RRe%2cRc#2#:Rf#2Rg#2Rh#:Ri#:Rj#2S05#2#:S06#2S07#2S08#2S09#2S0:#2Rk#2S0;#2S0<#2Rl#2Rm#2Rn#2Ro#2Rp#2Rq#2Rr#2Rs#2#:#:Rt%8<%2t!s2$<%2<!s''0U!u}$X#NRU#8Ru%:<#:R<#D!sJ-!s'6g00O_#8Rv%4a#7Ra%2<#:!s$'!sT2%\33P3P9MOO9MOv9MOb3M9MbO3P3P3P5MO7MO'e3P9Pgh7Me'ePv%1MRM#1#JPi%1S#3#4!s$$J#7Pv%1L!xd$e#0#3PiPXPv%1e!s1+VKRK#4Re#JPf%1GRG#1Rh!x\$X#O#ORg#1Rb#1R3#=R<#1#X#ORw#1#O#O#7Rx!t-+#3Pi%8DPd%1VRy#1RzPi%DcR{Pd%>z!s4$8NR|Pd%0yRyPi%0:R}#4#3#3#7Pd%1YR~PiPaPd%0~R~#;RaPiP|PdPZPiPOPdP\Pi%0gPd%>hPiPbPd%>GRGPi%7SPdPHPi%J8#4#=#H#715vWPc!|G%0RW!}&$7RH%H2R2,[dPcPHPd%0!|8%HPiPv!s5'0Rc#;RS!tB%%>H!sD+;IRIPi%V~#L#9#7PdP1!s@&>BRBPiPv%A:R:,5dPi%A8R1#8,Rd%15R5#1R~#4,[dPi%L<#L!s$-!sp$%>~R~Pi%0w!vu%Pd%>CPi%H2#H!s$%Pd%17R7#>R2Pi%;T#J#4!sb&1]R]!x<${PdP}PiPuPdP9!ti%P7Pi%8:,RdPd%05R5Pi%14R4#1R:#>R7#0R}#a!tw$Pd%>!sG%V:#aR:!s;&P^Pi%DsPdP_PiPrPdPzPiPqPd%>yPiPpPdPaPiPoPdP[PiPnPdP!wY$4RGPdPI!tU&H!x1&S!tm&!uc$`#=PdP5!xT&2Pi%4;!ub$v%0MRM#J!sc$v%3M!s/&0eRe#>PfPx15vNPfPG!#4a$;RG#0RN,jd!t=&4!s-&}PiPv15d:!wd$4QRQ!wJ$!sB$BPi%A9R9!u^$RBPd%;RRR!ve%Q04PiPmPdQ02PiPlPdPcPiQ0<PdQ00PiQ0;Pd%>ARAPiQ05PdP8Pi%Dj!w7&!wX$J#9!wi$;PdPNPiPBPdPYPiQ08!vA%Q0715d1PiQ0615d!ww$1ddPPi%DkPdPVPiQ0:PdPWPiQ09PdPRPi%0]#=#4#X#4#`R]#8%EV,id%;\#3R\#0!~X&3#N%Ew5hd%1Q#3RQ,dd%EQ'c%E\%4c!}%$N's15vUPiP{%;J#3#3,rv%3A!sA$cPv%=I!|Z$4#NPiPuCq!~G'!#3>&JLPiQ03Pv%9K#3PfPOPv%VePf%73%\6DB!s$%3bCo3b3bDFD<D<FWCnD<D<DFDTD?!s0$!s$%?DFFWDFD@FW!s`&T!sJ$F!s$&!sP,@D?D@!s$$FDFD?DTD?FW!s:$?!s$$@FW!s2$TDT!sR+?D@!t^'DBM<m,gER3;I3Rf1Q]]Re1C@@Rv'CRO'CRK,C@Ri,C@RL'CRX,C@Ru'C1U0=P@Pu1U?>RuP@PXPuQ01PL1U0DP@!{>$@PKPuPfPO1UF3PePv1U0]P@P@PuPuC_FY!s$%g00P=Ru1fu?R@g00QIR0g00RS3KRv7K?#^/Q=ASu?v=I?>%]6R61f6?Rvg00S[#]R=g00T;3K7S?=I?>g00UC9K@0Re9Ku!se$DASu?e!sC&VK9Kv=9S6!sT'WSg00X\5ltg00Ye,gE5IFg00Zm!sl$0!sl']ASu?0!s[&\5!sl/'C3Z!s$%do"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem rz_run_lf : ltac2:(zQ "ia2!h8!iqd!it1!hq9!q7!ilf!ht9!v5!p4!k1!it7!oa!hr9!itd!k6!j7!jh1!jk0!jo4!js3!kgf!km0!kmb!kn6!ko3!koe!kp4!ksf!lg8!lh1!lhd!lia!lj2!lj7!ljf!q0!hub!lk5!lke!ll7!lm2!lme&>0@1$2@1$1#k0@1$5@1$2@1$1#8&@2$4@1$2@1$1#k0@1$2@1$1#k0>4segs@1$0$hb>4fuel$e>5stops@1$0$f>3scr$b>2pc$f>2sr@1$0$i3>2kn@1$0$7>2nx$e>3ss'$c>3scs@1$0$3>4scr'$b>3kn'@1$0$7>4scs2@1$0$3>3hs2@1$0$8>1E$i2>1M~0>3rom~0>1R@2$h1@1$1#5@1$2@1$1#k0>5model$hc>1T$hf>0@3$6@2$4@2$4$c@1$0$3$b@7$i7^h4^h3$ha^h2^h1@5$i0^h0^f@1$9$i6^e^d@1$9$3@4$a@2$4$c@1$0$3$b@4$a$c@1$0$3^c^b^a>0@3$6@2$4@2$4@1$0$7@1$0$3@1$0$8@3$i1@1$d^d^f@1$9$8@4$a@2$4@1$0$7@1$0$3@1$0$8@4$a@1$0$7@1$0$3^a^9^8>0@3$h6^8^h1^5>0@4$h5^h7^9^8^h1>0@4$h7^h8^9^a^f>0@4$h7^h9^a^b^d>0@3$6@1$5@1$2@1$1#k0@1$hd^8@1$h9@1$2@1$1#k0>0@3$6@1$0~1@1$he^9@1$9~1>0>2R'@2$h1@1$1#5@1$2@1$1#k0>2M'~0>0@3$h6^h0@1$i5^h6^2>0@4$h5^hf^h1^2^h4>0@3$6~0^3@3$i9^h2^h1@1$d^h8>0@2$i8^h3@1$d^h9@4$h4^i2$h3@2$h0@5$h2?2fx^6@2$h8@1$1#k0@1$i4^ha^5^h2^h0^f@4$h4^hd$h3@2$h0@5$h2?2fx^c@2$h8@1$1#k0^h9^e^d^b^a").
Proof.
ltac2:(KReplay.run1 (kr_t_RefPrintfFirst ()) ["FPX1"] "h01Rh12R'h21Eh32HKh42HRh53HR'h62Hch75Hconth83Hexh92Hhh:5Hlazyh;3Hlfh<3Hmsh=3Hsch>4Hsc2h?1Mh@2M'hA1ThB4fuelhC3hs2hD2knhE3kn'hF5modelhG2nxhH2pchI3romhJ3scrhK4scr'hL3scshM4scs2hN4segshO2srhP3ss'hQ5stopsp;1p;2p;5p;7p;4p;3p;=p;:p;Dg004Aj11Tg003\j12Tg00]=j1=Tg00][j1?Tg005[j1DTg0037j1TTg000Nj2RTg00BPj24Tg004aj17Tg00^>j5JTg00_Jj7HTg00`Sj48Tg005Aj33Tg00a3j15Tg00b9j3UTg00c?j3>Tg00dMj4BTg00e[j4ATg00fkj1STg00gbj1QTg00hDj1NTg00i<j1KTg00jCj3<Tg00kSj2;Tg00CMj16Tg00lbj2:Tg00mWj49Tg00n^j3CTg00A@j2@Tg00oal=ITg00A[j2GTg010gl:LTg011mj5MTg0132lDFTg001:j5OTg0146j2PTg014\j5ETf5R0f4R1f3R2f2R3'Pf1R4f0R5DEp=0g015]#1g016\R6g00HjR7#1g00QIR8g00J4#1g00K;#1R9g00P=R:g00LiR;#1R<g00S[R=#1R>g017;g00LD#2R?#2#2R@#2#2#2#=RA#?RB%=@#?#D[R@%T?#=/RBR?g018Ag019714:<RC/48fCRDfBREg01:8fARFf@RGf?RHf>RIg01:X#7f=RJf<RKDJ%7;FHPCP8P:P<f;R:f:RCC8f9R;C833149<RL/4>%5K%7=R=7UIPLP>P9P<P;f8R>C8f7RLC833A>LG1fFRMP>PLPGCBfGRNP>P;PICAfHROP;PCPKCA%DB%SL%QB3314BBRB#1%N>%7B33fERB#KRP=>H4fNPGP4PDCB%5N9<FGRQ93@3%5ORR,;EfQg01;aRSp,2fxRTP0PAfIRU#6P1PFE0/:HPIC9[[[[^@@^1?P?A>HP5RP%5BRV,;HRWfMRXPTPKPAPUPIPJE0RYPTP5PA%6BA<HIVPJE03CRV'@'@X0?fLRZPSPTP:PAPOPJPKE0/:CP;C9PPPWPVPXPS1:Y:PCC9%5M,;GfOPTPIPAfKRCPGPHE0PTP3PA%6NPQPHE03CfPRQPSPTPHPAPZPFPGE0PTP2PA%6OA<EFRRAPGE0PIPJf6RGP0P5P1P2PAP3PQPEPFPRfJRRP=PBfDR=PDP:P4P;PLM=I1G@AP4O6M:LW<W;X5PDMX1?PTPZPCPRPUPOPNPMPBP=PDPEPIPJPKP:P>PGP0P1MDFDOW7W:W9W>W=W3W4W6W8WAWFW0XI@W?W2WCXM<XE9XK8WLWPXG6WDWOXH7WJWQWBWNo"). Qed.

(* [comment removed for export] *)
Definition p1_regions : ltac2:(zQ "20!h8!lr4@1$0$1") := ltac2:(zQ "90!j7!lrf!q7!jb!it7!hg5!hga!k1!ve@3$3@2$2$1$0@4$4$1$0@2$5@1$8N0-kt0+kt0@3$3@2$2$1$0@4$4$1$0@2$5@1$6Z+vpqp8+u8@3$3@2$2$1$0@4$4$1$0@2$5@1$6Z+hiruq8+1@1$7@2$2$1$0").

Lemma p1_covA : ltac2:(zQ "d0!hr4!h8!hq9!hr9!p4!q7!kp4!ht9!ije!ls7!lt5!itd!oa@3$7$4@2$a$9@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$8$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefPrintfFirst ()) ["FPX1"] "p;2p;1p;3p101<gp4p70R0p101=ip4p710p8P0p101>Ep4p710p8g00A[j26Tg004Aj15Tg00BPj21Tg00C0j30Tg00a3j14Tg01>aj22Tg005Aj33Tg00S[R0g01:8R1'6g01?gg00P=R2g00Li#5R31123g00QIg00RS3030#4'2=301do"). Qed.
Lemma p1_covB : ltac2:(zQ "d0!hr4!h8!hq9!hr9!p4!q7!kp4!ht9!ik7!ls7!lt5!itd!oa@3$7$4@2$a$9@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$8$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefPrintfFirst ()) ["FPX1"] "p;2p;1p;3g00A[j26Tg004Aj15Tg00BPj21Tg00C0j30Tg00a3j14Tg01>aj22Tg005Aj33Tg00S[R0g01:8R1'6g01?gg00P=R2g00Li#5R31123g00QIg00UC3030#4'2=301do"). Qed.
Lemma p1_covC : ltac2:(zQ "d0!hr4!h8!hq9!hr9!p4!q7!kp4!ht9!il0!ls7!lt5!itd!oa@3$7$4@2$a$9@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$8$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefPrintfFirst ()) ["FPX1"] "p;2p;1p;3g00A[j26Tg004Aj15Tg00BPj21Tg00C0j30Tg00a3j14Tg01>aj22Tg005Aj33Tg00S[R0g01:8R1'6g01?gg00P=R2g00Li#5R31123g00QIg00Zm3030#4'2=301do"). Qed.

Lemma sw_post_frame_mod : ltac2:(zQ "h01!iqd!it1!lu4!htf!mgb!mh2!j7!mh9!mhf!ilf!h8!q7!mld!mma!mr4!mrf&>0@1$1@1$0#k0@1$9@1$1@1$0#8>3mem~0>2su$6>1f$6>4bufp@1$1@1$0#k0>5bufsz@1$1@1$0#k0>4mem'~0>2rs@1$a@2$b@1$1@1$0#k0$6>0@6$e^7^6^5^4^3^2>0>1x@1$1@1$0#k0>0@2$d^1^3@2$3@1$5@2$3@2$7@2$f^9+n0@2$2@1$0#k0^2@2$8@2$2@1$0#k0^2^9@2$3@1$5@2$3@2$7@2$4^8+i0@2$2@1$0#k0^2@2$8@2$2@1$0#k0^2@2$4^8+j0@1$5@2$3@2$7@2$4^8+j8@2$2@1$0#k0^2@2$8@2$2@1$0#k0^2@2$4^8+k0@3$c^9^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["FPX1"] "##4ap'0h01xh11ah21Hh32Hah43Hagh53Hgrh63Hrsh72N1h82N2h92N3h:2_Hh;3_H0h<3_H1h=4bufph>5bufszh?1fh@3memhA4mem'hB2rshC2sui009swp_agreei01!s3$growsi02!s3$wbasei038!s3$endi04!s2%posp;1p;2p;6p;3p;4g003\j12Tg00]=j1F!s/$[j1DTg005[j1HTg00BPj2OTg004Aj1GTg01A4R0j6KTg01B>j2ATg0037j1CTg006=j17Tg01C?j2;!s/$\j2:Tg01DFj28!s/$bj24Tg00A@j23Tg01E>j3NTg01FAj25!tN$Aj39!s8$^j2ETg0146j2@Tg008ij11Tg01Gcj4?Tg01Hcj2JTg01Iej2>Tg00@^j2BTg011mj6I!u>$5j4LTg01Jmj1=Tf0R1#2#2p=6f1R2/31#=p=<f5R3f4R4'5f3R5'8f2R61521'4'3#=p=01521,46,35#=p=Mg00LDR7#2R8#6R9#6R:#2R;#FR<#DR=%F9#DR9#HR>[R?g00HjR@1O=@#Gf6RAP3P4P5P6P2EKP0f7P!s8+1A15f9R3%C7R7#C#2#6RA#2#7R0';1:<2RB'814B3'<f8RC%7:R:PBPBPC%67#6#7R7E0PC%7ARA!s>&7;R;E0'3'3[^0=AN345[P1f<RD/;01:<1RE'814ED'<15D:RE/8BPBPDP7CMf=RFPA1:<6RGPGPFP;E0f;RHP5O1f@P5O159>[[[^0=1EFC%G9!uk$Cg01KFRIP31@<Eg00O@#1!s$1REC?f:R3,JH,>E,B939PIP3%C8#2#6#7,5F,@<PEC?1>ED,B959CPIPHf>/5A!s@,F!s@%1A1DfB!uH$/8B14BD'<fARCP!v;&P!v4$P!v1&P!v--1A1FRCf?P2O1fDR9P2!uJ$R>[^1=1EDFfCRF!s}+F'<R0PD!s}&D!s}$D!s}&DP;E0P>PFP:P!vK%7E0P9!v]$5R<P<P9!sH$3P4P6P2P1O4W9W8X70!s5&2EIX3CX1=P4CLW6W<W;W:W5W4!yC'P1O5n60!s#$1!s,&51100101103104102W2WBXA?X>=X==X?@WCW@o"). Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section First.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variable model : ltac2:(zQ "10!lg8$0").
  Hypothesis Hh : ltac2:(zQ "60!iqd!it1!koe!ilf!ht9!lh1@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!iqd!it1!q7!h8!k1!ht9!lhd&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd1 : ltac2:(zQ "90!iqd!pt0!ko3!il9!ilf!ht9!ptb!pu8!pv5@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+1@2$3$1@1$6@2$2@1$0#k0+1").
  (* LPS 75d69e00: the stdout write needs the launch's channel reader
     (LibStdioCall.stdio_call_sound_post's premise), constant over the run. *)
  Hypothesis Hrdr : m_channel_reader model = true.

  Definition ENV : ltac2:(zQ "40!h8!iqd!ljf!it1>4vals@1$0@1$3@1$1#k0$2") := ltac2:(zQ "70!h8!iqd!it1!k1!ng1!ngd!nkc\4vals@1$0@1$2@1$1#k0@2$5@1$6^1@1$4@1$3@1$0@1$2@1$1#8").

  (* [comment removed for export] *)
  Definition p1_regions_w : ltac2:(zQ "50!h8!q7!iqd!j7!it1@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "a0!iqd!j7!it1!q7!jb!it7!ko3!k1!mrf!lu4@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0@2$8@2$9@1$0#k0?3sp0+kt0+kt0@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0+vpqp8+u8@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$6@1$0#k0+hiruq8+1@1$7@2$3@1$2@1$0#k0$1").

  Lemma p1_regions_denot : ltac2:(zQ "f0!iqd!it1!h8!q7!ht9!j7!nme!nsb!nt2!oj2!ok0!lr4!nkc!mh9!lu4>4vals@1$2@1$1@1$0#k0>0@3$4@1$1@1$0#k0@2$c^1N0?3sp0>0@2$d+hggggglg0@2$e@1$0#k0?3sp0@3$4@1$2@2$3@1$1@1$0#k0$5@4$6$b@2$3@1$1@1$0#k0$5@1$a@1$7^3$9$8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["First"] "##0Hh03Hloh12P0h21bh31rh44valsp;1p;2p;3p;6p;4g00]=j1TTg00][j1ITg004Aj1FTg01LMj2ETg005Aj3;Tg006=j17Tg01C\j2:Tg01DFj2HTg00BPj2BTg0037j14Tg00:Pj1UTg01FAj2<Tg0146j23!sJ$\j11!t:$aj1DTg00GAj32!t$$?j2STg00A[j2RTg002Yj6QTg01MOj1ATg00C0j3OTg01NUj1NTg01O\j2MTg01Pcj1LTg00DRj3JTg007bj1KTg009Hj2>!u<$[j1GTg01=ij4CTg01Qij1PTg00`Sj4@Tf0R0#1#1p=9%1!s0$#1p=5%10#4p=8f2R1g00HjR2f1R3P0C@p=6%4!sD$?%40#1p=0g01RjR4P2P!sH&=g00LDR5#9R6#5R7#TR8#IR9#Fg00O@R:,E0p,3sp0R;5;9%97#5!s$$8#8!s-$71:8;R7'HP9P;1B92R;#FR<1:80%46R6#4#8#5R=#UR>'<,38%7=R=569g00O_R?,38,:8R@%?5RA#4#0#8#0!s$$8#0#9#7RB!s]%1A!s6&A569%16#0#?#?!sR&!s@%6,<@!t0$5R5569%D;R@52;!s%%1S7=,38=69=138B=69A1386=695=2;!sN&R@3;X291R<@1E1:P3EQg01<gR3P;f3#AAO420R7#N'M,:8%L7!tj$AJ420569X331B42R4%K:/>>/==%G?R?/>B/=A1>?6/=5%D452452432CC=;<@eP3P;%A1#Pg01?gCCg01T25;<eW0W1W4o"). Qed.

  Lemma p1_regions_flat : ltac2:(zQ "a0!iqd!mh9!it1!lu4!h8!ht9!nsb!oj2!oka!nkc>4vals@1$4@1$2@1$0#k0>0@3$5@1$2@1$0#k0@2$9^1N0?3sp0>0@2$1+hggggglg0@2$3@1$0#k0?3sp0>0@2$1@2$3@1$0#k0?3sp0+nvvvvvvvvvvf@2$8@1$6^4$7").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["First"] "##@@h01Hh11rh27__arithh34__ffh48__varmaph55__with62Hah76__sat0h8!s/%1h94__x1h:3Hhih;3Hloh<2Hrh=2P0h>!sL%2h?!s/%3h@1bhA4valsp;1p;2p;3p;4p;6p;7p;8g003\j12Tg00]=j1c!s/$[j1_Tg004Aj1YTg01LMj2VTg005Aj3STg006=j17Tg01C\j2ETg01DFj23Tg01UAj3vTg007bj1rTg0037j10Tg00:Pj1pTg009Hj2P!sn$[j1d!s\$XR0j2DTg01MOj1>Tg01V2j35Tg01FAj21Tg01W=j2`!t<$bj28!s8$Zj2^Tg01XBj3]!u+$aj1\!s8$fj2[Tg01YDj1Z!s/$bj1xTg01ZMj2wTg00gbj1uTg01[0j2X!s/$Sj3qTg01\6j2oTg00A[j2n!s8$Xj2jTg01]Dj3i!s/$cj4hTg002Yj6gTg01NUj1MTg01O\j2KTg01Pcj1NTg01>Ej6LTg01^Uj1fTg01_3j2eTg00`Sj4kTg00C0j3lTg00DRj3m!tL$@j2TTg01`:j4R!s/$ej7UTg01aIj3a!s/$lj7sTg01bPj8tTf0R1#2!s$%p=A%21#2p=I%21#0p=F%0!s-$J!s-$!s$/p=Hg01RjR2g00HjR3f1R4P1Ckp=Og01<gR5?S41p=4%0!sy$6!si+p=bAl231p==Am!s-$<g00O_R2/31p=9f2R61T41'Tp=?1324/T1p=@1X31p=:P6g01c4R7g01cSR8P8g01d3R9P3P4g01dSR:P1CRg01e:R;FUp=GAa341p=CP3P4P!sD$p=B!sV&eZ!s6%Qf3R:P7P8P8P9P6!s0+4P;FUP1Fsp=;P!sG/4P1Gtp=Wg00LDR7#2R;#2R<#AR=#cR>#_R?#Yg00O@R@,V1p,3sp0RA5S?%I=#A!s$$F#F!s-$7RB1E>ARC'3%J7RD#JRE#J#H!s$+7RF,3Cg01?gRG9v51P0%r@%0<R<#0#F#ARH#pRI'P%7HRH'ORJ/44%d2RK%2E#F#6!s$$F#6#I#7RE'P%2D!s3&D'ORL/44%2<#6#b!sQ&!sB%<,PK%77RK'ORM/44g01fARN'D'Df6RO#>%=6%<635P114J6P5PJf8RP#>RQ%=1RR%<1RS35X15P?PA1E>1/1IRA%7;R;%7=R='`RT,8A%9HRU11AH/3T3?'@X@?1^;=R?182;%9=182T[[RA%9;RVg01f^RWA];=4UW6R=%9T\W^6V!sA$g:RW#\RX%YWRW1[34%Z3RY%x3RZ1w37R7%:F5GZ%u8R8PZ%:B=GZ7P8PZPZ1X32R8%:I,C7R7'BPZPZ%:;=q3>R;,Q7!s6%HR[,B81C7[=GZ;C!s$%WCW1oZ9R9P1P6g00S[R[g01:8R7'n1j16=S[7dAi324ChR7b3b4b5X93131F13B4116IRI18IT11IH/3T7?U'@[[^93P1PCf7RCPPO3b2b>b?1VC@POEg%>CR@%=JRU#M'K,E>%NU'1!sm%%<JRJ#911IJ!vr&eA5@UJeP:P1ELW0P1O114L614M6/DN'DP014L:14M:/DNf4R6#=%<655QP!sN$P5PLf:#>RQ?5RS!x@&P=PVPXPW%f3R3PY!v?%E,C8RJ,B!vr%QJ;!s=%DRU!vV$JU!vV,P9P!v&&112ERE18ET%9D11ED!u+&P1b2b7b8f9#>RE%=LRD!uc+D'1RU18UT%<LRL#911UL!uc,EDLef5RL!ue/!ua$P014MLPN%=O%<O!uW&MOP5PMf<#>RO!uW6P!uT+<,C8RY!uT+Y!uT&KR3!uT$Y3!uT:<R<18<T%9K11<K!uT3;#>R<%=MRK!uT+K'1R>18>T%<MRM#911>M!uT,<KMePC!uR,PN%=P%<P55OP1n010!s#%X0NP1O1n20!s9'2110!s3&!s`%!sB51!sBC<X15%>:/eGeW:W;W=WAo"). Qed.

  Theorem p1_sound : ltac2:(zQ "i11!iqd!it1!op0!ko3!oq3!nsb!jk0!hh7!jb!k1!ilf!ht9!jh1!oqc!jo4!or7!js3!kgf!os2!km0!kmb!osf!h8!k6!mld!nt2!ot7!ou0!oua!ov3!lia!ovd!nkc&>0@1$1@1$0#k0@1$a@1$1@1$0#8>4vals@1$h6@1$1@1$0#k0>1R@2$6@1$0#5@1$1@1$0#k0>1M~0>1K$he>0@3$b$h7@2$h5@1$1@1$0#k0^4Ni2>0@3$b@1$1@1$0#k0@2$i0^5N0?3sp0>0@3$h4@1$5^6$hc^5>0@4$h3$2@1$5^7^5$ha>0@1^5@1$9$4>0>2Rj@2$6@1$0#5@1$1@1$0#k0>2R'@2$6@1$0#5@1$1@1$0#k0>2M'~0>0@3$h4@1$5@3$7@1$1@1$0#k0^c@1$h2^3$hd^2>0@4$h3$2@1$5@3$7@1$1@1$0#k0^d@1$h2^4^2$hb>0@3$h8^c^3$h9@4$h1$2$h0@2$c@5$e?2fx^5@2$3@1$0#k0+knnnc^4@1$f$2?5model^c@4$h1$2$h0@2$c@5$e?2fx^9@2$3@1$0#k0+knoi8^8@1$f$2?5model@2$hf@3$8$4@2$d@2$3@1$0#k0+1@2$3@1$0#8+j0@3$8$4@2$d@2$3@1$0#k0+1@2$3@1$0#8+a@1$9$4^7").
Proof.
    (* LPS 75d69e00: replay replaced (it applied stdio_call_sound_post at the old
       arity). Shape from boost-beast http_request RefPrintfFirst.v p1_sound; pcs are
       boost-json's own (0x47828 entry, 0xe0464 ioctl, 0xdfa40 write, 0xe0488 resume,
       0x4777c exit, all from p1_itinerary / the sym_exec seeds above). *)
    intros vals R M K HL P0 HR HK HKnil HCONT.
    pose proof (know_nth RSEGS _ _ p1_kn 1%nat _ HK eq_refl) as Hrg. cbn [kentry_ok edenot ev ENV] in Hrg. rewrite P0 in Hrg.
    pose proof (p1_regions_flat vals P0 ltac:(lia) ltac:(lia)) as RF.
    pose proof (p1_regions_denot vals P0 ltac:(lia)) as RD.
    eapply (rz_run_lf RSEGS FUEL1 STOPS1 scr0 0x47828 p1_sr p1_kn 34 (fst (fst p1_rA)) (snd (fst p1_rA)) (snd p1_rA)
              (fst (fst p1_cA)) (snd (fst p1_cA)) (snd p1_cA) (ENV vals) M (seg_rom RSEGS) R model);
      [ vm_cast_no_check (@eq_refl _ p1_rA) | vm_cast_no_check (@eq_refl _ p1_cA)
      | exact HR | exact HK | constructor | constructor | exact Hh | exact Hlazy | ].
    clear HR HK. intros RA MA HR HK EQA LFA.
    pose proof (log_covered_frame (ENV vals) M p1_regions _ p1_covA RF LFA) as FA. rewrite <- EQA, RD in FA.
    change (s_regs (fst (fst p1_rA))) with p1_srA in HR. change (fst (fst p1_cA)) with p1_knA in HK.
    change (s_pc (fst (fst p1_rA))) with 0xe0464%Z.
    eapply (rz_ioctl_winsz RSEGS _ _ _ model ECALLW (Z_to_bv 64 1) (FdChannel (Z_to_bv 64 1)));
      [ vm_compute; reflexivity | apply is_ecall_ECALLW | exact Hh | exact Hlazy
      | regv HR (17 : reg); reflexivity | regv HR (10 : reg); reflexivity
      | change (bv_unsigned (Z_to_bv 64 1)) with 1%Z; lia | exact Hfd1
      | regv HR (11 : reg); reflexivity | ].
    rewrite v_addi_pc4 by lia. change (0xe0464 + 4)%Z with 0xe0468%Z.
    pose proof (regs_set_a0 (ENV vals) _ _ (errno_ret ENOTTY) (ELit (2^64 - 25)%Z) HR
                  ltac:(cbn [edenot]; apply bv_eq; reflexivity)) as HR'.
    clear HR. change (sr_upd p1_srA (ridx 10) (ELit (2 ^ 64 - 25)%Z)) with p1_srA' in HR'.
    eapply (rz_run_lf RSEGS FUEL1 STOPS1 scr0 0xe0468 p1_srA' p1_knA 34 (fst (fst p1_rB)) (snd (fst p1_rB)) (snd p1_rB)
              (fst (fst p1_cB)) (snd (fst p1_cB)) (snd p1_cB) (ENV vals) MA (seg_rom RSEGS) _ model);
      [ vm_cast_no_check (@eq_refl _ p1_rB) | vm_cast_no_check (@eq_refl _ p1_cB)
      | exact HR' | exact HK | constructor | constructor | exact Hh | exact Hlazy | ].
    clear HR' HK. intros RB MB HR HK EQB LFB.
    pose proof (log_covered_frame (ENV vals) MA p1_regions _ p1_covB RF LFB) as FB. rewrite <- EQB, RD in FB.
    change (s_regs (fst (fst p1_rB))) with p1_srB in HR. change (fst (fst p1_cB)) with p1_knB in HK.
    change (s_pc (fst (fst p1_rB))) with 0xdfa40%Z.
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
      eapply (rz_run_lf RSEGS FUEL1 STOPS1 scr0 0xe0488 (sc_sr p1_sc) (sc_kn p1_sc) 66 (fst (fst p1_rC)) (snd (fst p1_rC)) (snd p1_rC)
                (fst (fst p1_cC)) (snd (fst p1_cC)) (snd p1_cC) (ENV vals') MC (seg_rom RSEGS) _ model);
        [ vm_cast_no_check (@eq_refl _ p1_rC) | vm_cast_no_check (@eq_refl _ p1_cC)
        | exact HR | exact HK | constructor | constructor | exact Hh | exact Hlazy | ].
      clear HR HK. intros RC MF HR HK EQC LFC.
      pose proof (log_covered_frame (ENV vals') MC p1_regions _ p1_covC RF' LFC) as FC. rewrite <- EQC, RD' in FC.
      change (s_regs (fst (fst p1_rC))) with p1_srF in HR. change (fst (fst p1_cC)) with p1_knF in HK.
      change (s_pc (fst (fst p1_rC))) with 0x4777c%Z.
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
  Variable model : ltac2:(zQ "10!lg8$0").
  Hypothesis Hh : ltac2:(zQ "60!iqd!it1!koe!ilf!ht9!lh1@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!iqd!it1!q7!h8!k1!ht9!lhd&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd1 : ltac2:(zQ "90!iqd!pt0!ko3!il9!ilf!ht9!ptb!pu8!pv5@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+1@2$3$1@1$6@2$2@1$0#k0+1").
  Hypothesis Hrdr : m_channel_reader model = true.

  (* [comment removed for export] *)
  Record p1H (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z) : Prop := P1H {
    Q1  : getr regs 1 = Z_to_bv 64 0x4777c;
    Q2  : getr regs 2 = sp;
    Q11 : getr regs 11 = Z_to_bv 64 0;
    Qsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    QspLo : (0x100000500 <= bv_unsigned sp)%Z;
    QspHi : (bv_unsigned sp <= 0x7fffffffffff)%Z;
    Qstk  : stk_ok RSEGS mem sp 1232;
    Qimg  : forall i, (0x10000 <= i < 0xf1000)%Z -> mem (Z_to_bv 64 i) = None;
    Qcells : cells_ok mem p1_cells;
    Qcan  : rdn RSEGS mem (Z_to_bv 64 0x12b6f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    Qcan64 : (0 <= can < 2 ^ 64)%Z }.

  (* [comment removed for export] *)
  Record p1Post (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (can : Z)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := P1P {
    P_sp  : getr regs' 2 = sp;
    P_ra  : getr regs' 1 = Z_to_bv 64 0x4777c;
    P_a0  : getr regs' 10 = Z_to_bv 64 2;
    P_cs  : forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    (* [comment removed for export] *)
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 1232), 1232%Z); (Z_to_bv 64 0xf9a98, 232%Z); (Z_to_bv 64 0x12bea8, 1%Z)];
    (* [comment removed for export] *)
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0xf9a98) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0xf9aa0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0xf9aa8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wend  : rdn RSEGS mem' (Z_to_bv 64 0xf9ab8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12c2a8));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0xf9ac0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bea8));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0xf9ad0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bea8));
    P_write : rdn RSEGS mem' (Z_to_bv 64 0xf9ae0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xdfa40));
    P_buf   : rdn RSEGS mem' (Z_to_bv 64 0xf9af0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bea8));
    P_bsz   : rdn RSEGS mem' (Z_to_bv 64 0xf9af8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1024));
    P_fd    : rdn RSEGS mem' (Z_to_bv 64 0xf9b10) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1));
    P_mode  : rdn RSEGS mem' (Z_to_bv 64 0xf9b20) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0xf9b24) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_lbf   : rdn RSEGS mem' (Z_to_bv 64 0xf9b28) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_can   : rdn RSEGS mem' (Z_to_bv 64 0x12b6f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 can));
    P_stk   : stk_ok RSEGS mem' sp 1232 }.

  Definition p1_vals : ltac2:(zQ "50!iqd!it1!h8!j7!jk0>4regs@2$4@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3can$3@1$2@1$1@1$0#k0") := ltac2:(zQ "90!iqd!it1!jb!hh7!k1!j7!jk0!os2!ko3\4regs@2$6@1$0#5@1$1@1$0#k0\2sp@1$1@1$0#k0\3can$5@3$3@1$1@1$0#k0@3$2@1$1@1$0#k0^2@3$2@1$1@1$0#k0@2$8@1$0#k0^1@1$4@1$1@1$0#k0@1$7^3").

  Lemma p1_ev_junk : ltac2:(zQ "h00!iqd!it1!k6!htf!ht9!ph9!pj4!pja!j7!jk0!pk0!pk8!pq5!pr0!pr5!ko3>4regs@2$9@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3can$8>1i$2>0@2$3@2$6N2^1@2$7^1Ni2@3$4@1$1@1$0#k0@2$d@1$b@3$c^5^4^3^2@2$a^5@2$f@1$0#5@1$e@2$5^2N2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["Plain"] "##Iih04__p1h14__p2h24__x1h34__x2h42H2h53Hi0h67__arithh74__ffh84__p3h98__varmaph:5__with;4cstrh<1ih=1nh>1xh?2z2h@1HhA2HihB1bhC3canhD7defaulthE1lhF5lemmahG1mhH4regshI2sphJ1yp&0p;1p;2p;3p;<p;6p;4p;=p;9p;5p;Bp;7p;8g003\j1<Tg0037j1lTg00]=j1O!s/$[j1`Tg000Nk20ITg008iR0j12Tg02UCR1j2WTg02aoR2j2!sG$A@j20Tg03L[j2[Tg005Aj31j1JTg01maR3j13Tg006=j1KTg01C?j27Tg01FAj2ATg01nAk20;!s0$dk305!s~$[j2;Tg02JDl<PTg01DFR4j26!s1$bR5j24Tg02VCj6dTg032Ej4gTg01oAj1jTg03M2j2kTg01UXj2H!s8$Tj2FTg03N=j3G!s/$fj2LTg00:Pj1mTg03ORk20!sT$P3k30GTg004aj1]Tg00GAj3!tm$4Aj1\Tg01Xfk20FTg01^Uk10ETg02]4k40DTg01YDk10C!s0$bk10>Tg01ZMj2iTg01[0j2C!uY$ik30=Tg01`:j4@Tg00gbk10<Tg01aIj3eTg01\6k20:!s0$Xk20!va$]Dk304!s0$ck40!wn$KLj4_Tg0146j28Tg01gfj2VTg02_kj2T!uQ$\k100Tg01hFj1UTg01iLj3NTg03QLj4?j1z!s2$hj4QTg03ROj1~Tg03S>j4RTg03T5j3{!s/$kj1yTg03UZj6}Tg03VEj2MTg03W1l=xTg02<;j2D!s8$^m901Tg03XXj2wTg01=ij4vTg03Y4k60!yB$2Yj6^Tg03Z<j5uTg01LMk206j1tTg02DTk108Tg02FTk209!sP$^j2hTg03[aj3sTg01MOj1rTg03\kj2qTg033QmB0?!yC$lm<0@!yD$fj6p!wA$ek70!zM$alk70BTg03]Hj7oTg01bPj8nTf0R6#2!s$%p=9%26#2p=|g00O_R7/q6p==g00HjR8f1R9;16p=>g016\R:P:P:P8P8P8g03]lP3P3P3f6R;g03^Lf5R<f4R=f3R>f2R?P9P6NB0?p=b!s_+0!sZ$>g03_3P!sH%<0@p=a!sF$1P3P4g0383P<P=P>!sH%M<Pp=c!sG$2P3P5g038U!sG4SA1867p=ZP9g01c4R5g01cSR2P2g01d3R4P6Epp=YP8P9g03H?P6C@p=XP9P5P2P2P4P6g01e:K0Ap=:P?!s=+9P6K0Bp=B!s:1Fop=fP>!s9+!tZ$Gnp=Eg00LDR5#<R1#l#OR0%<1#<R@#<#<RA#<#ORB#`RC+0Ig00O@RD#2RE#2RF/W6%2FRG#2#9!s$/RH#|RI,I6'01[9FRJ#2RK#2RL=1:9%39RM%K1RN'7#=RO%K5RP'ARQ/APRR/>MP:P8%J:RSP3%J8%36R3,>MA1:9620;96405XJ:X>:PLPR1A6PX>8RRPKPQPRPJPO1796#=XG8X=8ROP9PM1;8MRRPFPN1;8NRQFbCaCaP9PMPRM<P1WF9RK1I9IRL'016NMRT%l@#<#KRU,4MRV'0RWPKPLPTPVPFPNPQ!sc%Ec!s-%PIPU1;8URRESEdP6CgPW%j?%3?RW,67%3>RM/7NRV,k7147V%=VRT/>V'016V7%ZT'0'H%3=/7NRT#=RVP8p-0RLg01g:RK1F8FRX1F8E1F8DRE5G85G8g03_WRY'LRZ1F8G%m5-0H8>0G8X=G8E!sM$/LY1LEY%]KRE55K55K35%\KRYP820F8?P9&0E8H0DRX&0C8RG&0>8R[1Y[=1i85R51i81R11C8NR\60=8R]'X,:[5B[R^P8P]g01dSR]1C87R_C@,:[1X5_,:[R_5B[5f[&0<2R2P[P8P\P]P1!sJ%Y[<R]5B[P21C8PR\9e85=e8\/X1,:[CECE20:[4R4P6P?g00S[R\g01:8R`';2076?=1\`dB04879H02R`b7b9b:X28X38X0LW1179NR\,>6,0?Ra16\7%Z6R\'0'H16N?/0=1A?P/AP/>>[[^28^38^0L^1LP6%3;RP/4U17PN,47PPP9P?P=O6b6b?b4b;b5C_18B?%]CRP55C95C>Rb,VC/TJ=1:9RcePc18B>=5CP95C=Rc,VC1[?FRd'TRe=1:?PC%JCRf&00CPCP>18B=!sT&<RP%U;5NCRg18B7RBC?PC1VCP1[>FRP'TRhPgPBC?%\CRiPC^DCRj]ERk^=:RlP:PkPSPiPj%JiPCPCPfPfCQRmCQRnCQRo!sG$nPiPjPm!sF%%~CCRCRCR9{lo%zCP>PhP:PS%y:PhP>P6E}PgPg1MigPBPB1MCBM=x%3P,80,D;RPPP1MCPN901WFP6!s{$d%U<RiPBC?RgA1C6PXBCRPPC%3d!s\$<RhPP1;ChPCPdP:PC1803,D;X<:R31wDHCvP!uo$P3PdPHPB1IdH17WN#=R3%KARA'4PdP3POP?PW1;8WRO!}R%FbPHPA1;8AES1WF?RH1I?IR3!~:$WRD14WURP'0RSPHP3PDPP!~2&?PWPOEc!s-%PIPUP!~-%9CgPS%j>167M1k7T147T1>VT'016T7%ZV!}u%</7N#=P8A5KZEPYPXPGP[AB[]_9f[^P2P[1Y[;P8P1g01eZ!|e$U!{v$!{p$P8P5P11C8A!s:$CECEP4P!{?3X1LX8L10>\,Ha14?U,0<14?A!{%1^8LP6f7#3R6,6N176NRN/67147NP6!{3&7!{3/J03E^A1CghePCPeANCci!wE&cPiPBPdDuE^O2b@%U=9NCbRb0069%3J!x;$=R051Ce%tb%O@#`#\#]$08+09/h9=1C0eAs=>?#r!s5'WAX<:XC8XICWHo"). Qed.

  Lemma p1_regs_ok : ltac2:(zQ "a0!iqd!it1!ilf!j7!jk0!pk8!prf!pq5!oua!kmb>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2sp@1$1@1$0#k0>3can$3>0@4$6^4^3^2^1@3$9@1$5@3$7^5^3^2$8^5").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["Plain"] "#$U/p'0h02Hih11ni001nh27__arithh34__ffh48__varmaph55__with61bh71ih82Hah94__p1h:4__x1h;3Hi0h<2PHh=3Q12h>2Q3h?2Q4h@5Qcan0hA6Qcan65hB7Qcells0hC5Qimg0hD5Qsp17hE6QspHi0hF6QspLo0hG5Qstk0hH7__sat66hI!s0&7hJ!s0&8hK3canhL4cstrhM3memhN4regshO2sphP1xi012Q1i023Q11i032Q2i044Qcani05!th%4i066!ti%i074Qimgi08!ti$6i095!tj$i0:5!tj$i0;4Qstkp%0p&0p;1p;2p;4p;3p;6p;<p;7p;5p;8g003\j1FTg0037j16Tg00]=j1]!s/$[j1`Tg000Nk20!sK$5[j1kTg03`CR0k40<Tg00c?k301Tg006=j18Tg0146j2STg01C\j2VTg03aKj2i!si$Aj3JTg01DFR1j27!sC$kk400!s;$bR2j25Tg00A@j22Tg00gbj1mTg03blj2xTg004Aj1lTg008iR3j1!s`$Gcj4sTg01Iej2rTg00@^j2qTg01W=j2pTg02aoR4j21Tg029Oj3[!u&$[k10ETg03d2k10DTg03QLj4RTg03[aj3bTg03Z^j2oTg02UCR5j2BTg02VCj6A!t]$ak10@Tg01^Uk10?Tg01YDk10=!s0$bk10;Tg01\6k20:!uR$[j2a!s9$Xk209Tg01]Dk30!v[$]ck407Tg01maR6j1WTg01FAj2UTg032Ek406Tg01oAk105Tg03e7k204!ua$Zk203Tg01XBj3~!s/$fj2}Tg02]4j4gTg01[0j2fTg01ZMj2{!sq$fk602!sq$hj4yTg01MOj1_Tg02<;j2PTg01O\j2^Tg03L[j2wTg02JDl<hTg01`:j4X!s/$ej7YTg01alj7vTg02KLj4uTg03g;j5tTg002Yk60>!uB$ll<n!sT$Ij3ZTg01bPk80BTf2R7f1R8f0R93b#_p=9%69#Fp=N%69#6p=\!s-$#6#6p=c%F9#8p=If4R:f3R;g03EFR<9[78'P;J9p=<A[89<p>0A1P78=J;9p=j%F!sy$Q!s-$#F#Fp=O!s}+!s$'p=T%F!tA$dg00O_R=/79p=KAb:;7#_g00J4R>P8g03;JR?P9CR'^p=4f5R@P;P7g03hHRAP8CR,P:!t[$31P;7%_8/^95J:p>0Cf7RBf6RCP@P:PAP;CR'PP>P8P!sv$,^73Jp==1w89#W,S7,P;p=Dg00HjRD/a9p=;g016\REPDP5P6P1g0383!st$;P7P8P9M<hp=EPEPDP4P6P2g038U!sG4>1fD9p=:PCg01c4R2g01cSR4P4g01d3R1P@P2P4P4P1PDP:g01dSR5P;CXg01e:RFFYP7!sH-8g01eZRGP9CXPFFYFvp=?PBPC!tH/CuDtp=@!s=%1a:;1o78P9J0>p=C1U:;/U7/U8/U9p=HP!u:%DP3P6P6PCg03_3RH!sv$!sA1;PH!uP'nM<np=G!ti1P5!td'p=|AZD:;=ZD7=ZD8=ZD9p=M!sU2!u;+p=zP;!sA+!t1$L0Bp=e%09#0#0#0p=Lg00LDRF#FRG#6R5#]RH%FGR6#FR3#FS00#FS01#FRI#]RJ#`RK+0F%]3#`RL#kRM\K!v='H0<P0!vL'A9@;7@01?@P9PKf?R0PH%8FRN%63S02#6#N#\#N#c#N#I,SJD<PKf@RO%8GRG-0AHRPf>CjPKfARQPH%65S03#8RR1SJ=D<1VJOQ00#8RS'i=JD=%QI#O#ORT#F#O#N#N#Q#O#I1VJQ'7fB,VJ%6FRF#6S04#6S05#6S06#\#T!s$+8'7g01KFRQfDfC%66S07#6S08#F!su$IH00%8T/79Q05#FS09#Q!t6&O#I,59'2fGRT1SJ8O1%mL5JM[^7DfFRMg03iV'x%lLRL#kPQPTQ07#FS0:#6#d!v%$d#c#Q!v%$g00O@RQ#0RU#0RV#0RW#0RX#0RY#0RZ#0R[#0R\CsfE,SJ,r\,qL3J%KM%8IRI,pGS0;,5M'2fJRMfH;9TP?PM%0\RT#0RL#0R]#0R^#0S0<#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk#0Rl#0Rm#0Rn#0Ro#0Rp#0Rq,19RrPEPKfNRs%`HRtP8A[H=<R<PsfLRufKRvP8&0E=RwD4E3^0rP811QqfMRr$0DPKPrPtPQPAP<CRAbrvMP>PQP?PwCRI0CeW0PE%09R?/1qPKfPR>Pt%08S0=P<P>PsPrQ0=P!t&$]0P911UqP0PKfOR0PtPUP<P0PrPuPU!sJ%!sv&?!sv'RRUPtQ0=#0S0>P<PUP>P0Q0>!sx/VqPOPKfQROPPA9O0sR0/oQCjePKPOPtPV!t3$VPwG=!t,'S0!t-&TR?PtQ0>#0S0@P<P?PUPOQ0@!t-/WqPKfSR0PHPYPVCDRQPKP?!|J$P9D<X6KPKPQA90O>S0APYP0POP>PY1BVYR>%0q!yO$s,1YRP'2%85Ru,7GRrQ02#IRv,5uRM'2S0BP>PPPrPMPVPG%;GRMPYPu%;uRrEEPYPuPrPsPv%;vRrE>EAg01g:RP$0@R>%lPRP&0?DRA&0=DRx&0;DRyPy%:GRz%:uR{PyP{%:vR{F?20:y1R|P9P7g00S[R}g01:8R~'a20997=J}~dB08D=8H07R~b3b4b5Q0BP9b2G@GCPKP0PtPWP<Q0APW!vy+Q0?#0!v{+VRWPtQ0@#0S0AP<PWP?P0Q0A!v{/XqPKfUR}PHPZPVCDS0BPKPWPH%86!v|+Q0BA9}0US0BPZP}P0PUPZ1BVZS0C11ZsS0D'2%FFRF#8RU,7GS0E15UvR0'2S0FQ0CQ0DQ0E!xu$GPMPZPU%;UR0EEPZPUP0PsPvP!vs$!wJ$APxPyPyPz%:UR0PyP0P{F?P|P!v$+F!v$-}PtPXP<Q0BPX!v$:XRXPtQ0A#0S0BP<PXPWP}Q0B!v$/YqPKfW!y}$[!v$%FPKPXPHPu!v#-FA90}?S0FP[P0P}P?P[1BV[S0E11[!v#%Q04#8R?,7GR}15?vRu'2S0CQ0EQ0DP}Pu!u{&[P?%;?RuEEP[P?Pu!u{=?RuPyPu!u{3C!x}2YP<Q0FPY!u{:ZRYPtQ0B#0RuP<PYPXP0Pu!uy/ZqPKfY!x{$\!uy,YPHPU!uy1}0WS0FP\!xz$WP\1BV\!xz$\sRW'2%83R3,7GR0153vRU'2S0DQ0CPW!yQ$!uu%\P3%;3RUEEP\P3PU!uu=3RUPyPU!uu3D!xr2Z!uu%Z!uu1RZ!ut%\RUPt%0uR0P<PUPY!u1$!ur-[qPKf[RWPHPT!ur%?PKPUPHP?!ur-?A9W}XS0?PTPWP}PXPT1BVTS0F11T!xm'7#8RX!xm&XvR?'2S07Q0F!xm%?!uv&TPX%;XR?EEPTPXP?!uv=XR?PyP?!uv37!uv-WPtP[P<Q0?P[!#6g,Z!ut'^R[Pt%00R?P<P[PU!~j$!ut-\qPKf]!xh$L!ut,[PHP3!ut1}WYS0?PLP}PWPYPL1BVLS0711L!~d'5R5#8RY,7GRW15YvR3!~c&7Q0DPWP3!uv&LPY%;YR3EEPLPYP3!uv=YR3PyP3!~bC\!uv%\!uv7`R\Pt%0?R3P<P\P[P}P3!uv/TqPKf_!xl$]!uv,\PHPX!xl3US0?P]!xl$UP]1BV]!xl$]sRU'217GRR}15RvRX!{\&FPU!y?$!ul%]PR%;RRXEEP]PRPX!ul=RRRPyPR!{\?WPtPT!ul%T!ul7bRTPt%03RRP<PTP\PWPR!ul/LqPKfaRXPHP^PVCDR}PKPTPHPY!uk+P}A9XW[S0?P^PXPWP[P^1BV^S0D11^sR[!#8G$W#8R},7GRY15}!~P&!{V$[PY!~P+^P}%;}!~P$^!v\$!ur<}!~P9!x`/XPtPL!ur%L!ur7dRLPt%0RRUP<PL!|q$U!ur/]!#@D$cROPtP]P<POPXP\P]!#A>/!st+fR]Pt%0UR\P<P]PLPOP\!st/^qPKfe!vh$_!vh$YPKP]PHP}!vh,YA9XOTS0?P_PXPOPTP_1BV_!yT$_sRT!#90$FRO!|M'}!|M$['2S04Q0FPTP}P[!vj&_!|L%[EEP_PYP[!|L?[PyP[!vj34!vj2^!vj%^!vj7hR^Pt%0\R[P<P^P]PXP[!ut,Q0<!sM%gR}PHP`!uv$TPKP^PH!#K$$8!u{,TA9}XLS0?P`!{|$LP`1BV`S0411`sS0F'2Q05#8RL,7GRX15LvRT'2S05Q!u{%XPT!uy&`PL%;LRTEEP`!xP$!uy<LRTPyPT!uy35!#3G0Q0<!uz$Q0<!u{/S!uU'jRZPt%0[RTP<PZ!{%$T!xr/_qPKfi!xr$a!#3J+Z!|]0Q0?A9X}]S0?PaPXP}P]Pa1BVaS0511asR]'217GSR}15SvRY!|V&5P]P}PY!uo&aPS%;SRYEEPaPSPY!uo=SRYPyPY!|VC_!xj%_!#<$,<#0R_!un%lRYPt%0TR}P<PYPZ!u,$!un-`qPKfkR]PHPb!un%<!#>t%L!un-<A9]X^S0<Pb!yW$^Pb1BVbS0?11b!xg'2#8R^!xg&^vRL'2S02!wY$F!yB$!uv%bP^%;^RLEEPbP^PL!uv=^RLPyPL!uv32!uv-]PtP`P<Q0<P`!xe-_!ut'nR`Pt%0}RLP<P`PY!~\$!ut-aqPKfm!xd$c!ut,`PHPS!ut1X]ZS0<PcPXP]PZPc1BVcS0211c!ut':#8RZ,7GS0:15ZvR]'2S0?Q02Q0FQ0:P]!uv&cPZ%;ZR]EEPcPZP]!uv=ZR]PyP]!uv3?!xn2a!uv%a!uv/!{]+pR_Pt%0LRaP<P_P`PXPa!uw/bqPKfo!xm$d!{],_PHP^!{]1]XYS0?Pd!xm$YPd1BVdS0:11d!uw'8!#5P&X15YvR^'2S08Q0:!xm%^!uu&d!#5Q$^EEPdPYP^!#5Q>^PyP^!uu38!xm2b!{e%b!{e1!uw+rRbPt%0aR^P<PbP_P]P^!uw/cqPKfq!xp$e!uw,bPHPZ!~V2]`S0?Pe!xp$`Pe1BVeS0811e!uw%%I5R`,7GR]15`vRZ'2S0:Q08Q0F!yI$!uu%eP`%;`RZEEPeP`PZ!uu=`RZPyPZ!uu3:!xl2c!uu%c!uu:tRcPt%0^RZP<PcPbPXPZ!uu/dqPKfs!xn$f!uu,c!#5M4]X_S0?Pf!xn$_Pf1BVf!xn$fsR_'2%65#8R5!xm&5!#5S+:P_!yG$!uu%fP5%;5RYEEPfP5!#5S>5!#5SD]PtPd!uu%d!uu1Rd!ut%v!#5S$ZRXP<PYPc!u3$!ut-eqPKfuR_PHPg!#5S0`!~]1_]bS0<Pg!yV$bPg1BVgS0?11g!{d'3#IRb!xm&bvR`!xm&?!xm%`!uv&gPb%;bR`EEPgPbP`!uv=bR`PyP`!xm?_PtPe!~[%e!~[-d!ut'xRePt%0XR`P<PePY!~^$!ut-fqPKfw!xj$h!ut,ePHP5!ut1]_cS0<PhP]P_PcPh1BVh!xj$h!ut,6#8Rc,7GR_15cvR5'2S03!~\&_P5!uv&hPc%;cR5EEPhPcP5!uv=cR5PyP5!uv33!xn2f!uv%f!uv7zRfPt%0`R5P<PfPeP]P5!uv/gqPKfy!xl$i!uv,fPHPb!xl3YS0<Pi!xl$YPi1BViS0311i!~Y'W!#5P$]15YvRb!xj&3!xj%b!ur&i!#5P$bEEPiPYPb!#5P>bPyPb!xjCg!ur%g!ur7|RgPt%05RbP<PgPfP_Pb!ur/hqPKf{!xj$j!ur,gPHPc!xj3eS0<Pj!xj$ePj1BVj!xj$jsRe'2%6W#8RW!xg&WvRc!~V+e!yC$!ur%jPW%;WRcEEPjPWPc!ur=WRcPyPc!~VCh!ur%h!ur7~RhPt%0bRcP<PhPgP]Pc!ur/iqPKf}!xf$kPVCDRePKPh!#MO0eA9_]fS0<Pk!xd$fPk1BVkS0F11ksRf'2%IFR],7GRe15]!#5F%!{T$f!|z$!un%kP]%;]RYEEPk!yR$!un<]!#5F8!xb3i!un%i!un6p+01ARiPt%0cRYP<PiPhP_PY!uq/j!sN&@RePHPl!ut$fPKPiPHPW!ut,fA9e_gS0<Pl!x5$gPl1BVlRg11l!#8=%F#8RF,7GRf15FvRW!uu$PgP_PfPW!ut&lPF%;FRWEEPlPFPW!ut=FRWPyPW!ut?ePtPj!ut%j!ut:CRjPt%0YRWP<PjPiPePW!ut/k!sN&BRfPHPm!ut$_PKPjPHP]!ut,_A9fehS0<Pm!x;$hPm1BVmRh11m!{[%IOR_!~N&_vRg!ur%hPeP]Pg!ur&mP_%;_RgEEPm!v`$!ur<_RgPyPg!ur?fPtPk!ur%k!ur:ERkPt%0WRgP<PkPjPfPg!ur/l!sN&D!~R$n!{^+kPHPF!{^0]fiS0<Pn!{\$iPn1BVnRi11n!{]%6O#8RO!{_&OvRF'2RhPi!vH$F!us&nPO%;ORFEEPnPOPF!us=ORFPyPF!us1Ph!~L2l!ur%l!ur:GRlPt%0gRhP<Pl!|x$h!ur/m!sN&FRFPHPo!ur+lPHP_!ur0F]jS0<PoPFP]PjPo1BVoRj11osR]'2Q09#8Re!#5C%evRf'2Ri!#5r%f!ur&oPe%;eRfEEPoPePf!ur=eRfPyPf!ur2i!ur-FPtPm!ur%m!ur:IRmPt%0hRiP<Pm!|v$i!ur/n!sN&H!{Z$p!{Z+mPHPO!{Z1FkS0<PpPfPFPkPp1BVpRk11psRF'2Q06#8!{\%O!{\$]'2RjPkPFPO!#LJ'p!{[%]EEPpP_!#LJ>_!#LJ6Pj!{Z2n!ur%n!ur:KRnPt%0iRjP<Pn!}d$j!ur/o!sN&J!{Z$q!ur$OPKPnPHPe!ur,OA9]flS0<Pq!{Z$lPq1BVqRl11q!{Z$Q01!{Z5kPl!{Z0q!{Z,q!{ZCePyPe!ur2k!{Z2o!ur%o!ur:MRoPt%0jRkP<Po!}d$k!ur/p!sN&LRnPHPQ!#88'o!{Z1fA9n]mRfPQ!si$mPQ1BVQRm11Q!{Y&0#!xg+H!xg$o'2RlPmP]!|Z%!us$Q!xg%MEEPQP_PM!xg?_PyP_!us2l!us-nPtPpP<PfPp!ur&%0d/1q%0k!uv$%W8RpPN!s$%DH!s0i/5OS00Pd1U9NXPDRdP!s$apO1S0<O1S01O1S06O1S09O1S0:O1S0FO1S03O1S0?O1S08O1S02O1S05O1S04O1S0DO1S07O1S0CO1RfO1RnO1RlO1R{O1R_O1RzO1RrO1RvO1RsO1RMO1RQO1RVO1RoO1RHO1R]O1RmO1PdPkPmPdPjP]PdPiPHPdPhPoPdPgPVPdPWPQPdPYPMPdPcPsPdPbPvPdP5PrPdP`PzPdPXP_PdPZP{PdP^PlPdPaPnPdPLPfPdP}Q0CPdPTQ07PdP[Q0DPdP\Q04PdPUQ05PdPRQ02PdP3Q08PdP?!#Nv$0Q03PdPuQ0FPdQ0BQ0:PdQ0AQ09PdQ0@Q06PdQ0>Q01PdQ0=Q0<PdP8Pp%;pFG!s$A!}?%E>P9H06Q00&057%W7#!|#$N,VJRF004S%KF%KSp+01P,VJ/iS#K[[203GI15=G%KIQ0;,5=[[%KGRSg01f^RJA~GI8UW8Q0;#K\J^8Sp-0RS!{U$DPD1}D8P8PACg!s+&xPy1fD=1{D6R65|y%m4R=PyP6%:NR6P!s$$DMP!s0h=zyeP=Py!$5A';J02CeCe!}$,X:DW9%K9P8!|XvP;[[^:D^9SP9!#44$TRSPt%LB#L!s$/RtP<P!w?$Rp+01QPt!#4p$%WBP:P@O4b2bHbIbJbLb;W0X7EP9O1n0110001020111100X1!s>_0!s>~!s>~!s>~!s>~!s>R0!t-~!s>~!uN\!s>AP9O1!{l$CyWAW@WBWCWGWEWFWDW=W?W>f:f9f8!$C+2O;n40!{g$!s#$1;110110310210810:10910;107106104105W<XKDXOKWMWNo"). Qed.

  Lemma p1_know_ok : ltac2:(zQ "b0!iqd!it1!ilf!j7!jk0!pk8!prf!pq5!ot7!km0!op0>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8>2sp@1$1@1$0#k0>3can$3>0@4$6^4^3^2^1@4$9$a@1$5@3$7^5^3^2^4$8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefPrintfFirst ()) ["Plain"] "##Z6p'0h07__arithh14__ffh28__varmaph35__with44__x1h51mh61dh76__sat0h8!s/%1h97!s/$66h:!s0&7h;!s0&8h<1zh=1xh>2Hah?4__x2h@1bhA4cstrhB2E0hC2E1hD2HdhE2HmhF3HsphG2PHhH3Q12hI2Q3hJ2Q4hK5Qcan0hL6Qcan65hM7Qcells0hN5Qimg0hO5Qsp17hP6QspHi0hQ6QspLo0hR5Qstk0hS2Z0hT3canhU1ihV3memhW1nhX4regshY2sphZ1yi002Q1i013Q11i022Q2i034Qcani04!tP%4i056!tQ%i064Qimgi07!tQ$6i085!tR$i095!tR$i0:4Qstkp%0p&0p;1p;2p;4p;3p;6p;7p;9p;8p;<p;@p;5p;Bg003\j12Tg0037j11Tg00]=j1T!s/$[j1sTg000Nk20PTg005[j1fTg03`CR0k40>Tg03[aj3LTg01MOj1MTg00dMj4^Tg006=j17Tg029Oj3WTg02<;j2\Tg0146j2:!sz$Aj3<Tg01C\j28Tg03aKj2NTg01DFR1j20!s:$kk406!s;$bj2=Tg00A@j25Tg00gbj1_Tg03blk20!u;$4Aj1pTg008ij1>Tg01Gcj4kTg01Iej2hTg00@^j2jTg01W=j2uTg03jaj1t!t%$[j2FTg03Z^j2ZTg007bj1rTg00:nk20YTg00<7k30X!s:$Pk10WTg009Hj2!s9$=@j2oTg00>Ik20V!v'$[k10OTg00Gak30N!tv$aj1lTg03kgk10MTg01lQk30Lj4yTg01^Uk10JTg01YDk10I!s0$bk10HTg01[0j2gTg01\6k20E!s0$Xk20DTg01]Dk30A!s0$ck40@Tg002Yj6[Tg01O\j2YTg03lmk70=Tg03e7j2d!v,$Zk20!wX$XBk30;!s0$fj2bTg01ZMj2]Tg03n4k707Tg03o;m905!t^$Sk304Tg040Ck803Tg02UCR2j2aTg02KLj4STg01FAR3j23Tg01maR4j1ITg02Ifk102Tg02M<k408Tg02JDl<cTg041Hm@00Tg042Nj4RTg01oAj1~Tg02]4j4}Tg043Nk50?Tg00B5j4|Tg044`k20BTg01NUk10CTg01Pcj1{Tg01V2j3zTg045dk20FTg0267k20G!si$Pj2iTg0471j3x!s/$Mk50KTg048Uj6w!x8$Aj3vTg01`:j4q!s/$ej7nTg01alk70QTg01bPk80!u%$aIk30STg032lm<0TTg033QmB0UTg049^k60ZTf0R5#2#2p=B%15#1p=O%2!s-$;!s6$#1#1p=mg00HjR6g00O_R77<5p=P%2!s`$!s$,p=@!s:+p=D!sf+!s$'p=K%15#2p=e1075p=4g00K;R8f1R9;v5p=C1g65p=9P6P9g01eZP5Cqp=U!s4$c4R:g01cSR;P;g01d3R<P5g01e:R=Fnp=Vg00S[R>g01:8R?!tt$Hf2R@P:P;P;P<!s}&dSP5CqP!sZ$6P!sD,9P5K0Qp=Gf3R=!s<+@P9P5L0Rp=J1F65p=Ag016\R:P6P2P4P1g0383f5R2f4RAP=!sW%M<cp=`B0S695p=?P6P7!sA'E[p=QP:P6!s$$4P4P2P!s^+N<0Tp>09!sD&!s$%3P5P9P@P3P=PAP2f6R3f7R4f8RBf9S00NB0Up>0:P8!so,J0Zp=Eg00LDRC#2RD#1RE#TRF%2DRG#2RH#2RI#BRJ#TRK#sRL+0P%TH#sRM#fRN\L!sp'H0>P0!t#'g01KFR0AL2=@#MPAg03<RS01C^P5f?%7CROg03EFRP5WF'\%1H#O#;!s&$m#B#7,:K5<Lf@RQ%7DRR=WFP'\f>RS5<LfART%1E#7!s<%1:K7RP5<L18KQ%7IRI'N#P%BJ#@RQ#D#;#;#@#7RF18KT'0fB,8K%1CRT#ORE#1RU#O#K!s$+7RV'0P0fDfC%1GRG#1#;#DRW#7RXH06%7QRQ/05%BE#;#D!t#$E,=5'5fGRY1:K9O1%_M5<N[^U6fFRNg03iVRZ+01%pM!vR$[P0PY%;GRG#2!uh$e#m#e#B#7RY,:Kg00O@R\#>R]#>!s$/R^CkfE,:K,h^,jM3<%4N%7JRJ,uRR_,=N'5fHRN#t18KNR`#41=`_'5fIR`,FLfKRa?L`N#M/Z\=<L`1:K`RN,FLfLRbfJ;L`#M/Z]=<LN1F6718KPRN#PfNR`?Lba#MRcfMRd%r\Re00YIRfB0XeFVRg&0WW,Xe/oXRW20VQERh&0O7Ri/XY%r]S0280N^S03%2U!vT+U,XiRj%;T#B!s8&T'oRk%l8S04'CRl'CRm'CRn'CRo'CRp'C&0MZB0L0cdRqPfPpP0PcPdPePIg01g:Rp#lRf%ppRp&0J6Rr&0I6Rs&0H6Rt1g67Ru%9I'U'V20Et<R<P5P@1F>?S0520D5@#HdB0A679H0@R?b1b2b31=7IP5b0PLPb18K5R>/NI#PX@Lf;1Zc\R\P@E[1Yce,8KRv!sC$eK0=PqPgPo!tp+FPV!sh$0F>10>V'5X@L18KbR>/dIRo%4>%4IR>18K`/NI#4[[Rg20<RJRw1=7R%4J1=7_Rx[[Ry%4RRzg01f^R{B0;RJ9UW>RJ%4_\{^>zRzPfPp1b69R{PsPt1]6CRC%9V56tR|%_;R;Pt%9F=6tCR}P;AGt}|CJCJP<P!uk&X46105V10F910F@10@V'5[[^46P5fPR|,8KR~f=PSO3b0b9b:b;P!u~%0Fv10vV'5eK07PqPWPn!uz+bPXP@PBPoPgPwPyPJP!tx$P!tt$P}P;%9XR}96tuA6t}C5Gt!tb4F5%4X10X9'5!t\%P~PSO2!tS'N905PqPhPm!tC&QPE!t1$rPs%9Q96tu!sw,%4Q!xG$!tY/!sN$E%9R>046KRR56t!sW,10E_P5b0b7b8P4L03PqQ03Pl!t:&iPPPYP^Q021:Ka1FLPP91a]^%7HRH,0ORPP]PO%AOP^PH%AHR]E`!tC,O%9HRO!t>0PPP5b0CS1a^^10HHRPP^PHP]!s+%!sc,A6tOO!s]635YRP#4X<6!t5,Y,?uRa!v#1137YRY#4!v+$NP5CQ%I^Ri,3P/0_X<613YiRl/0_RE13YHRQ/0_RmP6P6P1P5X=6RhP11095$02XZ6X=6PlPQPh!s$$6P6g03Hf1395H08#AX56XW6PYPY%AYPiPHPhPh%I5#AX=:!uQ%J09N:0:P_P_%A_M<c!wj31?aO=6tR!uk-m!w`'CSPEe!u=%P0P`1:KPP^Ck1:Kb!#66$5<[X<6P2!sJ%N@00PqPkQ04135UR[#41=[_%4TRM13[T/0_'5'5'5%49R[%I9,3@/0TR^P0fRRb13AU/3=,:KP@CR#H[[^5:^66'5!vW$7URP#41=P_13PT/0_,5M'5'5R`P0fQRE13P=Rm!sd+\^\!sf&!zT5URa,?uRO96tu1UOR,Vt%9TR]!s6$?O]=6tR5Gt!s%%!v7-`!zq+EPmP@%~@Rm%I@#4R`18KERH/dIRh%4HfS,8K/NI#4\>[R>!}Y5A6tuCP;1?OC!tU$a!}U2%4513P9RP,0U!}T&BP3!}T,bAPmP`PhP!t&161b6@P9PrC}!#4]%DRD,?C=6t]!t<$D%1G!#9,'G#956!~w3X?61359/0T13P@/0G[^46^?6P5%I4PBP2!#4V+bAI0?XE^XD[X5:X66C|PN!w43A6tuu1UuR,V!vl11077/5x!vq'-0B7CQ&0CjR7,Yc,8K%{jRx'3R?#41=?_13?!xd-P0PEfO9Lb|#MRb/Y7,8K/3x!yV/!xp,'5eAzcjTP0PE20Fbj!sM<!#4-%kCye20G8qDE!s$,!s@$ZQ051i6:/i6g04:?;xZ#HdP3I0KEw!sd%Q01C^ebSbCbBbFWLWKWMWNWRWPWQWOWHWJWIf:Q00PBP4P3!#Ea-O;n4000010!s#$1;110010210110710910810:106105103104WGXT6XYLWVWXo"). Qed.

  Theorem printf0_first : ltac2:(zQ "h41!iqd!it1!ko3!oq3!op0!jb!k1!ilf!jh1!oqc!jk0!jo4!or7!js3!kgf!j7!prf!ps6!lia!ovd&>0@1$1@1$0#k0@1$7@1$1@1$0#8>4regs@2$a@1$0#5@1$1@1$0#k0>3mem~0>2sp@1$1@1$0#k0>3can$f>1K$h2>0@4$h0^5^4^3^2>0@1^2@1$6$3>0>5regs'@2$a@1$0#5@1$1@1$0#k0>4mem'~0>0@6$h1^9^8^7^6^2^1@4$e$4$d@2$8@5$b?2fx^3@2$2@1$0#k0+knnnc^2@1$c$4?5model^6@4$e$4$d@2$8@5$b?2fx^8@2$2@1$0#k0+knoi8^7@1$c$4?5model@2$h3@3$5$3@2$9@2$2@1$0#k0+1@2$2@1$0#8+j0@3$5$3@2$9@2$2@1$0#k0+1@2$2@1$0#8+a@1$6$3^4").
Proof.
    (* LPS 75d69e00: replay replaced (p1_sound gained the reader premise). Shape from
       boost-beast http_request RefPrintfFirst.v printf0_first; the canary cell is
       boost-json's 0x12b6f8. *)
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
    - krd HK 0x12b6f8%Z 8%nat Hc. rewrite Hc. cbn [ev ENV]. rewrite P1. reflexivity.
    - intros a n Ha Hn. eapply frame_mod_store_ok; [exact FM|]. apply Qstk0; assumption.
Qed.
End Plain.
(* [comment removed for export] *)
