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
  Hoare RefExitBase RefStdioDefs RefStdioWrite LibStdioCall RefPrintfBufBase RefPrintfFirst LibTail LibDiagKn Spec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefHdrErr () := KReplay.lz_vm "#%7VC47Corelib7Program6Basics4flipC46Stdlib5Lists4!s+#6nth_ok!s_,4Init5Logic8eq_ind_rK!s},Numbers7BinNums8positive01!sKG2I!t672eq00!s@29Datatypes4list00K!sFA1!sf<6option!sh/!to31Z02K89OSSVerify6Proofs:boost_json:fuzz_parse3lib8SymExec23SX24expr01C13~~~!smc2!sm&!tz?3!t3c3!t33!vQ23nat!v0_6kentry05!v2c!so'6!sok7!sok4!soc5sadd!yM,7!snN<LibStdioCall9s!s0#_res!sr+!{pC!|:=4prod!|z?!sF$1!}|83an!sa5!~?,1K!s[<1C!zG<fstC!{S]s_pc!v2%!t0=sndC!wC\:!wC%call!t6&!sq\6sc_ret!smc4sc_f!skc5!sk#d!tYgs!skgl!{>B!#8P$!#4^e!|O&I!#6]a0!smc!t^'!so'!#8[>0!#<fF3!tZ]8sideco!~:#!t\&!#4Yf0!xA3!uP61K4ELinuxProcessSemantics5Riscv5Instr5aluop!#3d3!#:j11!uv]9sym_state!xFe7script!uu+c!viO9RefHdrErr5hs_rA!y23!{{3bool00!t1^cA!tt`6hs_sr!sjeknA!vLdsc!w7eC!sidc!sico_rA!sid!xEdo!xEfo!xEfo!xEeo!xEeo!xEc!vo%F!|zf!sj&!#6S=N02I45stdpp9bitvector;definitions2bv00C!sI@DZ_to_bv_obliga!s:#_1!#EJC2!s{A7!s{&!#>gO8PropExec3rdn!ur'!uTC1!t1/!t&96images5Plain1M?loaded_segment!#@aV4Spec9msg_short!sh[;!sh#overru!uf&I!#;=?0!t1P6SymAux7sregio!t/&!#G_+!#V3$7!s+#Def3map!#V376!#V3$C!#M/]_log!vAV!u6&;log_c!vD#ed!{w3!#;j71!}'Z9h_!vH%s!t{ZRun7vals_ev!w3'!z|?;bv_unsignedC5!#Zi%6ZArith6BinInt1Z2le!sB<3opp!sC=ad!s|=3sub!vDZ3ENV!uT&!#G6\a_base!smdedenot!smc5a_off!z_]6r!tU-I!#V?b!#Dy`;!{&+_w!zB'!#a[42In!#`G8o!tN#!u8O=!u8'Sound4SX2S4fla!wZ'!z><pow!{Y>t!sB<>pow_pos_nonneg!sN<:!sN#!sJ%K!uw'9micromega6VarMap1t02I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PE!#aA#!sIE1!sIE6!sIE3!sIE7K!uPL1C!sQ55Tauto8B!sJ&!sH6:Z!sp+=Z!sT$CheckerC!w7<4find!sqAC!sq0_s!z3#!xN@1!~/W<!|Q'!{0,K!uz<G!vF'4!sJF5!sJF8!w6<5eKind!#P0<unit!zG8!se%4kind!yy8!xh13Op2!yZ#!t5@!#aj85False!#lk3!sC%4True!|b8!xP-;!~#%!wp$!uB8!tz65C!#VW?7Prelude5bv!#@s4!#FX,length!#5Ub7regs_ok!#:4U!st7know!st,7!#9SQDrive9junk_vals!#D12!#E:2app!t1P5Frame9f!s+#_mo!#b@V!#Ij'7seg_rom!#:T<9nth_error!t0P9!u~'X8!vk$nth!wbi9!#`d$!wd,!#:':6of_na!#:s34Znat5Nat2Z7inj_iff!#HP77iff_sym!sf>9is!#;4<!#3g23!#?BY>!#?B+!#5o+!srZ?!sr,!#As,!#aW:?!s<25State5event02!{|RhapeAlg6t_emi!tG'!#b,f1!ymV!#D00carry!z[i8sc!vx1!#O]86Forall01!#HT]s!x9#s!|bjmem_!#ILZ!u}7log!zl-!#>LVA!#Q6,_!#5A#!#73^8blob!#P0-!~O7f_equal!$'K;trans!#9Qcu_sm!#u?'!{h]3env!{b+!v2O!#tQ3wb!slhp!vy>8iff_refl!#BC5;ZifyClasses5mkrel!#GnD4!snB;rew_!tB%v!sQB3inj!#@W@3Sem5alu64!#<QX5v_ad!#=;V7LibTail7vadd_wZ!{gW!#=~'alu!tU,K!#Q=:1!xsasp!trV!#>h-img_!#bd'C!#:6Pm_fds!sZQ9fd_lookup!#;JP7FdE!#{1%!s^P8m_halted!tuRm_vm_lazy!#y+PRef!we$Defs7s!#Tp#t!#X8&!#EHU7outside!yZ'!|f4!#Og+3!t,P>RefPrintfFirstA!ty&_!#F`2!zt13Nat!#_U#!z'Y@!#Hn'_!#KI%!t3&!#G%4:!sG%_ap!#f'3Peano2lt!tSZ=!#c?%!t%#_l!#7-fsr!slgkn!y<\D!w|+!#;w$_s!#=RX!y'29rz_run_l!$0ec7sc_bufp!snc8!sn%sz!socE!$4m+!#YR$!{d$!s|V!#oD#1W!#8v^4mks!#J5Q3Run6config01!#4OO!#J4'8realiz!$-P+!#=KA7!#=v%!#Ge\8sym_exec!t>H5mk!~Z$!sK@6!sK$2!#A773not!#P2E7!x]Rcfg=hunspe!yQ#cf!#rN%!#|tZFUELH!si`6STOPSH!~Me4scr!#kZ`=!#xv'_le!#4}&!#Tz<6inj_lt!t;Z4h!#6w'!sh]!#6sW!|R+4TS!$@F&I!#U#V0!$%k]kn!$%k%!$<[]s!$<[/!t[Z7hs_cov!$/:`<hs_itinera!#Un&!#d@H!#kz68ZifyInst7Inj_Z_Z!{5eimg!xVW!#F3'0!v{a!$0v`?!$&[,!}O,!z:\o!z:,!uL\o!yIgo!yI3!v>g!xX+!uRaC!yE'!#F:7e00!#H$6sub!#;7A9and_morph!#eZ;8max_spec!|OD5Psatz!#wT7!sO8!#w76!#o7:!#xQ>3Pol!#qTE!tD&4!$`i,!u|&?Rel!$6}#!s6&=eq_Tran!$Ij$!$1o;nth!sr59M!vl#isms:re!vU#tful!tAE<eq_Reflex!t@0!s|5Jr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^??eq!tM#per!tT;!sR,@!u$0per!#G>Yget!#Mp&!t<>M!#La$co_!$6~#v_impl!|2%ism!x{<seq!#>3Q!#PO%;nth_map_!sh#!tl&!#Qv4=app_nth2_plus!#G[\2!#dn&!#7U[!#uf-!$,|;max!#GRE6!sg+5!sf$8!#4}#Na!#4l+!#Cs<;inj_sub_max!sM>8!sM%cc!#DfCe!#4<M1i!v\Y3hfH!#M6'!#uK;modulo!ydP!$;K%6stk!#{:X9LibDiagKn8cell!#|v,!#@/I>!#e?#!sE+@word_to_le_bytes!t\Z9cana!#xy-!smO7Seq!{`#9!~X#_zero!{b`9h_ev_junk!}^2!yG,9SatDivModCZ!#Y6#!#yR$!$63&!tFO@!#Md'BufBase>!$%V%_by_idx!tR%!#g,7!$+^$1!t=a9all!t@#32!vS`5HF_FR!zP`:diag_!zU$!snV!#8N'9u64_range!|-akn!tZ\!}]&<kalign_int!zQ'!smY!uD$!smc=kwr_of_!#3B[!sn&:!#li#!t[/!#3AX8store!tY#!z~`=data_!sr+!yOVAgentLib7!yO#li!#|Gi6estart!w-];k!#6Z#!xd[!{0,;!#6Z%know!so`?!}W,!sse;!$6w%!#kq#!#5:1!$&a82!t8Z6CANARY!t3%!#=hY6hfP!#qI,!#9P\!$:[/!sm]!$:T0!#Zi\a!$+y-!t\P!#p#';!sj%!|H#!#t_\B!#nI+!~%1k!wva1!w/`8hs!#lU$!}|]7reg_val!wpdsr_g!${4W!#KH'5krea!#wG'!#@b3!#j?/eq!#k{#!t6X9!t6$!#~[+!wC\o!wC/!#^H\!$gT,".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4conshc3nilhc3nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~ke6kentryke4EVarke2SAke4ELit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9RefHdrErr4FPX1~~~~~~q95HF_FRke5KWordke3KWrhc3app69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~hg66CANARYhg6adiag_cellshg68kn_cellske6KAlignke4KImgke6KRange46Stdlib6ZArith6BinInt1Zhnf3opp69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLibStdioCall~~~~~~hpe9stdio_reshpe4SCR_ke4exprhc4prodke8sidecondhc3fsthc4pair37Corelib4Init5Logicih82eqke9sym_stateih83andq95hs_schc3sndke7scriptshc4boolq95hs_rAq95hs_rCke4s_pchc4Somehc6optionhpe4sc_fhpe5sc_fdhpe4sc_lhpe6sc_rethpe4sc_shpeastdio_callq95hs_cAq95hs_cCq96hs_knAq96hs_srAq95ho_scq95ho_rAq95ho_rCq95ho_cAq95ho_cCq96ho_knAq96ho_srAq96ho_srFq96hs_srF04Npos35stdpp9bitvectorbdefinitionsjj82bvhc4None69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~jm23rdn69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~jq49msg_short69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~ju8floaded_segmentsjj87Z_to_bvjq4bmsg_overrunhc6length69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymAux~~~~~~kl47sregionke5saddrhc4trueq99h_regionskl4blog_coveredke5s_logke3env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~kt08blobs_evke3Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~lhd7vals_ev69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9RefHdrErr~~~~~~lm15HF_FRhnf3subjj8bbv_unsigned37Corelib5Lists7ListDeflrc3map79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9RefHdrErr5Sound~~~~~~lta3ENVltabh_regions_wlm19h_regionskl46rdenothnf2lekl4cregions_flat3h5LinuxProcessSemantics5Riscv7Preludemlf5bvmap3h5LinuxProcessSemanticsfLinuxProcessSem3Runmoe5mkCfgjm24mkstjm27seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~mt6dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~nhe8realizeskt09junk_vals79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~nn27know_oknn27regs_ok3h5LinuxProcessSemanticsfLinuxProcessSem5Statensd5event69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~og49frame_modlm14h_knlm14h_srlm16hs_knFlm16hs_srFnhe4TSetnhe6t_emitjq41Wlm16ho_knFlm16ho_srF37Corelib4Init3Natop83sub37Corelib4Init5Peanoor12leor12ltjm24getrlm13ENV79OSSVerify6Proofsaboost_jsonafuzz_parse3lib9RefHdrErr5Plain~~~~~~ou06h_valske2evhnf6of_natou03hfHou06hfPostnsd5Modelnsd8m_haltednsd9m_vm_lazynsd7FdEntrynsd9FdChannelnsd9fd_lookupnsd5m_fds" s.
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
Definition HF_FR : Z := 256%Z.
Definition STOPSH : ltac2:(zQ "20!j4!h9@1$0$1") := ltac2:(zQ "30!h9!jb!k2@3$1$0+tvqk0@3$1$0+knls4@1$2$0").
Definition FUELH : nat := 5000.

(* [comment removed for export] *)
Definition h_sr : list expr :=
  Eval cbv in (map (fun i => match i with
                          | 0 => ELit 0%Z | 2 => EVar 0 | 4 => ELit 0x10b6b8%Z
                          | _ => EVar (3 + i) end)%nat (seq 0 32)).

Definition h_kn : ltac2:(zQ "20!j4!od@1$0$1") := ltac2:(zQ "h10!od!jb!p6!pd!q2!ua!v2!va!hg0!k2!hk2!hkc!hla!hm6!hmf!hn6!hp7@3$8$0@3$1$0@2$d@1$2N0+h0@3$1$0@3$f@1$2N0+hggggglg0+nvvvvvvvvvvf@3$1$0@2$7@2$3@1$2N0@1$h0$5$5@3$1$0@2$e+hggg0+vhgg0@3$1$0@2$7@2$3@1$4Z+vpgg0+jkgg0@3$1$0@3$6@2$3@1$4Z+hgrmh0N4@1$2N1@3$1$0@3$6@2$3@1$4Z$aN8@1$2N2@1$9$0@1$c$b").

Definition sc_dummy : ltac2:(zQ "10!htd$0") := ltac2:(zQ "50!q2!k2!hua!hv2!od@c$2ZZZ@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$0Z@1$1$3@1$1$4").

(* [comment removed for export] *)
Definition hs_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x47588 h_sr [] h_kn 35) []).
Definition hs_cA := Eval vm_compute in (carry (s_log (fst (fst hs_rA))) h_kn []).
Definition hs_srA : list expr := Eval vm_compute in (s_regs (fst (fst hs_rA))).
Definition hs_knA : list kentry := Eval vm_compute in (fst (fst hs_cA)).
Definition hs_sc : stdio_res := Eval vm_compute in
  (match stdio_call 35 hs_srA hs_knA with Some r => r | None => sc_dummy end).
Definition hs_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0xe02d8 (sc_sr hs_sc) [] (sc_kn hs_sc) 67) []).
Definition hs_cC := Eval vm_compute in (carry (s_log (fst (fst hs_rC))) (sc_kn hs_sc) []).
Definition hs_srF : list expr := Eval vm_compute in (s_regs (fst (fst hs_rC))).
Definition hs_knF : list kentry := Eval vm_compute in (fst (fst hs_cC)).

Lemma hs_itinerary : ltac2:(zQ "i10!h9!j4!hv9!ig0!igb!ih1!iic!hv2!ij2!ije!ik5!k2!ikd!od!il3!ild!htd!im4!imc!q2!in4!inb!io2!iob!ip3!ipc!iq4!iqe!ir6!is4!isc!it4!itd@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h1+tvqk0@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h1@1$b$3@2$9@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$hd@1$b$3@2$9@3$6@1$h6$h0@3$hcNi3$i0$hf@2$h5$h0$a@2$9@3$6@2$2@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0@1$ha$a@1$h7$a@1$h8$a@1$hb$a@1$h9$a@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0+ugit8+vppq8+2@1$h3+hjptc@1$h3+hf@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h2+knls4@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h2@1$b$3@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$he@1$b$3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "##DDp;1p;3p;2p;<p;4p-1R0p10000R1p4p710p9P0P!s2$2!s3/3110p9!sQ$N!sO&1000i!s2&8g001Gj11Tg001lj10Tg002Qj39!s/$kj1WTg003Kj1V!s/$kj1bTg004Mj1>!s/$kj1=Tg0062j18Tg0079j1\!s/$Wj3eTg008^j12Tg009=j2cTg00:Fj3aTg00;Oj2ZTg00<Xj2`Tg00=aj2@Tg00>il<lTg00@5j2^!s/$Wj2OTg00A7j4H!s/$Wj2<Tg00B2j2S!s/$Lj4I!s/$gj3LTg00CDj1]Tg00DIj3U!s/$fj3kTg00F1j1jTg00G8j1iTg00H=j1hTg00ICj1gTg00JHj1fTg00KMj3:!s/$mj3KTf0R1#!s$&p=T%0!s-$4%01#0p=7%11#0#0#0p=G!s:$#0#>p=A!s>$p=3%1!sV$5!sB&p=C!sL'0p=;%>1#=p=?%21#2p=R!s-$#2#2p=Jg00M6R0f2R2#8f1R3#8=:013:p=DA:0319:02p=N%83=:01p=[!t:$!s$/p=M%\1,@3p=F%01#>p=d!tM%>!s;$Yf3R4/@2?K31p=_!uB&p=Qg00N=R5f4R6%>4'@?K23;:1p=E%04!u4%#>,@6?K23=:51p=6%1!s?9Bf6f5;K6AK4!s9%5:5p=PA:5319:52p=X!sA+p=mg00OFR1g00OdR4#1R3#0R2#1R6#1R7#T#4#7#G#AR8;98g00PIR9#WR:%V9R9;99R;g00QTR<#bR=%13R3#1R>#1R?#7R@#1RA#3RB#0#5RC#4RD#4#ARE%04RF#>RG%C3R3#C#4#4#3#5#ARH%0FRI#1RJ#0#3#5RK#1RL#1#3#3RM#3#;#?RNPNPNg00R`#=RO%1J#3#4#5!s&$7#?RJ%??RPg00S>g00SjRQ#8RR%0IRI#0RS#0RT#0RU#\#=3eRV%2QRQ#2RW#RRX#RRY#RRZ#2#RR[#2R\#2#J#JR]#2R^#2R_#2R`#2Ra#2Rb#2Rc#2Rd#2Re#2Rf#2#JRg%=H%3SRh!ta$3Ri!uR$G#?%2g#JRj#8%2jRj!s'%?4%Jj!s:2!s'7=ER4%8_R_%8`R`%2j#R!te$!sO1%V03D3D9Def9Dcd9Dab3N5NP3D3D3D5NP7!s2$N,[Y7NV'[PO%1CRC#0RV#0PZPNPO%1V!s/'!s@$!s3'DRDPZPOPOP!s-&%1BRB#0RD#7RV#1RY#1Rb#0Ra#CPX%1?#5#M#M#MR?#1#5#T#MRd#1!s:$?1FR3PZP`%72R2#0,FRPZP_%1FRF#C!s4$%8^1FRTPZ%8]1FR2PZ%8\1FRSPZ%8[1FRIPZ%5I#3RI!v}&3#dR[#=%>S,cR%7URU#;#;RS#0#;#3!yQ$A%>d5aR1FRU%>U'Z%>S%7>#4#7R>#C#;#A'`%0ARA!sZ$;,YO%C6#;!s?$ZPO%Ci#3#APX%8QC_%0K!z^$4#T#ARi,@OPZ%8W%G>#4R>#0#ARW!s;%0I!xx$7#;#?%7@#5R@#7RI#;#AR6!sI$P4%3!z\'7,Y!s[$7!{<$!{>%G#?POPS!w?'IPZ%=6PO%1@R@#4#5PZ%=iPO%3@#3R@PZ%G>!sX$@PZ%=W%TA!sr$ARA!t_%=A1@OEPX%?F!xV$PZ%=8PO%7VR!xk&PV!t:&0YPX%=GPO%QaPX%??R?POPbPXP?!y+&#0Rb#4RaPZP4PO%3bRb!y?&!s-&%3!sL$!u3'!yU0!u[%7!su'BRB#CPZ%Ga#!s6%#5PQ!sT$QKRK#0RB#4Ra#QPX!si+!st&7L#3RL#0#3!sB&QL#3!sd+0MRM!tP,M!s/&Ca!sE%PB!sZ&3K!ul'h!yi$;Rh#C!tO'hPQPO%V5DEDED6D6!s++BDB!s+$!s8'B!s+&E!s2'FP!s:+BFPFP3X3X3XCmFPFPFP!sN,DBM<l,^<RO;9ORQ1O11Rh/O1RZ/O0RK/O0RXPKP0PZP0PhP1!s$$HPECHPGCHPJCHPPCHRP;9PRJA91[[RG1<;;RE'<RH'<RB'<Ra,<;RM'<1S18P;PM1S:9RMP;PaPMPQPB1S=OPJPH1SXPPGPE1S1[P;P;PMPMCI!s$/g00TIRM1OM:R;g00UUREg00V_3LRG7L:#]=918AUM:G=9:9%W5R51O5:RGg00Wb#WR8g00XB3L7U:=9:9g00YEg00ZI5kgg00[MRg,^<59=!ul3%jg%igCH%hgCH%ggCH%fgCH=9XPg00\P9L;ERE9LM!tS%[AUM:E!t1&]S9LG89U5!tB$'<!s$/do"). Qed.

(* [comment removed for export] *)
Definition ho_rA := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0x475a4 h_sr [] h_kn 35) []).
Definition ho_cA := Eval vm_compute in (carry (s_log (fst (fst ho_rA))) h_kn []).
Definition ho_srA : list expr := Eval vm_compute in (s_regs (fst (fst ho_rA))).
Definition ho_knA : list kentry := Eval vm_compute in (fst (fst ho_cA)).
Definition ho_sc : stdio_res := Eval vm_compute in
  (match stdio_call 35 ho_srA ho_knA with Some r => r | None => sc_dummy end).
Definition ho_rC := Eval vm_compute in (sym_exec RSEGS FUELH true STOPSH scr0 (SS 0xe02d8 (sc_sr ho_sc) [] (sc_kn ho_sc) 67) []).
Definition ho_cC := Eval vm_compute in (carry (s_log (fst (fst ho_rC))) (sc_kn ho_sc) []).
Definition ho_srF : list expr := Eval vm_compute in (s_regs (fst (fst ho_rC))).
Definition ho_knF : list kentry := Eval vm_compute in (fst (fst ho_cC)).

Lemma ho_itinerary : ltac2:(zQ "i10!h9!j4!hv9!ig0!igb!ih1!iic!hv2!ij2!ije!iu6!k2!ikd!od!il3!ild!htd!iue!iv6!q2!in4!inb!io2!iob!ip3!ipc!iq4!iqe!ir6!ive!jg6!jge!jh7@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h1+tvqk0@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h1@1$b$3@2$9@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$hd@1$b$3@2$9@3$6@1$h6$h0@3$hcNi3$i0$hf@2$h5$h0$a@2$9@3$6@2$2@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0@1$ha$a@1$h7$a@1$h8$a@1$hb$a@1$h9$a@4$5@2$2@2$2@2$2$0$0$0$7$7@4$5@2$2@2$2$0$0$0$7@4$5@2$2$0$0$0@4$5$0$0+ugit8+vppq8+2@1$h3+hhkm8@1$h3+hf@2$9@3$6$0@1$h4@3$4$8@1$1$3@3$4@2$2$8@1$1$3$e$h2+knls4@2$9@3$6@1$1$3@3$c$8@1$1$3@3$4@2$2$8@1$1$3$e$h2@1$b$3@3$6@1$1$3@3$c@1$1$d@1$1$3@3$4@2$2@1$1$d@1$1$3@1$1$f$he@1$b$3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "##CNp;1p;3p;2p;<p;4g001Gj11Tg001lj10Tg002Qj39!s/$kj1WTg003Kj1V!s/$kj1bTg004Mj1>!s/$kj1=Tg0062j18Tg0079j1\!s/$Wj3eTg008^j12Tg009=j2cTg00:Fj3aTg00;Oj2ZTg00<Xj2`Tg00=aj2@Tg00>il<lTg00@5j2^!s/$Wj2OTg00A7j4H!s/$Wj2<Tg00B2j2S!s/$Lj4I!s/$gj3LTg00CDj1]Tg00DIj3U!s/$fj3kTg00F1j1jTg00G8j1iTg00H=j1hTg00ICj1gTg00JHj1fTg00KMj3:!s/$mj3KTf0R0#1!s$%p=T%00#1p=4%00#0p=7%10#!s$$p=D!s:$#0#>p=A!s>$p=3%1!sV$6!sB&p=C!sL'0p=;%>0#=p=?%20#2p=R!s-$#2#2p=Jg00M6R1f2R2#8f1R3#8=:103:p=EA:1309:12p=N%83=:10p=[!t:$!s$/p=M%\0,@3p=G%0!tg$d!tM%>!s;$Yf3R4/@2?K30p=_!uB&p=Qg00N=R5f4R6%>4'@?K23;:0p=F%04!u4%#>,@6?K23=:50p=5%1!s?9Bf6f5;K6AK4!s9%5:5p=PA:5309:52p=X!sA+p=mg00OFR0g00OdR4#1R3#0R2#1R6#1R7#T#4#7#D#AR8;98g00PIR9#WR:%V9R9;99R;g00QTR<#bR=%13R3#1R>#1R?#7R@#1RA#3RB#0#6RC#4RD#4#ARE%04RF#>RG%C3R3#C#4#4#3#6#ARH%0FRI#3#3#6RJ#1RK#1#3#3RL#3#;#?RMPMPMg00R`#=RN%0IRI#1RO!tw$4#3#D#?RP%??RQg00S>g00SjRR#8RS%0IRT#0RU#0RV#\#=3eRW%2RRR#2RX#RRY#RRZ#RR[#2#RR\#2R]#2#J#JR^#2R_#2R`#2Ra#2Rb#2Rc#2Rd#2Re#2Rf#2Rg#2#JRh%=H%3TRi#6#4#3Rj!uN$D#?%2h#JRk#8%2kRk!s'%?4%Jk!s:2!s'7=ER4%8`R`%8aRa%2k#R!te$!sO1%V13E3E9Efg9Ede9Ebc3N5NQ3E3E3E5NQ7!s2$N,[Z7NW'[PN%1CRC#0RW#0P[PMPN%1W!s/'!s@$!s3'DRDP[PNPNP!s-&%1BRB#0RD#7RW#1RZ#1Rc#0Rb#CPY%1?#6#M#M#MR?#1#6#T#MRe#1!s:$?1GS3P[Pa%72R2#0,GSP[P`%1FRF#C!s4$%8_1GSUP[%8^1GS2P[%8]1GSTP[%8\1GSIP[%1O#3RO!v}&3#dRI#=%>T,cS%7VRV#;#;RT#0#;!yc$;#A%>e5aS1GSV%>V'Z%>T%7>#4#7R>#C#;#A'`%0ARA!sZ$;,YN%C6#;!s?$ZPN%Cj#3#APY%8RC_%0J!z^$4#T#ARj,@NP[%8X%D>#4R>#0#ARX!s;%0O!xx$7#;#?%7@#6R@#7RO#;#AR6!sI$P4%3ORO#0RT#7,Y!s[$7#3!{{$6#4#D#?PNPT!w?'OP[%=6PN%1@R@#4#6P[%=jPN%3@#3R@P[%D>!sX$@P[%=X%TA!sr$ARA!t_%=A1@NEPY%?F!xV$P[%=8PN%7WR!xk&PW!t:&0ZPY%=GPN%QbPY%??R?PNPcPYP?!y+&#0Rc#4RbP[P4PN%3cRc!y?&!s-&%3!sL$!u3'!yU0!u[%7!su'BRB#CP[%Db#!s6%#6PR!sT$QJRJ#0RB#4Rb#QPY!si+!st&7K#3RK#0#3!sB&QK#3!sd+0LRL!tP,L!s/&Cb!sE%PB!sZ&3J!ul'i!yi$;Ri#C!tO'iPRPN%V5DFDFD5D5!s++BDB!s+$!s8'B!s+&F!s2'FP!s:+BFPFP3X3X3XCmFPFPFP!sN,DBM<l,^<RN;9NRR1O00Ri/O0R[/O1RJ/O1RYPJP1P[P1PiP0!s$$HPECHPGCHPPCHPQCHRQ;9QRPA90IIRG1<;;RE'<RH'<RB'<Rb,<;RL'<1S08P;PL1S:9RLP;PbPLPRPB1S=NPPPH1SYQPGPE1S0IP;P;PLPLCI!s$/g00TIRL1OL:R;g00UUREg00^V3LRG7L:#]=908AUL:G=9:9%W5R51O5:RGg00Wb#WR8g00_Y3L7U:=9:9g00`\g00a`5khg00bdRh,^<59=!ul3%jh%ihCH%hhCH%ghCH%fhCH=9YQg00cg9L;ERE9L!tS&IAUL:E!t1&dj9LG89U5!tB$'<!s$/do"). Qed.

(* [comment removed for export] *)
Lemma hso_srF : ltac2:(zQ "50!j4!iic!ji0!ji9!hv2@3$1@1$0$4$2$3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "##+qp;1p;2p;3g002kj1BTg008^j10Tg001lj11Tg004Mj1:!s/$kj19Tg0062j14Tg003Kj1>Tg00B2j2ATg002Qj3@!se$Gj18Tg00KMj35Tf0R0#0#0p==%0!s0$#0p=2%80#8p=7%80#1p=3%1!s6$?g00M6R1f4#4f3#4f2R2#4f1R3#4=51055155135p=6A51309512p=;%43=510p=<%B1R0g00SjR3#=#2R2#0#2R4#0R5#0#2#2R6#0R7#0R8#0R9#0R:#0R;#0R<#0R=#0R>#0R?!s\$@g00OdRA#1#1#1RB#7#3#3!s+$1#1!s+$:#9%43%1B!s>$?!sF0:#9%0@#2R@#4%0@R@!s'$P4P5%:A#9%2@!s@1!s'7P6P7P8P9P:P;P<P=P>P?%0@#=!uA$!sT1%>1D6!s$'3;D63;,<23;'<'Ag00emg00g15@0do"). Qed.

(* [comment removed for export] *)
Lemma msg_short_img : ltac2:(zQ "b0!jj2!jl5!j4!jlb!inb!io2!iic!jpd!jtb!khe!kj1@3$6@1$5@1$2@1$1@1$0#8@4$7$9\0@1$1@1$0#k0@1$3@1$1@1$0#8@2$a@1$0#k0+hjptcNhf@2$4@1$2@1$1@1$0#8$8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "##0Ip;1p;2p;4p;3g001lj11Tg00h5j1=!s/$Sj1<Tg002kj1@Tg003kj1GTg001Gj10Tg004Mj14Tg00i6j28!sJ$Kj1?Tg00@5j2>Tg00B2j2F!sJ$ij1ETg00jKj2DTg008^j16Tg00k1j4A!t:$Qj3BTg00l1j3;Tg00KMj3:Tf0R0#1#4p=5f3R1f2R2f1R3/803;p=3f4R4A;123;:0p=9A:2309:41p=2%60#6p=C!s-$#6#6p=7g00OdR0#1R4#1R1#1R3#=R2#<R5#@R6#GR7P5P2%0!tD$R8#1R9#1R:#0#0#4R;182;!sG%8R8#0R;#1#5R<182<!s=$18!s\$0#4R<P2P<C3R!s?%00#1R0#0#1R=#4R>P2P>C3!sZ%3!tU$!s;+R>P5P!s\&;R;#5!sq21!v0%5R?P2P?!sk&0=#4R?182?!s5$5=R=P2P=C3R=P5P>!uK,0!sN18R8P2P8C3R8!t@&#4R;P2P;!t#&50R0P2P0C3R0P5P=!sL%9!v7$0!sR,R;P5P0!t9&=P5P!su%1:!sK$:P2P:C3R:!uP&>!sG&;P5P:!t5%9R9P2P9!tD$!sr'2%04#5R41824%?5D9D2!s$49!s&&!s2%9,>6'Fg00lT%13#=R3#<%E5U%01!x1$1#!s-%0!s--5,D3g00Sj#6#C#7!s$/CAg00m[,>65B7do"). Qed.
Lemma msg_overrun_img : ltac2:(zQ "b0!jj2!jl5!j4!jlb!inb!io2!iic!jpd!kjc!khe!kj1@3$6@1$5@1$2@1$1@1$0#8@4$7$9\0@1$1@1$0#k0@1$3@1$1@1$0#8@2$a@1$0#k0+hhkm8Nhf@2$4@1$2@1$1@1$0#8$8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "##0Vp;1p;2p;4p;3g001lj11Tg00h5j1=!s/$Sj1>Tg002kj1ITg003kj1HTg001Gj10Tg004Mj1:Tg00i6j29!sJ$Kj1ATg00@5j2@Tg00B2j2G!sJ$ij1FTg00jKj2ETg008^j16Tg00k1j4C!t:$Qj3BTg00l1j3?Tg00KMj3;Tf0R0#1#1p=8%00#:p=5f3R1f2R2f1R3/903?p=2%1!sB$4f4R4A?123;;0p=<A;2309;41p=3%60#6p=D!s-$#6#6p=7g00OdR0#1R4#8R1#=R3#>R2#IR5#HR6P2P3%0!tP$R7#1R8#1#0#5R9P3P9C2R9!sG%7R7#0R:#1#4R;P3P;C2R;!sA$87#5R7P3P7C2R7!su&#1R0#0R<#1R=#:R>P3P>C2!sV%1R>#:R?P3P?C2R?P2P!t2&:R:!tG44:R:P3P:C2R:!sL%8R8#0R@#4RA193AP2P!tC%5@R@P3P@!t5&04R4#0!s$$5R@193@P2P!u$%18#5R8P3P8C2R8P2P:P2P!tV-<#4R<P3P<!sq$8!sZ%0!uG$8!sA,R<P2P<!tI%=!s;0!tw%58!t2'!t+&7!sA+10#4R0P3P0!sC$!sk%4=R=P3P=!u6&44R41934%A2D<D3!s$4<!s&&!s$$,@5'Gg00lT%1>#=R>#>%F2U%01!x<$1#8!v#$1#0#8#4,E>g00Sj#6#D#7!s$/CCg00n],@55B6do"). Qed.
Lemma msg_short_len : ltac2:(zQ "60!kkb!k8!iic!jj2!jtb!jl5@3$2$1@2$0@1$5@1$3#8$4Nhf").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "###up;1p;2g008^j11Tg00B2j22Tf0R0#1#1p=3%1!s0$#1p=0g00oag00Sj#1#3#0!s$/'2o"). Qed.
Lemma msg_overrun_len : ltac2:(zQ "60!kkb!k8!iic!jj2!kjc!jl5@3$2$1@2$0@1$5@1$3#8$4Nhf").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["FPX1"] "###up;1p;2g008^j11Tg00B2j22Tf0R0#1#1p=3%1!s0$#1p=0g00oag00Sj#1#3#0!s$/'2o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition h_regions : ltac2:(zQ "20!j4!kod@1$0$1") := ltac2:(zQ "b0!h9!kp8!hv9!jb!ih1!ua!pd!k2!q2!p6!hp7@3$3@2$2$1$0@4$4$1$0@2$6@1$9N0@1$a$5$5@3$3@2$2$1$0@4$4$1$0@2$6@1$8Z+vppq8+u8@1$7@2$2$1$0").

Lemma hs_covA : ltac2:(zQ "d0!igb!j4!ig0!ij2!ild!hv9!kq0!iic!kq7!im4!kr3!ks2!il3@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefHdrErr ()) ["FPX1"] "p;2p;1p;3p1010@p4p70R0p1011Bp4p710p8P0p1011^p4p710p8g00B2j26Tg002kj15Tg00@Wj21Tg00Bgj30Tg012:j14Tg013@j22Tg002Qj33Tg00WbR0g014FR1'6g014fg00TIR2g00PI#5R31123g00UUg00V_3030#4'2=301do"). Qed.
Lemma hs_covC : ltac2:(zQ "d0!igb!j4!ig0!ij2!ild!hv9!kq0!iic!kq7!imc!kr3!ks2!il3@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefHdrErr ()) ["FPX1"] "p;2p;1p;3g00B2j26Tg002kj15Tg00@Wj21Tg00Bgj30Tg012:j14Tg013@j22Tg002Qj33Tg00WbR0g014FR1'6g014fg00TIR2g00PI#5R31123g00UUg00\P3030#4'2=301do"). Qed.
Lemma ho_covA : ltac2:(zQ "d0!igb!j4!ig0!ij2!ild!hv9!kq0!iic!kq7!iue!kr3!ks2!il3@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefHdrErr ()) ["FPX1"] "p;2p;1p;3g00B2j26Tg002kj15Tg00@Wj21Tg00Bgj30Tg012:j14Tg013@j22Tg002Qj33Tg00WbR0g014FR1'6g014fg00TIR2g00PI#5R31123g00UUg00^V3030#4'2=301do"). Qed.
Lemma ho_covC : ltac2:(zQ "d0!igb!j4!ig0!ij2!ild!hv9!kq0!iic!kq7!iv6!kr3!ks2!il3@3$7$4@2$a$8@1$b@3$0$3@1$1$2@3$0@2$5$3@1$1$2$c$9$6").
Proof.
ltac2:(KReplay.run1 (kr_t_RefHdrErr ()) ["FPX1"] "p;2p;1p;3g00B2j26Tg002kj15Tg00@Wj21Tg00Bgj30Tg012:j14Tg013@j22Tg002Qj33Tg00WbR0g014FR1'6g014fg00TIR2g00PI#5R31123g00UUg00cg3030#4'2=301do"). Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Sound.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variable model : ltac2:(zQ "10!pkc$0").
  Hypothesis Hh : ltac2:(zQ "60!jj2!jl5!jlb!io2!iic!pl5@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!jj2!jl5!hv9!j4!k2!iic!pm1&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd2 : ltac2:(zQ "90!jj2!pme!kj1!inb!io2!iic!pn9!po6!pp3@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+2@2$3$1@1$6@2$2@1$0#k0+2").
  (* LPS 75d69e00: the stderr write needs the launch's channel reader
     (LibStdioCall.stdio_call_sound_post's premise), constant over the run. *)
  Hypothesis Hrdr : m_channel_reader model = true.

  Definition ENV : ltac2:(zQ "40!j4!jj2!ksa!jl5>4vals@1$0@1$3@1$1#k0$2") := ltac2:(zQ "70!j4!jj2!jl5!k2!lgb!lh7!ll6\4vals@1$0@1$2@1$1#k0@2$5@1$6^1@1$4@1$3@1$0@1$2@1$1#8").

  Definition h_regions_w : ltac2:(zQ "50!j4!hv9!jj2!h9!jl5@1$0@2$1@1$4@1$2#k0$3") := ltac2:(zQ "b0!jj2!h9!jl5!hv9!jb!ih1!lpd!kj1!k2!lq6!lqd@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$7@1$0#k0@2$9@2$a@1$0#k0?3sp0$6$6@3$4@2$3@1$2@1$0#k0$1@4$5@1$2@1$0#k0$1@2$7@1$0#k0+vppq8+u8@1$8@2$3@1$2@1$0#k0$1").

  Lemma h_regions_denot : ltac2:(zQ "f0!jj2!jl5!j4!hv9!iic!h9!lt3!mhc!mi3!mj2!mjf!kod!ll6!mk9!lqd>4vals@1$2@1$1@1$0#k0>0@3$4@1$1@1$0#k0@2$c^1N0?3sp0>0@2$d+hggggglg0@2$e@1$0#k0?3sp0@3$4@1$2@2$3@1$1@1$0#k0$5@4$6$b@2$3@1$1@1$0#k0$5@1$a@1$7^3$9$8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["Sound"] "##/Nh03Hloh12P0h21bh31rh44valsp;1p;2p;3p;4p;6g00h5j1MTg00hSj1ETg002kj1ATg015mj2@!s8$Qj39Tg001lj10!s/$Gj11Tg004Mj1:Tg016oj28Tg017Yj2CTg00@Wj2BTg0185j1Q!s/$Rj2;Tg00jKj25Tg00A7j42Tg003Kj1?Tg00KMj33!sS$oj2PTg00B2j2OTg000ij6LTg019Lj1=!sA$gj3KTg01:Mj1ITg01;Tj2HTg01<[j1GTg00DIj3FTg0062j1JTg00=aj2<!u3$kj1DTg011Bj4>Tg01=aj1NTf0R0#0#0p=6%0!s0$#0p=4%1!s-$7g00OdR1#6#4R2#MR3#ER4#Ag00SjR5,@0p,3sp0R6594%62R2#0#4!s$$7#1!s-$:1836R7'CP4P6g00OFR6,B4R8#AR9P4P61830%:2R2#QR:';,53P2C2!sT&R`R;,53,83%11#1R1#1#1#6!s++7!s$$6#:R<!sa$%01!s6&1C2%?8R=538538!t7$P72!t+-153<P1C2=38=538R=39X241O9=f2R7/@5f1ELg010@R>P!sg$f3#=g01>bR4?K60R?#I'H,83%G?!tK$AF460C2X3>1B46R0P4P6%J5/<:!tB'%D;/<!tD$%?053033C>=99=eP>P8%=7#Ng014fC>g01?j599eW0W1W4o"). Qed.

  Lemma h_regions_flat : ltac2:(zQ "a0!jj2!mk9!jl5!lqd!j4!iic!mhc!mj2!mkf!ll6>4vals@1$4@1$2@1$0#k0>0@3$5@1$2@1$0#k0@2$9^1N0?3sp0>0@2$1+hggggglg0@2$3@1$0#k0?3sp0>0@2$1@2$3@1$0#k0?3sp0+nvvvvvvvvvvf@2$8@1$6^4$7").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["Sound"] "##<Fh01Hh11rh22Hah37__arithh44__ffh58__varmaph65__with74__x1h83Hhih93Hloh:2Hrh;2P0h<6__sat0h=!s/%1h>!s/%3h?!s/%4h@1bhA4valsp;1p;2p;3p;4p;6p;7p;8g001lj10Tg00h5j1a!s/$Sj1^Tg002kj1VTg015mj2Q!s8$Qj3ITg001Gj11Tg004Mj18Tg016oj2ETg017Yj22Tg01A3j3rTg0062j1oTg0185j1nTg00=aj2PTg00A7j4O!sn$kj1c!s\$JR0j2JTg019Lj1:!s:$dj35!sg$Rj23Tg01Boj2_Tg01CLj27!s/$hj2]Tg01DPj3\Tg003Kj1[Tg01E4j2Z!s/$Rj1YTg01F0j1X!s/$[j2WTg00iij1sTg01G>j2U!s/$aj2qTg01HDj3F!s/$gj3pTg01IJj4HTg01J5j2mTg00B2j2l!s8$Wj2hTg01KCj3g!s/$bj4fTg000ij6eTg01:Mj1KTg01;Tj2MTg01<[j1NTg011^j6LTg01LTj1dTg01M2j2i!t1$gj3jTg00DIj3k!v[$Wj2GTg01N9j7T!s/$]j7bTg01OAj8`Tf0R1#0!s$%p==%01#0p=A%11#1p=D!s-$!s$/p=Cg010@R2f1R3;I1p=;g01>bR4g00OFR5;j1p=>Ak451p=9g00R`R6/21p=6f2R71G31'Gp=@1263/G1p=B1U51p=?P7g01OeR8g01PDR9P9g01PdR:P5P3g01QDP1CHg01QkR;FTp=4P3P8P9P9P:P1P!s9$SP7!s9+3P1Fbp=<f3R;!s;+7P3P1G`p=Rg00OdR8#0R<#0#=R=#aR>#^R?#Vg00SjR@,Q1p,3sp0RA5I?%A=RB#0#=!s$$1#0#1!s0$8RC1E>ARD'2%D8RE#DRF#D#C!s$+8RG,2Dg014fRH9r21P0P4P5%o@%8BRB#nRI'PPBCORJ/;3!sA$c6%AF#D#A#D!t6$!s&%A#8RF'P%0E!s5+ECOR4/;3g01RKRK'Jf6RL#:%>7%9735P11;J7P2PJf8RM#:RN%>1RO%91RP35X12P?PA1E>1/3IRA%8<R<%8=R='_RQ,7A%6BRR13AB/2Q3@'BX@?1]<=R?176<%6=176Q[[RA%6<RSg01RhRTA\<=3UW2R=%6Q\T^2S!sA$SDRT#[RU%VTRT1Z53%Y5RV%X5RW1W58R8%?G54W%s9R9PW%?C=4W8P91U56R9%?BRX,q59F58R854WP5P8g01T0RY%?<=p5>R<CH,SWA4W9XAF58X=4W<5<W!s%%CRCR1mW:R:P1P7g00Wb!y}$4FRX'l1h17=I8XdAg563CfRXb4b5b6X75121G12C3137IRI17IQ13IB/2Q7@R'B[[^75P1PDf7RDPMO3b3b>b?1QD@PLEe%:DRD%>JR@#K'M,E>%N@'3RM17MQ%9JRJ#613MJ!v{&eA5D@JeP;P1ELW0P1O11;47/JKP01;4;PKf4R0#>%9055NP11;40P2P4f:#:R0?5OP!x>&P=PSPUPT%d5PV%?F9F59RV94W9P5PVPYP!vI%%?ERY94W9AF5VY!vM0P:P!uy&136FRF17FQ%6E13FE!t{&P1b3b<b=f9#:RF%>4RE!uZ+E'3R>17>Q%94R4#613>4!uZ,FE4ef5!uZ,PK%>L%9L550P1n010!s#%X0KP1O1n20!s9'2110!s3&!s`%!sB51000W:X12%:;/iHeW8W9W;WAo"). Qed.

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
    change (s_pc (fst (fst rA))) with 0xdfa40%Z;
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
      eapply (rz_run_lf RSEGS FUELH STOPSH scr0 0xe02d8 (sc_sr sc) (sc_kn sc) 67 (fst (fst rC)) (snd (fst rC)) (snd rC)
                (fst (fst cC)) (snd (fst cC)) (snd cC) (ENV vals') MC (seg_rom RSEGS) _ model);
        [ vm_cast_no_check (@eq_refl _ rC) | vm_cast_no_check (@eq_refl _ cC)
        | exact HR | exact HK | scs_nil | scs_nil | exact Hh | exact Hlazy | ];
      clear HR HK; intros RC MF HR HK EQC LFC;
      pose proof (log_covered_frame (ENV vals') MC h_regions _ COVC RF' LFC) as FC; rewrite <- EQC, RD' in FC;
      change (s_regs (fst (fst rC))) with srF in HR; change (fst (fst cC)) with knF in HK;
      change (s_pc (fst (fst rC))) with 0x475c4%Z;
      apply (HCONT Rj RC MF HR HK);
      eapply frame_mod_trans_same; [exact FA|];
      eapply frame_mod_trans_same; [exact FC0 | exact FC] ].

  Theorem hs_sound : ltac2:(zQ "i11!jj2!jl5!khe!mhc!mo5!hg0!io2!iic!mra!ms3!msb!ngd!nl9!nm5!nr7!ns2!kj1!kkb!j4!k8!k2!nvb!ojc!mi3!ok9!ol1!ol9!om3!omd!on5!onf!jtb!ll6&>0@1$1@1$0#k0@1$6@1$1@1$0#8>4vals@1$h2@1$1@1$0#k0>1R@2$4@1$0#5@1$1@1$0#k0>1M~0>1K$hc>0@3$7$h3@2$h1@1$1@1$0#k0^4Ni3>0@3$7@1$1@1$0#k0@2$i0^5N0?3sp0>0@3$f@1$3^6$h9^5>0@4$e$2@1$3^7^5$h8>0@1^5@1$h4$h5>0>2Rj@2$4@1$0#5@1$1@1$0#k0>2R'@2$4@1$0#5@1$1@1$0#k0>2M'~0>0@3$f@1$3@3$5@1$1@1$0#k0^c@1$d^3$hb^2>0@4$e$2@1$3@3$5@1$1@1$0#k0^d@1$d^4^2$ha>0@3$h6^c^3$h7@4$c$2$b@2$8@5$9?2fx^5@2$h0@1$0#k0+knls4^4@1$a$2?5model^c@4$c$2$b@2$8@5$9?2fx^9@2$h0@1$0#k0+knlo8^8@1$a$2?5model@2$hd@2$he+2$hf^7").
Proof.
  (* LPS 75d69e00: replay replaced by the tactic it recorded, now with the reader premise. *)
  unfold W.
  hf_sound 0x47588%Z hs_rA hs_cA hs_srA hs_knA hs_sc hs_rC hs_cC hs_srF hs_knF
           hs_itinerary hs_covA hs_covC msg_short_img msg_short_len msg_short.
Qed.

  Theorem ho_sound : ltac2:(zQ "i11!jj2!jl5!khe!mhc!mo5!hg0!io2!iic!mra!ms3!msb!ngd!nl9!nm5!nr7!ns2!kj1!kkb!j4!k8!k2!nvb!ojc!mi3!ok9!ol1!oo4!ooe!omd!on5!onf!kjc!ll6&>0@1$1@1$0#k0@1$6@1$1@1$0#8>4vals@1$h2@1$1@1$0#k0>1R@2$4@1$0#5@1$1@1$0#k0>1M~0>1K$hc>0@3$7$h3@2$h1@1$1@1$0#k0^4Ni3>0@3$7@1$1@1$0#k0@2$i0^5N0?3sp0>0@3$f@1$3^6$h9^5>0@4$e$2@1$3^7^5$h8>0@1^5@1$h4$h5>0>2Rj@2$4@1$0#5@1$1@1$0#k0>2R'@2$4@1$0#5@1$1@1$0#k0>2M'~0>0@3$f@1$3@3$5@1$1@1$0#k0^c@1$d^3$hb^2>0@4$e$2@1$3@3$5@1$1@1$0#k0^d@1$d^4^2$ha>0@3$h6^c^3$h7@4$c$2$b@2$8@5$9?2fx^5@2$h0@1$0#k0+knls4^4@1$a$2?5model^c@4$c$2$b@2$8@5$9?2fx^9@2$h0@1$0#k0+knlq4^8@1$a$2?5model@2$hd@2$he+2$hf^7").
Proof.
  unfold W.
  hf_sound 0x475a4%Z ho_rA ho_cA ho_srA ho_knA ho_sc ho_rC ho_cC ho_srF ho_knF
           ho_itinerary ho_covA ho_covC msg_overrun_img msg_overrun_len msg_overrun.
Qed.
End Sound.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Plain.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable model : ltac2:(zQ "10!pkc$0").
  Hypothesis Hh : ltac2:(zQ "60!jj2!jl5!jlb!io2!iic!pl5@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!jj2!jl5!hv9!j4!k2!iic!pm1&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd2 : ltac2:(zQ "90!jj2!pme!kj1!inb!io2!iic!pn9!po6!pp3@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+2@2$3$1@1$6@2$2@1$0#k0+2").
  Hypothesis Hrdr : m_channel_reader model = true.

  (* [comment removed for export] *)
  Record hfH (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) (tid can : Z) : Prop := HFH {
    H2  : getr regs 2 = sp;
    H4  : getr regs 4 = Z_to_bv 64 0x10b6b8;
    Hsp16 : (bv_unsigned sp mod 16 = 0)%Z;
    HspLo : (0x100000500 <= bv_unsigned sp)%Z;
    HspHi : (bv_unsigned sp <= 0x7fffffffffff)%Z;
    Hstk  : stk_ok RSEGS mem sp HF_FR;
    Himg  : forall i, (0x10000 <= i < 0xf1000)%Z -> mem (Z_to_bv 64 i) = None;
    Hcells : cells_ok mem diag_cells;
    Htid  : rdn RSEGS mem (Z_to_bv 64 0x10b610) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
    Htid32 : (0 <= tid < 2 ^ 32)%Z;
    Hcan  : canary_ok mem can }.

  (* [comment removed for export] *)
  Record hfPost (regs : bvmap 5 word) (mem : word -> option byte) (sp : word)
                (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop := HFP {
    P_sp  : getr regs' 2 = sp;
    P_tp  : getr regs' 4 = Z_to_bv 64 0x10b6b8;
    P_a0  : getr regs' 10 = Z_to_bv 64 1;
    P_cs  : forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list -> getr regs' r = getr regs r;
    P_frame : frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - HF_FR), HF_FR); (Z_to_bv 64 0xf99a8, 232%Z)];
    P_flags : rdn RSEGS mem' (Z_to_bv 64 0xf99a8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
    P_rpos  : rdn RSEGS mem' (Z_to_bv 64 0xf99b0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_rend  : rdn RSEGS mem' (Z_to_bv 64 0xf99b8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
    P_wpos  : rdn RSEGS mem' (Z_to_bv 64 0xf99d0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bea0));
    P_wbase : rdn RSEGS mem' (Z_to_bv 64 0xf99e0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x12bea0));
    P_lock  : rdn RSEGS mem' (Z_to_bv 64 0xf9a34) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 4294967295));
    P_stk   : stk_ok RSEGS mem' sp HF_FR }.

  Definition h_vals : ltac2:(zQ "50!jj2!jl5!h9!j4!mo5>4regs@2$4@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3tid$2>3can$2@1$3@1$1@1$0#k0") := ltac2:(zQ "90!jj2!jl5!jb!h9!kj1!hg0!k2!mo5!nm5\4regs@2$7@1$0#5@1$1@1$0#k0\2sp@1$1@1$0#k0\3tid$3\3can$3@3$5@1$1@1$0#k0@3$2@1$1@1$0#k0^3@3$2@1$1@1$0#k0@2$4@1$0#k0^2@3$2@1$1@1$0#k0@2$4@1$0#k0^1@1$6@1$1@1$0#k0@1$8^4").

  Lemma h_ev_junk : ltac2:(zQ "h00!jj2!jl5!h9!k8!ije!iic!oqa!os5!osb!mo5!ot1!ot9!pi2!pic!pj1!kj1>4regs@2$9@1$0#5@1$1@1$0#k0>2sp@1$1@1$0#k0>3tid$2>3can$2>1i$3>0@2$4@2$7N3^1@2$8^1Ni3@3$5@1$1@1$0#k0@2$d@1$b@4$c^6^5^4^3^2@2$a^6@2$f@1$0#5@1$e@2$6^2N3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["Plain"] "##J`h04__p1h14__p2h24__x1h34__x2h42H3h53Hi0h67__arithh74__ffh84__p3h98__varmaph:5__with;4cstrh<1ih=1nh>1xh?2z3h@1HhA2HihB1bhC3canhD7defaulthE1lhF5lemmahG1mhH4regshI2sphJ3tidhK1yp&0p;1p;2p;3p;<p;6p;4p;=p;9p;5p;Bp;7p;8g001lj1?Tg001Gj1MTg00h5j1X!s/$Sj1cTg01TWk20JTg008^R0j10Tg033GR1j2YTg02HKR2j2!sG$AWj21!sE$aj2_Tg002Qj32j1ETg01^]R3j13Tg004Mj1ITg018oj26!s/$Rj29Tg01_=k20;!s0$`k306Tg00B2j28Tg025Jl<UTg017YR4j25Tg01CLR5j24Tg0348j6gTg02V2j4iTg01`=j1l!sA$aj2mTg01AJj2FTg035Cj2G!s/$lj3HTg036Uj2NTg0079j1nTg037Ak20I!s0$bk30HTg003Kj1aTg00KMj3;!u[$kj1`Tg01E4k20GTg01LTk10FTg02DUk40D!sD$Rk10?Tg01F0k10>!s0$[j2kTg01G>j2A!uY$ok30=Tg01IJj4BTg00iik10<Tg01HDj3[Tg01J5k20:!s0$Wk20!v#$KCk304!s0$bk402Tg026Rj4eTg00jKj27Tg01UCj2OTg02FGj2WTg038Kk101Tg01X?j1PTg01YEj3QTg039;j4Cj1z!s2$Wj4TTg03:>j1~!s/$mj4STg03;dj3}Tg03<Zj1{Tg03=Ij6|Tg03>4j2^!s/$`l=yTg03?Mj2DTg03@Nl9xTg03AHj2wTg011Bk403!s9$dj6vTg000ij6bTg03Blk50!u9$5mj2uk108Tg01nLk109Tg021Zj2tTg03CNj2jTg03DQj4sTg019Lj1rTg03EUk20@Tg02XGmB0!w8$Wbl<q!yC$bk60BTg01N9k70C!s0$]j7pTg03F2j7oTg01OAk80ETf0R6#0!s$%p=<%06#0p>00g00R`R700@6p=>g00OFR8f1R9;26p==g00oaR:P:P:P8P8P8g03FVP3P3P3f6R;g03G6f5R<f4R=f3R>f2R?P9P6NB0Ap=d!s_+0!sZ$>g03G]P!sH$M<qp=V!sE$1P3P4g03HAP<P=P>!sG'Up=f!sG$2P3P5g02_I!sG4RA2867p=]A;?969;=>p=KP9g01OeR5g01PDR2P2g01PdR4P6J0Bp=\P8P9g02hBP6CBp=ZP9P5P2P2P4P6g01QkK0Cp=:P?!s=+9P6Fpp=@!s92op=hP>!s9+!tf$L0Ep=Lg00OdR5#?R1#M#XR0%?1#?R@#?#?RA#?#XRB#cRC+0Jg00SjRD#0RE#0RF#0RG/Y6%0G#<!s$/RH#0$00RI,J6'11_9GRJ#0RK#0RL#0RM=2:9%39RN%M5#IRO'6#>RP%I5RQ'9RR/9QRS/9QRT/=NP:P8%E:RUP3%E8%36R3,=NA2:9620;96406XK:X>:PMPT196QX>8RTPLPSPTPKPRPTPJPP1696#>XG8X=8RPP9PN188NRTPGPO188ORRFdCVCVCVP9PNPTM<U1YG9RK1J9IRS'115ONRL%M@#M#IRM,4NRV'1RWPKPSPLPVPGPOPR!sc%Ef!s-%PIPM188MRTEREgP6CiPW%l?%3?RW,57%3>RN/6ORV,m7147V%>VRL/=V'115V7%]L'1'F%3=/6ORL#>RVP8p-0RSg01SDRK1G8FRF1G8E1G8DRE5H85H8g03HcRX'NRYPK1G8G%n5-0I8>0H8F=H8E!sO$/NX1NEX%aKRE5;KDK%`KRXP820G8?P9&0F8H0DRF&0?8RZ&0>8R[1\[=1k85R51k81R11A8OR\60=8R]'Z,:[5@[R^P8P]g01QDR]1A87R_CB,:[1Z5_,:[R_5@[5h[&0<2R2P[P8P\P]P1!sJ%\[<R]5@[P21A8QR\9[85=[8\=[8\/Z1,:[CLCL20:[4R4P6P?g00WbR\g014FR`'82056?=2\`dB04879H02R`b7b9b:X28X38X0SW1169OR\,=6,1?Ra15\7%]6R\'1'F15O?/1=19?Q/9!s%$=>[[^28^38^0S^1SP6%3;RQ/4M16QO,47PQP9P?P=O6b6b?b4b;b5CePCP=PC17B>RQ17B?%aCRb5;CDKRc,OC/WJ=2:9RdePdPCP<!sQ$=RdA;CQbDKRQ,OC1_?GRe'WRf=2:?PC%ECRg&01CPCP>PCP;!s[$<A;CdbDKRdf7Rb#P5QCRh17B7RBCCPC1OCd1_>GRd'WRiPhPBCC%`CRjPC^DCRk]ERl^=:RmP:PlPUPjPk%EjPCPCPgPgCTRnCTRoCTRp!sG$oPjPkPn!sF%%~CCSCSCS9}mp%zCP>PiP:PU%{:PiP>P6E|PhPh1^jhPBPB1^CBM=y%3d,70,DbRdPd1^CdM9xWFP6!sz$e%P;RjPBCCRhA2C6dXBCRdPC%3e!s[$;RiPd18CiPCPeP:PC1703,DbX<:R31wDHH03P!uo$P3PePHPB1JeH16WO#>R3%IARA'4PeP3PPP?PW188WRP!}q%FdPHPA188AER1YG?RH1J?IR3!~Y$WRD14WMRd'1RUPHP3PDPd!~Q&?PWPPEf!s-%PIPMP!~M%9CiPU%l>157N1m7L147L1=VL'115L7%]V!~<%</6O#>P8A;KYEPXPFPZP[A@[]_9h[^P2P[1\[;P8P1g01T0!},$M!|>$!|8$P8P5P11A8A!s:$CLCLP4P!{[3X1SX8S11>\,Fa14?M,1<14?A!{B1^8!{E$bRb,5O16bORO/57147OPb!{K&7!{K/EvEbA2ChiePCPfAQCQj!wC&QPjPBPeI07EbO2b@%P<9QCcRc/u9%3J!x:$<R052Ce&08c%X@#c#`#a$09't/j9=2C0e!#<0&Cs#r!s:'WAX<:XC8XJ8XICWHo"). Qed.

  Lemma h_regs_ok : ltac2:(zQ "a0!jj2!jl5!h9!io2!mo5!ot9!pi2!pjb!ol1!ns2>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>2sp@1$1@1$0#k0>3tid$2>3can$2>0@5$7^5^4^3^2^1@3$9@1$5@4$6^6^4^3^2$8^6").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["Plain"] "#$Z:p'0h02Hih11ni001nh27__arithh34__ffh48__varmaph55__with61bh71ih82Hah94__p1h:4__x1h;2H3h<2H5h=5Hcan0h>7Hcells0h?3Hi0h@5Himg0hA5Hsp17hB6HspHi0hC6HspLo0hD5Hstk0hE5Htid0hF6Htid33hG2PHhH7__sat34hI!s0&5hJ!s0&6hK3canhL4cstrhM3memhN4regshO2sphP3tidhQ1xi012H2i022H4i034Hcani046!tz%i054Himgi06!tt$6i075!tu$i085!tu$i094Hstki0:4Htidi0;!tu%2p%0p&0p;1p;2p;5p;3p;4p;6p;<p;7p;8g001lj1GTg001Gj1ETg00h5j1_!s/$Sj1^Tg01TWk20FTg003kj1mTg03IOR0k50:Tg01Uck300Tg004Mj1!sN$jKj2XTg016oj2UTg03JRj2jTg002Qj3LTg017YR1j25Tg03K2j4~Tg01CLR2j22Tg00AWj26Tg00iij1eTg03L3j2w!si$kj1lTg008^R3j1!tI$k1j4sTg03M9j2rTg00@5j2qTg01Boj2pTg03NAj2oTg02HKR4j21Tg00l1j3]!u2$kk10DTg03OHk10CTg039;j4TTg03DQj4cTg033GR5j2BTg0348j6@!v3$Kk10>Tg01LTk10=Tg01ERk10<Tg01F0k10;Tg01J5k209Tg00B2j2a!s9$Wk208Tg01KCk307!s0$bk406Tg03PMj6?Tg03CNj2hTg01^]R6j1YTg018Rj2VTg02V2k404Tg01`=k103Tg03QTk202!vp$hj2}Tg01DPj3|!ti$4j2{Tg02DUj4fTg01G>j2g!tz$[j2z!sp$bj6xTg03REk405Tg019Lj1`Tg03?Mj2RTg01;Tj2b!v3$aj2vTg025Jl<kTg01IJj4ZTg01N9j7[!s/$]j7tTg026Rk40?Tg000ik60@Tg02Wbl<nTg01HDj3\Tg01OAk80BTf3R7f2R8f1R9f0R:Cc#`p=7g03SXR;9]9:p=u1R89=L7:p=d%E:#Gp=P%E:#Ep>0E%G!s7$Q%G:#Fp=Jf4R<A]89;,R7;L:p=<!sH$#G#Gp=S!s]$!s$/p=W%E!s`$Mg00R`R=/5:p=Kf5R>P<P7P8Cc#`g00M6R?P9g02_kR@P:CT'bp=4P7P8g03T4RAP9CT,R<=L>:p=31R78%`9/b:5L<p>0A1v9:#Y,X8,R7p==g00OFRB/a:p=8g00oaRCPBP5P6P1g03HAP!tM&P9P:M<kp=APCPBP4P6P2g02_I!sG4:1gB:p=9f6R2g01OeR4g01PDR1P1g01PdR5P>P4P1P1P5PBP<g01QDRDP7CZg01QkREF[P8!sH-9g01T0RFP:CZPEF[Ftp=D16<!tD&H0?p=>f7RGP2P>1a<71h89P:J0@p=C!tn$AP7CT,R2P?P9P!vU$,b85LGp=;1V<7/V8/V9/V:p=HPC!uW$BP3P6!u[%3G]RH!sm$!sA17PH!um'nM<np=I!u+1PD!u#'p=yA\B<7=\B8=\B9=\B:p=N!sU2!uV+p>01P7!sB+!t2$L0Bp=i%0:#0#0#0p=Og00OdRE#GRF#ERD#_RH%GFR6#GR3#GRI#GRJ#GRK#_RL#^RM+0F%_3#^RN#mRO\M!w},I0:P0!x6-2!z0&7@00@2P:PMf@R0%FFRF,uHS00f>CdPMfARPPH%F6RQ%EIS01#G#E#P#E#PRR#P#E$0E#Q#J,XLD<1UL0%FIRI'j=LB=%QK#S#SRK#G#S#P#P#Q#S#J1ULP'5fB,UL%EES02#ES03#ES04#ES05#E#W!s$+M'5g00lTR0fDS06fCg03UBC~%FK/5:Q04#GS07#Q!t'&S#J,2:'6fGRK1XL9O1%eN5LO[^7BfFROg03VE'w%lNRN#mP0PK%GR!sd&J,XLg00SjRR#0R0#0RS#0RT#0RUCsfE,XL,rU,qN3L%KO%FJRJ,pFS08,2O'6fIRN/oOfKROPNfHPKC7P@PO%0US09#0RK#0S0:#0RN#0RV#0RW#0RX#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk#0Rl#0Rm,1:RnPCPMfORo%^HRpP9A]H=;R;PofMRqfLRrPOP9&0D=RsE4E3^0nP911RmfNRn$0CPMPnPpPRPAP;CTPnPrPOfJCcP?PRP@PsCTI0AeW0PC%0:S0;/1mPMfQR@Pp%09S0<P;P@PoPnPqQ0<P!t2$]0P:110mPMfPR?PHPUPTC=ROPMP@PH%FEREP:D<X6MPMPOP?PnPqPrC7S0=PU!s5'PU1BTURr%0mRq#0RO#0RA,1URtQ02#FRu/5QRv%E3S0>#MRw,2QRx'6S0?PrPtPvPxPTPu%8uRxPUPQ%8QRvEAPUPQPvPAPw%8wRvE:E@g01SDRt$0>Rr%ltRt&0=BRy&0<BRz&0;BR{P{%9uR|%9QRQP{PQ%9wRQFD209{5R}P:P8g00WbS0@g014FR~'aQ0@208:8;L~dB07B=9H06R~b3b4b5Q0?P:b2D>E?GCPMP?PpP0P;Q0=P0PsG;!w6$Q0;#0!w8+SR0PpQ0<#0S0=P;P0P@P?PoQ0=!w:/SmPPPMfRRPQ00PPP?PoPnC7Rn/hRCdePMPPPpPSP;PnPS!t81RS!t7%URnPpQ0=!tJ$!sO$0PPP@Q0;!t7/TmPMfTRRPHPK!xK$o!y_$HPu!xH,oPRPPP@P?C7S00PK!s5'PK1BTKS0?11KAS0@Q02#GR?#FR@,5uS0212@wRo'6S0AQ0?Q!sH$PoPTPuPxPKP@%8@RoEAPK!z8$APwP!x7$!xf$yPzP{P{P|%9@RoP{PoPQFDP}P!wA+A!wA0RPpPTP;Q00PT!v/+%0SS00!v-%WRSPp!wR&AP;PSPnPRP0Q0A!v-/UmQ06PMfVRoPpPUP;!ut$0PPPU!sM%!w/&0#0RU!t#%YRPPpQ0A#0S00P;PPPSPoPnQ00!t#,Q09!sS%XR0PHPNPTC=S06!x6$H%FD!w3+Q06P0!}=$RC7S06PN!s5'PN1BTNS0211NAS0@%F3R3,5uRR123wRn!|A$Q02Q0@PRPn!w+&NP3%83RnEAPNP3Pn!w+=3RnP{Pn!w+3!{G1!zz$9P;Q06Q09!w--U!v+'[!z5%0#0S09!z5$PP0PS!sT$!w,,KmPMfZ!z5$V!v&,nPHP@!v%0RP0PSPo!v%%V!s5'PV1BTV!z7$V!v%$E6Ro#FRS!z5'SwR@'6S0B!z5,@!v/&VPS%8SR@EAPVPSP@!v/=SR@P{P@!v/3B!z54K!v-$PK!v,7]RK!vQ$#0S06P;PK!x9$PQ06!y3/:!sS%\R@PHPW!v/%BPMPKPHQ03#F!v2-BP@!}6$0C7S0BPW!s5'PW1BTW!y5$W!v2$GDS0?#FR0!v3$C120wRP'6S0D!y;%Q0CPP!v3&WP0%80RPEAPW!{S$!v3<0RPP{PP!v33D!v30@PpQ0:P;Q0BQ0:!v5/S!ua'_RUPpQ06#0S0BP;PU!~c$nQ0B!y=/NmPMf^RPPHPX!v4%DPMPUPHP3!v1-DPPP@!|@'DPX!s5'PX1BTXS0C11X!y=%DRD#FRR,5uRn12RwR3'6S02Q0CQ0@PnP3!v-&XPR%8RR3EAPXPRP3!v-=RR3P{P3!v-32!v-0PPpPNP;Q0DPN!#7S,:#0RN!v,%aR3PpQ0B#0S0:P;P3PUPPPK!v\$!v,,VmPMf`RnPHPY!v,,3PHPS!v,0nPPPKP@!v,%Y!s5'PY1BTY!y8$Y!y8%?R@#FRK!y7'KwRS'6S0E!y7,S!v/&YPK%8KRSEAPYPKPS!v/=KRSP{PS!v/3E!v/0nPpPV!v/%V!y5-N!v,'cRV!yY$#0S0DP;PVP3PnPUQ0D!v,/WmPMfbRSPHPZ!v,%EPMPVPHP0!v,-EPSPnPUPPC7S0EPZ!s5'PZ1BTZ!y4$Z!y4%?R?#FRP,5uRU12PwR0!y4/UP0!v'&ZPP%8PR0EAPZ!}1$!v'<PR0P{P0!y4ASPpPWP;Q0EPW!v'7eRWPpQ0D#0R0P;PWPVPSP3P0!v%/XmPMfdRUPHP[!v%,WPHPR!v%0U!sa$n!v%%[!s5'P[1BT[!y0$[!#=_$3#GRn#FR3!y2$3123wRR'6S0C!y2'3PR!v,&[!#9Y$REAP[P3PR!#9Y>RP{PR!v,3C!v,0UPpPX!v,%X!v,/S0E!v-%gRNPp%00RXP;PNPWPUPVPX!v+/YmPMffRRPHP\!v+%CPMPNPHPK!v+-CPR!sa$SC7S0CP\!s5'P\1BT\S0311\!v+%4!#9R%RV12SwRK'6S04Q03Q0@PVPK!u~&\!#9P$KEAP\PSPK!#9P>KP{PK!u~34!#9P3YP;Q0CPY!#3;,E#0!v$+iRYPp%0XRKP;PYPNPRPWPK!v$/ZmPMfhRVPHP]!v$,YPHPP!v$0V!sa$U!v$%]!s5'P]1BT]S0411]ARU15uIRW12I!#9?%@Q04PUPW!#9=']PI%8IRPEAP]PI!#9=>I!#9=8@!ux0VPpPZ!ux%Z!ux1RZ!uw%kRPPp%0KRWP;PPPYPV!y#$!uw-[mPMfj!|#$^!|#,P!#981E!xh$N!#98$EP^!s5'P^1BT^S0C11^!xy%>!#96&N!#96+4!#3$%N!#96'^!#96+^!#96W4!{y4[!{y%[!{y-Z!u}'mR[Pp%0WR3P;P[PPPUPYP3!u}/\mPMflRNPHP_!u},[!#901EPN!sa$V!u}%_!s5'P_1BT_!xv$_AS0@%JoRV,5uRY12V!#9'%CQ04Q0@PY!#9&'_PV%8VRSEAP_!|f$!u{<V!#9&8!~v1NPpP\!u{%\!u{7oR\Pp%03RSP;P\P[PNPPPS!u{/]mPMfnRYPHP`!u{,\PHPI!u{0Y!sa$!{s$EP`!s5'P`1BT`!xz$`!u{$MoRo!#8z%o!{x&!xx'U!{y+`Po%8o!{y$`Po!{y?o!{y9!xx1YPpP]!u{%]!u{7qR]Pp%0SRPP;P]P\PY!x~$!u{-^mPMfp!{w$a!u{,]!#8x5YP[PN!u{%a!s5'Pa1BTa!xx$a!{w%?#JRN,5uR[12N!#8s+!xz$[!#8r'aPN%8NRREAPa!|g$!u}<N!#8rJ^!u}%^!u}7sR^Pp%0PRRP;P^P]PUP\PR!u}/_mPMfrR[PHPb!u},^PHPV!u}0[!sa$Y!u}%b!s5'Pb1BTb!xz$b!u}'MRY,5uR\12YwRV!#NL%!x|$\PV!u}&bPY%8YRVEAPb!|g$!u}<YRVP{PV!#NL@[PpP_!u}%_!u}7uR_Pp%0RRVP;P_P^P[P]PV!u}/`mPMftR\PHPc!u},_PHPo!u}0\!sa$!{y&c!s5'Pc1BTcS0?11c!~v%DRU,5uR]12U!#UP%C!#NA$P]!#UO'cPU%8URoEAPcPU!#UO>U!#UO8!xz1\PpP`!u{%`!u{7wR`Pp%0VRoP;P`P_P\P^Po!u{/amPMfvR]PHPd!u{,`PHPN!u{0]!sa$[!u{%d!s5'Pd1BTd!xz$dAR[%MDRD,5uR^12DwRN!#;o%CP[P^PN!uy&dPD%8DRNEAPdPDPN!uy=DRNP{PN!#;o@]PpPa!uy%a!uy7yRaPp%0oRNP;PaP`P]P_PN!uy/bmPMfxR^PHPePTC=R[PMPaPHPY!ux+!u7$]P_P\!uw%e!s5'Pe1BTeS0@11eAR\%J@R_!~o&_wRY!xs&@!yK$Y!uw&eP_%8_RYEAPeP_PY!uw=_RYP{PY!xrA^PpPb!uw%b!uw7{RbPp%0NRYP;PbPaP^P`PY!uw/cmPMfz!~n$f!uw$\PMPbPHPU!uw,\!uy$`P]!uw%f!s5'Pf1BTfR]11fAR`%M@R@!~h&@wRU!uv$P]P`P\PU!uu&f!#^:$UEAPfP@PU!#^:>UP{PU!uuA[PpPc!uu%c!uu7}RcPp%0YRUP;PcPbP[Pa!#]f&!uu%dmPMf|!~f$g!uu$`PMPcPHP!#]0+!u7$[PaP^!uu%g!s5'Pg1BTgR^11gARa%J?R`,5uRD12`wR]!uu%^PaPDP]!uu&gP`%8`R]EAPg!v_$!uu<`R]P{P]!~`Ed!uu%d!uu6p+01@RdPp%0UR]P;PdPcP\PbP]!ux/emPMf~RDPHPh!ux$aPMPdPHP_!ux,aPD!s_$!~a&h!s5'Ph1BThR[11hARb%M?R?,5uRa12?wR_'6R^P[!z5$_!uw&hP?%8?R_EAPhP?P_!uw=?R_P{P_!uw1P^!uv0DPpPe!uv%e!uv:BRePp%0]R^P;PePdPDPcP^!uv/f!sP&AR_PHPi!uy+e!#_z/!u:$DPc!~c'i!s5'Pi1BTiR\11iARc%JnRa,5uR@12awRb'6R[P\PcP@Pb!uy&iPa%8aRbEAPiPaPb!uy=aRbP{Pb!uy2[!uy0_PpPf!uy%f!uy:DRfPp%0^R[P;PfPeP_PdP[!uy/g!sP&CRbPHPj!uy$@PMPfPHP`!uy,@Pb!sb$DC7R@Pj!s4'Pj1BTjRD11jARd%MnRn,5uR`12nwRc'6R\PDPdP`Pc!ux&jPn%8nRcEAPjPnPc!ux=nRcP{Pc!ux2\!ux0bPpPgP;P@Pg!uw:FRgPp%0[R@P;PgPfPbPeP@!uw/h!sP&E!~g$k!uw$cPMPgPHP?!uw,!|L%eP_C7RcPk!s4'Pk1BTkR_11kAReQ07#F!{n%`!{n$d'6RDP_PeP`Pd!uy&k!{n%dEAPkP?Pd!{n?dP{Pd!uy2D!~f4hP;PcPh!uy:HRhPp%0@RcP;PhPgP\PfPc!uy/i!sP&G!~h$l!uy$dPMPhPHPa!uy,d!~Y$fPbC7RdPl!s4'Pl1BTlRb11lARfQ05#F!{n%`!{n$e'6R_PbPfP`Pe!uy&l!{n%eEAPlPaPe!{n?eP{Pe!uy2_!~i4iP;PdPi!uy:JRiPp%0cRdP;PiPhPDPgPd!uy/j!sP&I!~h$m!uy$ePMPiPHPn!uy,e!~Y$gP\C7RePm!s4'Pm1BTmR\11mARg15uJRn12JwR`'6RfP\PgPnP`!us&mPJ%8JR`EAPmPJP`!us=J!#n\6Pf!~c4jP;PePj!us:LRjPp%0dReP;PjPiP_PhPe!us/k!sP&KRfPHPq!us$gPMPj!{i1gPf!sb$DC7S05Pq!s5'Pq1BTqRD11qARhQ01#FRg,5uR?12gwR\'6RbPDPhP?P\!uz&qPg%8gR\EAPq!v_$!uz<gRgP{Pg!uz2b!uz0fPpPkP;Q05Pk!u{:NRkPp%0eRbP;PkPjPfPiPb!u{/l!sP&MRjPHPO!u{+k!{k1g!sb&_C7RgPO!s4'PO1BTOR_11OARiQ0>#JRf!#;V%fwRH'6RkP_PiPaPH!uz&OPf%8fRxEAPOPfPx!uz=fRfP{Pf!uz2k!uz0jPpPlP;PgPl!uy&%0Z/1m%0b!u}$%Y9RlPE!s$%DH!s0i/2JS0>PZ1V:EXQBRZP!s$alO1S05O1S01O1S07O1S0EO1S0CO1S0@O1S0?O1S04O1S03O1RgO1RjO1RkO1RQO1RfO1R|O1RvO1RwO1RAO1RxO1ROO1RuO1RTO1RHO1RaO1RiO1R_O1R\O1RqO1R?O1RhO1RDO1PZPbPDPZPePhPZPdP?PZPcPqPZP@P\PZP[P_PZP^PiPZP]PaPZPUPHPZPYPTPZPNPuPZPoPOPZPVPxPZPRP!#jU$wPZPSPvPZP3P|PZPWPfPZPKPQPZPXPkPZP0PjPZQ0DPgPZQ0:Q03PZQ0BQ04PZQ06Q0?PZQ09Q0@PZQ00Q0CPZQ0AQ0EPZQ0;Q07PZQ0=Q01PZQ0<Q05PZP9Pl%8lFI!s$A!#4=$E:P:H04Q0>&038%Y8#Kp+01O,ULR`002I%K`%KIp+01QR`,UL/jI#K[[1}FJ12=F%KJQ08,2=[[%KFRIg01RhRLA|FJ9UW8Q08#K\L^8Ip-0RI!{Q$BPB1{B9P9PyCf!s+&zP{1gB=1zB6R65y{%e1R=P{P6%9ER6P!s$$DNP!s0h>01{nP=P{!$:D'7ExCiCi!||,X:BW9%K:P9!|RvP7[[^:B^9IP:!#43$URIPp%OG#O!s$/RpP;P!w@$Sp+01RP`Pp!#4q$%YGP<P>O4b2bHbIbJbLb?W0X7CP:O1n0110001020111100X1!s>w0!s>~!s>~!s>~!s>~!s>~!s>~!s>+0!sV~!sV,P:O1!{l$H05W=WFWEW>W@WDWBWCWAW<W;f:f9f8PGP2!$Iq-O;n5!so$!su%01;110110210610810710910510410:10;103WGXKBXPBXOMWMWNo"). Qed.

  Lemma h_know_ok : ltac2:(zQ "b0!jj2!jl5!h9!io2!mo5!ot9!pi2!pjb!ok9!nr7!khe>4regs@2$4@1$0#5@1$1@1$0#k0>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>2sp@1$1@1$0#k0>3tid$2>3can$2>0@5$7^5^4^3^2^1@4$9$a@1$5@4$6^6^4^3^2^5$8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefHdrErr ()) ["Plain"] "##\Up'0h07__arithh14__ffh28__varmaph35__with44__x1h51mh61dh72Hah86__sat0h9!s/%1h:7!s/$34h;!s0&5h<!s0&6h=!s0&7h>!s0&8h?1zh@1xhA4__x2hB1bhC4cstrhD2E0hE2E1hF2E2hG2H3hH2H5hI5Hcan0hJ7Hcells0hK2HdhL5Himg0hM2HmhN3HsphO5Hsp17hP6HspHi0hQ6HspLo0hR5Hstk0hS5Htid0hT6Htid33hU2PHhV2Z0hW3canhX1ihY3memhZ1nh[4regsh\2sph]3tidh^1yi002H2i012H4i024Hcani036!tl%i044Himgi05!t\$6i065!t]$i075!t]$i084Hstki094Htidi0:!t]%2p%0p&0p;1p;2p;5p;4p;3p;6p;7p;9p;8p;<p;@p;Bg001lj12Tg001Gj16Tg00h5j1W!s/$Sj1cTg01TWk20ZTg003kj1qTg03IOR0k50FTg03DQj4ETg019Lj1FTg01W1j4aTg004Mj15Tg00l1j3oTg03?Mj2uTg002Qj3<Tg00jKj2:Tg016oj27Tg03JRj2OTg017YR1j20Tg03K2k40@Tg01CLj2;Tg00AWj29Tg00iij1`Tg03L3k20!t>$2kj1bTg008^j1?Tg00k1j4jTg03M9j2hTg00@5j2lTg01Boj2mTg03NAj2xTg03WMj1wTg00B2j2ITg03CNj2VTg0062j1]Tg009=k20XTg00:Fk30WTg0185k10!sM$=aj2UTg00;Oj2sTg00<Xk20P!v4$kk10OTg00Kmj3p!vw$Kj1nTg03XSk10NTg01]Mk30Mk401Tg01LTk10KTg01ERk10JTg01F0k10ITg01G>j2iTg01J5k20!wS$JWk20DTg01KCk30C!s0$bk40BTg000ij6XTg01;Tj2\Tg03YYk70ATg03QTj2f!w0$hj2eTg01DPj3d!tJ$4j2^!tI$[j2_Tg03Z`k70?Tg03[gm90>Tg01Hgk30=Tg03\ok80<!v8$RR2j23Tg01^]R3j1LTg03^4j4RTg01`=k10:Tg02DUk409Tg03_4k508!wL$Lk406Tg03`Fk207Tg01:Mk10;Tg01<[k104Tg01Adk303Tg03aJk202Tg033GR4j2tTg026Rj4[Tg024lk100Tg027=j4~Tg025Jl<kTg03bWl@|Tg03c]k60HTg01i9j2{Tg03dfk30!u/$f3j6z!x0$Mj3yTg01IJj4rTg01N9j7v!s/$]k70QTg01OAk80!u^$HDk30STg02Wbm<0TTg02XGmB0UTg03g<k60YTf0R5#6#2p=Q%65#6p=J%2!s-$>%25#2p=Pg00OFR6g00R`R77<5p=T!sB$!s$/p=G!s:+p=H!sr$!s$/p=N1075p=1g00N=R8f1R9;y5p=B1i65p=8P6P9g01T0P5Crp=Y!s4$OeR:g01PDR;P;g01PdR<P5g01QkR=Fvp=Zg00WbR>g014FR?!tl$Mf2R@1095'9p==P@P:P;P;P<!t0&QDP5CrP!se$4!sD-9P5K0Qp=Df3R=!s<+@P9P5L0Rp=KB0S695p=CP6P7P=!sA%EXp=S1I65p=@g00oaR:P6P4P3P1g03HAf5R4f4RA!sV'M<kp=gP:P6!s$$3P3P4P!sD+N<0Tp=}!sC&!s$%2P5P9P@P2P=PAP4f6S00f7R2f8R3f9RBNB0Up>0GP8!sn,J0Yp=Ag00OdRC#2RD#6#WRE%2DRF#2RG#2RH#2RI#2RJ#WRK#cRL+0Z%WG#cRM#qRN\L!st,I0FP0!tu,g00lTR0Q00!s8%CE#FP4g02`mS01CaP5f@RO%5DRPg03SXRQ5oE'uf>5<LfARR%5FRS=oEQ'u%QH#J#>#QRQ#Q#J#Q#P#5,:K5<L17KO%5HRH'O#T%PJRO#GRE#H#>#>#G#5RT17KR'0fBRU,7K%6CRV#JRW#6RX#J#N!s$+5RY'0P0fDfCg03UBRZH0@%5ERE/05%PW#>#H!sw$W,;5'9fGR[1:K9O1%`M5<N[^X6fFRNg03VER\+05%bMRM#qS02P0P[%PQ!sh$5RQ,:Kg00SjR[#?R]#?R^#?#?R_CjfE,:K,h_,lM3<%1N%5IRI,mPR`,;N'9fIRa/xN%wa17KaRN#1%5JRJ,mPRb!sG%JRN,ILfLRcPNPafHCE#F/V[=<LN1:KNRd,ILRefMRffKRgPNPa!sH%]=<LdPefNRePcPgPN!s=%^=<Ld1I671:K7Rd,7KRN#TfPRgPePfPcCE#FRafORh%][Ri00XHRjB0WiTYRk&0VZ,Ui/sZS0320PEWS04&0O7Rl%2X!vm+X'URm%>V#P!s7&V'sRn1UlQ%]]S057p_S06g03g],Ul%?_#?!vM$o%]^3pS07%n8S08'BS09'BS0:'BS0;'BS0<'BRp'BRq'B&0N\B0M0ahR\PjPqP0PaPhPiPHg01SDRq#nRj%bqRq&0K6Rr&0J6Rs&0I6Rt1i67Ru%8H'Y'Z20Et<R<P5P@1I>?20D5@#MdB0C679H0BR?b1b2b31;7HP5b0PLPe17K5R>/OH#TXBLf=1Va[S0=P=EX1\ai,7KR[!sD$eK0AP\PkPp!tn+TPY!si$0T>?=>YXBL17KeR>/fHS0>%1>%1HRp17Kg/OH#1[[S0?1ePIRk1;7PRv%1I1;7`[[Rw%1PRxg01RhRyAdPI9UW7RI%1`\y^7xR`1ePJRz%1J1;7bR{[\vRvAdPJ9VyX7xRJ%1b!sP%xPjPq1^69RyPsPt1_6CR|%8Y54tR}%`;R;Pt%8T=4t|R~P;ADt~}CKCKP<P!v<&X46105Y10T910T@?=@Y[[^46P5fTR},7KS0@PRPUO3b0b:b;b<b=b>Q!vR&0T[?=[YeK0?P\Q03Q0<!vN+ePZP=f:RiQ0>Q0?PkPwPIP`PzPvPJP!u0$P!u+$P~P;%5ORO#8R~94tuA4t~|5Dt!tv4T5%1O?=O9!tp%Q0@PUO2!tg/107Z?=Z>eN90>P\Q04Q0;!ta&EPW!tC$rPs%8E94tu!t,,%1E!y:$!tk/!sN$W%8P>0=6KRP54t!sW,10WbP5b0b8b9PBL0<P\PnQ0:135XRW#11;Wb%1VRE13WV;=b'9'9%19RW%L9,3@/0VR>P0P}13AX/3=,:KP@CR#M[[^5:^66'9X?6137XRZ#11;Zb13ZV==E!so$RUP0fSRO13Z=RT!sb+\>\W!sd%!u>5XR~,CuR[94tu1Y[P,Zt%8VRY!s6$C[Y=4tP5Dt!s%%!u],PU!u[+OPTP@&0:@S0:%L@#1RT17KORU/fHRR%1UfU,7K!{b$\p[Rp!x_=A4tu|P;1C[|!t_$~!xW2%1513Z9RZ,0X!xX%PiP3!xW1bCQ0:PTPRP!t7961^6@P9PrH09!|%&DRD,C|=4tY!tJ$D%QF#J!#5S'F#854!z13XA61359/0V13Z@/0F[^46^A6P5%LBPiP2!{}1bCI08XM>XKWX5:X66H06PN!wS3A4tuu1YuP,Z!w311077/9{!w8'-077CS&0;mR{,\a,7K&04mRF'3!y&7P0POP}fRfQPgCE#FR}/\{,7K/3F!yv/!y:,'9eB03amVP0PO202}m!sN<!|O&nH01eP\Q06Q09!s:&lPdPQP_Q051:Kf1ILdP@1t]_%5CRC/0SRdP]PC%@CP_PS%@SR]Eg!zT,C%8SRC!|g0PdP5b0C[1t_o%5GRG,!sk$_PSP]PoPG%@G!sh/G94tC!sd635QRd#1X?6!sR,Q,CuRG!~W1137QRQ#1!~\$NP5CS%L_R7,3d/0b!}9$Q7Ru/0bRo13QSRf/0bRlP6P6P1P5X@6RnP11095$00X^6X@6PuPfPn!s$$6P6g02hi1395C~#@X56XZ6PQPQ%@QP7PSPnPn%L5#@X@:!uY%E}N:0GPbPb%@bM<k!yS31CGC=4tP!ui-l!yG'C[Poe!u;%Q02P0Pg1:KdP_Cj1:Ke!#@[&X?6P2!sL%M@|P\Q07Q08!x;$^PcP9P4J0H1{8\DA!s$/B0Lah3Ez!xf%Q01CaebVbFbEbDbNWIWTWSWJWLWRWPWQWOWHWGPiPBP3P2Q0!#Ec,P5O;n5000001!s+$01;110010110510710610810410310910:102WUXW6X]6X\LWYW[o"). Qed.

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

  Theorem hdr_short_fwrite : ltac2:(zQ "h41!jj2!jl5!khe!io2!h9!mra!mo5!ms3!msb!ngd!nl9!kj1!k2!nvb!pjb!pk2!omd!on5!onf!jtb&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4regs@2$6@1$0#5@1$1@1$0#k0>3mem~0>2sp@1$1@1$0#k0>3tid$4>3can$4>1K$h0>0@5$e^6^5^4^3^2>0@1^2@1$c$d>0>5regs'@2$6@1$0#5@1$1@1$0#k0>4mem'~0>0@5$f^a^9^8^2^1@4$a$2$9@2$5@5$7?2fx^3@2$b@1$0#k0+knls4^2@1$8$2?5model^6@4$a$2$9@2$5@5$7?2fx^9@2$b@1$0#k0+knlo8^8@1$8$2?5model@2$h1@2$h2+2$h3^4").
Proof.
  hf_plain hs_sound.
Qed.

  Theorem hdr_overrun_fwrite : ltac2:(zQ "h41!jj2!jl5!khe!io2!h9!mra!mo5!ms3!msb!ngd!nl9!kj1!k2!nvb!pjb!pk2!omd!on5!onf!kjc&>0@1$1@1$0#k0@1$3@1$1@1$0#8>4regs@2$6@1$0#5@1$1@1$0#k0>3mem~0>2sp@1$1@1$0#k0>3tid$4>3can$4>1K$h0>0@5$e^6^5^4^3^2>0@1^2@1$c$d>0>5regs'@2$6@1$0#5@1$1@1$0#k0>4mem'~0>0@5$f^a^9^8^2^1@4$a$2$9@2$5@5$7?2fx^3@2$b@1$0#k0+knls4^2@1$8$2?5model^6@4$a$2$9@2$5@5$7?2fx^9@2$b@1$0#k0+knlq4^8@1$8$2?5model@2$h1@2$h2+2$h3^4").
Proof.
  hf_plain ho_sound.
Qed.
End Plain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
