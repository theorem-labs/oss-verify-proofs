(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame Hoare.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefExitBase RefStdioDefs RefStdioWrite.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_LibStdioCall () := KReplay.lz_vm "#%7eC47Corelib7Classes9Morphisms?eq_proper!s,#xy!sR5?Relation!sb'Reflexive!sR-Program6Basics4flip!tD?Mtrans_co_eq_inv_impl_m!sE&K!s`,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!u?#s2bv00C!sI@;bv_unsignedC56Stdlib6ZArith6BinInt1Z3leb!sC=ad!s`?tb!v?,4Init9Datatypes4andbI!sD15Logic3and!u0#!sA7iff!t=<2le!sB>tC4!sB&4Bool!s'$=!tR#_true_!t##!x:>Ir!x~'_!s0,!yb:!s\,F!sR0!z=>>!sY+_Prop@and!t`#!yC+!uN<6leb_le!tS?:respectful!sM?NR!tz,artial_app!tPGtb_ltK!x8<1!x887!uY$ndc89OSSVerify6Proofs:boost_json:fuzz!t^#se3lib1U<LibStdioCall3inrC13~~~!y^82eq00I!z><bool00K!sFA1!#31D>!wo#T!~I#!}k$I!}i=Z!t=/!~T=3!tBE=!tB#!#4Q6!sV:?Equivalence_PER!|k9not!sqE8symmetr!{+Fnot!{+1!z=?!#6'$sym_co!#6+4!y=_8inr_!{i#!yB%!ur86!#7I#d!sB89False!sE#K!y};!y=F?!v$#e!wM,!z7B2!xsJS!wT%ic!{i84True!{k4!sB%5!uM$!{h4!s_/1C4ELinuxProcessSemantics?!s<22Fs2Fs!u%,5Lists7!s+#Def3mapC7!x/N8SymDrive;nth_map_seq!x+>8!x+%_r!~L<6op!vX#!~n?list00C!z#O=SymExec2Sound4SX2S7know_ok!t|%K8!ulR!st$3SX25saddr01!ul&!tdb4flat!sqi6estar!ss'!xDO7StoreOk9mem_grows!xA8!wY,3or!#>`82or00!~q_9!~q#f!{f#!wn&!y+A1K!#>z&9micromega6VarMap1t02!sD@3I!sD?0!sD6=RingM!s4'7Formula!}_#!sQ47Env!sT#5PExpr!#D^>!#9U+1!snE3K!|VC!uj75Tauto8G!u#'7C!sJ<B!sJ&!sH6:Z!uq+=Z!sT$CheckerC!vf<4f!#7a#!sq?C!sq0_s!{5#!#D?5:or!#D>%r!uWF3!{eP!z?#KnowFrame8kn_f!s/#!|VV!so0=!#3v%!st/K!yjL1!u\F4!sJF6!sJF5!sJF8!u1D3Op205!yp<5eKind!#83<unit!|X8!se%4kind!v4#!sf@1!ttI3I!#8L[3env00!#FZ%!sl\6kentry!soe4e!~t#0!zj5!sf96images5Ubsan1M?loaded_segments!#I%&!}f?;!#K+$!tt$!#G\>1Z!wt/!#?]06Forall!#5l-!sG91!ye+!sF%4!s+#8flat_mapI!sdB0!sd7?!sC%_!sk'!#:K_kimg_cut!#>K&!t>62In!s=7=!tU'!s,$!#Ar75proj1K!y{d1!#A$b!so'2!sok3!sok4!#@6Bapp!#V\6orb!#?K$_!#W]>!#Tq#gt!{J@2!#YZ<pow!#['@7Z_to_bv!y67:!y6&!u7#!t0;>pow_pos_nonneg!sN<:!sN#!sJ%!#?HD!#6a<3na!#B18!#6`05Psatz!sOM!#:@6!#3v:2!#D=A!#Cw@!#B>E7!#HSO3Lib2Nd:and_elimF!{?l5!sok6!sok7!sok8!so%!#V6_!#6v&!~]&!#MOa9!th%!#P&'!ti_;!}n&one'!#<=1!~<-6Ex!s2#00!#>8\!#Q=%!#?$&!}k@0!~2A1!}8N1!#V,PAgentLib7u64_lit!y[c!#@~$!#T&V!zJ1edenot!x]e6u!uL#0!t^da_ba!#RQ&!sm]5a_off!y$B4prod!#YEQ!t409split!x<,!#;'@C!#;'%_!#o8-!#@}66eq_sy!#iE<7add_0_r!sGCl!ytc2!zci!#8Z%!|>QProp!sn#5v_add!v~G5bv_eq!#?OAbv_wra!#?0<6modulo!sF<?!vy#mod_idemp_r!uKY=!tU&64!sr#!uSG@!yS'!yP,!#c}85Riscv3Sem5alu64!toY7alu!w>,!xoc4!smi5!smi6!smi7!smi!#>C%K!#4S@!#tO9!#kt#alK!xz@5Instr!x|#op01!sRN2!sRN3!sRN4!sRN5!sRN6!sRN7!sRN8!sRN9!sRN:I!sRM0!#wZ=N!#[t7!#[451!t?Hmul!t?#!#3?O6SymRun<!{9#_vars_l!#;Z'!{?:9!$$g#pro!#q-P9!#q-&X6kindex!|NB!#g4&!|P33Nat3su!#l'3Peano2l!#s{5!s@+!#Z&79nth_erro!#=,+5!#91#8!s^$!t<#!t@&!sF?8sub_diag!#uH72ex01!#:Y<of_nat!#T5<!tJ/!sC&4Znat5Nat2Z7inj!$,90!#3p-iff!#?z#!y~5;Zify!#x=%5mkrel!sKB7rew!#Vl6!tZ-9i!#TyC8max!#{x#!#W;?3!#RG=3Pol!#dVE!#TK%4!#S9D4!uoB;!uo&_rev!#SdV9ex!#Sc$1!|iB8list_!#h34!y\,0!y<=max!xTE!#\<-!sK96!sK$2!xS>8!z/#succ!sJ>;!sJ%b_!td#!sM=6!sM#!$3%-!}h0!{y=6to!|A@9mod_small!#JC\4ridx!ww'!vQ48!vQ#Inst@!}t%_!t`%_eq!ueD!~H>eq!$:m<7eqb_neqK!$<HC1!xQB9and!$-|$!#Ec@7Prelude6!#Ho#b!#Fg@4BvWf!$'+;nth!#X}_!wR#!#Nn,!#Q]\sr_ge!#;%B6length!t5aupd!yT<!wT0not!wT'!t^:7!yp#!$2a/!v}2seq!#eY7!u>%!$-`#!#:{>!xK$!se57e!#[&#b!#<p6add!t@?!$0d[?sr_after_call_j!va'!zfG5bv!tF#!w|O!$046regs!#_0g:s!s0#!u?$!sse<lit_even_re!$/HV!#B^+:is_kwr_cov!|]c:base_rang!$#SV!#ES%:s!#EQ2!skWkn!sk1k!w2^9!x#%res!#`7'!{3X9junk_vals!slW!#U&'seg_rom!{qA!$;=25State5m_fdsC5!#BI'!#BA%6IntDef!$M;&!sE=!#ER5!#<t+eqb_!#3a@!sI'!#5Y49SatDivModCZ!#Z7#!#Df$!#rD<!$'V21!}Qa!#8V#!#?'#!wa^4getr!|SV!#3}5@!|Y,!$2a%!#39c?!#cm'_!#gS,!u`Y9u64!~G/!#mx_!#Og$_som!#gWc8!#Qp#eqb!wLi;!su'_!$C[@!#J+$f!#MIB3inj!#7LY<kwr_store!#:&'!~YK>!#;\#!sE+8!sl'!$+W_!$,D#abs!#m@e!zK[!v;,;!sj%!#nx-!v:Y@word_to_le_bytesC3!#Fc$7tac!sG#<!#`9%_helpK!v_RRef!v_$Defs7sw_fi!#W+#!u#&!yP&!$'[+8or!#YOU5Hoare;ret_ok!#>`#!t/%I!t{bpo!$K:#!wmU!#=$%>vals!$ZF#agre!#>^]9env!sj0!}&A8or!#Gu$!#9:E2!#E{Y!#DQ#!#E}+!#5idF!#Hx&!#F|6!t#_=!t#,!#KW+!#=G@_de!$T`26Specif7sum!$]1$!x6W7!y#$ev!xxV!w@+>!#DZ+_nth!yk]<!#|-$!zZ\!#4:+=!uM&!{Q$r!wxe?n!wu+_s!$G^'!sx_@!sx-other!#6z`!#M6%_ex!#7k`<!~6$pp_know!u\e>!$/y&!#Auj>!#Au+!z1#!tpg!$L~-!#|L&!#@@bmkAlu!#Cg/!tqQ=!#8G&Write?ref_!#Lm$w!s6#!sy%!#v'\!$JL#!#M[_5kread!uQV!tV05!vE$!x2e5sc_wb!snjp!sne4sc_s!smil!uLisp!x\W!#K-&3rdn!tVif!#_e'!#S7N9fd_lookupK!s^P7FdE!$K2%!s^P8m_halt!$+F<!tu:m_vm_lazy!wudr!w5ik!w}f6sc!#]tY!#T@+mks!$<R&!vpJ3Run6config01I!#4RPhapeAlg8realizes!#GW&!ySQ5event!#EdS!tK&6t_em!$??'!#FsD:!#7-X9!#7-#_!}V+i!xW^!#_G,!#P^c5two64!z;e7SC_KEPT!sp%I!~\Y!#G?P4Scfg=hunspell_scfg!tLW!yU&!$aqB2!s|RMode!#IaR!zS+4TS!#pu+!te4!#v<'7Inj_Z_Z!#:Zbf!xnfsc_buf!#=&e8!sp%sz!sq%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04cons03nil06option37Corelib7Numbers7BinNumsj61Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~l34expr04None04bool04andb3h5LinuxProcessSemantics5Riscv5Instrqb5aluopqb5mulop04Somel35two6446Stdlib6ZArith6BinInt1Zud3eqbud3lebud3ltbud6modulol36kentryl35saddrud3addl34KImg03app03orb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcLibStdioCall4FPX1~~~~~~hk89kimg_cut136Stdlib5Lists4Listhpb8flat_mapj64Npos35stdpp9bitvectorbdefinitionshs12bvhs1bbv_unsigned04true37Corelib4Init5Logichv93andhv92eqhv93iffhk83inrud2leud2lt05falsehv93notl32SA79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~ik56estart69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLibKnowFrame~~~~~~ip48kn_frameik54flatik57know_ok69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~iv2floaded_segments69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~jjb9mem_growsl33envhk88kimg_cutl34ELitl36edenotud3pow04pair04prodl39split_liths17Z_to_bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~jsdcexpr_vars_lthv92ex37Corelib4Init3Natkhc3sub37Corelib4Init5Peanokj52le69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9SymDriveX~~~~~~kkf6kindexhpb9nth_errorkj52ltl34ridxud6of_nat37Corelib5Lists7ListDefkr83nthl36sr_get06lengthl36sr_upd69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~kv0fsr_after_call_j" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition SC_KEPT : ltac2:(zQ "20!h8!he@1$0$1") := ltac2:(zQ "30!he!i3!i9@3$1$0N1@3$1$0N2@3$1$0N3@3$1$0N4@3$1$0N8@3$1$0N9@3$1$0Nh2@3$1$0Nh3@3$1$0Nh4@3$1$0Nh5@3$1$0Nh6@3$1$0Nh7@3$1$0Nh8@3$1$0Nh9@3$1$0Nha@3$1$0Nhb@1$2$0").

Record stdio_res : Type := SCR_ {
  sc_f : Z;            (* [comment removed for export] *)
  sc_fd : Z;           (* [comment removed for export] *)
  sc_ret : Z;          (* [comment removed for export] *)
  sc_wb : expr;        (* [comment removed for export] *)
  sc_wp : expr;        (* [comment removed for export] *)
  sc_bufp : expr;      (* [comment removed for export] *)
  sc_bufsz : expr;     (* [comment removed for export] *)
  sc_s : expr;         (* [comment removed for export] *)
  sc_l : expr;         (* [comment removed for export] *)
  sc_sp : expr;        (* [comment removed for export] *)
  sc_sr : list expr;   (* [comment removed for export] *)
  sc_kn : list kentry  (* [comment removed for export] *)
}.

Definition lit_even_ret : ltac2:(zQ "30!ie!kf!p2>1e$2@1$0$1") := ltac2:(zQ "f0!kf!p2!p9!he!pf!q5!ie!sf!t7!tf!u5!hg5!hgb!hh1!hh7\1e$1M1\1e$1@1$6$0^1\1r$0M4\0$4@1$6$0@2$5@2$5@2$b@2$e^1+2Z@2$cZ^1@2$d^1$a@2$9$0^1@1$2$0\1n$3@1$2$0\2op$7\1a$1\1b$1@1$2$0\2op$7\1a$1\1b$1@1$2$0\2op$8\1a$1\1b$1@1$2$0\2op$8\1a$1\1b$1@1$2$0\2sx$4\2lo$3\1n$3\2e0$1@1$2$0\2sx$4\1k$3\1i$0\1n$3@1$2$0").

(* [comment removed for export] *)
Definition kimg_cut1 : ltac2:(zQ "30!kf!hi0!h8>1a$0>1n$0>1K$1@1$2$1") := ltac2:(zQ "f0!hi0!i9!i3!kf!pf!hi9!p2!h8!hj1!he!hj7!hgb!hh1!hje!hk3\1a$3\1n$3\1K$0M0\1K$0@1$7$0^1\2a0$5\1w$9\1v$6@3$2$0^4@1$1$0\2a0$5\2n0$6@3$2$0^3@1$1$0\2a0$5\2n0$6\1k$9@3$2$0^4@1$1$0\2lo$3\2hi$3M4\0$4@1$7$0@2$e@2$b^1^5@2$b@2$8^5^4^2@3$2$0^3@1$1$0@3$d$0M4\0$4@1$7$0@2$c^2^5@3$2$0@2$a^2^5@1$1$0@1$1$0M4\0$4@1$7$0@2$c@2$8^5^4^1@3$2$0@2$a@2$8^5^4^1@1$1$0@1$1$0\1e$6\1m$3@3$2$0^3@1$1$0\1e$6\2lo$3\2hi$3@3$2$0^4@1$1$0\2a0$5\2n0$3@3$2$0^3@1$1$0\2a1$5\2n1$3\2a2$5\2n2$3@3$2$0^5@1$1$0").
Definition kimg_cut : ltac2:(zQ "30!h8!kf!hi0>1k@1$0$2>1a$1>1n$1@1$0$2") := ltac2:(zQ "50!hi0!kf!h8!hoe!hqe\1k@1$2$0\1a$1\1n$1@4$4$0$0@2$3^2^1^3").

Definition stdio_call (nv : nat) (sr : list expr) (kn : list kentry) : option stdio_res :=
  match nth 10 sr (ELit 0), lit_even_ret (nth 1 sr (ELit 0)) with
  | ELit f, Some ret =>
    match kread RSEGS kn (ELit 0) (f + 120) 4, kread RSEGS kn (ELit 0) (f + 40) 8, kread RSEGS kn (ELit 0) (f + 56) 8,
          kread RSEGS kn (ELit 0) (f + 88) 8, kread RSEGS kn (ELit 0) (f + 96) 8,
          kread RSEGS kn (ELit 0) 0xfbc78 8, kread RSEGS kn (ELit 0) 0x12ec38 8 with
    | Some (ELit fd), Some wp, Some wb, Some bufp, Some bufsz, Some (ELit cg), Some _ =>
      let sp := nth 2 sr (ELit 0) in
      let '(qb, k0) := split_lit sp in
      let qk := (k0 - 112)%Z in
      match kindex (is_kwr_cov qb qk 112) kn 0, base_range kn qb with
      | Some _, Some (blo, bhi) =>
        if ((0xfc000 <=? f) && (f + 232 <=? 0x12ec38)
            && ((fd =? 1) || (fd =? 2)) && (cg mod two64 =? 0x12ec38)
            && (4294967296 + 112 <=? blo + k0) && (bhi + k0 <=? 0x800000000000)
            && expr_vars_lt nv bufp && expr_vars_lt nv bufsz
            && sr_vars_lt nv sr && kn_vars_lt nv kn && Nat.eqb (length sr) 32)%bool
        then
          let k0 := kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8 in
          let k1 := kn_frame k0 qb qk 112 in
          let k2 := kn_frame k1 (ELit 0) (f + 32) 16 in
          let k3 := kn_frame k2 (ELit 0) (f + 56) 8 in
          Some (SCR_ f fd ret wb wp bufp bufsz (nth 11 sr (ELit 0)) (nth 12 sr (ELit 0)) sp
                     (sr_upd (sr_after_call_j sr SC_KEPT nv) 10 (nth 12 sr (ELit 0)))
                     (KWord (SA (ELit 0) (f + 32)) 8 (mkAlu ALU_ADD bufp bufsz)
                      :: KWord (SA (ELit 0) (f + 40)) 8 bufp
                      :: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3))
        else None
      | _, _ => None
      end
    | _, _, _, _, _, _, _ => None
    end
  | _, _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inr : ltac2:(zQ "40!kf!pf!hra!hte>2lo$0>1n$0>1x@1$3@1$2#k0$1") := ltac2:(zQ "80!hra!kf!hu4!q5!hj1!hgb!hh1!hte\2lo$1\1n$1\1x@1$7@1$0#k0@2$3@2$5^3@2$2@1$0#k0^1@2$6@2$2@1$0#k0^1@2$4^3^2").

Lemma inr_spec : ltac2:(zQ "d0!hra!kf!hu4!pf!hv3!igd!ih4!iha!ii1!hj1!ii8!iid!hte>2lo$1>1n$1>1x@1$c@1$0#k0@2$7@3$6$3@3$8^3^2^1$4@2$5@2$a^3@2$2@1$0#k0^1@2$b@2$2@1$0#k0^1@2$9^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##0Hh05lemmah11Bh21Hh32H0h42H1h52loh61nh71xp;1p;2p;3p;4p;6p;;p;5p;9p-1R0g0000R1p4p710p9P0p1000\!s611HR2!s8,P!s2$2!s3/31!s4%g001fR0!sR'g002`j11Tg003Ej1K!s/$cj1@Tg004Fj26Tg0050j2=!s/$Mj24!s/$jj2:Tg006Gj29!s/$eR2j22Tg007@R3j23!s1$Yj27Tg0085j25TP1j2J!s5$Qj2ITg0092j3F!s/$hj4;Tg00:[R1j6ETg00;Mj2C!s/$mj4BTg00<Tl;ATg00=Oj2?!s/$oj4<Tg00>Jj5D!s/$gj3>Tg00?mj3GTP0l9HTg00@Gf0!vn$@g3Gp=0p-0R4P3g00AGf5R5f4R6f3R7f2R8f1R9P0M9Hp=8g00B8R:g00BV#1!s$-KR;#@16;0R<,=8R=1489R>,:<R?'9#0%0=R@%0?RA'2'316;9RB,=7RC1478RD,:BRE!sN%CRC%0ERE'2RFP0177BRG15BDRD'2RBPB1J4BRHE8W01I=?178<R?,3@PF12GERFPCPGP0PEPEP!uF%C;9F43RCPEC;EEPBPBP!sd%C8<15<>R@,3APFPBP4P4^14P3P4P4P3P3CBP2P1PG!s4$CPGC;PEPDP0M;A!sm-?<>12?@R@PB[R?P?PGPDPB16;81467'516;7R;,751456,5;P9P0C<W4X3GP0DDX2@RGPGC<O2O2O2A>890#0/3@eW7X6:W5o"). Qed.

Lemma inr_false : ltac2:(zQ "e0!hra!kf!hu4!pf!ij2!igd!ih4!iha!ij9!ii1!hj1!ii8!iid!hte>2lo$1>1n$1>1x@1$d@1$0#k0@2$7@3$6$3@3$9^3^2^1$4@1$8@2$5@2$b^3@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@2$a^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##/-p'0h01Hh13Heqh22H0h32H1h41eh51bi001bh65lemmah72loh81nh91xp;1p;3p;2p;6p;7p;4g002`j11Tg003Ej1E!s/$cj1@Tg00>gj38Tg004Fj2<Tg007Yj2;Tg005Mj2:Tg0085j25Tg006ej26!sJ$@R0j24Tg00Ckj3?Tg00?mj30Tg00D]j12Tg00E6j6D!s/$aj3CTg00FSj7BTg00GNj3ATg00HYj6=Tg00I5j27!s/$Tj29Tg00=oj4>Tg00@GR1f0R2g00@gR330p=3g00B8R4g00BV#1!s$-ER5#@f2R6f1R7;82R8#31<52R9,;61:67,59'6'4p-0R9P0g00In9?90f3R:?867R;g00J`R<5011<57R5,;:1::6,55'6R5#2%3;R;#2P!sd%K@P;P5P2ED9C5;FBW6AA672P8P1P1A012<%32#2'4P2A013<R8A0133R6#2R;[P8\;P7!sS$3P1P9P2g00L0R5g00LLR0n0110000020000X41g00LiR:P<P2E=P01702R=b3b1X26P;eX081913P6P7P2O1,78b1X0;C>A01<<R;A01<3R8#2R7[P;\7P!tw%<!tJ%P0P5!t@4P:P3!t;%P!t7&8P7eX0;191<X07C>!sY1b5O2W9X84W7o"). Qed.

(* [comment removed for export] *)
Lemma know_ok_frame3 : ltac2:(zQ "h60!hra!ik0!kf!ioa!hte!hu4!ie!igd!ij9!it3!p2!itf!hj1!ii8!iid!iu7!ji8!h8!ih4!jn5!jo2!hi0>1E$h4>1M>0@1$4@1$0#k0@1$6@1$4@1$0#8>2M'>1x@1$4@1$0#k0@1$6@1$4@1$0#8>2kn@1$h1$h5>2b1$a>2o1$2>2n1$2>2b2$a>2o2$2>2n2$2>2b3$a>2o3$2>2n3$2>0@4$f$h0^d^c^a>0@3$b^e@2$1^a^9^8>0@3$b^f@2$1^8^7^6>0@3$b^h0@2$1^6^5^4>0>1x@1$4@1$0#k0>0@1$8@2$7@2$d@2$3^h2@2$1^e^d@2$5@1$0#k0^1@2$e@2$5@1$0#k0^1@2$c@2$3^h2@2$1^e^d^c>0@1$8@2$7@2$d@2$3^h3@2$1^c^b@2$5@1$0#k0^2@2$e@2$5@1$0#k0^2@2$c@2$3^h3@2$1^c^b^a>0@1$8@2$7@2$d@2$3^h4@2$1^a^9@2$5@1$0#k0^3@2$e@2$5@1$0#k0^3@2$c@2$3^h4@2$1^a^9^8@3$h2@1$6@1$4@1$0#8@1^h3^4@1^h4^4>0@2$h3^h1^h0@4$f$h0^h3^h1@4$9@4$9@4$9^h0^f^e^d^c^b^a^9^8^7").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##U{p'0h01xh12Hxh22E3h31bi001bh42E2h51Hh64__x1h74__x2h84__x3h92loh:1nh;7__arithh<6heq_a1h=!s/%2h>!s/%3h?4__ffh@4__p1hA8__varmaphB5__withC1EhD2F1hE2F2hF2F3hG2G1hH2G2hI2G3hJ2HKhK2HghL4HouthM1MhN2M'hO2M1hP2M2hQ2O1hR2O2hS2O3hT2a1hU2a2hV2a3hW2b1hX2b2hY2b3hZ2knh[2n1h\2n2h]2n3h^2o1h_2o2h`2o3p%0p;1p;4p;2p;3p;6p;<p;7p;8p100MEp4p70p100N3p4p7210p!s@$NOp4p710g00OWR0!s3%p8g002`j1>Tg003Ej1U!s/$cj1PTg00P5j1]!s/$Wj1MTg00Q7j4hTg00REj2GTg00SMj3JTg004Fj27Tg00D]j16Tg00TXj2LTg00?mj32Tg00Uej2ETg00>gj30Tg00Vjj23Tg0085j2?Tg005Mj2@Tg007Yj2BTg00WGj2CTg00ITj2;!s8$aj3_Tg00Xmj1^Tg00YMj2N!s/$kj4\Tg00ZIj1[!s/$gj1ZTg00[Rj2HTg00\5j1Y!s/$Zj3RTg00]=j1W!s/$_j6nTg00^Cj2m!s/$ej2lTg00_Qj3kTg00`0j4j!s/$bj1TTP0j6gTg00GNj3fTg00a@j6eTg00HYj6d!s8$dj4QTg00bml<KTg006eR0j2cTg00d;j4S!s/$fj7bTg00eJj7a!s/$nj7`Tg00fRj8iTf2R1f1R2f0R3'G'Lp=5f4R4f3R5'B1@23,?1'cp=4g00@GR6A0512;23p=8g00@gR79263p=:g00J`R8!s4%<A2623p=Og00B8R9/;3p==A2923p=AP9P2g00g6P3CSp=D!s4%]R:g00h<R;P;g00h\R<P3g00i<Fbp=9!s[&i\!s[%FP1P:P;P;P<P2P3Fap=X!s92`p=VP5!s9+1P2P3Gip=IA2123#6p=1g00jCg00BVR=#>R>#>#>R?#!s-$#UR@#PRA%U?#PR?#]RB[PB^0ARCg00kI#Mg00lRRDg00mYREf<RFf;RGf9RHChf=RIf8RJ,GHRKf7RL3Jf>RMf6RN,GLf5RO3Jf?RP1GO4;J5fARQ?5IFRR17@3RSPSPRPGD4#6fBRRf:RT75GRU17@2RVPVPUPH!sC$CRU/LKRK17@1RWPWPKPLD4#6PRP5O1PUP5O152B[[[^0Af@RK/EPA5RMIP9A5UFGP9fDRX?5THP9P6PBA01I3A02T3'3fERYP3O1RZPXP3O1n010!s#$20000X0APC!sY&G3fFR[P3O1PZ!sL61?SO1@OR/BS'CRCA0OK2P61;63RZPNPQP1P3C8P6PJPUP4!s2&BA0JQOR\,32fLR]POO1R^fKR_PO!tY3=2B^]4P2A0LR5R^#:P_P4O1,;BW4%<^A0LK4P6PZ1O\3P6PTPUPL!t4'1382fOR\PJ!t-$NR`PJ!t-82P2A0HRN!t-$`PLO1Ra,;BW2%<^P0A0123R^#<P5PVPVP5P1D4S00#6[RVP1PSPSP1P2D4Rb#!|R%Rc#<Rd[P4PWPWP4P5D4S01#6\dA_123P2n20!tT'1!tU$!vm%X:9X99RdPV^0A^:9^99RVP3PFfGRWPJP4O4PF17@JRePePFPW!x}$dPVP3PIP[PTP5O4PI17@T!y`$IP[!yG&GfSRdfIRffHRg35Rh#=1AMhRheS02PhfTRifMRj;5]Rk#=1AKkRkeS03PkfURlfQRmfPRn35Ro#=1ARoRoeS04Pog00n`Rp#^S05%MpRpP91N91P21N95C\Rq%[9Rr%Z9Rs1H9>R>1H9=Rt'D,9s%Y=,H9R=9R9tRu/F>,9s5Xs%W;RvPs!~:'1Ft>,9s1D>u,9s5VsEnCI1ms<RuP3P11;671l31#:dg00oL=k92CjRwb?bAbBX69X79X891?231@31/B2'CP2P1P1P2P5D4g00LL[[^69^79^89P3Pm17@PPXPMO4b;b<b=b>P1P3O4b2b5b4b5!yr&8RxPaPjPL!yj6aeW2n011!s;+1P3O1b2b3W4!s>64b3P5P2O1PgP2!~4$RaeW1X0APa\C^0APgP3O1%W?R?51BA0NQ2A0OM2'3P6!s$$BP3P_P5O1fJRCP5!ta41B?P3P2PHP1P2O!tj10b3P4P2O1Ra=1B?!tG%1EW1RyePy1?SN1@NQ!~@%yA0NP2P6PZPLPK!~<+HPR!~<,P2P`!~2$zPj!s-${!t[1!~`%G[OR|/32PzP!sF252B!}I%JQ5R}#:P6P7!uY&!sR492BzX36PjP4O1R{,;BA0TY4R~/37%T~EgW2%<}P~!#3&$|3P6PIPg!#3&%n!~x$|!x>%28PmPJO1P|!t\54P2A0FWNR|#:P0%:^Q00[R^%:cRc\bQ01\cAf!~8FcP^!~8,^P3PMPfPJP2O4PMPePePMPfD4Q02PhQ03PkQ04Pop-0RoQ05PpPqPrPs1F>t,9sAR9>=R=,Dt!{~%PvPs1D!|;%F=!s;$X!s;$!|X'POEeCICIPuP!|,3W@RwP2P3!y9$1D41?211@15!|=%O!|--^@oRoP3PlPIO1Ru!vY%78R<fVPIO1Pu!v[4P`PU17@IP4PFO6!|`'b4b5W4%<!wC$PxPnPLO1P\!|[5,;B!|A0100!|A'!|q;PO!{3$|92Ba!|V-y^0APOP3O1=1B?A0LK2!|K'A0TY5Ry/33PjP5O1RaP]!|S:!{F'4!uu${!sH5]1P3!sz%HX1R;/37P]P1O1R:P_!s-$s!s|713y!{J'!s|8X36P3P7%TyEdA1Ba?P3b1W1!wF%;8P:P!s}7y!uW'1338P\!}C$8Pz!sP6\PN!v6%!u5'P<!tW9PM!vb$2!tJ%Px!sL:3W1!wc00P2O1b!s<:A1B|!#3}'45R|eP|1?SL1@LK!#3}$SA0JQ!#3}$HPR!#3}'GPX!#3}/nPOO1P8!#3%38!#3V$TU5R8#:PcP^P3PFPY!y@$!#<B$OR@P@PFPYD4fR?5gWRF#=1AIFRFePFA5d]_Rd#=1APdRdePdA5in\Rn#=1AQnRnePnPwPoP3PiPTO1PlPTO152BPCPQPVP4PH!{b-2b5W2%<81;Bu!{'0!{C'2b3P_P2O1PN!#8^&u!{-&u\S^0APN!{-,HR!{-+P3P\P5O1P`!z|:\P4!xU-`P1!s4%PMP5!xC&j!s:+!x1<!wm$OCRAePAPEPjPNP_PCPfPgPWCQR_P[PYPXCQPUPRPQ!sH$L!sJ$!s>$!s6$]PL!sX'PKPPPOP4M<K!tU$1M<KPIP2P3M<KbIbSbHbRbGbQbPbObVbUbTWKWLWFWEWDWJX]9X`9XYDX\9X_9XXDX[9X^9WWWZWNWMWCo"). Qed.

Lemma Forall_one' : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof.
ltac2:(KReplay.run1 (kr_t_LibStdioCall ()) ["FPX1"] "h01Ah11Hh21Ph31xp;1p;2p;6p200R0g00ojR1p4p710p8g00Xmj12Tg010Kj21TP1j60Tf0R1p-0[f1R2P2P1O1f3R3f2R4P2%23P11134E0W1W3W2X00o"). Qed.

Lemma kimg_cut_sound : ltac2:(zQ "a0!hra!kf!iu7!ji8!hte!h8!ie!jo2!hi0!jo8>1E$7>1M>0@1$4@1$0#k0@1$6@1$4@1$0#8>1k@1$5$8>1a$1>1n$1>0@4$2$3^5^4^3@4$2$3^6^5@3$9^4^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##_\p'0h04__x1h13HKKh23Hinh31Hh44__x2h51Ah61Ph77__arithh84__ffh96__sat3h:!s/%4h;8__varmaph<5__with=4__x3h>1ih?1xh@2E1hA2E2hB3HaphC4__x4hD2a0hE1bi001bhF1dhG1mi011mhH1ni021nhI2n0hJ1BhK2HahL4Hap1hM4Hap2hN2HihO4__x5hP2b1hQ2b2hR1ei031ehS1fhT2hii042hihU1lhV2l1hW2l2hX2loi052lohY2lshZ1yh[1Eh\2H0h]2HKh^3Hhih_4Himgh`1Kha1Mhb1ai061ahc2a1i072a1hd2a2i082a2he1ki091khf2k0hg2n1i0:2n1hh2n2i0;2n2hi1vi0<1vhj1wi0=1wp%0p&0p;1p;4p;3p;5p;2p;6p;7p;8g002`j1JTg003Ej1j!s/$cj1bTg00P5j1n!s/$Wj1OTg00Q7j4fTg010lj4ZTg011Ij33!s/$jR0j5tTg012Nj2mj3rTg013Zj3RTg0141j3_!s/$Sj6~!s/$nj3[Tg0167j2YTg017@j3VTg018Ij2CTg0050j24!s/$Mj20Tg00Vjj2HTg00ITj2dTg00Xmj1g!sJ$jj25Tg019Rj3FTg006eR1j26!s:$oj2lTg0085j21Tg01:Pj2kTg01;0j1^!s/$Nk20:Tg007Yj28!s9$kk209Tg00]=j1hTg00?mj3ITg01<Qk408Tg00=Ok207Tg01=0k20!t?$=Xk30!u2$YMj2NTg00ZIk103!s0$gk102Tg01><j2eTg00[Rj2MTg00^Cj2|!s/$ej2{Tg00_Qj3zTg00`0j4y!s\$_j1QTg01?>j2P!s/$gj3STg01@Pj2cTg01A<j3U!s/$\j1xTg01B:j3wTg00\5j1a!u/$oj4L!x?$Kj2v!sA$Zj3`!sS$]j6uTg01Cbj2WTg01Dkj3TTg01F4j2\Tg01G=j4]Tg01HFj3sTg01IQj3}k400Tg01Jak401Tg00d;j4i!s/$fj7qTg00fRj8p!v<$kj4oTg00enk705Tg00mYR2f1R3f0R43}p=7g00kIR5f3R6f2R7?r3433p=@AR534p=;A3!s-$AP2P7P3P4H00p=:P5!s4'1p=>g00@GR8?I34p=K1C73=U54p=<g00@gR99I84p=Eg00J`!s2%2g00oLR:/84p=?g00B8R;P3g00i\P4Cip=D!s4$g]R<g00h<R=P=g00h\R>P4g00i<Fqp=9P6P<P=P=P>!t^%Gpp==P;!s3%Cop=BP!s}%g6!s}%GP7!sX+3P4K05p=Xg00jCg00BVR<#JR?#JR@#JRA#J#J#JRB#jRC#b%jA#bRA#nRD[%O5REP2f4RFP6P7CfP0p4p710RG!s0%210R0p-0\4RH%O7RI%O6\6RJP1PFP6P4P3CZ9367f5RKP7P4O193KFXFK;37RL[P3!s9%F6XFF=3F3PKPFP3P7CZ93F6[RMf6RNPKP7P6CZ93KF\L!t#$!uo$DtP4n20010!s#$12!s-%0WSWYW6WJW5PM^SJ^YI^6H^J0^5GP4P5P517NKPF1m67g01Ko!uI'%O3R0P1A3734ARF47PFP3O1[^?6RJ[AR643P6!s8&7A3673RM[RLA3F67RO\JA_734!ta:UX6HW5PL^U0^6H!tX&f8RLf7RJ'7!un$4C@XF5PK1;4Nf9RP/7LRQ/AJ1;4PRRf<RSf;RT;:3RU[^?5[1;4Lf:RV=:T3[^?517VP/AL[A_5QJ!vf$4E~A:PL3P5f=RQ/7SPVPPP7C@^1U^2RP7g01LLRRg01MTRUg00lRRWA[734f>RX';fARYf@RZA[6733:fBR[/7YR\A[F67R];>4P\f?R^PXP]C@eW1W2WiWjWD!wh%O31Y34/;S1Y739:^X17Z^R]1Y67R_;>4P]PQPSP_!sa&XIWXDR!s_$2AV734/;XAV6739:YZAVF67R_=>\4P\P^PX!s],fU!s`&!tC'C!tC%C!tC&47Q10QS/46'HP81d84S00146X10XQ/4F'H/K4P814KZ10Z^/4N!s8$fDRUfCR_'7R`P8PEP3%g5Ra9<JNP8PE15JYA<JYaPan!x_'!x^$!sC$0YZRb/5NA<bN!sH45F5!s71'A]BP314F^10^X/4K'HRc#E17_[1CNK;>6WB%2cP11H34#2%27Rc%23Rd'6[Re%24,6d1H73#2Rd[%26/6c\d1l34P3!zM7XQ8XP8Pe^Q8^P8P414NYRN14bJRbP3O3%2N%2b'6P114J[#210[Y/4L#2fFRJfERb'7!ux%P_A<P_!ux:_[RN/5LA<NL!ux7'AP414PU#210bU/4T#2P11434#21137RP[RN114314!uN$e[1176\e1k!uL<Z;X?;RePN^Z;^?;RNP4PSfGRdP7O311dSPePNP4fIRNfHRe'0RcP^P6O311^c%?ZS01%^?Rc%^BRB+0:Rf,8^18Y4114Z'6fNRg209C3RhO1%hARA5ID[^>;fMRifLRj!v4%fJRk,5ZA<Zk!v7:kNRl/5^A<l^!v79Q0118Zf18_4114['6fPRlPhO1=IDA[^>;P1AF6349367A3F63,6ORO[A3674,6MAFF73!#6?%AFK6793KF\O!#66&H08!#4T8XWIXV0X6HX5GPM^WI^V!#4\-QRG/7lRH!xi%UgR0A<Ug!u84RI!u\%giRM/5_S02A<M!y:5RM1AHI1AHMP0P8Q00fOR0,5b!}A%5dG/K4fURMfTRH'7!s{%P3fRRO=<e!st4'A]@P315JlRm#EP11534#E1173[R111341573#ERn[1167\n207!y]<G;XH;S03P1^G;^H;S04P4PePOP3O311eOfVR1/7MRnfSRo,CNRp%?N18ofRq18k4114H'6RkfWS05!w|'S06[^>;RA'6206cBRD11:c%?B11:f[[Rh%?cRrg00L0RsB04cB3UWKRB%?f\s^Kr!sB$n`Rs#gRt%OsRu1N;3S07&03;Rv&02;Rw1e;:Rx1M;<Ry'D,9wRz%h=R=PzC=1|w>R>P4P71d891{47#EdAz;:3CyR:b8b;b<X0;%?4%?3[^0;P4PjPTO2b7b9b:PqPAPDPhPBPrg01N3RA#QRq#QR9,P;1P;q1P;A5S;RA5S;g01NRRq'c=UstRzPu1N;7%x;R{7B3PvPw1M;?R|1e;c=w;CRC!t|$P=Pw1Gy|!s1$1DyC,9wRCC=C=P>P!tq,X4;183fS08187f\P[^0;^4;P4fKS09P1PVPXO4!u,&LP3!u,'P!tV%F?B7{Rc1N;6R}!t]'D!tD$R~1M;@R@,G|,9w5X!t`$%a<,M;R<,G@!tg%G|<,9wR<9Xw~S0:!tn7X=;XC;18431136'611F61876116F'6R~[!u&&^=;^C;P4fXS0;PiPFPgP6PZO6!u4%O2XNkX>;CLCLA:1Mpe3>b@b3W@%2m17Ho,v5RmW@n01!{+%20100P4O1b@bEQ02!|g$100g/5U!|g%0Gl/5J!s2$PEP310OGRG?<d!|`4,AI]AP310l0/5bRb#EQ03Q!{q$GPd!{q%Gd10oORO/CeRG%?O18efRe10Ho/84114N'6RNQ!{`&o'6!wP/AB}7{?B3{!wF%x!v{%PwA`;y|R}!w4+Dx},9w!w':%?71037,161076#?!vv-!z}$MP1PTPSO5!x|&ePo!tR+tPuQ07PvPwPCP=PC!t/2184fQ08!{p%Q09PV!{q+!yj-%Q9,P;=S;A/cq=Ust!yy$K?B6{9Bc!yr$%a?,M;9`;@R@/D|,9w=Xw<!{R&!u[%Q!y\?XO;106F/83/6P10FK,13P!yX2^O!ts$5Q!y\-XO7!y\,N!y\-Ge5>nbAb3WA%2bPmWA!yV6AbECLO5b3W_W^W\PQEubMb3bLb3WMWL!#C'$!#6=/!s/&bBb3WB!sx-001!sx$BbE!#Cv$1C67!#CA&T;XX;!ss%1W!#C<$W!#C<%W67Rm=>]!#DT&m!sZ'G;XRW!sZ%AT!#DT%T!#DT&TF!s]%!#DT'm!t90XRW!#DT'\!t>%\!t>&\67R^!t>-^!s_'I;!#El'!#<1&C]/;Z!#KP&C]9:_[PK!s6%C]R_=>`4P`PYPZ!#E{+h;XdRXg;XcR!sl'O4!vE$900083010610=10<2!s1%2!s9&210921105104201031013!s-%!s9'61024010710:10810!vq&b1W2X`5O4b3O6b3P2PKPFAs673CfeW]XH;Xb;WeWaW[o"). Qed.

Lemma u_lit0 : ltac2:(zQ "70!ih4!hra!kf!jp4!jpb!jo2!hu4>1E$5@3$0$2@2$6@1$1#k0@2$4^1@1$3ZZ").
Proof.
ltac2:(KReplay.run1 (kr_t_LibStdioCall ()) ["FPX1"] "h02Hah11Eh27__arithh34__ffh46__sat0h56__sat1h68__varmaph75__witp;1p;2p;3p;4p;7g002`j10Tg01;0j17Tg01=0j2=Tg0085j24Tg007Yj21Tg01;Nj2LTg01=Xj3>Tg00Xmj1<Tg00PWj1;Tg01A\j1:Tg00ZIj18Tg00Zgj19Tg01><j22Tg00d;j46Tg003Ej1MTg01B:j3KTg00enj7JTg00^Cj2ATg00ITj2?Tg00^ej2@Tg00?mj35Tg00_Qj3BTg00`0j4CTg006ej2DTg01O>j2ETg01PBj1FTg01QIj2GTg004Fj2HTg00dfj7ITf1R0g00g]R1g00h<R2P2g00h\R3f0R4g00i<FIp=3g00jCg00oLR5g00BV#0R6#7R7%06#0#0#0#0R6#7R8'=145711581L78R9,45R:[[1157R;g00L0R<A>780UW01159\<^0;g00n`R;#<%;;g00B8R;#:%8;%9;R<P1P2P2P3P;12;5R2g00i\P2C6,3<P;P2g00g612;7%M6R65K;C6,3<FJ1A<3P4f2R<g00@GR3g00@gR7'?1@4<=537dAB;50CCb3b6b71155/D:P4b2b4b5'E%F5,G4,H6=5;5eW1o"). Qed.

Lemma flat_abs0 : ltac2:(zQ "90!ii8!kf!jq4!jp4!ik0!jo2!itf!hj1!iid>1E$5>3off$1>1n$1>0@2$0Z^2>0@2$0Z^2>0@2$0@2$7^4^3@2$2+2+k0>0@2$8^5@2$2+2+k0@3$6^7@2$4@1$3Z^6^5").
Proof.
ltac2:(KReplay.run1 (kr_t_LibStdioCall ()) ["FPX1"] "h02Hah14__x1h24__x2h31Eh42H0h53Hlth62Hnh73Hnwh87__arithh94__ffh:6__sat1h;6__sat2h<8__varmaph=5__with>1nh?3offh@1zp;2p;1p;3p;4p;6p;7p;8g005Mj22Tg002`j15Tg01;0j1>Tg01;Nj2]Tg007Yj26Tg0085j24Tg006ej21Tg01=0j2FTg01=Xj3ETg00Xmj1DTg00PWj1BTg00YMj2ATg01A\j1\Tg00Ykj4UTg00ZIj1TTg00Zgj1PTg00[Rj2=Tg01><j2<Tg003Ej1LTg01B:j3KTg00d;j4;Tg00]=j1GTg00\Zj3:Tg00^Cj2HTg00ITj2ITg00^ej2JTg00?mj3CTg00_Qj3MTg00`0j4NTg01PBj1OTg01QIj2?Tg004Fj2@Tg01RPj1QTg00OWj6RTg00REj2STg01SYj1[Tg01T`j1ZTg00SMj3YTg00dfj7VTg00enj7WTg00fRj8XTg00oLR0f0R1'6p=0f1R2g00g]R3g00h<R4P4g00h\R5P1g00i<FVp=3g00B8R6P2g00i\P1C;p=7f2R7P3P4P4P5P2P1FWp=9f3R8P3P4P4P5P7P2P1GXp=8g00jC%02R31287g00BVR9#5R:#>R;%5:#5#5#5#5R<#>R=']R>'6f4R?/4>P6P0f6R@,21RA#014A>f5RB#0RC12AB/6>'1'1'1X@61F;=140;%0=140>[[%0;RAg00L0RDAE;=2UW0%0>\D^0Ag00n`RA#D%BAP61A67P2%\6CU%T6%P6RAP61=69R9g00g6RD1<6;%L<R<5K6R;C;,3A%G4R4PA1=6:R:9:69/7;,3AP4PA1<60R=/7:,3AREP4PA17=9,3AP4A:6=9R9,7=,3AP6P9PDP;C;,3AA:69:/7;,3A99AE59A59AC8C8C8C81HA5P1P7g00@GRAg00@gR5'I1J17=CA5dAM602CNb9b<b=X16X26141>1227/6>%08R7120?R2#0142>122B/6>,1C'1'1\7[[[^16^26P1f7f8P8P?PBP@O6b8b:b;%O0R0,?@,@<%Q@ER1S0BR0#[,?@,@<%Z0'2R<#014<>%0?12<?/6>'1'1'1eAY@0?eW5W7X63W4X>6X?6W3o"). Qed.

Lemma split_lit_denot : ltac2:(zQ "d0!p2!hra!kf!ih4!jpb!jqa!jr0!jo2!jr6!hj1!js2!hte!hu4>1E$7>1e$0>1b$0>1k$2>0@3$3@2$6$0$2@1$8^3@4$5$0$2^2^1@3$3@1$b@1$1#k0@2$4^5^4@2$a@1$1#k0@2$9@2$c@1$1#k0@2$4^5^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##{>p'0h01Hh12H0h21bi001bh31ki011kh41zi021zh51ni031nh62opi042oph72e2h81ei051eh92e1h:4e2_1h;4e2_2h<2sxi062sxh=2Hah>7__arithh?4__ffh@6__sat0hA!s/%1hB8__varmaphC5__withD2b1i072b1hE2b2hF2e'hG2e0i082e0hH1ii091ihI2k0hJ2loi0:2lohK1EhL1Gi0;1ai0<2b0i0=3op0i0>1pp%0p&0p;2p;1p;3p;4p;7p;6g01UfR0k209Tg01VFk108Tg00?mj31Tg002`j1YTg003Ej1}Tg01QIj23Tg004Fj2@!sA$cj1WTg01;kj2ATg01WPj2sTg01XBj4oTg005Mj2>!s8$^k107Tg01PBj1cTg00ITj2_Tg01Y?j1v!so$0j1gTg01=0j2uTg0085j2jTg007Yj2[!sJ$Nj2r!sJ$Xj3qTg00Xmj1pTg00PWj1nTg01A\j1mTg00ZIj1l!s/$gj1kTg01><j2fTg00d;j4^Tg01B:k306Tg00enk705Tg00^Ck204!s0$ek20!un$_Qk302Tg00`0k40!vE$6eR1k200Tg01O>j2~Tg00OWj6bTg00HYj6]!uW$`j1RTg01Zgj3!u{$[nj2|Tg01]0j3{!s/$Tj2GTg01^:j2ETg00]_j6z!s8$Zj4yTg01_Cj1aTg01`Mj2`Tg01a<j3x!s/$dj2wTg01bhj3OTg01coj3NTg01e6j3MTg01f=j4UTg01gDj4PTg01hKj4X!s/$kj6\!v5$fj7tTg00lRR2g00B8R3f1R4f0R5CXp=5P3f4R6f3R7f2R8P4P5Ebp=D1A459178p=dP2P3P5g00oLR9CXp=?f5R:1@84/>5,A7716p=4P6P3P7P!sh%\p=iA1345p==P6P2!s?/hA1245p=01345,@8p=C1>45,A8p=FP4g00g]R;g00h<R<P<g00h\R=!tO$i<Ftp=eP2P6!sx+]p=6!tp$4P9CX=185p=9!t[&2P3P8P9CX!tJ';A1395p=<!tc&!sG48P3P9!t&/:P2P3g01iHR>?745P!ux$ZA7>45p=2!s-$,38p=Bg01j4?745p=Ig01j`!s2%Qg01kL!s2%Sg01l8!s2%Vg01ld!s2%Tg01mP!s2%Jg01n<!s2%Hg01nh!s2%Lg01oT!s2%Kg00jC20923R?&088154531g00BV#YR@#Y!s$'RA#}RB13:5RC'@RD%WBREf6RF/341AB5RG31X43PE1ABDPC1sBCCo1>D9RH&07DDDXF2PEPCPBPHCd^F2P2P2P?P5%c9RH/55RC%?4g020@RDP?P8!sD%1585RI%?6RJ%?FRKP!s$$f7RK#?RLPLn0110<000810102101033010=10;107!s1D4010610:103108!s4&1109103%?7RLP!s$2!t?$4000:0!s#6!sL&JPJ!sN$5!tg5410010<!s1&;100!s19!tg?156751?PE13K4PBPB13K:P6E4]0P615:6RJ91?CP?P0!zW$3P5P5n200110>000120105102S00X8?RC15H415F:RLP5Di1=4:!sb+2P5P4!sb91X8?R015H815KFRMP4Dh10HKf8RN,0HPHf9RO,=:f=RP%cFRQ'3RRACBP4f:RS5FBRT51E[X221=6NP3P:PEPR!uF%PHP5E4X33!|U$E1ABFRRPB1>5FCdX43P:A1ERGX431AB:RG,_E1>9:%v:DD1AB9,@B%g@R@%gARA'uS021j9@1[9A1r@ARU,j9RV[[S031[9@RWg00L0RXAq@A4UW=S041[9U\X^=WS05g00n`RW#pS06%nWS07%m3S08%l3S09%k3RWP;P<P<P=P31f39RXg00i\PXC^,eWP3PXg00g61f3@>063BS0:!s@$K05204W=S0;P5P8g00@GR@g00@gRA'_20358=1@AdB02394H01RAb?bBbC1[99000VP5b>b@bA,~9EbPEf<RV%c:RY'3!vg%VHP:E4ePOP5E]W0POP5D6W0P5O1b1!s+%W0X43P5O1g01MTRH%R5RZ=9?JP?PC%R4RJPLP5D;%<!y,$%R8RLPMP4D810LK%R7RM/0N%R6R[%<OR\%RFR],3PR^=1ET[X22%<NPEP^PBPBP^!xG'K%R:R^O1POP5C:!ti;W5P5O1P!~q-PIA7784RI#?A7:67RT#?R_P!s$$A7F:6R_#?R`P`!~z~3A7845R`#?RaP!s$2!#3$@15ONRa51?PD!uK$5!uK$81565A7467Rb#?A77F:#?RcP!s$$A76KF!s5%!uI~3A7578!tD,!s$,!uGAf;Rc/5SRd51?PEf>Re/3b!z:%eVPcE4]0P7!u[$415751Z781Z:6RbP!s$$1ZF:RbPb!uP~315SORb51?!#9j&15:5Rf12:4Rg#?1ZK7RhP!s$$1ZN6RhPh!t]~315VcRh!vM%?Ri/3g!vM%iPPV!vM$815PVRg91?fP?PC15F415ePRf!#7D%PP?P015K815ieRj!#6v$Kif@Rk,0NPOfARl,=:fERm?BcQRQACBm4fBRn5FBRo!#6s+k!#6s%QPBACBmcRQ/>5CdX33PEfDRp/3SRq/|GRr1>QFRs,ABRt91E5X2Eg020lRu%W5Rv%W4RwP1%W8?1451@781@74'=R1[1@841@85'=%W7?184[Rx%W6?178\1A{84!#:9&!|,&2!ym&WEWDW5Px^Ew^Dv^5uP5PB1@BRRR,>QRu,ABRvPt1GBufFRw=CBVRx/>KR1,AB,@BRy,=5X431GBFRz1>x5R{,GB/=y!s;%sRy1GBK,>x!s<$!sQ$>QzR|/EU1GB1R}!sf&EFUR~1E{U/=}!s6$sUR}1EKU,>x/EU!sa%P}1E1U!sX&_3}1>Q~/EUPQPFPUQ02Q03Q04Q05Q06Q07Q08Q09P!#9',Q0:g021J!#9$%EzQ0;P!#89%A13U9g00LL[!#8<&CyDDPy%asDDPz%aFDD1GB|%a|DD1@Bt1`BsDDPR1`BF!s8$v1`BuDDO4b01@Bq=FB:Ru91EreAx>qG1wqGEbABpSY=1EuePl!#8|%l!#8|=12:Z=9?g!za$2FJPf!#8s$PRf!z^$2KLRLPj!#8v%i12NM/0k12O[%<lR[ABmc]R]=1Eo!#8q$kPEP]PBPBP]!#8q&i12S^O1Pl!#8p%!t]95H!t]%O`15lkR`59?!tb%SI15nlRIP5D;P[P?P0A7678,2cR^fCR]/5nRo!tn%^]12VT/0p12P_%<mR_fIRTA7NKF7BiR^ACBT4=FBwRM!|M&%<pRL!#:t4]A7KF:,2eO1Pm!u,&m!u,8;2X:2X6D!#JA$O3AO845R^,2O=9?`P?PCAO784Rj,2SP!u:/O678RJ,2cRZP!u5&Z]AO:67RZ,2V/0pAOF:6Ru,2PAONKFRY9BTiRq=1EM\_X22PEPq!u,$q!u,,OKF:Rq!u/-X0L!u0Jg0221RGAN845R>!u7/N784Rr!u73N678Rv,2cRR!u7'R]AN:67RR!u7&NF:6Rs,2PANNKFRt!u7$|!u7/|!u7$|!u7,NKF:R|!u7MW6!w@+M845Rz!u//M784R`!u/3M678R[,2cRI!u/'I]AM:67RI!u/&MF:6Ry,2PAMNKFRU!u/$T!u//T!u/$T!u/,MKF:RT!w@OG!u0'!#Po&CURL,2c=9?oP?PC!#R4&CUR_,2V15p]RM!}T%]R9P?P0P:!sJ%CURA,2PRW15mpRp!uJ%WmPF!sG%CURW,2e/0wPK!s:%CURX,2ifGR=#<R<fKR;POPNPKPFCURQ7BlR~ACB;4fH5FBR}!|<+wR1PEP~!us$~!us'm!s`%P:CUR~,2kO1P=!|C&=!uw872X5HXJHX<@!ur'O4!u|+PRx!u|7PRo,2VP!ux$P!uu1PR9,2PRMP!uq&M!uq,PRM!uq2PRw,2i!ue+PRO9B;lR;=1E}\<!xL%;!uW$;!uW5PRm!uW-X01!uX:5HXH3XI!uX1!#P\,11021110331!#PF+!s1C41!#?u,5!s4&!#?u%P5O1W01I84=9?bP?PC1I78Pd!yF%SRSP?P01I67R=Ph!vD%=V1I:6/0P1IF:%<eR=1INK,3nR1ACBn4=FBiR;!xi&PEP1!v3$1!v3'V1IKFO1Pe!v$%fPe!v$71Q!t`-Q!t`'P!t]%Q67R1!t]'1V1Q!t]%QF:1Q!tX&=1E;\=!tO:Q!tOGS!tO-S!tO2S!tO2S!tO%SF:1S!tOGS!tOGV!tO-V!tO2V!tO2V!tO%VF:1V!tOGV!tOGT!tO-T!tO2T!tO2T!tO%TF:1T!tOGT!tOGJ!tO-J!tO2J!tO2J!tO%JF:1J!tOGJ!tOGH!tO-H!tO2H!tO2H!tO%HF:1H!tOGH!tOGL!tO-L!tO2L!tO2L!tO%LF:1L!tOGL!tOGK!tO-K!tO2K67RS!tO'SV1K!tO%KF:1K!tO%n!tO/n!tO$n!tO,K!tOFn0110;000:01!s$5!#4l$X72X9!#B'/9?^aP?PCPjPb!u#$\P?P0PJPd!t{%Jc10ZVPu13lYRYACBl4=FBeRu51E\fX22%<VRZPEPY!u&$Y!u&'cPqO1PP!#:C%P!#:C:!t[3>!t[%r!t[0v!t['vc10RVPs13ltRt=1Eu!tQ$PEPt!tL$t!tL,|!tL'X0Z!tMAG!tM-z!tM%`!tM0[!tM'[c10IVPy13lURU!tM/U!tM$U!tM,T!tMXLdP?Q00XG?P_Ph!#9O$cRcP?Q01XG?PAPg!tX%AP10WePX%<iRX13]!#Qr$]4=FBkRk!#9G+Q!tf$Q!tf'PP~O1Pi!tf%=Pi!tf88!#>y6A9?xd!v:$o!tg%Pc!v:$9!t`'9P10MePw13]ORO=1Ek\X!tR%O!tR$O!tR,m!tRE!#=sG0!#=sn4O1bLW0X33X22X82WKo"). Qed.

Lemma split_lit_vars : ltac2:(zQ "a0!p2!ih4!kf!pf!hv3!kg6!he!jqa!jr0!jr6>1n$6>1e$0>1b$0>1k$2>0@3$1@2$8$0$2@1$9^3@4$7$0$2^2^1>0@3$1$3@2$5^5^4$4@3$1$3@2$5^6^4$4").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##``p'0h01Hh12H0h22Hvh31bi001bh42opi012oph52n0h62e2h71ei021eh82e1h94e2_1h:4e2_2h;2sxi032sxh<2e0i042e0h=1ii051ih>2k0h?2loi062loh@1zi071zhA2_HhB1ki081khC1ni091ni0:1ai0;2b0i0<2b1i0=3op0i0>1pp;2p;1p;3p;4p;6g01UfR0j2ZTg01VFj1YTg00?mj39Tg01PBj1STg00ITj2TTg01Y`j1CTg01Zgj36Tg022]j2PTg023dj3WTg006eR1j2UTg01bhj3GTg01coj3HTg01e6j3ATg01f=j4JTg01gDj4KTg01hKj4M!s/$kj6OTg00HYj6XTg00lRR2g00B8R3f1R4f0R5CMp=3g00@GR61P45g00@gR739p=2P2P3P5g00oLR8CMp=:f4R9P3f3R:f2R;P4P5EOp=RA9345p=BP9P2P:P!s?+QA9245p=0P2P9!s?+Xp=4!t%$4P8CM=9;5p=8P9P3P:!s=$;P8CM!si'7A9385p=;!t&&!sG45g01iHR<?645p=1P2P3A6<45P!u$$N!s2$,P;=967p=<A9657p=Vg01j4!sY%@g01j`!s2%?g01kL!s2%Eg01l8!s2%>g01ld!s2%Ig01mP!s2%Lg01n!tI&=g01nh!s2%Dg01oT!s2%Fg01MTR<1Z23R=%Y;134539129:P2P2P=P5%S8R8/35R>%:4g020@R?P=P;!sD%13;5R@%:9RAf6RB#:RCP!s$$f7RC#:RDPDn0110;000810107101093010=10:10<!s1D40103106109104!s4&8105109%:!t1$!s$1!t?$1000:0!s#6!sL&APA!sN$2!tg5110010;!s1&:100!s19!tg?139:59=12C4f8RA/2B]2]0P9f5RD/39RE99=>%S4R>,2AP=P0!yS$3P5P5n200110>000120102107RFX7=RG138;13CBRHP4DR1B;B!sa+2P5P4!sa80X7=RI138:13ACRJP;DQ108Af9RK,08P8f:R8,BBf>RL/24RM[X321BDK1T67RNW0P8P5D4W0P5O1b1!s+%W2W0X@3P5O1%C5RO=8=E%C4RE!uE%G%C;RPPHP4D7%!tt$I%C:RHPJP;D510HA%C9RJ/0K%CDRQ%;8RRP!tG$%;KP9!tB>5<P5O1P!zA-P@A6:;4R@#:A6D9:RM#:RSP!s$$A6BD9RS#:RTPT!zG~9A6;45RT#:RUP!s$2!zMA13KARU59=f<RV/2@P?!uR$5!uR$:13D5A64D9RW#:A6:CB#:RXP!s$$A69AC!s5%!uP~9A659:!tD,!s$,!uNAf;RX,3VRY59=f?RZ/2Wf@RW/2L!{o%!uV$;1395119:R[#:1NBDR\P!s$$1NCBR\P\!uO~913X8R\!}[$L[!#5D&13C5R[11C4R]#:1NK:R^P!s$$1N89R^P^!ta~9f=R^,3LR_59=fAR`/2]fBR]/2W!vS%13ZLRa99=[A<]A>P=PG13K;13`WR>!~q&WP=P!~L&]`R[!~L&]fCRb,0XPVfDRc,BBfHRd/24Re!~L&bfGRf/P^Rg?W79%VgA9677R7'UP112dLP7fIR1/2ZP5fJRg/2WP4XA7W2P4P5O2n20!xz$!#4$$!s#%b2W0Pc!#3B?11CO=8=aA<]AE!uE$1KPP>!#3=$WR>!uB$18HRHP[!#3@%]11XJ/0b11VQ%;cRQP!u9$%;bP9!t>>!#3>$11XT13b]Rb58=fFRT?<V@P=PGA69:;,1^fER@/3cReP4D7PQ!tN%LMRM13T@R@!tR%MT11ZS/0fA6CBD,1W%;dfL/24[X32RS%;fP9W0RMPd!t[::2X92X4?!#?[$O3AG;45RJ,1X=8=bAG:;4RH9<TV!ti$G9:;R[,1^P!td-AGD9:R8,1LRPP!tf&PTAGBD9RP,1Z/0fAGCBDRK,1WPSP!t[Mg0221REAH;45Ra!tb'H:;4RO!tb+H9:;R7!tb3HD9:Rh,1LRi!tb'iTAHBD9Ri!tb&HCBDRj!tbHW4!v>+A;45Rk!tZ'A:;4Rb!tZ+A9:;RX!tZ3AD9:RQ,1LRl!tZ'lTAABD9Rl!tZ&ACBDR@!v>JE!t['!#DZ&CJRM,1^=8=e!#Do&CJRS9<dLP=PGPD!s<%CJRm,1Z13fTRn!{?%TRTP=PIPB!sJ%CJRo,1WRp13dfRf!tz%pdPC!sG%CJRp,1`/01PA!s:%CJRq,1]%;gfN!z4'r%;1!z4$sPg!u?:62X5<X?<X;6!u:'O4!uD+KRt!uD3KRe!uD4KRu,1ZP!u@$P!u=1KRT,1WRnP!u9&n!u9,KRn!u92KR1,1]PrP!t~=5<X=3X>!t~1!#C;=!#C0<!#C;:2!#6}0!t0$2W2W01@:;=8=\1@9:,2!ux$1@D913^VRg!x3%VRs!~|$@BDRrP_!ui%rL1@CB/0Z1@AC12c4\>X32R>%;ZRc!we$rPW!ue91?!tA&?!tA,?D9P!t=$P!t:%?BDR`!t:'`L1?!t:%?ACP>P!t$=E!t$&E!t$,E!t$2E!t$2E!t$%E!t$B>!t$&>!t$,>!t$2>!t$2>!t$%>!t$BI!t$&I!t$,I!t$2I!t$2I!t$%I!t$BL!t$&L!t$,L!t$2L!t$2L!t$%L!t$B=!t$&=!t$,=!t$2=!t$2=!t$%=!t$BD!t$&D!t$,D!t$2D!t$2D!t$%D!t$BF!t$&F!t$,F!t$2FBDRD!t$'DL1F!t$%F!t$A!}_$:000:!#>W&!s#/!|y,X62X8!#;S/8=JU12VHP=PGP[P\!tY$RP=PIP8PY!tU%8V10P^PK%;L12]!#5Y$]%;^!|r$9PL!#5Y<!t:3aU12VO!t:$7!t:0h!t:'hV10i^PjP]P!t$DE!t$-kU12Vb!t$$X!t$0Q!t$'QV10l^P@!t$SM\12LSP=PFX<=Pm!wt-0X<=Po!ws'oL10pZPq!wn?X7!#8e6A8=t\12Le!u5$u!x~/PT!t,'TL10nZP1P>PNX0c!t0<!#7oL1!#7orXB3X32X72WCo"). Qed.

Lemma kindex_some : ltac2:(zQ "e0!hi0!he!ih4!tf!pf!ie!igd!h8!hv3!kh6!kie!kk9!kob!kp5>1p>0$0$4>2kn@1$7$0>1i$1>1j$1>0@3$2@1$5$1@3$c^4^3^2@2$3$1^1@2$9$0\1K$0@2$6@3$2@1$5$0@3$d$0^5@2$a^3^4@2$3$0^1@2$6@3$2$4@1^6^1$8@2$b^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##N&p'0h01Kh11Hh21jh32HPh44__x1h54__x2h61ih72H0h81ni001nh94Hle0h:7__arithh;4__ffh<4__p1h=4__p2h>8__varmaph?5__with@4__x3hA4__x4hB4cstrhC5cstr0hD1ehE2knhF1xhG2H1hH2H2hI3HP'hJ3HlehK2HnhL2IHhM2K'hN1bi011bhO1mhP1phQ4resthR1yhS2z1hT2z2i021op&0p;1p;3p;2p;6p;4p;<p;5p;Bp;7p;8g00PWj1fTg00P5R0j1kTg024Gj3CTg025Kj2:Tg00?mj30j1\!s;$mj27Tg026DR1j23Tg00Xmj1[Tg00]=j1ZTg00HYj6XTg00I5k20>!s0$Tj2BTg01>_R2j14Tg01hkk604Tg006ej21!s}$^j1{Tg00=oj4LTg0278j3G!s/$VR3j2uTg0286j1sTg00OWj6r!s8$[j4dTg0295R4j15Tg01;0j1nTg005Mj2;!sC$Uj28Tg02:2j2m!s/$Uj3lTg02;2l<jTg007YR5j26!s:$Wj4iTg02<>j1h!s/$cj2gTg0085j2PTg00WGj2KTg01?>j2FTg02=Ek10=!s0$ck20<Tg02>Dj3eTg01@Pj2NTg01A<j3ETg00YMj2T!s8$\k10;!s9$kj4RTg00ZIk10!w&$Zgk102Tg00[Rj2OTg002`j1^Tg00\5j1z!vy$<j2a!s8$Zj3]!tF$mj3`Tg00d;j4STg00^Cj2v!s/$ej2tTg00_Qj3xTg00`0j4yTg02?Pj4cTg01B]j5}Tg02@;j5~Tg02A?k500!s0$ak20!wz$B;j2q!s/$Xl<pTg02C=mB0!wJ$?gj3oTg00a@k606!tY$fk707Tg00enk708!s0$Jk709Tg00fRk80:Tf3R6g00kIR7f2R8f1R93Gf0R:30p=Vg00@GR;g00@gR<70:p=2119:,18p=U2017:p=Af5R=f4R>=G76;08119:'1p=<AE79:p=@A0689/1:p=wg00oLR?/q:p=>g00B8R@?09:p==g01MTRAPAP@P@P2P4P4P6g02CcP8P9P:M<pp=QPAP!sI'@P3!sK$4f6R3g02DGP=P>P6!sU%NB05p=Y!sR$1P4P5g02Dn!sH/M<jp=WA0@:?p=HAo@9:p=?P9g00g]R5g00h<R1P1g00h\R2P:J06p=bP@P9g021JP:CSp=IP9P5P1P1P2P:g00i<K07p=9P8!s=+9P:K08p=J!sa%0i\!sa%D!sJ39p=_P6!s:+!tt$L0:p=MAG768=0>!ve%|P;\7%f7R5P7%kARBAC>891:A:RC30%k7RDP>17861:7:RECVRFP3P:O1#2RG1368RH3UX07#A[^2A^6AXE5%[7RI=C69=0BCPB%ZAP0PAp-0RJ!uN$LLRKg00L0n101102000210!s#$XDBg00Li1:A9P:EXPKPDPI176>PEPG13>6E<!t<$00>:b7W1X2AX6AAC=8!t<$f7RG!tl%=UFH!tf/1@>6=C3!tb%GP=O1P;1B;:f8RCP3O1=0;:P;f:RHPC!s4'PBP91:A3RFf;RI%43RK7CCn0!t{&200001:A=RL50BPD1@IHRM17GCPEf=RN!tW%13CG!u'&RO]1]3P9f9RPPGO1RQ#21:A>RR90BLPBP!vG$PAP:P:PG!v<01!v<&PFPLP:J04A0A3=A0AG3PAPCPDf<RL,@N179HPEf?RF!tL'H9!tL&X2AP7PD1@LIR017PPPEf>RS!sN'PPRT!sP$PIPAg01N3RUPDP0P:1:7LPSPLO1#2PTE<X8A1:7IRT=0DTPNPI!x|$013CCRV'1RW1BDTP0PVP6%{CCLCLPDAG7MUPTPWCwe1uCC%sCErCdPGP:EXW1P:O1b7W1W3g00J`90;Q%4=9CHG=0BRP7PDPP%4GRR,73PECVRBPL!zD&Q13R3RR!zD$PD1@HP173GPEPQ13G3!ur&PBPQPRPOPNP9O1#2%4P/3C!v,%SNRC17HIROPEf@RE!v/'IHRR!v/%6%4HRQ,7PRW#4RT17PHRM50ARV%5PR0%5HRXg00BVRY#nRZ';R['8#>R\/;ZR]180X#>R^'=PAP@%\AP4%\@%59%5:'=A0A9:1m9:3lXRAXFAPTP]1;:ZR]XF@RTPWP\189:#>XO@X8@R\PPP01B@0RWPQP[PTPHPX1B@XR4CQR_FYCQPMP^P!sN$PWPHPXP4FYM<j13QP16[0R[PQPTPXO1P_!sK%EWP:CiP[%hIR[%5IRW,6?R0P[P0%5LR0%5NR['8RP,g?1P?P%>PR_/=P'116P?%H_'1'K%5SR_,8[#>P@%5FR[/;Z,8_!s[0Q!s[-Q!s[%E!sM$!s\$g00n`RQ%4URP#4R\#4#4R^#4,F@&0=Y-0<@RM1F@^R^5e@1F@\R\1F@URU'?'?R`'?g01NRRa'N1F@PAe@M\/?!sE$,?^/Na1?^U/Na1N`a%[QRa5EQ!s%%3E%fQRQP@P@1T@>P8&0;@R`CRP91T@6CR&03@RU&02@R^1b^31O@YR\%^YRM#^,O@RP%zY,O@RY1a@ZRb5]@Rc5`@Rd'I,9^5J^1a@?Re,Dd,9^1I\e!s<%5_^%Z1R1P^P@Peg00g6A`@PYRYCS,9^1O@MRM/IY!sj&DYe,9^1b^G!sb%P1P^1DcP,9^P1A]@\bRb/IM,9^CMCMCM1v^2R2P:P81B;<1t:8#2dAx@?9CyR<b;b>b?X4@X5@X@@XA@X<JX=J1;8Z,86R;,=:,1>16;?%H:'1'K18>6R;,P?1=8;'116;?/13'K1;>Z/6=1;6Z/=>[[[^4@^5@^@@^A@^<J^=JP:%H6fARJ#5R3fB#5R;/;Z'8,P?P3P;P6P9P8P>PGO9b:bTbHbSbGbCbBb9CcPVPA%4IRV,7HR;#4R3PD1@FSP:1:7=PJP=!}j%LIE<X8APDPNP;1:7>R;CVPEP>O1#2R>/1RREP6P>PRP8PR16WXPIPW1B@WRR!|8%EW13VH1;WZ/6XRZPVPTPWO1PTPIPWPRCQ!sM'P9CiPZ%hLRL16?0R0PLP0PaPQ!yY$8P9P`CRPUP^1DbM!wf$1D\!w`%P2P!wB016]91698!vT&P:P_P[P6O3b:!uw'!#6D$PC!vI$ED|ePOP:EXb7CdWJWIXKBD}XM7PGPKP=P:O3D~W1W3n01!#92$20001P:P8O2b3bN!#<#&WLXQ5X07P:I00WEWPo"). Qed.

Lemma ridx_lit : ltac2:(zQ "70!he!ih4!kq2!hra!kq8!kqf!js2>1n$0>0@2$2^1Ni0@3$1$0@1$4@2$6@1$3#5@1$5^2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##9nh04__x1h11xh23Hn0h37__arithh44__ffh54__p1h68__varmaph75__with84__x2h94cstrh:2H0h;2Hnh<1nh=1yh>1zh?2z0p;1p;2p;3p;<p;4p;6p;7p;8g01>_j11Tg02EPR0j2GTg002`j16Tg00\5j1qTg003Ej1_Tg0295R1j14Tg01]Tj2W!s`$hR2j1BTg00?mj30j1DTg02B;j29Tg02:2j2L!s/$Uj3pTg00ITj2?Tg02;2l<JTg01;0j1]Tg0085R3j28!sC$Wj4YTg02<>j1XTg007Yj27!s8$cj2VTg006ej25Tg00WGj2FTg01?>j2=!s/$gj3:Tg01@Pj2CTg02=Ej1U!s/$cj2TTg02>Dj3OTg00Xmj1NTg01A<j3>Tg00PWj1MTg00YMj2E!sA$\j1P!s8$kj4QTg00ZIj1R!s/$gj1STg00a@j6oTg00[Rj2KTg00d;j4<Tg01><j2ITg00eJj7mTg00]=j1eTg00^Cj2^!s/$ej2`Tg00_Qj3aTg00`0j4bTg02?Pj4cTg01^:j2\Tg02FHj3dTg00OWj6H!vd$kj2ZTg004Fj2fTg01`Mj2g!sS$kj1h!w]$Xl<i!tg$fj7j!t^$nj7kTg00fRj8lTf0R4#1!s$%p=2g00B8R5g01MTR6P5P5P2f4R2P1f3R7g02H0f2R8f1R9P4M<ip=nP6P5P0P1P3g02H]f5P2P7P8P!sG$Jp=[P9g00g]R3g00h<R0P0g00h\R:P4g00i<Fjp=3P8P3P0P0P:P9P4Fkp=AP5!s`$i\P4C<p=@P7!sI+!t+$Glp=;g01N3R;#1R<#1R=#1R>#1#2!s$/R?,G4P5g00BVR@#6RA#q#_RB%49RC'WRD%B4=068X>5REP5PCPE%BCRE=069g00oLRF/9CRG=05CP6P5%D6P1%D5%44905CA06941L943pX=6X16PEPGP4X1519F4X15PCPC1?5CRGDnP9PCPGM<J1G9?%6A#6!s$$]RE,8CR1!sE%P?PE1?5EE[P4CYR?P1%X8RG%48,7FRH%47RI,VF18FI19FIRJ=05I'517IFA05JF'5'F%42RJ,9FP5p-0RIg00n`RK1=5=R=1=5<1=5;R;5:55:5g01NRR<'C1=5>%U@,T5=O5==:!sI&/C<1C;<%NKR;5>K5>K3>%MKRKP51E58P9%P5CQ%R5R<%S5R=P=!wo+!s0,2EoP51K5@R@g021JR21K5ARAC<,3=R35A=1I5FR>,@A,3=P5P@P2P>!sD$5A=Fm%e0R0P=1@>!sF$0P3C;C;1^=:R:P4P8g00@G!yz$@gRA'?1`48=03AdAa5F9CbRAb4b6b7X05X85W5A0549,58179FA054!vT$17F8R3A0587[[^05^85^5IP4f6#4RI,8FPIP9P8P7O5b3b?b:b9b2Cc1\CEP?P1PGPHP;PK1E59P<!t{$@,3=R>P0P!uI$g00g61I5E!ul%@P0AA=>@C;C;P:P!tp,17F4189E188E,53!tZ$P4PJP9P8O3b3b9b29dCEEH%BD=069e1ZBCRD,fB1gBCEH%h!s=%W;X<6o"). Qed.

Lemma sr_get_nat : ltac2:(zQ "c0!p2!kq2!h8!he!igd!ih4!ksf!hra!jp4!kt6!kqf!js2>2sr@1$2$0>1n$3>0@2$4@2$1N0^1@2$1^1Ni0@3$5$0@2$9^3@2$b@1$7#5@1$a^2@4$6$0^2^3@1$8Z").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##<Kh04__x1h14__p1h23Hn0h37__arithh44__ffh58__varmaph65__with74cstrh81Hh91nh:1xh;1yh<1zh=2Hnh>3Hnzh?1bh@2srp;1p;2p;3p;6p;4p;<p;7p;8g00PWj1OTg02EPR0j26Tg006eR1j22Tg02I?j2@Tg00?mj30Tg00D]j19!sA$\j2ZTg002`j1:Tg00\5j1UTg003Ej1RTg0295R2j15Tg01;kj2ETg004Fj2DTg02J=j3MTg01]Tj2bTg00ITj24!sg$cj1^Tg0085R3j21!sg$0j1[!s^$`j6ITg02;Wj4HTg02<>j1GTg007Yj2ATg00Xmj1YTg00YMj2XTg00ZIj1W!s/$gj1VTg01><j2FTg00[Rj2TTg00d;j4=Tg00a@j6QTg00]=j1P!s/$_j6STg00^Cj2m!s/$ej2lTg00_Qj3kTg00`0j4jTg00HYj6iTg01^:j2gTg02FHj3fTg00OWj6>Tg01`Mj2eTg02KIj3CTg02L6j2aTg01PBj1`!s\$kj1L!sA$Yj47Tg02?Pj4_Tg02M5j2cTg02N@j2d!uE$_j1?!v5$2l<N!uE$fj7]Tg00enj7\Tg00fRj8hTf0R4#?!s$%p=3g00@GR5g00J`R6704p=8g01MTR7g00B8R8P0P2P3g02H]R9g01N3R:g00oLR;f3R<f2R=f1R>P4M<Np=KP7P!sY&P9f5R9f4R3P<P=P!sH'JP>g00g]R2g00h<R0P0g00h\R?P4g00i<F]p=<P=P2P0P0P?P>P4F\p=;P<!s9+!st$Ghp=Bg00lRR@#O16:4%3:#3!s$/RA,64'2P11@>4#8A08=>#9R1[A08>4#91@=>#8[RB1@<=#8\11Z>4P4n20010!s#$12!s-%0X;8X:8PB^;8^:8!ty$BVRB#:R1#U#RRC%5=RD,ECRE'DRFg00LiRG9MC;RH,DCRIP81bCDRJA084I#9X<8RKP8PDPK148IPH%^Ce,DC908;P8P;%53RK=084!sQ$16:<RL16<ARM'2%5<RN,1;RO%:1#:!s$$[R1,1NRP'2RQPLPMPOPP148;RPP<PN148NROCKP<PNPOPAP11481ROEJEIP=CHPQ%G31A;Kp-0RKg00n`RQ#YRM%OQRQ1X8>RL%W8RR%V8RSP81F8;RTg00g6RU1T8BRBC=,<SRVPS!wl+<EQRW5;S%P0RX!s>-8PBg021JPT!sZ$ESCB1mS?R?P4P=g00@gR0,451l4==050dAk8;>CjR0b4b5b6X08W111;4R2/2>A08>;g00LL[[^08^1KP4f6#5RY/11PYP=O3b3b7b2PIP4Eib81gD116:=R:16=ARY'211;DRZ11D1R['2R\P:PYPZP[PPP=PD148DRPCKP=PDPPPAP1POEJROEIP>CHRAP\%G<RP1A;NRZPMPQPLPRPSP8PBPU1F81!v7%U9;SVPXP8PTg00i\P!vO%=;SUCBP?P!uS,1141RB,221A;>11>1R2'2[^08P4%59R9P=O2!uI%9fD1E>A08JI#9ePF1eCDE>O3b8%5>,ECRD=CCH#8ePG1aC;d9MC;9CCD#8P5P6P5P@P4%`;R6P@1ECN#LP3P6C7n!{c'!{b$P@P<!s>%RN50@X?5P7P=P@P4!s<%=0@NX97P@P=P<P6C7,4@%LEPYP[!z$$\PPP!v6-A;SWUPXP!ul3X1K12>BP2!x4+11;9P9!x/,C_,c=E>ACCEHP4E>b>1d=DP@P>P=P6C750@eW=X97W@o"). Qed.

Lemma length_sr_upd : ltac2:(zQ "70!p2!ktf!he!h8!ih4!kq2!ku7>2sr@1$3$0>1n$2>1e$0>0@2$5^2@2$1$0^3@3$4$2@2$1$0@3$6^4^3^2@2$1$0^4").
Proof.
ltac2:(KReplay.run1 (kr_t_LibStdioCall ()) ["FPX1"] "p'0h02Hnh11ni001nh24__x1h31eh43Hn0h57__arithh64__ffh74__p1h88__varmaph95__with:4__x2h;4cstrh<5cstr0h=2srh>1xh?2IHh@5cstr1hA1hhB1thC1yp;1p;2p;3p;<p;4p;6p;5p;7p;8g00PWj1ITg02EPR0j22Tg00Xmj1MTg0295R1j11Tg00?mj39j1DTg02:2j2VTg02:Uj3STg00ITj23Tg02;2l<ATg0085R2j28Tg02;Wj4KTg02<>j1:Tg01A\j1ZTg00YMj2HTg00Ykj4GTg00ZIj1YTg00Zgj1XTg01><j2ETg00\5j1WTg00[Rj2@Tg00d;j4FTg00]=j1UTg00a@j6TTg00^Cj2RTg00^ej2QTg00_Qj3OTg00`0j4PTg02?Pj4CTg01A<j3;Tg01>_R3j15Tg01;0j1dTg005Mj2=Tg00\Zj3LTg002`j1bTg00OWj6aTg02A?j5`Tg02OGj2JTg02Ogj3_Tg007Yj2]Tg00dfj7\Tg00fRj8^Tg02BXl<[Tg00lRR4f0R5'Jp=0f2R6f1R7;_5,J4p=4g01MTR8?975p=6P8g00B8R9P0P1P2g02H]R:f3R;P6P7g01N3R<g00oLR=P5M<Ap=c1]=5p=7P7g00g]R>g00h<R?P?g00h\R@P5g00i<F\p=<P9P7g00g6P5CFp=?P;P>P?P?P@P6P7P5G^p=>P8P9P0P1P2P:f5R:f4R2P;P6P7P5M<Ap=BP8P8P9P9P3P1P1P;g02CcP6P7P5M<[p=N%I4R3P4%06,27A4;67%0;'6[^34^18R0X=3%M4RA#0RB,27A4A67RC/6B%1CRD%1BRE599P8P9%D8P1%D9%17R1%1559916751V753SXC8X>8PCPD139DPBPE139EM<A126<%16RD/8=RCP6PD139D139=CcP5CKPC%:B%7E%:2%12#7A4A:2RB#:%1B#7p-0RBg00n`RC#MRF%ICRCP9%Z9RGP71H97CG%Y9RH%X9RIP91E9=RJg00i\g00BVRK#W,@9RLCF,<I%U?RMPI1?LJ,<IPMPIP>P?P?P@P;ETC>C>1RI@R@P5P6g00@GR?g00@gR>'31Q56=9?>dAO9=7CPR>b6b8b9X29W7%75187=P;[[^29^7BP5f7RBf6R=54A#1=99E%1BP6P2O4b5b@b<b;b4CCW0X34X18A;42;#0,27P8%0:#5RE,25A;4B=RA?47;%0A'6]0P6%02#5,2<138EA;4=:RE?4<6%0E'6eW0%55RE%0=#5'2P8%0BR<f8RA#0#5,6EX18%5<RE,38A4B72P=P7P2127<%1<R=,81P7P11391R?P<P=139=RLEB%57RJ/2E%dKRN,=11==N'8ROPJ1=5NRPX>9RQP1O1PQP7P1P?CNPEPQP=O1PQP<P=PLCNEBP5CKPO%:6%7Df9#0RD#:%1D#7PFPCP91H96P7PGCGPHPI1@9KRH1E9NRG5L9%bK,@9RK=L9G'?,<IPM1?HK,<IC>P@P>b6b8b9X29X:91=7N,8P1876[^29^:9P5f;#0#1%1:P;O3b5b<b;b4CCO3EaA;4ABRA?4J2%0A'6eW0X18P5O1n0110000020011100P5O1W0X34X18X?0XB3XA4P5D`W=o"). Qed.

Lemma nth_sr_upd_same : ltac2:(zQ "90!p2!ktf!h8!he!ih4!kq2!ksf!jp4!ku7>2sr@1$2$0>1n$3>1e$0>0@2$5^2@2$1$0^3@3$4$0@4$6$0^3@3$8^4^3^2@1$7Z^2").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##7zp'0h02Hnh14__x1h21ni001nh31eh43Hn0h57__arithh64__ffh74__p1h88__varmaph95__with:4__x2h;4cstrh<2srh=2IHh>5cstr0h?1hh@1thA1xp;1p;2p;3p;4p;6p;5p;<p;7p;8g00PWj1JTg02EPR0j21Tg02Ogj37Tg01PBj1^Tg02LYj48Tg00?mj33Tg00Xmj1CTg0295R1j12Tg0085R2j25Tg00ITj26Tg02;Wj4BTg02<>j1>Tg007Yj2:Tg00YMj2ITg00ZIj1W!s/$gj1VTg01><j2FTg00[Rj2ETg00d;j4DTg00]=j1TTg00a@j6STg00^Cj2R!s/$ej2QTg00_Qj3OTg00`0j4NTg01A<j39!t$$_R3j14Tg01;0j1MTg005Mj2<!sL$\j1P!ti$kj4KTg00\Zj3HTg002`j1UTg02?Pj4]Tg02A?j5\!vM$Gj2[!ub$2l<G!t{$fj7ZTg00fRj8YTg02BXl<XTg00lRR4f0R5'[p=0g01MTR6g00B8R7P0P1P2g02H]R8f3R9f2R:f1R;g01N3R<g00oLR=P5M<Gp=LP;g00g]R>g00h<R?P?g00h\R@P5g00i<FZp=;P7!sM%6P5CDp==P9P>P?P?P@P:P;P5GYp=?P6P!tK&P8f5R8f4R2P9!sG%!t:$@P6!sJ$7P3P1P1P9g02Cc!sG'Xp=A%J4R1P4%0:,1;P4P:A79:;%^=R3C8=34;[^34^26R0X<1%C4RA#0,1;11:<%2:RB/5=RCP:PB167B167=CLP5CBPC%>9%29,:=p-0RCg00n`RD#CRE%JDRD1I7;%W7RF%V7RGP71F7=RHg00i\g00BVRI,E7RJCD,;G%T?RKPG1=JH,;GPKPG!v%+9ESC?C?1RG@R@P5P:g00@GR?g00@gR>'61Q5:=3?>dAO7=;CNR>b6b8b9X17W71:=515;=P9[[^17^7CP5P4P8A7A82P!uv%2%28RAP;P:O4b5b;b4W0X34X26A9429!v'$P6%08#4,15P4P;f7RCf6R?594?7;9!sn&9]0P:%02#4,1<164:P4P<A94?8?7<:!sK&:eW0%45%0?#4'1P?P;P2%0CR?,1;%2;R<%2?R8'5P;P<167<RHP?P81678RLE@%4;RM%4?RN'1%MIRO,<<1<8O'5RPPM1<5ORQXA7RRP<O1PRP;P<PHCAPNPRP8!s8$?P8PLCAE@!x1$P%>:1:=Bf9#0RB#>%2B,:=PEPDP71I7:P;%P7CKPFPG1F7ORF9H7J%U!x$$I=H7F'=!wv$1=JI,;GC?P@P!wE,X:71<;O,5Q15;:!wF$:7P5f;#0#2PAP9O3b5b>b;b4C]O3P4PMf8=94C?7M!wc+eW0X26P5O1n0110000020011100P5O1!wq'X=0X@1X?4P5D\W<o"). Qed.

Lemma nth_sr_upd_other : ltac2:(zQ "80!p2!he!ih4!ksf!jp4!h8!ij9!ku7>2sr@1$5$0>1n$1>1m$1>1e$0>0@1$6@3$2$1^3^2@3$2$0@4$3$0^3@3$7^5^4^2@1$4Z@4$3$0^3^5@1$4Z").
Proof.
ltac2:(KReplay.run1z (kr_t_LibStdioCall ()) ["FPX1"] "##D^p'0h03Hneh11mh21ni001nh34Hne0h47__arithh51eh64__ffh74__p1h88__varmaph95__with:4__x1h;4__x2h<4cstrh=5cstr0h>2srh?1xh@2IHhA3IHnhB1hhC1thD1yp;1p;3p;2p;4p;6p;5p;<p;7p;8g00PWj1OTg01PBj1`Tg00D]j10Tg00Xmj1UTg00?mj33j1LTg0295R0j18Tg02:2j2s!s/$Uj3lTg00ITj2:Tg02Pnj3@Tg02;Wj4JTg01A\j1aTg00ZIj1_!s/$gj1]Tg01><j2NTg00]=j1\Tg00a@j6[Tg00^Cj2Z!s/$ej2YTg00_Qj3XTg00`0j4W!se$_R1j11Tg02Ogj3=Tg01;0j1tTg005Mj2>Tg02<>j1GTg007Yj2ETg01?>j2VTg02=Ej1r!s/$cj2qTg02>Dj3k!sJ$gj3jTg01@Pj2i!u>$<j3STg00YMj2h!s/$kj4gTg00[Rj2QTg00\Zj3PTg002`j1eTg02?Pj4RTg00OWj6dTg02QWj6cTg02A?j5bTg02LYj4B!vR$2l<TTg00d;j4m!s/$fj7n!v@$_j6oTg00fRj8^Tg02BXl<pTg01MTR2f1R3f0R433#0p=4g00lRR5f2R6P3P4CBp=2P5f5R7f4R8f3R9;=6P3CB=354p=6A3234p=?g01N3R:=324p=AAS534p=5P5P9P!sU-Cg00B8R;?334p=7P2P;P8P0!sK$:g00oLR<P3P:P<P4M<Tp=fP;P3g021JP4Cmp=FP3g00g]R=g00h<R>P>g00h\R?P4g00i<Fnp=HP3P=P>P>P?P4Eop=IP9!s7+!uM$G^p=MP5P:!uZ'9A3!u$$;1:54p=<!th$4P0P3P6P9P8P7f6R@f7RAf8RB!ti$DP2!sL$;P1P0P0P9g02Cc!t-%M<pp=K%O5R0P51463R1P6P8P9P3%`<RCA268CE6[^55^12^22RDX>01?34RE#0P3%U5RF!sX$CA23FCRGE6]0^12RHX22%A4#0RIP2P3157FPCPGCC^0IP3A32::RJ#0RKPKA3;<<RL#0RM%L2RN%L;RO%83RP%84'71s347lEXD2X?2RE1:;<RQPQDf9@JLP4CJRJPMp-0RQg00n`RR#URS%ORRT%a;RU%_;RV%];RW1N;<RX/FX,HW,IW%\>RXPW!w7,E[CM1ZW?R?P4P6g00@GR>g00@gR=':1Y46=3>=dAX;<3CWR=b6b8b9W7!sK$LLRY\LP3[^7QRQP415@F/9C19FCRL';P3O2b4b3W0%14RZ#A#0R[P2%13R\15BFPCA2\FCR]CC^0[P3%1:R^#A#0A2^FC#<W0%1ZR_#A#0%1\?2!s:%X12P4O1n0110000020010100P4O1!sDAP3PFP:P9PCPGE6e!sS$%16R`/44RaP2%18Rb/44P3A=F7A,5C!x+%]0P3%19Rc=32:#0%<LW0%17/4ZP5PG1;4CX55P2%1A/4Z1;G!sW&@RL/4^%<CRdW0%1B/4_Pd!tpAA=F@BRd=23CP7P31?@3R_#0%8@Re/7PRf#0PNPOPEP@Pe1:;eRgP3PP1:;PRhM9D9@_f1?L\Rf#0g00BVR_#tRi,>e1>PiRj'7#0Rk1>4iRlX?;RmPeO1RnPmPPO1Ro'7!t+&LPnPmP@PePgCKP\PoPmP3PPPhCKRgM9D5@fP4CJPk%G6Rk%86,E<Rf%GB%8BRn,E<1V;^%r_,q;1V;:5k;5j;g01NR'i=SRSPTP;1h;6P3PUCgPVPW1Q;_RV1N;iRU5P;%e_,Q;R_=P;U'F!zz%PX1FV_!s2%CMP?P!zK&X:;X;;R=1>3i,7lPY[1736PY[[^:;^;;RYP4%87Rlf:R?#8P9O3b4b=b<b3CRO2EdP\15CdPCP]CCe!wg91!yY/cP7!yY/XAHX22P9P6P4EcX01X55X12X22P21449P815BARHP3P9PCA28HCE6]0P9%A6#0P2P3f9R6/5BRBP:!#3\%BCE6^0IP9PJPMP>PQP41;7?!|`'A=H:9!|x$HC';eX0KA236C#<P\15?6R6P:P7!|m$6CE6eX0[!|DA14Z8!tW$;R[/5?RKPcP@!tW$K!tW$aP7A32\!{c$?A=6`7!tK$6C';eW014cZP?P8P3PA1?83R?#0%88Rc/7PRZ!zq+8Pc1:;cR;!ya%!zm$?Z1?b\RZ#01>ci/7j#0RjPmPcO1Ri/7o!sa&bPiPmP8PcP;!zN&!zD%Z!zD$jPkPf%G@1E<eP=PYP4PlPn!xV24P\f</5[R[PbPA!v:$[C!x1'!x^<W0X2!sD31!sD+!xZ/X@DXC0XB5P4DbW>o"). Qed.

Lemma length_sr_after_call_j : ltac2:(zQ "60!he!h8!p2!ktf!ih4!lib>2sr@1$1$2>4kept@1$1$0>2nv$0@3$4$0@2$3$2@3$5^3^2^1Ni0").
Proof.
ltac2:(KReplay.run1 (kr_t_LibStdioCall ()) ["FPX1"] "h01ih14kepth21nh32nvh42srp;1p;2p;3p;6p;4g00PWj14Tg02R8j2;Tg02OGj22Tg00?mj35Tg00ITj2>Tg02RTj2<Tg00OWj63Tg02S3j1:Tg02SSj37Tg01PBj16Tg02LYj48Tg02Soj29Tg01Y`j1ATg00N3j4@Tg02TFj4?Tg02Tej3=Tg01>_j11Tf0R0#1#1#1#1p=0g00lRR1#4g01MTR2#4P2g01N3R3%03#0#0#0#0#0#0#0R4';R5,22R6A5204X22R7P2P4P71>24P61<43E3P2P1g00@GP1%:0f2R3572P1P0f3g00oL#6C8f1R6/90#An0100000020000X02R7P5C@,21P2P1P7P5C?E3A=360,21=524eX32W1W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* LPS 75d69e00: [ref_stdio_write] carries [m_channel_reader model = true] (after
   fd_lookup), so this statement carries it too, in the same position. The recorded
   replay applied [@ref_stdio_write] at the old arity; it is replaced by this explicit
   proof (text from boost-beast http_request LibStdioCall.v, beast's image constants
   mapped to boost-json's: the same three addresses [stdio_call] itself reads). *)
Theorem stdio_call_sound :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z ->
  (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe2ee8) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0xfbc78 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x12ec38 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hwphi Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hrdr Hh Hlz HKnil HCONT.
  set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
  set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
  set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
  apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
  apply andb_prop in Hcond as [Hf0 Hf232].
  apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
  (* [comment removed for export] *)
  assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
  { unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
    apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
  assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
  assert (R1 : getr R 1 = Z_to_bv 64 ret).
  { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
  assert (R10 : getr R 10 = Z_to_bv 64 f).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    rewrite H10. reflexivity. }
  assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R11 : getr R 11 = s).
  { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R12 : getr R 12 = l).
  { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
  set (sp := edenot E (nth 2 sr (ELit 0))) in *.
  pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
  pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply flat_abs0; lia. }
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0xfbc78 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x12ec38 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0xe2ee8) with (0xe2ee8%bv : word) by (apply bv_eq; reflexivity).
  eapply (ref_stdio_write R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            pending extra K).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst'.
  - lia.
  - lia.
  - constructor.
    + rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rfd. cbn [edenot]. reflexivity.
    + exact Rbufp.
    + exact Rbufsz.
  - split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
  - apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
  - exact Hfdlk.
  - exact Hrdr.
  - exact Hh.
  - exact Hlz.
  - lia.
  - lia.
  - exact Hlenp.
  - exact Hlene.
  - exact H30.
  - exact Dw.
  - exact Ds.
  - exact Hsl.
  - exact Rpend.
  - exact Rextra.
  - apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
  - exact HKnil.
  - (* [comment removed for export] *)
    intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply HCONT.
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [lia|]);
            lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
              first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
            end.
        - unfold SC_KEPT. cbn [In]. lia. }
      apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
        [ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
      assert (HK3 : know_ok RSEGS E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
Qed.

(* [comment removed for export] *)
(* LPS 75d69e00: [ref_stdio_write] carries [m_channel_reader model = true] (after
   fd_lookup), so this statement carries it too, in the same position. The recorded
   replay applied [@ref_stdio_write] at the old arity; it is replaced by this explicit
   proof (text from boost-beast http_request LibStdioCall.v, beast's image constants
   mapped to boost-json's: the same three addresses [stdio_call] itself reads). *)
Theorem stdio_call_sound_post :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (model : Model) (res : stdio_res)
         (pending extra : list byte) (K : TSet),
  let E := Env (vals_ev vals) ebs in
  regs_ok E sr R -> know_ok RSEGS E M kn ->
  stdio_call (length vals) sr kn = Some res ->
  let wb := bv_unsigned (edenot E (sc_wb res)) in
  let wp := bv_unsigned (edenot E (sc_wp res)) in
  let s := edenot E (sc_s res) in
  let l := edenot E (sc_l res) in
  let su := bv_unsigned (edenot E (sc_sp res)) in
  (wb <= wp)%Z ->
  (wp <= 0x800000000000)%Z ->
  (wp - wb = Z.of_nat (length pending))%Z ->
  (bv_unsigned l = Z.of_nat (length extra))%Z ->
  (Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30)%Z ->
  (wp <= su - 112 \/ su <= wb)%Z ->
  (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z ->
  (bv_unsigned s + bv_unsigned l <= 0x800000000000)%Z ->
  rdn RSEGS M (Z_to_bv 64 wb) (length pending) = Some pending ->
  rdn RSEGS M s (length extra) = Some extra ->
  fd_lookup (m_fds model) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  m_channel_reader model = true ->
  m_halted model = None -> m_vm_lazy model = [] ->
  K [] ->
  (forall R' M',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     sw_post M su (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
     realizes RSEGS (mkCfg (mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS)) model) K) ->
  realizes RSEGS (mkCfg (mkst R (Z_to_bv 64 0xe2ee8) M (seg_rom RSEGS)) model)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  intros vals ebs sr kn R M model res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0xfbc78 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x12ec38 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hwphi Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hrdr Hh Hlz HKnil HCONT.
  set (wb := bv_unsigned (edenot E wbe)) in *. set (wp := bv_unsigned (edenot E wpe)) in *.
  set (s := edenot E (nth 11 sr (ELit 0))) in *. set (l := edenot E (nth 12 sr (ELit 0))) in *.
  set (su := bv_unsigned (edenot E (nth 2 sr (ELit 0)))) in *.
  (* [comment removed for export] *)
  apply andb_prop in Hcond as [Hcond Hlen32]. apply andb_prop in Hcond as [Hcond Hkv]. apply andb_prop in Hcond as [Hcond Hsv].
  apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
  apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
  apply andb_prop in Hcond as [Hcond Hcgv]. apply andb_prop in Hcond as [Hcond Hfd12].
  apply andb_prop in Hcond as [Hf0 Hf232].
  apply Z.leb_le in Hf0. apply Z.leb_le in Hf232. apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'.
  apply Z.eqb_eq in Hcgv. apply Nat.eqb_eq in Hlen32.
  (* [comment removed for export] *)
  assert (Hretv : (ret mod 2 = 0 /\ 0 <= ret < two64)%Z).
  { unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool eqn:Hb; [|discriminate]. injection Hret as ->.
    apply andb_prop in Hb as [Hb Hb3]. apply andb_prop in Hb as [Hb1 Hb2].
    apply Z.eqb_eq in Hb1. apply Z.leb_le in Hb2. apply Z.ltb_lt in Hb3. lia. }
  assert (RG : forall n, (0 < n < 32)%nat -> getr R (Z_to_bv 5 (Z.of_nat n)) = edenot E (nth n sr (ELit 0))).
  { intros n Hn. rewrite (HR (Z_to_bv 5 (Z.of_nat n))), sr_get_nat by exact Hn. reflexivity. }
  assert (R1 : getr R 1 = Z_to_bv 64 ret).
  { replace (1%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 1)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    unfold lit_even_ret in Hret. destruct (nth 1 sr (ELit 0)); try discriminate.
    destruct ((z mod 2 =? 0) && (0 <=? z) && (z <? two64))%bool; [|discriminate]. injection Hret as ->. reflexivity. }
  assert (R10 : getr R 10 = Z_to_bv 64 f).
  { replace (10%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 10)) by (apply bv_eq; reflexivity). rewrite RG by lia.
    rewrite H10. reflexivity. }
  assert (R2 : getr R 2 = edenot E (nth 2 sr (ELit 0))).
  { replace (2%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 2)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R11 : getr R 11 = s).
  { replace (11%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 11)) by (apply bv_eq; reflexivity). apply RG. lia. }
  assert (R12 : getr R 12 = l).
  { replace (12%bv : bv 5) with (Z_to_bv 5 (Z.of_nat 12)) by (apply bv_eq; reflexivity). apply RG. lia. }
  set (sp := edenot E (nth 2 sr (ELit 0))) in *.
  pose proof (base_range_sound RSEGS E M kn qb blo bhi HK Hbr) as Hqbr.
  pose proof (split_lit_denot E (nth 2 sr (ELit 0)) qb k0 Hsq) as Hsqd. fold sp in Hsqd.
  assert (Hq : su = (bv_unsigned (edenot E qb) + k0)%Z).
  { subst su. rewrite Hsqd. apply u64_lit. lia. }
  pose proof (u64_range sp) as Hspr2. fold su in Hspr2.
  (* [comment removed for export] *)
  destruct (kindex_some _ _ _ _ Hki) as (KW & Hnth & HKW & _).
  destruct KW as [| | | | | |[cb ck] clen|]; try discriminate. cbn [is_kwr_cov] in HKW.
  apply andb_prop in HKW as [HKW Hc2]. apply andb_prop in HKW as [Hcb Hc1].
  apply expr_eqb_eq in Hcb. subst cb. apply Z.leb_le in Hc1. apply Z.leb_le in Hc2.
  pose proof (kwr_store_ok RSEGS E M kn _ qb ck clen (k0 - 112) 112%nat HK Hnth Hc1 ltac:(cbn; lia)) as Wst.
  assert (Wst' : store_ok RSEGS M (Z_to_bv 64 (su - 112)) 112 = true).
  { unfold adenot, v_addi in Wst. cbn [a_base a_off] in Wst.
    replace (bv_unsigned (edenot E qb) + (k0 - 112))%Z with (su - 112)%Z in Wst by lia. exact Wst. }
  (* [comment removed for export] *)
  assert (FL : forall off n, (0 <= off)%Z -> (0 < n)%Z -> (off + n <= 2 ^ 64)%Z -> flat E (SA (ELit 0) off) n).
  { intros off n A B C. apply flat_abs0; lia. }
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 120) 4 (ELit fd) HK Hfd ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rfd.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 40) 8 wpe HK Hwp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 56) 8 wbe HK Hwb ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rwb.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 88) 8 bufp HK Hbufp ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufp.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) (f + 96) 8 bufsz HK Hbufsz ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rbufsz.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0xfbc78 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x12ec38 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0xe2ee8) with (0xe2ee8%bv : word) by (apply bv_eq; reflexivity).
  eapply (ref_stdio_write R M model su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
            pending extra K).
  - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
  - exact R10.
  - exact R11.
  - exact R12.
  - exact R1.
  - lia.
  - lia.
  - exact Wst'.
  - lia.
  - lia.
  - constructor.
    + rewrite Rwp. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rwb. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
    + rewrite Rfd. cbn [edenot]. reflexivity.
    + exact Rbufp.
    + exact Rbufsz.
  - split; [|exact Rcan]. rewrite Rcg. cbn [edenot]. f_equal. f_equal. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. unfold two64 in Hcgv. rewrite Hcgv. reflexivity.
  - apply orb_prop in Hfd12 as [H|H]; apply Z.eqb_eq in H; subst fd; lia.
  - exact Hfdlk.
  - exact Hrdr.
  - exact Hh.
  - exact Hlz.
  - lia.
  - lia.
  - exact Hlenp.
  - exact Hlene.
  - exact H30.
  - exact Dw.
  - exact Ds.
  - exact Hsl.
  - exact Rpend.
  - exact Rextra.
  - apply ret_ok_even. rewrite u64_lit by (unfold two64 in Hretv; lia). lia.
  - exact HKnil.
  - (* [comment removed for export] *)
    intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply HCONT.
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [lia|]);
            lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
              first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (1%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G1, R1; reflexivity
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                    | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
            end.
        - unfold SC_KEPT. cbn [In]. lia. }
      apply (regs_ok_ext E' (sr_after_call_j sr SC_KEPT (length vals)) _ R');
        [ rewrite length_sr_upd by (rewrite length_sr_after_call_j; lia); reflexivity | | exact HRj ].
      intros i Hi. rewrite length_sr_after_call_j in Hi.
      destruct (Nat.eq_dec i 10) as [->|Hne].
      * rewrite nth_sr_upd_same by (rewrite length_sr_after_call_j; lia).
        unfold sr_after_call_j. rewrite nth_map_seq by lia. cbn [existsb SC_KEPT Nat.eqb orb].
        change (edenot E' (EVar (length vals + 10))) with (vals_ev (vals ++ junk_vals R') (length vals + 10)).
        rewrite vals_ev_app_r. unfold vals_ev, junk_vals. rewrite (nth_map_seq (fun i => getr R' (Z_to_bv 5 (Z.of_nat i)))) by lia.
        replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10.
        apply (edenot_agree (length vals)); [exact Hag|]. apply sr_vars_lt_nth. exact Hsv.
      * rewrite nth_sr_upd_other by lia. reflexivity.
    + (* [comment removed for export] *)
      destruct HPOST as [Pagree Pgrows Pwend Pwpos Pwbase].
      assert (HK' : know_ok RSEGS E' M kn) by (apply env_app_know; [exact Hkv | exact HK]).
      assert (HK0 : know_ok RSEGS E' M (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8)) by (apply kimg_cut_sound, kimg_cut_sound, HK').
      assert (HK3 : know_ok RSEGS E' M'
                (kn_frame (kn_frame (kn_frame (kimg_cut (kimg_cut kn (f + 32) 16) (f + 56) 8) qb (k0 - 112) 112)
                   (ELit 0) (f + 32) 16) (ELit 0) (f + 56) 8)).
      { assert (Eqb : edenot E' qb = edenot E qb).
        { symmetry. apply (edenot_agree (length vals)); [exact Hag|].
          apply (split_lit_vars (length vals) (nth 2 sr (ELit 0)) qb k0 Hsq). apply sr_vars_lt_nth. exact Hsv. }
        apply (know_ok_frame3 E' M M'); [exact HK0 | | apply flat_abs0; lia | apply flat_abs0; lia | | exact Pgrows].
        - unfold flat, estart. cbn [a_base a_off]. rewrite Eqb. lia.
        - intros x N1 N2 N3. apply Pagree.
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. lia.
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; lia|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
    + (* [comment removed for export] *) exact HPOST.
Qed.
End FPX1.
