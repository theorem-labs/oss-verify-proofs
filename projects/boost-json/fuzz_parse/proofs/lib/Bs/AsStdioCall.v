(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the launch's channel reader. *)
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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib SpecConsts SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX LibKnowFrame Hoare.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import LazyRestrict LazySR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import RefExitBase RefStdioDefs AsLazyRun AsStdioWrite.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_AsStdioCall () := KReplay.lz_vm "#%;LC47Corelib7Classes9Morphisms?eq_proper!s,#xy!sR5?Relation!sb'Reflexive!sR-Program6Basics4flip!tD?Mtrans_co_eq_inv_impl_m!sE&K!s`,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!u?#s2bv00C!sI@;bv_unsignedC56Stdlib6ZArith6BinInt1Z3leb!sC=ad!s`?tb!v?,4Init9Datatypes4andbI!sD15Logic3and!u0#!sA7iff!t=<2le!sB>tC4!sB&4Bool!s'$=!tR#_true_!t##!x:>Ir!x~'_!s0,!yb:!s\,F!sR0!z=>>!sY+_Prop@and!t`#!yC+!uN<6leb_le!tS?:respectful!sM?NR!tz,artial_app!tPGtb_ltK!x8<1!x887!uY$ndc89OSSVerify6Proofs:boost_json:fuzz!t^#se3lib2Bs;AsStdioCall3inrC13~~~!y^82eq00I!z><bool00K!sFA1!#31D>!wo#T!~I#!}k$I!}i=Z!t=/!~T=3!tBE=!tB#!#4Q6!sV:?Equivalence_PER!|k9not!sqE8symmetr!{+Fnot!{+1!z=?!#6'$sym_co!#6+4!y=_8inr_!{i#!yB%!ur86!#7I#d!sB89False!sE#K!y};!y=F?!v$#e!wM,!z7B2!xsJS!wT%ic!{i84True!{k4!sB%5!uM$!{h4!s_/1C4ELinuxProcessSemantics?!s<22Fs2Fs!u%,5Lists7!s+#Def3mapC7!x/N8SymDrive;nth_map_seq!x+>8!x+%_r!~L<6op!vX#!~n?list00C!z#O=SymExec2Sound4SX2S7know_ok!t|%K8!ulR!st$3SX25saddr01!ul&!tdb4flat!sqi6estar!ss'!xDO7StoreOk9mem_grows!xA8!wY,3or!#>`82or00!~q_9!~q#f!{f#!wn&!y+A1K!#>z&9micromega6VarMap1t02!sD@3I!sD?0!sD6=RingM!s4'7Formula!}_#!sQ47Env!sT#5PExpr!#D^>!#9U+1!snE3K!|VC!uj75Tauto8G!u#'7C!sJ<B!sJ&!sH6:Z!uq+=Z!sT$CheckerC!vf<4f!#7a#!sq?C!sq0_s!{5#!#D?5:or!#D>%r!uWF3!{eP<LibKnowFrame8kn_f!s/#!|VV!so0=!#3v%!st/K!yjL1!u\F4!sJF6!sJF5!sJF8!u1D3Op205!yp<5eKind!#83<unit!|X8!se%4kind!v4#!sf@1!ttI3I!#8L[3env00!#FZ%!sl\6kentry!soe4e!~t#0!zj5!sf96images9AsanUbsan1M?loaded_segments!#I,&!}j?;!#K0$!tx$!#G`>1Z!wx/!#?a06Forall!#5p-!sG91!yi+!sF%4!s+#8flat_mapI!sdB0!sd7?!sC%_!sk'!#:O_kimg_cut!#>O&!t>62In!s=7=!tU'!s,$!#Av75proj1K!z#d1!#A+b!so'2!sok3!sok4!#@:Bapp!#V`6orb!#?O$_!#Wa>!#Tu#gt!{J@2!#Y^<pow!#[/@7Z_to_bv!y67:!y6&!u7#!t0;>pow_pos_nonneg!sN<:!sN#!sJB7compare!#?mD!#7-<3na!#BV8!#7,05Psatz!sOM!#:e6!#4?:2!#DbA!#DD@!#BcE7!#HxO3Lib2Nd:and_elimF!{`l5!sok6!sok7!sok8!so%!#V[_!#7?&!~~&!#Mta9!th%!#PO'!ti_;!~7&one'!#<^1!~]-6Ex!s2#00!#>]\!#Qb%!#?M&!}k@!#T/<:!~v%ison!#_}=!sk$1!}^N1!#VxPAgentLib7u64_lit!z%c!#Aq$!#TuV!zp1edenot!y'e6u!uL#0!t^da_ba!#SD&!sm]5a_off!yNB4prod!#Z8Q!t409split!x<,!#;r@C!#;r%_!#p'-!#Al66eq_sy!#j8<7add_0_r!sGCl!ytc2!zci!#9$%!|>QProp!sn#5v_add!v~G5bv_eq!#@>Abv_wra!#?w<6modulo!sF<?!vy#mod_idemp_r!uKY=!tU&64!sr#!uSG@!yS'!yP,!#dp85Riscv3Sem5alu64!toY7alu!w>,!xoc4!smi5!smi6!smi7!smi!#>i%K!#4S@!#uB9!#lg#alK!xz@5Instr!x|#op01!sRN2!sRN3!sRN4!sRN5!sRN6!sRN7!sRN8!sRN9!sRN:I!sRM0!#xM=N!#\g7!#\#51!t?Hmul!t?#!#3?O6SymRun<!{9#_vars_l!#;Z'!{?:9!$%Z#pro!#qyP9!#qy&X6kindex!|NB!#h#&!|P33Nat3su!#lv3Peano2l!#tn5!s@+!#Zq79nth_erro!#=,+5!#91#8!s^$!t<#!t@&!sF?8sub_diag!#v;72ex01!#:Y<of_nat!#T|<!tJ/!sC&4Znat5Nat2Z7inj!$-+0!#3p-iff!#?z#!y~5;Zify!#y0%5mkrel!sKB7rew!#W[6!tZ-9i!#UhC8max!#|k#!#X&?3!#Rm=3Pol!#eIE!#Tq%4!#S_D4!uoB;!uo&_rev!#T2V9ex!#T1$1!|iB8list_!#h~4!y\,0!y<=max!xTE!#]'-!sK96!sK$2!xS>8!z/#succ!sJ>;!sJ%b_!td#!sM=6!sM#!$3t-!}h0!{y=6to!|A@9mod_small!#JC\4ridx!ww'!vQ48!vQ#Inst@!}t%_!t`%_eq!ueD!~H>eq!$;`<7eqb_neqK!$=;C1!xQB9and!$/o$!#Ec@7Prelude6!#Ho#b!#Fg@4BvWf!$'w;nth!#YK_!wR#!#Nn,!#Q]\sr_ge!#;%B6length!t5aupd!yT<!wT0not!wT'!t^:7!yp#!$3T/!v}2seq!#fH7!u>%!$/S#!#:{>!xK$!se57e!#[P#b!#<p6add!t@?!$1W[?sr_after_call_j!va'!zfG5bv!tF#!w|O!$1#6regs!#_Vg:s!s0#!u?$!sse<lit_even_re!$0;V!#B^+:is_kwr_cov!|]c:base_rang!$$FV!#ES%:s!#EQ2!skWkn!sk1k!w2^9!x#%res!#`7'!#T<Xseg_rom!sjW!wu'9junk_vals!#GW&!$<0H3Run6config!#cyQ<LazyRestrictEsame_but_materialized!wnW!s|#SR8hid_s!$-f+!uDJ5State5m_fds!uC]8r!s/&!tK&5!#EX'!#EP%6IntDef!$Q=&!sE=!#Ha5!#@'+eqb_!#6p@!sI'!#8h49SatDivModCZ!#]F#!#Gu$!s,&!$/XE1!#4``!#;e#!#B:#!{^^4getr!#3bU!#745@!#3h+!$6c%!#6Hc?!#f|'_!#jb,!u`Y9u64!#5V-!#qU_!#Rv$_som!#jfc8!#U##eqb!wLi;!su'_!$G]@!#M;$f!#PXB3inj!#:[Y<kwr_store!#=9'!#3JJ>!#>k#!sE+8!sl'!$0U_!$1B#abs!#pOe!zK[!v;,;!sj%!#r/-!v:Y@word_to_le_bytesC3!#Ir$7tac!sG#<!#cH%_helpK!v_R<Ref!v`$Defs7sw_fi!#Z<#!u$&!yQ&!$/Z+8or!#\_U5Hoare;ret_ok!#Ap#!t/%I!t|cpo!$O>#!woU!#@9%>vals!$^J#agre!#Ao]9env!sj0!}+A8or!#K-$!#9<E2!#I4Y!#Gb#!#I6+!#5kdF!#L1&!#J56!t#_=!t#,!#Nh+!#=I@_de!$Xd26Specif7sum!$a5$!x6W7!y#$ev!xxV!w@+>!#Gk+_nth!yk]<!$#?$!zZ\!#4<+=!uM&!{Q$r!wxe?n!wu+!#Dp,!sx_@!sx-other!#6|`!#PG%_ex!#7m`<!~6$pp_know!u\e>!$3X&!#Awj>!#Aw+!z1#!tpg!$Q&-!$#]&!#@BbmkAlu!#Ci/!#8HR!tq&Write>as_!#O}$w!s5#!sx%K!#L,Pevent02!#yq\!$O,#1!#3-^5kread!v-V!tV05!vz$!xge5sc_wb!snjp!sne4sc_s!smil!uLisp!x\W!#Ke&3rdn!tVif!#cS'!{XO9fd_lookup!|8Q7FdE!$Og$I!#:aO!#Vb$4lzok!#C$W!#Qx+mkst!x0jr!snik!x8f6sc!#au+I!#3GPhapeAlg8re!#[J#s!w#Y!sm'6t_em!$AD'!#EgD:!#5EX9!#5E#_!{m+i!v[^!#aL,!#OTc5two64!x?e7SC_KEPT!x@&!|sY0I!#P4X=machine_s!su#!#FzQ4Scfg=hunspell_scfg!u;W!#<B%!$eXB2!s|RMode!#IDR!{B+4TS!#si+!te4!#y0'7Inj_Z_Z!#9`bf!y]fsc_buf!#<0e8!sp%sz!sq%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04cons03nil06option37Corelib7Numbers7BinNumsj61Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~l34expr04None04bool04andb3h5LinuxProcessSemantics5Riscv5Instrqb5aluopqb5mulop04Somel35two6446Stdlib6ZArith6BinInt1Zud3eqbud3lebud3ltbud6modulol36kentryl35saddrud3addl34KImg03app03orb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsStdioCall4FPX1~~~~~~hk89kimg_cut136Stdlib5Lists4Listhpb8flat_mapj64Npos35stdpp9bitvectorbdefinitionshs12bvhs1bbv_unsigned04true37Corelib4Init5Logichv93andhv92eqhv93iffhk83inrud2leud2lt05falsehv93notl32SA79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~ik56estart69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLibKnowFrame~~~~~~ip48kn_frameik54flatik57know_ok69OSSVerifyaboost_jsonafuzz_parse6images9AsanUbsan1M~~~~~~iv2floaded_segments69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~jjf9mem_growsl33envhk88kimg_cutl34ELitl36edenotud3pow04pair04prodl39split_liths17Z_to_bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~jt1cexpr_vars_lthv92ex37Corelib4Init3Natki03sub37Corelib4Init5Peanokj92le69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9SymDriveX~~~~~~kl36kindexhpb9nth_errorkj92ltl34ridxud6of_nat37Corelib5Lists7ListDefkrc3nthl36sr_get06lengthl36sr_upd69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~kv4fsr_after_call_j" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import SX2. Import SX2S.
Open Scope Z_scope.

#[local] Abbreviation RSEGS := AsanUbsan.M.loaded_segments.

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
          kread RSEGS kn (ELit 0) 0x1b3108 8, kread RSEGS kn (ELit 0) 0x711358 8 with
    | Some (ELit fd), Some wp, Some wb, Some bufp, Some bufsz, Some (ELit cg), Some _ =>
      let sp := nth 2 sr (ELit 0) in
      let '(qb, k0) := split_lit sp in
      let qk := (k0 - 112)%Z in
      match kindex (is_kwr_cov qb qk 112) kn 0, base_range kn qb with
      | Some _, Some (blo, bhi) =>
        if ((0x1b6d20 <=? f) && (f + 232 <=? 0x1b6f00)
            && ((fd =? 1) || (fd =? 2)) && (cg mod two64 =? 0x711358)
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
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##0Hh05lemmah11Bh21Hh32H0h42H1h52loh61nh71xp;1p;2p;3p;4p;6p;;p;5p;9p-1R0g0000R1p4p710p9P0p1000\!s611HR2!s8,P!s2$2!s3/31!s4%g001fR0!sR'g002`j11Tg003Ej1K!s/$cj1@Tg004Fj26Tg0050j2=!s/$Mj24!s/$jj2:Tg006Gj29!s/$eR2j22Tg007@R3j23!s1$Yj27Tg0085j25TP1j2J!s5$Qj2ITg0092j3F!s/$hj4;Tg00:[R1j6ETg00;Mj2C!s/$mj4BTg00<Tl;ATg00=Oj2?!s/$oj4<Tg00>Jj5D!s/$gj3>Tg00?mj3GTP0l9HTg00@Gf0!vn$@g3Gp=0p-0R4P3g00AGf5R5f4R6f3R7f2R8f1R9P0M9Hp=8g00B8R:g00BV#1!s$-KR;#@16;0R<,=8R=1489R>,:<R?'9#0%0=R@%0?RA'2'316;9RB,=7RC1478RD,:BRE!sN%CRC%0ERE'2RFP0177BRG15BDRD'2RBPB1J4BRHE8W01I=?178<R?,3@PF12GERFPCPGP0PEPEP!uF%C;9F43RCPEC;EEPBPBP!sd%C8<15<>R@,3APFPBP4P4^14P3P4P4P3P3CBP2P1PG!s4$CPGC;PEPDP0M;A!sm-?<>12?@R@PB[R?P?PGPDPB16;81467'516;7R;,751456,5;P9P0C<W4X3GP0DDX2@RGPGC<O2O2O2A>890#0/3@eW7X6:W5o"). Qed.

Lemma inr_false : ltac2:(zQ "e0!hra!kf!hu4!pf!ij2!igd!ih4!iha!ij9!ii1!hj1!ii8!iid!hte>2lo$1>1n$1>1x@1$d@1$0#k0@2$7@3$6$3@3$9^3^2^1$4@1$8@2$5@2$b^3@2$2@1$0#k0^1@2$c@2$2@1$0#k0^1@2$a^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##/-p'0h01Hh13Heqh22H0h32H1h41eh51bi001bh65lemmah72loh81nh91xp;1p;3p;2p;6p;7p;4g002`j11Tg003Ej1E!s/$cj1@Tg00>gj38Tg004Fj2<Tg007Yj2;Tg005Mj2:Tg0085j25Tg006ej26!sJ$@R0j24Tg00Ckj3?Tg00?mj30Tg00D]j12Tg00E6j6D!s/$aj3CTg00FSj7BTg00GNj3ATg00HYj6=Tg00I5j27!s/$Tj29Tg00=oj4>Tg00@GR1f0R2g00@gR330p=3g00B8R4g00BV#1!s$-ER5#@f2R6f1R7;82R8#31<52R9,;61:67,59'6'4p-0R9P0g00In9?90f3R:?867R;g00J`R<5011<57R5,;:1::6,55'6R5#2%3;R;#2P!sd%K@P;P5P2ED9C5;FBW6AA672P8P1P1A012<%32#2'4P2A013<R8A0133R6#2R;[P8\;P7!sS$3P1P9P2g00L0R5g00LLR0n0110000020000X41g00LiR:P<P2E=P01702R=b3b1X26P;eX081913P6P7P2O1,78b1X0;C>A01<<R;A01<3R8#2R7[P;\7P!tw%<!tJ%P0P5!t@4P:P3!t;%P!t7&8P7eX0;191<X07C>!sY1b5O2W9X84W7o"). Qed.

(* [comment removed for export] *)
Lemma know_ok_frame3 : ltac2:(zQ "h60!hra!ik0!kf!ioa!hte!hu4!ie!igd!ij9!it3!p2!itf!hj1!ii8!iid!iu7!jic!h8!ih4!jn9!jo6!hi0>1E$h4>1M>0@1$4@1$0#k0@1$6@1$4@1$0#8>2M'>1x@1$4@1$0#k0@1$6@1$4@1$0#8>2kn@1$h1$h5>2b1$a>2o1$2>2n1$2>2b2$a>2o2$2>2n2$2>2b3$a>2o3$2>2n3$2>0@4$f$h0^d^c^a>0@3$b^e@2$1^a^9^8>0@3$b^f@2$1^8^7^6>0@3$b^h0@2$1^6^5^4>0>1x@1$4@1$0#k0>0@1$8@2$7@2$d@2$3^h2@2$1^e^d@2$5@1$0#k0^1@2$e@2$5@1$0#k0^1@2$c@2$3^h2@2$1^e^d^c>0@1$8@2$7@2$d@2$3^h3@2$1^c^b@2$5@1$0#k0^2@2$e@2$5@1$0#k0^2@2$c@2$3^h3@2$1^c^b^a>0@1$8@2$7@2$d@2$3^h4@2$1^a^9@2$5@1$0#k0^3@2$e@2$5@1$0#k0^3@2$c@2$3^h4@2$1^a^9^8@3$h2@1$6@1$4@1$0#8@1^h3^4@1^h4^4>0@2$h3^h1^h0@4$f$h0^h3^h1@4$9@4$9@4$9^h0^f^e^d^c^b^a^9^8^7").
Proof.
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##U{p'0h01xh12Hxh22E3h31bi001bh42E2h51Hh64__x1h74__x2h84__x3h92loh:1nh;7__arithh<6heq_a1h=!s/%2h>!s/%3h?4__ffh@4__p1hA8__varmaphB5__withC1EhD2F1hE2F2hF2F3hG2G1hH2G2hI2G3hJ2HKhK2HghL4HouthM1MhN2M'hO2M1hP2M2hQ2O1hR2O2hS2O3hT2a1hU2a2hV2a3hW2b1hX2b2hY2b3hZ2knh[2n1h\2n2h]2n3h^2o1h_2o2h`2o3p%0p;1p;4p;2p;3p;6p;<p;7p;8p100MEp4p70p100N3p4p7210p!s@$NOp4p710g00OWR0!s3%p8g002`j1>Tg003Ej1U!s/$cj1PTg00P5j1]!s/$Wj1MTg00Q7j4hTg00REj2GTg00SMj3JTg004Fj27Tg00D]j16Tg00TXj2LTg00?mj32Tg00Uej2ETg00>gj30Tg00Vjj23Tg0085j2?Tg005Mj2@Tg007Yj2BTg00WGj2CTg00ITj2;!s8$aj3_Tg00Xmj1^Tg00YMj2N!s/$kj4\Tg00ZIj1[!s/$gj1ZTg00[Rj2HTg00\5j1Y!s/$Zj3RTg00]=j1W!s/$_j6nTg00^Cj2m!s/$ej2lTg00_Qj3kTg00`0j4j!s/$bj1TTP0j6gTg00GNj3fTg00a@j6eTg00HYj6d!s8$dj4QTg00bml<KTg006eR0j2cTg00d;j4S!s/$fj7bTg00eJj7a!s/$nj7`Tg00fRj8iTf2R1f1R2f0R3'G'Lp=5f4R4f3R5'B1@23,?1'cp=4g00@GR6A0512;23p=8g00@gR79263p=:g00J`R8!s4%<A2623p=Og00B8R9/;3p==A2923p=AP9P2g00g6P3CSp=D!s4%]R:g00h<R;P;g00h\R<P3g00i<Fbp=9!s[&i\!s[%FP1P:P;P;P<P2P3Fap=X!s92`p=VP5!s9+1P2P3Gip=IA2123#6p=1g00jCg00BVR=#>R>#>#>R?#!s-$#UR@#PRA%U?#PR?#]RB[PB^0ARCg00kI#Mg00lRRDg00mYREf<RFf;RGf9RHChf=RIf8RJ,GHRKf7RL3Jf>RMf6RN,GLf5RO3Jf?RP1GO4;J5fARQ?5IFRR17@3RSPSPRPGD4#6fBRRf:RT75GRU17@2RVPVPUPH!sC$CRU/LKRK17@1RWPWPKPLD4#6PRP5O1PUP5O152B[[[^0Af@RK/EPA5RMIP9A5UFGP9fDRX?5THP9P6PBA01I3A02T3'3fERYP3O1RZPXP3O1n010!s#$20000X0APC!sY&G3fFR[P3O1PZ!sL61?SO1@OR/BS'CRCA0OK2P61;63RZPNPQP1P3C8P6PJPUP4!s2&BA0JQOR\,32fLR]POO1R^fKR_PO!tY3=2B^]4P2A0LR5R^#:P_P4O1,;BW4%<^A0LK4P6PZ1O\3P6PTPUPL!t4'1382fOR\PJ!t-$NR`PJ!t-82P2A0HRN!t-$`PLO1Ra,;BW2%<^P0A0123R^#<P5PVPVP5P1D4S00#6[RVP1PSPSP1P2D4Rb#!|R%Rc#<Rd[P4PWPWP4P5D4S01#6\dA_123P2n20!tT'1!tU$!vm%X:9X99RdPV^0A^:9^99RVP3PFfGRWPJP4O4PF17@JRePePFPW!x}$dPVP3PIP[PTP5O4PI17@T!y`$IP[!yG&GfSRdfIRffHRg35Rh#=1AMhRheS02PhfTRifMRj;5]Rk#=1AKkRkeS03PkfURlfQRmfPRn35Ro#=1ARoRoeS04Pog00ndRp#^S05%MpRpP91N91P21N95C\Rq%[9Rr%Z9Rs1H9>R>1H9=Rt'D,9s%Y=,H9R=9R9tRu/F>,9s5Xs%W;RvPs!~:'1Ft>,9s1D>u,9s5VsEnCI1ms<RuP3P11;671l31#:dg00oP=k92CjRwb?bAbBX69X79X891?231@31/B2'CP2P1P1P2P5D4g00LL[[^69^79^89P3Pm17@PPXPMO4b;b<b=b>P1P3O4b2b5b4b5!yr&8RxPaPjPL!yj6aeW2n011!s;+1P3O1b2b3W4!s>64b3P5P2O1PgP2!~4$RaeW1X0APa\C^0APgP3O1%W?R?51BA0NQ2A0OM2'3P6!s$$BP3P_P5O1fJRCP5!ta41B?P3P2PHP1P2O!tj10b3P4P2O1Ra=1B?!tG%1EW1RyePy1?SN1@NQ!~@%yA0NP2P6PZPLPK!~<+HPR!~<,P2P`!~2$zPj!s-${!t[1!~`%G[OR|/32PzP!sF252B!}I%JQ5R}#:P6P7!uY&!sR492BzX36PjP4O1R{,;BA0TY4R~/37%T~EgW2%<}P~!#3&$|3P6PIPg!#3&%n!~x$|!x>%28PmPJO1P|!t\54P2A0FWNR|#:P0%:^Q00[R^%:cRc\bQ01\cAf!~8FcP^!~8,^P3PMPfPJP2O4PMPePePMPfD4Q02PhQ03PkQ04Pop-0RoQ05PpPqPrPs1F>t,9sAR9>=R=,Dt!{~%PvPs1D!|;%F=!s;$X!s;$!|X'POEeCICIPuP!|,3W@RwP2P3!y9$1D41?211@15!|=%O!|--^@oRoP3PlPIO1Ru!vY%78R<fVPIO1Pu!v[4P`PU17@IP4PFO6!|`'b4b5W4%<!wC$PxPnPLO1P\!|[5,;B!|A0100!|A'!|q;PO!{3$|92Ba!|V-y^0APOP3O1=1B?A0LK2!|K'A0TY5Ry/33PjP5O1RaP]!|S:!{F'4!uu${!sH5]1P3!sz%HX1R;/37P]P1O1R:P_!s-$s!s|713y!{J'!s|8X36P3P7%TyEdA1Ba?P3b1W1!wF%;8P:P!s}7y!uW'1338P\!}C$8Pz!sP6\PN!v6%!u5'P<!tW9PM!vb$2!tJ%Px!sL:3W1!wc00P2O1b!s<:A1B|!#3}'45R|eP|1?SL1@LK!#3}$SA0JQ!#3}$HPR!#3}'GPX!#3}/nPOO1P8!#3%38!#3V$TU5R8#:PcP^P3PFPY!y@$!#<B$OR@P@PFPYD4fR?5gWRF#=1AIFRFePFA5d]_Rd#=1APdRdePdA5in\Rn#=1AQnRnePnPwPoP3PiPTO1PlPTO152BPCPQPVP4PH!{b-2b5W2%<81;Bu!{'0!{C'2b3P_P2O1PN!#8^&u!{-&u\S^0APN!{-,HR!{-+P3P\P5O1P`!z|:\P4!xU-`P1!s4%PMP5!xC&j!s:+!x1<!wm$OCRAePAPEPjPNP_PCPfPgPWCQR_P[PYPXCQPUPRPQ!sH$L!sJ$!s>$!s6$]PL!sX'PKPPPOP4M<K!tU$1M<KPIP2P3M<KbIbSbHbRbGbQbPbObVbUbTWKWLWFWEWDWJX]9X`9XYDX\9X_9XXDX[9X^9WWWZWNWMWCo"). Qed.

Lemma Forall_one' : forall {A} (P : A -> Prop) x, P x -> Forall P [x].
Proof.
ltac2:(KReplay.run1 (kr_t_AsStdioCall ()) ["FPX1"] "h01Ah11Hh21Ph31xp;1p;2p;6p200R0g00onR1p4p710p8g00Xmj12Tg010Oj21TP1j60Tf0R1p-0[f1R2P2P1O1f3R3f2R4P2%23P11134E0W1W3W2X00o"). Qed.

Lemma kimg_cut_sound : ltac2:(zQ "a0!hra!kf!iu7!jic!hte!h8!ie!joc!jo6!hi0>1E$8>1M>0@1$4@1$0#k0@1$6@1$4@1$0#8>1k@1$5$9>1a$1>1n$1>0@4$2$3^5^4^3@4$2$3^6^5@3$7^4^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##`Ip'0h06__sat4h14__x1h23HKKh33Hinh41Hh54__x2h61Ah71Ph87__arithh94__ffh:!sf%3h;8__varmaph<5__with=4__x3h>1ih?1xh@2E1hA2E2hB3HaphC4__x4hD2a0hE1bi001bhF1dhG1mi011mhH1ni021nhI2n0hJ1BhK2HahL4Hap1hM4Hap2hN2HihO4__x5hP2b1hQ2b2hR1ei031ehS1fhT2hii042hihU1lhV2l1hW2l2hX2loi052lohY2lshZ1yh[1Eh\2H0h]2HKh^3Hhih_4Himgh`1Kha1Mhb1ai061ahc2a1i072a1hd2a2i082a2he1ki091khf2k0hg2n1i0:2n1hh2n2i0;2n2hi1vi0<1vhj1wi0=1wp%0p&0p;1p;4p;3p;5p;2p;6p;7p;8g002`j1KTg003Ej1j!s/$cj1bTg00P5j1n!s/$Wj1OTg00Q7j4fTg0110j4Z!s/$Mj32!s/$nR0j5uTg012Rj2mk300Tg013^j3STg0145j3`!s/$Wj6~Tg0152j3[Tg016;j2XTg017Dj3TTg018Mj2DTg0050j24!s/$Mj20Tg00Vjj2HTg00ITj2\Tg00Xmj1i!sJ$jj25Tg019Vj3FTg006eR1j26Tg01:3j2lTg0085j21!s8$Tj2kTg01;4j1_!s/$Rk20;Tg007Yj28!s9$ok20:Tg00]=j1hTg00?mj3JTg01<Uk409Tg00=Ok20!sV$=4k207!s0$\k304Tg01>@k203Tg00YMj2NTg00ZIk102!s0$gj1}!sL$aj2eTg00[Rj2MTg00^Cj2|!s/$ej2{Tg00_Qj3zTg00`0j4yTg01?Dj1R!s/$cj2PTg01@Lj3WTg01A5j2d!s/$aj3UTg01BAj1x!s/$_j3wTg00\5j1a!u8$oj4LTg010Oj2v!sA$Zj3cTg01CBj6tTg01DGj2^Tg01EPj3QTg01FYj2]Tg01Gbj4YTg01Hkj3sTg01J6j3rk40!w1$KFj4qTg00d;j4g!s/$fj7pTg00fRj8o!v:$kk405Tg00enk706Tg00mYR2f1R3f0R43rp=7g00kIR5f3R6f2R7@003432p=@AS534p=<A2!s-$AP2P7P3P4H01p=:P5!s4%Cqp=?g00@GR8?J34p=I1D73=U54p=;g00@gR99J84p=Eg00J`!s2%3g00oPR:/84p==g00B8R;P3g00i\P4Cgp=C!s4$g]R<g00h<R=P=g00h\R>P4g00i<Fpp=9P6P<P=P=P>!t]%Gop=>P;!tx'5p=BP!s~%g6!s~%GP7!sY+3P4K06p=Vg00jCg00BVR<#KR?#KR@#KRA#K#K#KRB#jRC#b%jA#bRA#nRD[%O5REP2f4RFP6P7CfP0p4p710RG!s0%210R0p-0\4RH%O7RI%O6\6RJP1PFP6P4P3CZ9267f5RKP7P4O192KFXFK;27RL[P3!s9%F6XFF=2F3PKPFP3P7CZ92F6[RMf6RNPKP7P6CZ92KF\L!t#$!up$DuP4n20010!s#$12!s-%0WSWYW7WJW6PM^SJ^YI^7H^J0^6GP4P5P517NKPF1m67g01LT!uI'%O3R0P1A2734ASF47PFP3O1[^?6RJ[AS643P6!s8&7A2673RM[RLA2F67RO\JA`734!ta:UX7HW6PL^U0^7H!tX&f8RLf7RJ'7!un$4C@XF5PK1<4Nf9RP/7LRQ/AJ1<4PRRf<RSf;RT;:3RU[^?5[1<4Lf:RV=:T3[^?517VP/AL[A`5QJ!vf$4E~A:PL3P5f=RQ/7SPVPPP7C@^2U^3RP7g01M1RRg01N9RUg00lRRVA[734f>RW'<fARXf@RYA[6733:fBRZ/7XR[A[F67R\;?4P[f?R]PWP\C@eW2W3WiWjWD!wh%O31X34/<S1X739:]W17Y]R\1X67R^;?4P\PQPSP^!sa&XIVXDR!s_$2AT734/<WAT6739:XYATF67R^=?[4P[P]PW!s],fU!s`&!tC'D!tC%D!tC&47Q10QS/46'HP81\84S00146W10WQ/4F'H/I4P814KY10Y]/4N!s8$fDRUfCR^'7R_P8PEP3%i5R`9;JNP8PE15JXA;JX`P`n!x_'!x^$!sC$0XYRa/5NA;aN!sH45F5!s71'A]BP314F]10]W/4K'HRb#E17^Z1DNK;?6WB%3bP11H34#3%37Rb%33Rc'6[Rd%34,6c1H73#3Rc[%36/6b\c1l34P3!zM7XQ8XP8Pd^Q8^P8P414NXRN14aJRaP3O3%3N%3a'6P114JZ#310ZX/4L#3fFRJfERa'7!ux%P^A;P^!ux:^ZRN/5LA;NL!ux7'AP414PU#310aU/4T#3P11434#31137RP[RN114314!uN$d[1176\d1k!uL<Z;X?;RdPN^Z;^?;RNP4PSfGRcP7O311cSPdPNP4fIRNfHRd'0RbP]P6O311]b%=YS01%_?Rb%_BRB+0;Re,8]18X4114Y'6fNRf20:C3RgO1%hARA5JD[^>;fMRhfLS02!v5%fJRi,5YA;Yi!v8:iNRj/5]A;j]!v89Q0118Ye18^4114Z'6fPRjPgO1=JDA[^>;P1AF6349267A2F63,6ORO[A2674,6MAFF73!#6@%AFK6792KF\O!#67&H09!#4U8XWIXV0X7HX6GPM^WI^V!#4]-QRG/7jRH!xj%UfR0A;Uf!u84RI!u\%fhRM/5^S03A;M!y;5RM1AHI1AHMP0P8Q00fOR0,5a!}B%5cG/I4fURMfTRH'7!s{%P3fRRO=;d!st4'A]@P315JjRk#EP11534#E1173[R111341573#ERl[1167\l208!y^<G;XH;S04P1^G;^H;S05P4PdPOP3O311dOfVR1/7MS06fSRl,DNRm%=N18leRn18i4114H'6RifWRo!w|'S07[^>;RA'6207bBRD11:bRg%=B11:e[Rp[Rq%=bRrg00L0RsB04bB3UWKRB%=e\s^KrRrP3g01NX203:b'\PgeO1RgPpg00ndRs#iRt%OsRu1N;3S08&02;Rv%};Rw1e;:Rx1M;<Ry'C,9wRz%h=R=PzC>1|w>R>P4P71\891{47#EdAz;:3CyR:b9b;b<X1;%=4%=3[^1;P4PhPSO2b8b0b:b0PnPAPDPqPBPrP!t]$1O>RA#RRn#RR9,P;1P;n1P;A5W;RA5W;g01O]Rn'd=UstRzPu1N;7%x;R{7B3PvPw1M;?R|1e;b=w;CRC!u&$P=Pw1Gy|!s1$1Cy!u>$CC>C>P>P!tw,X5;183eS09187e\P[^1;^5;P4Q02PoPTP]O4!u1+LP3!u1/P!tZ%F?B7{Rb1N;6R}!ta'C!tH$R~1M;@R@,G|,9w5V!td$%a<,M;R<,G@!tk%G|<,9wR<9Vw~S0:!tr7X=;XC;18431136'611F61876116F'6R~[!u-&^=;^C;P4fYS0;PfPKP0PFPXO6!u:'O2XNiX>;CLCLA:1Mme3?b@b4W@%3k17Hl,v5RkW@n01!{R%20100P4O1b@bEQ03!}5$100f/5U!}5%0Gj/5J!s2$PEP310OGRG?;c!}-4,AI]AP310j0/5aRa#EQ04Q!|?$GPc!|?%GcQ0610lORO/DdRG%=O18deRd10Hl/84114N'6RNQ!|1&l'6!wY3AB}7{?B3{!wO%x!w+%PwAc;y|R}!w=+Cx},9w!w4:%=71037,161076#=!w#-!{8$1PoPSPQO5!y3+dPl!tX0tPuQ08PvPwPCP=PC!t52184eQ09!|1%Q02PT!|2-!z#2%!{~$=W;A/dn=Ust!z6$K?B6{9Bb!z/$%a?,M;9c;@R@/C|,9w=Vw<!{k&!ug%Q!yq?XO;106F/83/6P10FK,13P!ym2^O;P4fXQ!yp-]O7!yp/N!yp-Ge3?bAb4WA%3aPkWA!yi6AbECLO5b4W_W^W\PQEtbMb4bLb4WMWL!#Ce$!#6v/!s/&bBb4WB!sx-001!sx$BbE!#DX$1D67!#C{&T;XX;!ss%1^!#Cv$^!#Cv%^67Rk=?\!#E6&k!sZ'G;XRV!sZ%AQ!#E6%Q!#E6&QF!s]%!#E6'k!t90XRV!#E6']!t>%]!t>&]67R]!t>-]!s_'I;!#FN'!#<j&CY/<Y!#L2&CY9:^ZPK!s6%CYR^=?_4P_PXPY!#F]+h;XdRXg;XcR!sl'O4!vE$900083010610=10<2!s1%2!s9&210921105104201031013!s-%!s9'61024010710:10810!vq&b2W3X`5O4b4O6b4P2PKPFAs673CfeW]XH;Xb;WeWaW[o"). Qed.

Lemma u_lit0 : ltac2:(zQ "70!ih4!hra!kf!jp8!jpf!jo6!hu4>1E$5@3$0$2@2$6@1$1#k0@2$4^1@1$3ZZ").
Proof.
ltac2:(KReplay.run1 (kr_t_AsStdioCall ()) ["FPX1"] "h02Hah16__sat1h21Eh37__arithh44__ffh56__sat0h68__varmaph75__witp;1p;2p;3p;4p;7g002`j10Tg01;4j18Tg01=4j2?Tg0085j22Tg007Yj21Tg01;Rj2MTg01=\j3CTg01>@j2>Tg00ITj24Tg00Xmj1<Tg00PWj1;Tg01BAj1:Tg00ZIj19Tg00Zgj1NTg01>aj27Tg00d;j45Tg003Ej1LTg01B_j3KTg00enj7BTg00^Cj2@Tg00^ej2ATg00?mj33Tg00_Qj3DTg00`0j4ETg006ej2=Tg01PIj2FTg01QMj1GTg01RTj2HTg004Fj2ITg00dfj7JTf1R0g00g]R1g00h<R2P2g00h\R3f0R4g00i<FJp=6g00jCg00oPR5g00BV#0R6#8R7%06#0#0#0#0R6#8R8'?1257R911581M78R:,25R;[R<[1157R=g00L0R>AC780UW0115:\>^0=P0g01NX1>57'4P9eO1P<g00ndR<#<%;<g00B8R<#:%9<%N<R9P1P2P2P3P<17<5R2g00i\P2C5,69P<P2g00g617<7%L6R65K<C5,69FB1@93P4f2R9g00@GR3g00@gR7'41A49=337dAD<50CEb4b6b71155/=;P4b3b1b5b1'F%G5,H4,I6=3<5eW2o"). Qed.

Lemma flat_abs0 : ltac2:(zQ "90!ii8!kf!jq8!jp8!ik0!jo6!itf!hj1!iid>1E$5>3off$1>1n$1>0@2$0Z^2>0@2$0Z^2>0@2$0@2$7^4^3@2$2+2+k0>0@2$8^5@2$2+2+k0@3$6^7@2$4@1$3Z^6^5").
Proof.
ltac2:(KReplay.run1 (kr_t_AsStdioCall ()) ["FPX1"] "h02Hah16__sat2h24__x1h34__x2h41Eh52H0h63Hlth72Hnh83Hnwh97__arithh:4__ffh;6__sat1h<8__varmaph=5__with>1nh?3offh@1zp;2p;1p;3p;4p;6p;7p;8g005Mj22Tg002`j15Tg01;4j1?Tg01;Rj2^Tg007Yj26Tg0085j23Tg006ej21Tg01=4j2HTg01=\j3FTg01>@j2ETg00ITj2>Tg00Xmj1BTg00PWj1]Tg00YMj2UTg01BAj1TTg00Ykj4QTg00ZIj1PTg00Zgj1NTg00[Rj2=Tg01>aj2<Tg003Ej1JTg01B_j3ITg00d;j4;Tg00]=j1GTg00\Zj3:Tg00^Cj2KTg00^ej2DTg00?mj3LTg00_Qj3MTg00`0j4CTg01QMj1OTg01RTj2@Tg004Fj2ATg01S[j1RTg00OWj6STg00REj2\Tg01Tdj1[Tg01Ukj1ZTg00SMj3VTg00dfj7WTg00enj7XTg00fRj8YTg00oPR0f0R1'6p=0f1R2g00g]R3g00h<R4P4g00h\R5P1g00i<FWp=4g00B8R6P2g00i\P1C;p=7f2R7P3P4P4P5P2P1FXp=9f3R8P3P4P4P5P7P2P1GYp=8g00jC%02R31287g00BVR9#5R:#?R;%5:#5#5#5#5R<#?R='^R>'6f4R?/3>P6P0f6R@,21RA#013A>f5RB#0RC12AB/6>'1'1'1X@61H;=130;RA%0=130>[RD[%0;REg00L0RFAF;=2UW0%0>\F^0EP2g01NX1E0;'>PAeO1PDg00ndRD#B%]DP61U67P2%T6CQ%P6%N6RDP61=69R9g00g6RA1<6;%J<R<5I6R;C;,4D%G4R4PD1=6:R:9:69/7;,4DP4PD1<60RE/7:,4DRFP4PD17E9,4DP4A:6E9R9,7E,4DP6P9PAP;C;,4DA:69:/7;,4D99DF59D59DC8C8C8C81KD5P1P7g00@GRDg00@gR5'>1D17=LD5dAM602CCb:b<b=X26X36131>1227/6>%08R8120?R7#0137>127B/6>,1C'1'1\8[[[^26^36P1f8f9P?PBP@f7O6b9b1b;b1%O0R0,@@,A<%R@ES1\0BR0#[,@@,A<%Z0'2R<#013<>%0?12<?/6>'1'1'1eAV@0?eW6W8X73W5X>6X?6W4o"). Qed.

Lemma split_lit_denot : ltac2:(zQ "d0!p2!hra!kf!ih4!jpf!jqe!jr4!jo6!jra!hj1!js6!hte!hu4>1E$7>1e$0>1b$0>1k$2>0@3$3@2$6$0$2@1$8^3@4$5$0$2^2^1@3$3@1$b@1$1#k0@2$4^5^4@2$a@1$1#k0@2$9@2$c@1$1#k0@2$4^5^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##|%p'0h01Hh12H0h21bi001bh31ki011kh41zi021zh51ni031nh62opi042oph72e2h81ei051eh92e1h:4e2_1h;4e2_2h<2sxi062sxh=2Hah>7__arithh?4__ffh@6__sat1hA!s/%3hB8__varmaphC5__withD2b1i072b1hE2b2hF2e'hG2e0i082e0hH1ii091ihI2k0hJ2loi0:2lohK1EhL1GhM!t'%0hN!s/%2i0;1ai0<2b0i0=3op0i0>1pp%0p&0p;2p;1p;3p;4p;7p;6g01W1R0k20:Tg01WQk109Tg00?mj30Tg002`j1YTg003Ek100Tg01RTj23Tg004Fj2@!sB$cj1XTg01;oj2ATg01X[j2tTg01YMj4pTg005Mj2?!s8$ik108Tg01QMj1bTg00ITj2\Tg01ZJj1w!so$4j1gTg01=4j2vTg0085j2jTg007Yj2[!sJ$Rj2s!sJ$\j3rTg01>@j2qTg00Xmj1oTg00PWj1nTg01BAj1mTg00ZIj1l!s/$gj1k!s\$aj2fTg00d;j4e!sS$_k307Tg00enk706Tg00^Ck205!s0$ek204Tg00_Qk30!v%$`0k402Tg006eR1k201Tg01PIj2~Tg00OWj6aTg00HYj6]!u`$kj1OTg01\2j37Tg01]9j2}Tg01^;j3|!s/$_j2GTg01_Ej2ETg00]_j6{!s8$ej4zTg01`Nj1`Tg01aXj2_Tg01bGj3y!s/$oj2xTg01d3j3MTg01e:j3NTg01fAj3LTg01gHj4JTg01hOj4TTg01iVj4WTg01j6j6^!v5$fj7uTg00lRR2g00B8R3f1R4f0R5CWp=5P3f4R6f3R7f2R8P4P5Eap=C1A459078p=cP2P3P5g00oPR9CWp=>f5R:1@84/?5,A7706p=4P6P3P7P!sh%^p=iA0345p==P6P2!s?/hA0245p=11345,@8p=B1?45,A8p=FP4g00g]R;g00h<R<P<g00h\R=!tO$i<Fup=dP2P6!sx+]p=6!tp$4P9CW=085p=9!t[&2P3P8P9CW!tJ'8A0395p=<!tc&!sG4:P3P9!t&/;P2P3g01jSR>?745P!ux$ZA7>45p=2!s-$,38p=Dg01k??745p=Hg01kk!s2%Ig01lW!s2%Ug01mC!s2%Qg01mo!s2%Vg01n[!s2%Rg01oG!s2%Kg0203!s2%Pg020_!s2%Sg00jC20:23R?&098154530g00BV#YR@#Y!s$'RA$00RB13:5RC'@RD%XBREf6RF/341AB5RG30X43PE1ABDPC1tBCCp1?D9RH&08DDCXF2PEPCPBPHCc^F2P2P2P?P5%b9RH/55RC%>4g021KRDP?P8!sD%1585RI%>6RJ%>FRKP!s$$f7RK#>RLPLn0110<000810102101033010=10;107!s1D4010610:103108!s4&1109103%>7RLP!s$2!t?$4000:0!s#6!sL&JPJ!sN$5!tg5410010<!s1&;100!s19!tg?156750?PE13K4PBPB13K:P6E4]0P615:6RJ90?CP?P0!zX$3P5P5n200110>000120105102S00X8?RC15H415F:RLP5Di1=4:!sb+2P5P4!sb91X8?R015H815KFRMP4Dh11HKf8RN,1HPHf9RO,=:f=RP%bFRQ'3RRABBP4f:RS5FBRT50E[X221=6NP3P:PEPR!uF%PHP5E4X33!|V$E1ABFRRPB1?5FCcX43P:A0ERGX431AB:RG,\E1?9:%w:DC1AB9,@B%g@R@%gARA'vS021j9@RU1[9A1s@ARV,j9RW[RX[S031[9@RYg00L0RZAr@A4UW=S041[9V\Z^=YS05P4g01NX1q9@'\PUeO1S06PXg00ndRU#oS07%nUS08%m3S09%l3S0:%k3RUP;P<P<P=P31f39!t6$i\PYCe,dUP3PYg00g61f3@>073BS0;!s@$K06205U=S0<P5P8g00@GR@g00@gRZ'\20458=0@ZdB03394H02S0=b?bBbC1[99001WP5b>b@bMb@,~9EaPEf<RW%b:RZ'3!w,%WHP:E4ePOP5E]W0POP5D6W0P5O1b1!s+%W!~5$5O1g01N9RH%O5RA=9?JP?PC%O4RJPLP5D8%<!yK$%O8RLPMP4D:11LK%O7RM/1N%O6R[%<OR\%OFR],3PR^=0ET[X22%<NPEP^PBPBP^!xe'K%O:R^O1POP5C;!ti;W5P5O1P!#37,PIA7784RI#>A7:67RT#>R_P!s$$A7F:6R_#>R`P`!#3@~A7845R`#>RaP!s$2!#3F@15ONRa50?PD!uK$5!uK$81565A7467Rb#>A77F:#>RcP!s$$A76KF!s5%!uI~3A7578!tD,!s$,!uGAf;Rc/5SRd50?PEf>Re/3b!z:%eWPcE4]0P7!u[$415751Z781Z:6RbP!s$$1ZF:RbPb!uP~315SORb50?!#:0&15:5Rf12:4Rg#>1ZK7RhP!s$$1ZN6RhPh!t]~315WcRh!vM%?Ri/3g!vM%iPPW!vM$815PWRg90?fP?PC15F415ePRf!#7b%PP?P015K815ieRj!#7<$Kif@Rk,1NPOfARl,=:fERm?DcQRQABBm4fBRn5FBRo!#79+k!#79%QPBABBmcRQ/?5CcX33PEfDRp/3SRq/}GRr1?QFRs,ABRt90E5X2Eg0227Ru%X5Rv%X4RwP1%X8?0451@781@74'=R1[1@841@85'=%X7?084[Rx%X6?078\1A|84!#:W&!|,&2!ym&WEWDW5Px^Ew^Dv^5uP5PB1@BRRR,?QRu,ABRvPt1GBufFRw=BBWRx/?KR1,AB,@BRy,=5X431GBFRz1?x5R{,GB/=y!s;%sRy1GBK,?x!s<$!sQ$?QzR|/EV1GB1R}!sf&EFVR~1E{V/=}!s6$sVR}1EKV,?x/EV!sa%P}1E1V!sX&\3}1?Q~/EVPQPFPVQ02Q03Q04Q05Q06PXQ07Q08Q09Q0:P!#93,Q0;g022U!#90%E{Q0<Q!#8A&A03V9g00LL[P5b>bAbNbACzDCPy%`sDCPz%`FDC1GB|%`|DC1@Bt1_BsDCPR1_BF!s8$v1_BuDCO4b01@Bq=FB:Ru90EreAy>qG1xqGEaADpSZ=0EuePl!#9+%l!#9+=12:A=9?g!zi$2FJPf!#8{$PRf!zf$2KLRLPj!#8~%i12NM/1k12O[%<lR[ADmc]R]=0Eo!#8y$kPEP]PBPBP]!#8y&i12S^O1Pl!#8x%!t]95H!t]%O`15lkR`59?!tb%SI15nlRIP5D8P[P?P0A7678,2cR^fCR]/5nRo!tn%^]12WT/1p12P_%<mR_fIRTA7NKF7DiR^ABBT4=FBwRM!|U&%<pRL!#:|4]A7KF:,2eO1Pm!u,&m!u,8;2X:2X6D!#Jh$O3AM845R^,2O=9?`P?PCAM784Rj,2SP!u:/M678RJ,2cRAP!u5&A]AM:67RA,2W/1pAMF:6Ru,2PAMNKFRZ9DTiRq=0EM\_X22PEPq!u,$q!u,,MKF:Rq!u/-X0L!u0Jg023<RGAN845R>!u7/N784Rr!u73N678Rv,2cRR!u7'R]AN:67RR!u7&NF:6Rs,2PANNKFRt!u7$|!u7/|!u7$|!u7,NKF:R|!u7MW6!w@+L845Rz!u//L784R`!u/3L678R[,2cRI!u/'I]AL:67RI!u/&LF:6Ry,2PALNKFRV!u/$T!u//T!u/$T!u/,LKF:RT!w@OG!u0'!#Q>&CJRL,2c=9?oP?PC!#R[&CJR_,2W15p]RM!}T%]R9P?P0P:!sJ%CJRU,2PRY15mpRp!uJ%YmPF!sG%CJRY,2e/1wPK!s:%CJR=,2ifGR<#<R;fKRXPOPNPKPFCJRQ7DlR~ABBX4fH5FBR}!|<+wR1PEP~!us$~!us'm!s`%P:CJR~,2kO1P<!|C&<!uw872X5HXJHX<@!ur'O4!u|+TRx!u|7TRo,2WP!ux$P!uu1TR9,2PRMP!uq&M!uq,TRM!uq2TRw,2i!ue+TRO9DXlRX=0E}\;!xL%X!uW$X!uW5TRm!uW-X01!uX:5HXH3XI!uX1!#Q&,11021110331!#Pl+!s1C41!#?},5!s4&!#?}%P5O1W01H84=9?bP?PC1H78Pd!yF%SRSP?P01H67R<Ph!vD%<W1H:6/1P1HF:%<eR<1HNK,3nR1ABBn4=FBiRX!xi&PEP1!v3$1!v3'W1HKFO1Pe!v$%fPe!v$71I!t`-I!t`'P!t]%I67R1!t]'1W1I!t]%IF:1I!tX&=0EX\<!tO:I!tOGU!tO-U!tO2U!tO2U!tO%UF:1U!tOGU!tOGQ!tO-Q!tO2Q!tO2Q!tO%QF:1Q!tOGQ!tOGV!tO-V!tO2V!tO2V!tO%VF:1V!tOGV!tOGR!tO-R!tO2R!tO2R!tO%RF:1R!tOGR!tOGK!tO-K!tO2K!tO2K!tO%KF:1K!tOGK!tOGP!tO-P!tO2P!tO2P!tO%PF:1P!tOGP!tOGS!tO-S!tO2S67RS!tO'SW1S!tO%SF:1S!tO%n!tO/n!tO$n!tO,S!tOFn0110;000:01!s$5!#4l$X72X9!#B'/9?^aP?PCPjPb!u#$\P?P0PJPd!t{%Jc11AWPu13lZRZABBl4=FBeRu50E\fX22%<WRAPEPZ!u&$Z!u&'cPqO1PP!#:C%P!#:C:!t[3>!t[%r!t[0v!t['vc11RWPs13ltRt=0Eu!tQ$PEPt!tL$t!tL,|!tL'X0A!tMAG!tM-z!tM%`!tM0[!tM'[c11IWPy13lVRV!tM/V!tM$V!tM,T!tMXLdP?Q00XG?P_Ph!#9O$cRcP?Q01XG?PUPg!tX%UP11YeP=%<iR=13]!#Qz$]4=FBkRk!#9G+Q!tf$Q!tf'PP~O1Pi!tf%<Pi!tf88!#>y6A9?xd!v:$o!tg%Pc!v:$9!t`'9P11MePw13]ORO=0Ek\=!tR%O!tR$O!tR,m!tRE!#=sG0!#=sn4O1bLW0X33X22X82WKo"). Qed.

Lemma split_lit_vars : ltac2:(zQ "a0!p2!ih4!kf!pf!hv3!kga!he!jqe!jr4!jra>1n$6>1e$0>1b$0>1k$2>0@3$1@2$8$0$2@1$9^3@4$7$0$2^2^1>0@3$1$3@2$5^5^4$4@3$1$3@2$5^6^4$4").
Proof.
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##``p'0h01Hh12H0h22Hvh31bi001bh42opi012oph52n0h62e2h71ei021eh82e1h94e2_1h:4e2_2h;2sxi032sxh<2e0i042e0h=1ii051ih>2k0h?2loi062loh@1zi071zhA2_HhB1ki081khC1ni091ni0:1ai0;2b0i0<2b1i0=3op0i0>1pp;2p;1p;3p;4p;6g01W1R0j2ZTg01WQj1YTg00?mj39Tg01QMj1STg00ITj2TTg01Zkj1CTg01\2j36Tg023hj2PTg024oj3WTg006eR1j2UTg01d3j3GTg01e:j3HTg01fAj3ATg01gHj4JTg01hOj4KTg01iVj4MTg01j6j6OTg00HYj6XTg00lRR2g00B8R3f1R4f0R5CMp=3g00@GR61P45g00@gR739p=2P2P3P5g00oPR8CMp=:f4R9P3f3R:f2R;P4P5EOp=RA9345p=BP9P2P:P!s?+QA9245p=0P2P9!s?+Xp=4!t%$4P8CM=9;5p=8P9P3P:!s=$;P8CM!si'7A9385p=;!t&&!sG45g01jSR<?645p=1P2P3A6<45P!u$$N!s2$,P;=967p=<A9657p=Vg01k?!sY%@g01kk!s2%?g01lW!s2%Eg01mC!s2%>g01mo!s2%Ig01n[!s2%Lg01oG!s2%=g0203!s2%Dg020_!s2%Fg01N9R<1Z23R=%Y;134539129:P2P2P=P5%S8R8/35R>%:4g021KR?P=P;!sD%13;5R@%:9RAf6RB#:RCP!s$$f7RC#:RDPDn0110;000810107101093010=10:10<!s1D40103106109104!s4&8105109%:!t1$!s$1!t?$1000:0!s#6!sL&APA!sN$2!tg5110010;!s1&:100!s19!tg?139:59=12C4f8RA/2B]2]0P9f5RD/39RE99=>%S4R>,2AP=P0!yS$3P5P5n200110>000120102107RFX7=RG138;13CBRHP4DR1B;B!sa+2P5P4!sa80X7=RI138:13ACRJP;DQ108Af9RK,08P8f:R8,BBf>RL/24RM[X321BDK1T67RNW0P8P5D4W0P5O1b1!s+%W2W0X@3P5O1%C5RO=8=E%C4RE!uE%G%C;RPPHP4D7%!tt$I%C:RHPJP;D510HA%C9RJ/0K%CDRQ%;8RRP!tG$%;KP9!tB>5<P5O1P!zA-P@A6:;4R@#:A6D9:RM#:RSP!s$$A6BD9RS#:RTPT!zG~9A6;45RT#:RUP!s$2!zMA13KARU59=f<RV/2@P?!uR$5!uR$:13D5A64D9RW#:A6:CB#:RXP!s$$A69AC!s5%!uP~9A659:!tD,!s$,!uNAf;RX,3VRY59=f?RZ/2Wf@RW/2L!{o%!uV$;1395119:R[#:1NBDR\P!s$$1NCBR\P\!uO~913X8R\!}[$L[!#5D&13C5R[11C4R]#:1NK:R^P!s$$1N89R^P^!ta~9f=R^,3LR_59=fAR`/2]fBR]/2W!vS%13ZLRa99=[A<]A>P=PG13K;13`WR>!~q&WP=P!~L&]`R[!~L&]fCRb,0XPVfDRc,BBfHRd/24Re!~L&bfGRf/P^Rg?W79%VgA9677R7'UP112dLP7fIR1/2ZP5fJRg/2WP4XA7W2P4P5O2n20!xz$!#4$$!s#%b2W0Pc!#3B?11CO=8=aA<]AE!uE$1KPP>!#3=$WR>!uB$18HRHP[!#3@%]11XJ/0b11VQ%;cRQP!u9$%;bP9!t>>!#3>$11XT13b]Rb58=fFRT?<V@P=PGA69:;,1^fER@/3cReP4D7PQ!tN%LMRM13T@R@!tR%MT11ZS/0fA6CBD,1W%;dfL/24[X32RS%;fP9W0RMPd!t[::2X92X4?!#?[$O3AG;45RJ,1X=8=bAG:;4RH9<TV!ti$G9:;R[,1^P!td-AGD9:R8,1LRPP!tf&PTAGBD9RP,1Z/0fAGCBDRK,1WPSP!t[Mg023<REAH;45Ra!tb'H:;4RO!tb+H9:;R7!tb3HD9:Rh,1LRi!tb'iTAHBD9Ri!tb&HCBDRj!tbHW4!v>+A;45Rk!tZ'A:;4Rb!tZ+A9:;RX!tZ3AD9:RQ,1LRl!tZ'lTAABD9Rl!tZ&ACBDR@!v>JE!t['!#DZ&CJRM,1^=8=e!#Do&CJRS9<dLP=PGPD!s<%CJRm,1Z13fTRn!{?%TRTP=PIPB!sJ%CJRo,1WRp13dfRf!tz%pdPC!sG%CJRp,1`/01PA!s:%CJRq,1]%;gfN!z4'r%;1!z4$sPg!u?:62X5<X?<X;6!u:'O4!uD+KRt!uD3KRe!uD4KRu,1ZP!u@$P!u=1KRT,1WRnP!u9&n!u9,KRn!u92KR1,1]PrP!t~=5<X=3X>!t~1!#C;=!#C0<!#C;:2!#6}0!t0$2W2W01@:;=8=\1@9:,2!ux$1@D913^VRg!x3%VRs!~|$@BDRrP_!ui%rL1@CB/0Z1@AC12c4\>X32R>%;ZRc!we$rPW!ue91?!tA&?!tA,?D9P!t=$P!t:%?BDR`!t:'`L1?!t:%?ACP>P!t$=E!t$&E!t$,E!t$2E!t$2E!t$%E!t$B>!t$&>!t$,>!t$2>!t$2>!t$%>!t$BI!t$&I!t$,I!t$2I!t$2I!t$%I!t$BL!t$&L!t$,L!t$2L!t$2L!t$%L!t$B=!t$&=!t$,=!t$2=!t$2=!t$%=!t$BD!t$&D!t$,D!t$2D!t$2D!t$%D!t$BF!t$&F!t$,F!t$2FBDRD!t$'DL1F!t$%F!t$A!}_$:000:!#>W&!s#/!|y,X62X8!#;S/8=JU12VHP=PGP[P\!tY$RP=PIP8PY!tU%8V10P^PK%;L12]!#5Y$]%;^!|r$9PL!#5Y<!t:3aU12VO!t:$7!t:0h!t:'hV10i^PjP]P!t$DE!t$-kU12Vb!t$$X!t$0Q!t$'QV10l^P@!t$SM\12LSP=PFX<=Pm!wt-0X<=Po!ws'oL10pZPq!wn?X7!#8e6A8=t\12Le!u5$u!x~/PT!t,'TL10nZP1P>PNX0c!t0<!#7oL1!#7orXB3X32X72WCo"). Qed.

Lemma kindex_some : ltac2:(zQ "e0!hi0!he!ih4!tf!pf!ie!igd!h8!hv3!kha!kj2!kkd!kof!kp9>1p>0$0$4>2kn@1$7$0>1i$1>1j$1>0@3$2@1$5$1@3$c^4^3^2@2$3$1^1@2$9$0\1K$0@2$6@3$2@1$5$0@3$d$0^5@2$a^3^4@2$3$0^1@2$6@3$2$4@1^6^1$8@2$b^4^3").
Proof.
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##N&p'0h01Kh11Hh21jh32HPh44__x1h54__x2h61ih72H0h81ni001nh94Hle0h:7__arithh;4__ffh<4__p1h=4__p2h>8__varmaph?5__with@4__x3hA4__x4hB4cstrhC5cstr0hD1ehE2knhF1xhG2H1hH2H2hI3HP'hJ3HlehK2HnhL2IHhM2K'hN1bi011bhO1mhP1phQ4resthR1yhS2z1hT2z2i021op&0p;1p;3p;2p;6p;4p;<p;5p;Bp;7p;8g00PWj1fTg00P5R0j1kTg025Rj3CTg026Vj2:Tg00?mj30j1\Tg0278j27!s/$OR1j23Tg00Xmj1[Tg00]=j1ZTg00HYj6XTg00I5k20>!s0$Tj2BTg01?DR2j14Tg01j6k604Tg006ej21!s}$ij1{Tg00=oj4LTg028Cj3G!s/$aR3j2uTg029Aj1sTg00OWj6r!s8$fj4dTg02:@R4j15Tg01;4j1nTg005Mj2;!sC$`j28Tg02;=j2m!s/$`j3lTg02<=l<jTg007YR5j26!s:$bj4iTg02=Ij1h!s/$nj2gTg0085j2PTg00WGj2K!uN$cj2FTg02>Pk10=!s0$nk20<Tg02?Oj3eTg01A5j2N!s/$aj3ETg00YMj2TTg01BAk10;!s9$kj4RTg00ZIk10!w&$Zgk102Tg00[Rj2OTg002`j1^Tg00\5j1zTg01>aj2a!s8$Zj3]Tg02@8j3`Tg00d;j4STg00^Cj2v!s/$ej2tTg00_Qj3xTg00`0j4y!s\$[j4cTg01CBj5}Tg02AFj5~Tg02BJk500!s0$lk20!wz$CFj2q!s/$cl<pTg02DHmB0!wJ$@Lj3oTg00a@k606!tY$fk707Tg00enk708!s0$Jk709Tg00fRk80:Tf3R6g00kIR7f2R8f1R93Gf0R:30p=Vg00@GR;g00@gR<70:p=2119:,18p=U2017:p=Af5R=f4R>=G76;08119:'1p=<AE79:p=@A0689/1:p=wg00oPR?/q:p=>g00B8R@?09:p==g01N9RAPAP@P@P2P4P4P6g02DnP8P9P:M<pp=QPAP!sI'@P3!sK$4f6R3g02ERP=P>P6!sU%NB05p=Y!sR$1P4P5g02F9!sH/M<jp=WA0@:?p=HAo@9:p=?P9g00g]R5g00h<R1P1g00h\R2P:J06p=bP@P9g022UP:CSp=IP9P5P1P1P2P:g00i<K07p=9P8!s=+9P:K08p=J!sa%0i\!sa%D!sJ39p=_P6!s:+!tt$L0:p=MAG768=0>!ve%|P;\7%f7R5P7%kARBAC>891:A:RC30%k7RDP>17861:7:RECVRFP3P:O1#2RG1368RH3UX07#A[^2A^6AXE5%[7RI=C69=0BCPB%ZAP0PAp-0RJ!uN$LLRKg00L0n101102000210!s#$XDBg00Li1:A9P:EXPKPDPI176>PEPG13>6E<!t<$00>:b7W1X2AX6AAC=8!t<$f7RG!tl%=UFH!tf/1@>6=C3!tb%GP=O1P;1B;:f8RCP3O1=0;:P;f:RHPC!s4'PBP91:A3RFf;RI%43RK7CCn0!t{&200001:A=RL50BPD1@IHRM17GCPEf=RN!tW%13CG!u'&RO]1]3P9f9RPPGO1RQ#21:A>RR90BLPBP!vG$PAP:P:PG!v<01!v<&PFPLP:J04A0A3=A0AG3PAPCPDf<RL,@N179HPEf?RF!tL'H9!tL&X2AP7PD1@LIR017PPPEf>RS!sN'PPRT!sP$PIPAg01O>RUPDP0P:1:7LPSPLO1#2PTE<X8A1:7IRT=0DTPNPI!x|$013CCRV'1RW1BDTP0PVP6%{CCLCLPDAG7MUPTPWCwe1uCC%sCErCdPGP:EXW1P:O1b7W1W3g00J`90;Q%4=9CHG=0BRP7PDPP%4GRR,73PECVRBPL!zD&Q13R3RR!zD$PD1@HP173GPEPQ13G3!ur&PBPQPRPOPNP9O1#2%4P/3C!v,%SNRC17HIROPEf@RE!v/'IHRR!v/%6%4HRQ,7PRW#4RT17PHRM50ARV%5PR0%5HRXg00BVRY#nRZ';R['8#>R\/;ZR]180X#>R^'=PAP@%\AP4%\@%59%5:'=A0A9:1m9:3lXRAXFAPTP]1;:ZR]XF@RTPWP\189:#>XO@X8@R\PPP01B@0RWPQP[PTPHPX1B@XR4CQR_FYCQPMP^P!sN$PWPHPXP4FYM<j13QP16[0R[PQPTPXO1P_!sK%EWP:CiP[%hIR[%5IRW,6?R0P[P0%5LR0%5NR['8RP,g?1P?P%>PR_/=P'116P?%H_'1'K%5SR_,8[#>P@%5FR[/;Z,8_!s[0Q!s[-Q!s[%E!sM$!s\$g00ndRQ%4URP#4R\#4#4R^#4,F@&0=Y-0<@RM1F@^R^5e@1F@\R\1F@URU'?'?R`'?g01O]Ra'N1F@PAe@M\/?!sE$,?^/Na1?^U/Na1N`a%[QRa5EQ!s%%3E%fQRQP@P@1T@>P8&0;@R`CRP91T@6CR&03@RU&02@R^1b^31O@YR\%^YRM#^,O@RP%zY,O@RY1a@ZRb5]@Rc5`@Rd'I,9^5J^1a@?Re,Dd,9^1I\e!s<%5_^%Z1R1P^P@Peg00g6A`@PYRYCS,9^1O@MRM/IY!sj&DYe,9^1b^G!sb%P1P^1DcP,9^P1A]@\bRb/IM,9^CMCMCM1v^2R2P:P81B;<1t:8#2dAx@?9CyR<b;b>b?X4@X5@X@@XA@X<JX=J1;8Z,86R;,=:,1>16;?%H:'1'K18>6R;,P?1=8;'116;?/13'K1;>Z/6=1;6Z/=>[[[^4@^5@^@@^A@^<J^=JP:%H6fARJ#5R3fB#5R;/;Z'8,P?P3P;P6P9P8P>PGO9b:bTbHbSbGbCbBb9CcPVPA%4IRV,7HR;#4R3PD1@FSP:1:7=PJP=!}j%LIE<X8APDPNP;1:7>R;CVPEP>O1#2R>/1RREP6P>PRP8PR16WXPIPW1B@WRR!|8%EW13VH1;WZ/6XRZPVPTPWO1PTPIPWPRCQ!sM'P9CiPZ%hLRL16?0R0PLP0PaPQ!yY$8P9P`CRPUP^1DbM!wf$1D\!w`%P2P!wB016]91698!vT&P:P_P[P6O3b:!uw'!#6D$PC!vI$ED|ePOP:EXb7CdWJWIXKBD}XM7PGPKP=P:O3D~W1W3n01!#92$20001P:P8O2b3bN!#<#&WLXQ5X07P:I00WEWPo"). Qed.

Lemma ridx_lit : ltac2:(zQ "70!he!ih4!kq6!hra!kqc!kr3!js6>1n$0>0@2$2^1Ni0@3$1$0@1$4@2$6@1$3#5@1$5^2^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##9nh04__x1h11xh23Hn0h37__arithh44__ffh54__p1h68__varmaph75__with84__x2h94cstrh:2H0h;2Hnh<1nh=1yh>1zh?2z0p;1p;2p;3p;<p;4p;6p;7p;8g01?Dj11Tg02F[R0j2GTg002`j16Tg00\5j1qTg003Ej1_Tg02:@R1j14Tg01^_j2WTg02G3R2j1BTg00?mj30j1DTg02CFj29Tg02;=j2L!s/$`j3pTg00ITj2?Tg02<=l<JTg01;4j1]Tg0085R3j28!sC$bj4YTg02=Ij1XTg007Yj27!s8$nj2VTg006ej25Tg00WGj2FTg01?cj2=Tg01@Lj3:Tg01A5j2CTg02>Pj1U!s/$nj2TTg02?Oj3OTg00Xmj1N!sS$aj3>Tg00PWj1MTg00YMj2ETg01BAj1P!s8$kj4QTg00ZIj1R!s/$gj1STg00a@j6oTg00[Rj2KTg00d;j4<Tg01>aj2ITg00eJj7mTg00]=j1eTg00^Cj2^!s/$ej2`Tg00_Qj3aTg00`0j4bTg02@[j4cTg01_Ej2\!w>$Sj3dTg00OWj6H!vd$oj2ZTg004Fj2fTg01aXj2gTg02H6j1h!w]$cl<i!tg$fj7j!t^$nj7kTg00fRj8lTf0R4#1!s$%p=2g00B8R5g01N9R6P5P5P2f4R2P1f3R7g02I;f2R8f1R9P4M<ip=nP6P5P0P1P3g02Ihf5P2P7P8P!sG$Jp=[P9g00g]R3g00h<R0P0g00h\R:P4g00i<Fjp=3P8P3P0P0P:P9P4Fkp=AP5!s`$i\P4C<p=@P7!sI+!t+$Glp=;g01O>R;#1R<#1R=#1R>#1#2!s$/R?,G4P5g00BVR@#6RA#q#_RB%49RC'WRD%B4=068X>5REP5PCPE%BCRE=069g00oPRF/9CRG=05CP6P5%D6P1%D5%44905CA06941L943pX=6X16PEPGP4X1519F4X15PCPC1?5CRGDnP9PCPGM<J1G9?%6A#6!s$$]RE,8CR1!sE%P?PE1?5EE[P4CYR?P1%X8RG%48,7FRH%47RI,VF18FI19FIRJ=05I'517IFA05JF'5'F%42RJ,9FP5p-0RIg00ndRK1=5=R=1=5<1=5;R;5:55:5g01O]R<'C1=5>%U@,T5=O5==:!sI&/C<1C;<%NKR;5>K5>K3>%MKRKP51E58P9%P5CQ%R5R<%S5R=P=!wo+!s0,2EoP51K5@R@g022UR21K5ARAC<,3=R35A=1I5FR>,@A,3=P5P@P2P>!sD$5A=Fm%e0R0P=1@>!sF$0P3C;C;1^=:R:P4P8g00@G!yz$@gRA'?1`48=03AdAa5F9CbRAb4b6b7X05X85W5A0549,58179FA054!vT$17F8R3A0587[[^05^85^5IP4f6#4RI,8FPIP9P8P7O5b3b?b:b9b2Cc1\CEP?P1PGPHP;PK1E59P<!t{$@,3=R>P0P!uI$g00g61I5E!ul%@P0AA=>@C;C;P:P!tp,17F4189E188E,53!tZ$P4PJP9P8O3b3b9b29dCEEH%BD=069e1ZBCRD,fB1gBCEH%h!s=%W;X<6o"). Qed.

Lemma sr_get_nat : ltac2:(zQ "c0!p2!kq6!h8!he!igd!ih4!kt3!hra!jp8!kta!kr3!js6>2sr@1$2$0>1n$3>0@2$4@2$1N0^1@2$1^1Ni0@3$5$0@2$9^3@2$b@1$7#5@1$a^2@4$6$0^2^3@1$8Z").
Proof.
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##<Kh04__x1h14__p1h23Hn0h37__arithh44__ffh58__varmaph65__with74cstrh81Hh91nh:1xh;1yh<1zh=2Hnh>3Hnzh?1bh@2srp;1p;2p;3p;6p;4p;<p;7p;8g00PWj1OTg02F[R0j26Tg006eR1j22Tg02JJj2@Tg00?mj30Tg00D]j19!sA$gj2ZTg002`j1:Tg00\5j1UTg003Ej1RTg02:@R2j15Tg01;oj2ETg004Fj2DTg02KHj3MTg01^_j2bTg00ITj24!sg$cj1^Tg0085R3j21!sg$4j1[!s^$kj6ITg02<bj4HTg02=Ij1GTg007Yj2ATg00Xmj1YTg00YMj2XTg00ZIj1W!s/$gj1VTg01>aj2FTg00[Rj2TTg00d;j4=Tg00a@j6QTg00]=j1P!s/$_j6STg00^Cj2m!s/$ej2lTg00_Qj3kTg00`0j4jTg00HYj6iTg01_Ej2gTg02GSj3fTg00OWj6>Tg01aXj2eTg02LTj3CTg02MAj2aTg01QMj1`Tg02H6j1L!sA$dj47Tg02@[j4_Tg02N@j2cTg02OKj2dTg01?Dj1?!v5$=l<N!uE$fj7]Tg00enj7\Tg00fRj8hTf0R4#?!s$%p=3g00@GR5g00J`R6704p=8g01N9R7g00B8R8P0P2P3g02IhR9g01O>R:g00oPR;f3R<f2R=f1R>P4M<Np=KP7P!sY&P9f5R9f4R3P<P=P!sH'JP>g00g]R2g00h<R0P0g00h\R?P4g00i<F]p=<P=P2P0P0P?P>P4F\p=;P<!s9+!st$Ghp=Bg00lRR@#O16:4%3:#3!s$/RA,64'2P11@>4#8A08=>#9R1[A08>4#91@=>#8[RB1@<=#8\11Z>4P4n20010!s#$12!s-%0X;8X:8PB^;8^:8!ty$BVRB#:R1#U#RRC%5=RD,ECRE'DRFg00LiRG9MC;RH,DCRIP81bCDRJA084I#9X<8RKP8PDPK148IPH%^Ce,DC908;P8P;%53RK=084!sQ$16:<RL16<ARM'2%5<RN,1;RO%:1#:!s$$[R1,1NRP'2RQPLPMPOPP148;RPP<PN148NROCKP<PNPOPAP11481ROEJEIP=CHPQ%G31A;Kp-0RKg00ndRQ#YRM%OQRQ1X8>RL%W8RR%V8RSP81F8;RTg00g6RU1T8BRBC=,<SRVPS!wl+<EQRW5;S%P0RX!s>-8PBg022UPT!sZ$ESCB1mS?R?P4P=g00@gR0,451l4==050dAk8;>CjR0b4b5b6X08W111;4R2/2>A08>;g00LL[[^08^1KP4f6#5RY/11PYP=O3b3b7b2PIP4Eib81gD116:=R:16=ARY'211;DRZ11D1R['2R\P:PYPZP[PPP=PD148DRPCKP=PDPPPAP1POEJROEIP>CHRAP\%G<RP1A;NRZPMPQPLPRPSP8PBPU1F81!v7%U9;SVPXP8PTg00i\P!vO%=;SUCBP?P!uS,1141RB,221A;>11>1R2'2[^08P4%59R9P=O2!uI%9fD1E>A08JI#9ePF1eCDE>O3b8%5>,ECRD=CCH#8ePG1aC;d9MC;9CCD#8P5P6P5P@P4%`;R6P@1ECN#LP3P6C7n!{c'!{b$P@P<!s>%RN50@X?5P7P=P@P4!s<%=0@NX97P@P=P<P6C7,4@%LEPYP[!z$$\PPP!v6-A;SWUPXP!ul3X1K12>BP2!x4+11;9P9!x/,C_,c=E>ACCEHP4E>b>1d=DP@P>P=P6C750@eW=X97W@o"). Qed.

Lemma length_sr_upd : ltac2:(zQ "70!p2!ku3!he!h8!ih4!kq6!kub>2sr@1$3$0>1n$2>1e$0>0@2$5^2@2$1$0^3@3$4$2@2$1$0@3$6^4^3^2@2$1$0^4").
Proof.
ltac2:(KReplay.run1 (kr_t_AsStdioCall ()) ["FPX1"] "p'0h02Hnh11ni001nh24__x1h31eh43Hn0h57__arithh64__ffh74__p1h88__varmaph95__with:4__x2h;4cstrh<5cstr0h=2srh>1xh?2IHh@5cstr1hA1hhB1thC1yp;1p;2p;3p;<p;4p;6p;5p;7p;8g00PWj1ITg02F[R0j22Tg00Xmj1MTg02:@R1j11Tg00?mj39j1DTg02;=j2VTg02;`j3STg00ITj23Tg02<=l<ATg0085R2j28Tg02<bj4KTg02=Ij1:Tg01BAj1ZTg00YMj2HTg00Ykj4GTg00ZIj1YTg00Zgj1XTg01>aj2ETg00\5j1WTg00[Rj2@Tg00d;j4FTg00]=j1UTg00a@j6TTg00^Cj2RTg00^ej2QTg00_Qj3OTg00`0j4PTg02@[j4CTg01Aaj3;Tg01?DR3j15Tg01;4j1dTg005Mj2=Tg00\Zj3LTg002`j1bTg00OWj6aTg02BJj5`Tg02PRj2JTg02Q2j3_Tg007Yj2]Tg00dfj7\Tg00fRj8^Tg02Ccl<[Tg00lRR4f0R5'Jp=0f2R6f1R7;_5,J4p=4g01N9R8?975p=6P8g00B8R9P0P1P2g02IhR:f3R;P6P7g01O>R<g00oPR=P5M<Ap=c1]=5p=7P7g00g]R>g00h<R?P?g00h\R@P5g00i<F\p=<P9P7g00g6P5CFp=?P;P>P?P?P@P6P7P5G^p=>P8P9P0P1P2P:f5R:f4R2P;P6P7P5M<Ap=BP8P8P9P9P3P1P1P;g02DnP6P7P5M<[p=N%I4R3P4%06,27A4;67%0;'6[^34^18R0X=3%M4RA#0RB,27A4A67RC/6B%1CRD%1BRE599P8P9%D8P1%D9%17R1%1559916751V753SXC8X>8PCPD139DPBPE139EM<A126<%16RD/8=RCP6PD139D139=CcP5CKPC%:B%7E%:2%12#7A4A:2RB#:%1B#7p-0RBg00ndRC#MRF%ICRCP9%Z9RGP71H97CG%Y9RH%X9RIP91E9=RJg00i\g00BVRK#W,@9RLCF,<I%U?RMPI1?LJ,<IPMPIP>P?P?P@P;ETC>C>1RI@R@P5P6g00@GR?g00@gR>'31Q56=9?>dAO9=7CPR>b6b8b9X29W7%75187=P;[[^29^7BP5f7RBf6R=54A#1=99E%1BP6P2O4b5b@b<b;b4CCW0X34X18A;42;#0,27P8%0:#5RE,25A;4B=RA?47;%0A'6]0P6%02#5,2<138EA;4=:RE?4<6%0E'6eW0%55RE%0=#5'2P8%0BR<f8RA#0#5,6EX18%5<RE,38A4B72P=P7P2127<%1<R=,81P7P11391R?P<P=139=RLEB%57RJ/2E%dKRN,=11==N'8ROPJ1=5NRPX>9RQP1O1PQP7P1P?CNPEPQP=O1PQP<P=PLCNEBP5CKPO%:6%7Df9#0RD#:%1D#7PFPCP91H96P7PGCGPHPI1@9KRH1E9NRG5L9%bK,@9RK=L9G'?,<IPM1?HK,<IC>P@P>b6b8b9X29X:91=7N,8P1876[^29^:9P5f;#0#1%1:P;O3b5b<b;b4CCO3EaA;4ABRA?4J2%0A'6eW0X18P5O1n0110000020011100P5O1W0X34X18X?0XB3XA4P5D`W=o"). Qed.

Lemma nth_sr_upd_same : ltac2:(zQ "90!p2!ku3!h8!he!ih4!kq6!kt3!jp8!kub>2sr@1$2$0>1n$3>1e$0>0@2$5^2@2$1$0^3@3$4$0@4$6$0^3@3$8^4^3^2@1$7Z^2").
Proof.
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##7zp'0h02Hnh14__x1h21ni001nh31eh43Hn0h57__arithh64__ffh74__p1h88__varmaph95__with:4__x2h;4cstrh<2srh=2IHh>5cstr0h?1hh@1thA1xp;1p;2p;3p;4p;6p;5p;<p;7p;8g00PWj1JTg02F[R0j21Tg02Q2j37Tg01QMj1^Tg02Mdj48Tg00?mj33Tg00Xmj1CTg02:@R1j12Tg0085R2j25Tg00ITj26Tg02<bj4BTg02=Ij1>Tg007Yj2:Tg00YMj2ITg00ZIj1W!s/$gj1VTg01>aj2FTg00[Rj2ETg00d;j4DTg00]=j1TTg00a@j6STg00^Cj2R!s/$ej2QTg00_Qj3OTg00`0j4NTg01Aaj39Tg01?DR3j14Tg01;4j1MTg005Mj2<Tg01BAj1P!ti$kj4KTg00\Zj3HTg002`j1UTg02@[j4]Tg02BJj5\Tg02PRj2[!ub$=l<G!t{$fj7ZTg00fRj8YTg02Ccl<XTg00lRR4f0R5'[p=0g01N9R6g00B8R7P0P1P2g02IhR8f3R9f2R:f1R;g01O>R<g00oPR=P5M<Gp=LP;g00g]R>g00h<R?P?g00h\R@P5g00i<FZp=;P7!sM%6P5CDp==P9P>P?P?P@P:P;P5GYp=?P6P!tK&P8f5R8f4R2P9!sG%!t:$@P6!sJ$7P3P1P1P9g02Dn!sG'Xp=A%J4R1P4%0:,1;P4P:A79:;%^=R3C8=34;[^34^26R0X<1%C4RA#0,1;11:<%2:RB/5=RCP:PB167B167=CLP5CBPC%>9%29,:=p-0RCg00ndRD#CRE%JDRD1I7;%W7RF%V7RGP71F7=RHg00i\g00BVRI,E7RJCD,;G%T?RKPG1=JH,;GPKPG!v%+9ESC?C?1RG@R@P5P:g00@GR?g00@gR>'61Q5:=3?>dAO7=;CNR>b6b8b9X17W71:=515;=P9[[^17^7CP5P4P8A7A82P!uv%2%28RAP;P:O4b5b;b4W0X34X26A9429!v'$P6%08#4,15P4P;f7RCf6R?594?7;9!sn&9]0P:%02#4,1<164:P4P<A94?8?7<:!sK&:eW0%45%0?#4'1P?P;P2%0CR?,1;%2;R<%2?R8'5P;P<167<RHP?P81678RLE@%4;RM%4?RN'1%MIRO,<<1<8O'5RPPM1<5ORQXA7RRP<O1PRP;P<PHCAPNPRP8!s8$?P8PLCAE@!x1$P%>:1:=Bf9#0RB#>%2B,:=PEPDP71I7:P;%P7CKPFPG1F7ORF9H7J%U!x$$I=H7F'=!wv$1=JI,;GC?P@P!wE,X:71<;O,5Q15;:!wF$:7P5f;#0#2PAP9O3b5b>b;b4C]O3P4PMf8=94C?7M!wc+eW0X26P5O1n0110000020011100P5O1!wq'X=0X@1X?4P5D\W<o"). Qed.

Lemma nth_sr_upd_other : ltac2:(zQ "80!p2!he!ih4!kt3!jp8!h8!ij9!kub>2sr@1$5$0>1n$1>1m$1>1e$0>0@1$6@3$2$1^3^2@3$2$0@4$3$0^3@3$7^5^4^2@1$4Z@4$3$0^3^5@1$4Z").
Proof.
ltac2:(KReplay.run1z (kr_t_AsStdioCall ()) ["FPX1"] "##D^p'0h03Hneh11mh21ni001nh34Hne0h47__arithh51eh64__ffh74__p1h88__varmaph95__with:4__x1h;4__x2h<4cstrh=5cstr0h>2srh?1xh@2IHhA3IHnhB1hhC1thD1yp;1p;3p;2p;4p;6p;5p;<p;7p;8g00PWj1OTg01QMj1`Tg00D]j10Tg00Xmj1UTg00?mj33j1LTg02:@R0j18Tg02;=j2s!s/$`j3lTg00ITj2:Tg02R9j3@Tg02<bj4JTg01BAj1aTg00ZIj1_!s/$gj1]Tg01>aj2NTg00]=j1\Tg00a@j6[Tg00^Cj2Z!s/$ej2YTg00_Qj3XTg00`0j4WTg01?DR1j11Tg02Q2j3=Tg01;4j1tTg005Mj2>Tg02=Ij1GTg007Yj2E!s^$cj2VTg02>Pj1r!s/$nj2qTg02?Oj3kTg01@Lj3jTg01A5j2i!s/$aj3STg00YMj2h!s/$kj4gTg00[Rj2QTg00\Zj3PTg002`j1eTg02@[j4RTg00OWj6d!v@$bj6cTg02BJj5bTg02Mdj4B!vR$=l<TTg00d;j4m!s/$fj7n!v@$_j6oTg00fRj8^Tg02Ccl<pTg01N9R2f1R3f0R433#0p=4g00lRR5f2R6P3P4CBp=2P5f5R7f4R8f3R9;=6P3CB=354p=6A3234p=?g01O>R:=324p=AAS534p=5P5P9P!sU-Cg00B8R;?334p=7P2P;P8P0!sK$:g00oPR<P3P:P<P4M<Tp=fP;P3g022UP4Cmp=FP3g00g]R=g00h<R>P>g00h\R?P4g00i<Fnp=HP3P=P>P>P?P4Eop=IP9!s7+!uM$G^p=MP5P:!uZ'9A3!u$$;1:54p=<!th$4P0P3P6P9P8P7f6R@f7RAf8RB!ti$DP2!sL$;P1P0P0P9g02Dn!t-%M<pp=K%O5R0P51463R1P6P8P9P3%`<RCA268CE6[^55^12^22RDX>01?34RE#0P3%U5RF!sX$CA23FCRGE6]0^12RHX22%A4#0RIP2P3157FPCPGCC^0IP3A32::RJ#0RKPKA3;<<RL#0RM%L2RN%L;RO%83RP%84'71s347lEXD2X?2RE1:;<RQPQDf9@JLP4CJRJPMp-0RQg00ndRR#URS%ORRT%a;RU%_;RV%];RW1N;<RX/FX,HW,IW%\>RXPW!w7,E[CM1ZW?R?P4P6g00@GR>g00@gR=':1Y46=3>=dAX;<3CWR=b6b8b9W7!sK$LLRY\LP3[^7QRQP415@F/9C19FCRL';P3O2b4b3W0%14RZ#A#0R[P2%13R\15BFPCA2\FCR]CC^0[P3%1:R^#A#0A2^FC#<W0%1ZR_#A#0%1\?2!s:%X12P4O1n0110000020010100P4O1!sDAP3PFP:P9PCPGE6e!sS$%16R`/44RaP2%18Rb/44P3A=F7A,5C!x+%]0P3%19Rc=32:#0%<LW0%17/4ZP5PG1;4CX55P2%1A/4Z1;G!sW&@RL/4^%<CRdW0%1B/4_Pd!tpAA=F@BRd=23CP7P31?@3R_#0%8@Re/7PRf#0PNPOPEP@Pe1:;eRgP3PP1:;PRhM9D9@_f1?L\Rf#0g00BVR_#tRi,>e1>PiRj'7#0Rk1>4iRlX?;RmPeO1RnPmPPO1Ro'7!t+&LPnPmP@PePgCKP\PoPmP3PPPhCKRgM9D5@fP4CJPk%G6Rk%86,E<Rf%GB%8BRn,E<1V;^%r_,q;1V;:5k;5j;g01O]'i=SRSPTP;1h;6P3PUCgPVPW1Q;_RV1N;iRU5P;%e_,Q;R_=P;U'F!zz%PX1FV_!s2%CMP?P!zK&X:;X;;R=1>3i,7lPY[1736PY[[^:;^;;RYP4%87Rlf:R?#8P9O3b4b=b<b3CRO2EdP\15CdPCP]CCe!wg91!yY/cP7!yY/XAHX22P9P6P4EcX01X55X12X22P21449P815BARHP3P9PCA28HCE6]0P9%A6#0P2P3f9R6/5BRBP:!#3\%BCE6^0IP9PJPMP>PQP41;7?!|`'A=H:9!|x$HC';eX0KA236C#<P\15?6R6P:P7!|m$6CE6eX0[!|DA14Z8!tW$;R[/5?RKPcP@!tW$K!tW$aP7A32\!{c$?A=6`7!tK$6C';eW014cZP?P8P3PA1?83R?#0%88Rc/7PRZ!zq+8Pc1:;cR;!ya%!zm$?Z1?b\RZ#01>ci/7j#0RjPmPcO1Ri/7o!sa&bPiPmP8PcP;!zN&!zD%Z!zD$jPkPf%G@1E<eP=PYP4PlPn!xV24P\f</5[R[PbPA!v:$[C!x1'!x^<W0X2!sD31!sD+!xZ/X@DXC0XB5P4DbW>o"). Qed.

Lemma length_sr_after_call_j : ltac2:(zQ "60!he!h8!p2!ku3!ih4!lif>2sr@1$1$2>4kept@1$1$0>2nv$0@3$4$0@2$3$2@3$5^3^2^1Ni0").
Proof.
ltac2:(KReplay.run1 (kr_t_AsStdioCall ()) ["FPX1"] "h01ih14kepth21nh32nvh42srp;1p;2p;3p;6p;4g00PWj14Tg02SCj2;Tg02PRj22Tg00?mj35Tg00ITj2>Tg02S_j2<Tg00OWj63Tg02T>j1:Tg02T^j37Tg01QMj16Tg02Mdj48Tg02U:j29Tg01Zkj1ATg00N3j4@Tg02UQj4?Tg02V0j3=Tg01?Dj11Tf0R0#1#1#1#1p=0g00lRR1#4g01N9R2#4P2g01O>R3%03#0#0#0#0#0#0#0R4';R5,22R6A5204X22R7P2P4P71>24P61<43E3P2P1g00@GP1%:0f2R3572P1P0f3g00oP#6C8f1R6/90#An0100000020000X02R7P5C@,21P2P1P7P5C?E3A=360,21=524eX32W1W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem stdio_call_sound :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (res : stdio_res)
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
  fd_lookup (m_fds mo) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  (* LPS 75d69e00: the reader premise, next to the fd_lookup one.  as_stdio_write gained it
     (LibWritev.writev_outcome via LazyFdNodes' lazy writev lemmas: with the reader gone the
     write is SIGPIPE), and the top discharges it from valid_input. *)
  m_channel_reader mo = true ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x198b60) M (seg_rom RSEGS) ->
  K [] ->
  (forall R' M' msF' mo',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS) ->
     realizes RSEGS (mkCfg msF' mo') K) ->
  realizes RSEGS (mkCfg msF mo)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  (* LPS 75d69e00: was a KReplay replay of as_stdio_write; the replayed term is one argument
     short of the new arity ("The 37th term has type lzok ... which should be a subtype of
     m_channel_reader mo = true"), and a replay cannot be given the extra argument without
     re-encoding its blob.  Written out instead.  Donor, statement and proof:
     a donor tree:
     projects/openssl/echconfiglist_parser/proofs/lib/As/AsStdioCall.v:283-465, with this
     tree's own addresses (0x52aa6c -> 0x198b60, 0x5b0610 -> 0x1b3108, 0xbce690 -> 0x711358),
     read from this file's own [stdio_call] body rather than from the donor. *)
  intros vals ebs sr kn R M L S Zr msF mo res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0x1b3108 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x711358 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hwphi Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hrdr OK RS HKnil HCONT.
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
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x1b3108 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x711358 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x198b60) with (0x198b60%bv : word) in RS by (apply bv_eq; reflexivity).
  eapply (as_stdio_write R M L S Zr msF mo su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
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
  - exact OK.
  - exact RS.
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
    intros R' M' msF' mo' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST OK' SB' HS' RS'.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply (HCONT R' M' msF' mo'); [ | | exact OK' | exact SB' | exact HS' | exact RS'].
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [(first [clear - Hfd12; lia | lia])|]);
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
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. (first [clear - Hfd12 Hretv Hq N1; lia | lia]).
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
Theorem stdio_call_sound_post :
  forall (vals : list word) (ebs : nat -> list byte) (sr : list expr) (kn : list kentry)
         (R : bvmap 5 word) (M : word -> option byte) (L S Zr : list (word * word)) (msF : machine_state) (mo : Model) (res : stdio_res)
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
  fd_lookup (m_fds mo) (Z_to_bv 64 (sc_fd res)) = Some (FdChannel (Z_to_bv 64 (sc_fd res))) ->
  (* LPS 75d69e00: the reader premise, next to the fd_lookup one -- see stdio_call_sound. *)
  m_channel_reader mo = true ->
  lzok RSEGS L S Zr (mkCfg msF mo) -> restrict L S msF = mkst R (Z_to_bv 64 0x198b60) M (seg_rom RSEGS) ->
  K [] ->
  (forall R' M' msF' mo',
     regs_ok (Env (vals_ev (vals ++ junk_vals R')) ebs) (sc_sr res) R' ->
     know_ok RSEGS (Env (vals_ev (vals ++ junk_vals R')) ebs) M' (sc_kn res) ->
     sw_post M su (sc_f res) (edenot E (sc_bufp res)) (edenot E (sc_bufsz res)) M' ->
     lzok RSEGS L S Zr (mkCfg msF' mo') -> same_but_materialized mo mo' -> hid_same L S msF msF' ->
     restrict L S msF' = mkst R' (Z_to_bv 64 (sc_ret res)) M' (seg_rom RSEGS) ->
     realizes RSEGS (mkCfg msF' mo') K) ->
  realizes RSEGS (mkCfg msF mo)
           (t_emit (map (WriteEv (Z_to_bv 64 (sc_fd res))) (pending ++ extra)) K).
Proof.
  (* LPS 75d69e00: was a KReplay replay of as_stdio_write, one argument short of the new
     arity.  Written out; donor a donor tree:
     projects/openssl/echconfiglist_parser/proofs/lib/As/AsStdioCall.v:503-686, with this
     tree's own addresses.  It differs from stdio_call_sound above in exactly two places:
     the HCONT application has one more slot, and the last bullet discharges it with HPOST. *)
  intros vals ebs sr kn R M L S Zr msF mo res pending extra K E HR HK Hc.
  cbv beta delta [stdio_call] in Hc. cbv zeta in Hc.
  destruct (nth 10 sr (ELit 0)) as [f| | | | | | |] eqn:H10; try discriminate.
  destruct (lit_even_ret (nth 1 sr (ELit 0))) as [ret|] eqn:Hret; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 120) 4) as [[fd| | | | | | |]|] eqn:Hfd; try discriminate.
  destruct (kread RSEGS kn (ELit 0) (f + 40) 8) as [wpe|] eqn:Hwp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 56) 8) as [wbe|] eqn:Hwb; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 88) 8) as [bufp|] eqn:Hbufp; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) (f + 96) 8) as [bufsz|] eqn:Hbufsz; [|discriminate].
  destruct (kread RSEGS kn (ELit 0) 0x1b3108 8) as [[cg| | | | | | |]|] eqn:Hcg; try discriminate.
  destruct (kread RSEGS kn (ELit 0) 0x711358 8) as [canv|] eqn:Hcan; [|discriminate].
  destruct (split_lit (nth 2 sr (ELit 0))) as [qb k0] eqn:Hsq.
  destruct (kindex (is_kwr_cov qb (k0 - 112) 112) kn 0) as [j|] eqn:Hki; [|discriminate].
  destruct (base_range kn qb) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  match type of Hc with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
  lazymatch type of Hc with Some ?x = Some _ => assert (Eres : res = x) by congruence end. clear Hc. subst res.
  cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn].
  intros Hwbwp Hwphi Hlenp Hlene H30 Dw Ds Hsl Rpend Rextra Hfdlk Hrdr OK RS HKnil HCONT.
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
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x1b3108 8 (ELit cg) HK Hcg ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcg.
  pose proof (kread_rdn RSEGS E M kn (ELit 0) 0x711358 8 canv HK Hcan ltac:(lia) ltac:(lia) ltac:(apply FL; lia)) as Rcan.
  rewrite adenot_lit0 in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan.
  pose proof (u64_range (edenot E wpe)) as Hwpr. pose proof (u64_range (edenot E wbe)) as Hwbr.
  fold wp in Hwpr. fold wb in Hwbr.
  (* [comment removed for export] *)
  replace (Z_to_bv 64 0x198b60) with (0x198b60%bv : word) in RS by (apply bv_eq; reflexivity).
  eapply (as_stdio_write R M L S Zr msF mo su f wb wp fd s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
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
  - exact OK.
  - exact RS.
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
    intros R' M' msF' mo' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 HPOST OK' SB' HS' RS'.
    set (E' := Env (vals_ev (vals ++ junk_vals R')) ebs).
    assert (Hag : env_agree (length vals) E E') by apply vals_app_agree.
    apply (HCONT R' M' msF' mo'); [ | | | exact OK' | exact SB' | exact HS' | exact RS'].
    + (* [comment removed for export] *)
      assert (HRj : regs_ok E' (sr_after_call_j sr SC_KEPT (length vals)) R').
      { apply (regs_after_call vals ebs sr R R' SC_KEPT Hsv HR).
        - intros i Hi. unfold SC_KEPT in Hi. cbn [In] in Hi.
          destruct Hi as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]];
            (split; [(first [clear - Hfd12; lia | lia])|]);
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
          + unfold estart in N1. cbn [a_base a_off] in N1. rewrite Eqb in N1. (first [clear - Hfd12 Hretv Hq N1; lia | lia]).
          + unfold estart in N2. cbn [a_base a_off] in N2. rewrite u_lit0 in N2. lia.
          + unfold estart in N3. cbn [a_base a_off] in N3. rewrite u_lit0 in N3. lia. }
      assert (Xb : edenot E' bufp = edenot E bufp) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufp]).
      assert (Xs : edenot E' bufsz = edenot E bufsz) by (symmetry; apply (edenot_agree (length vals)); [exact Hag | exact Vbufsz]).
      subst E'.
      repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply flat_abs0; (first [clear - Hf0 Hfd12 Hf232; lia | lia])|]); rewrite adenot_lit0.
      * rewrite mkAlu_denot. cbn [edenot]. fold E. rewrite alu_add, Xb, Xs. exact Pwend.
      * rewrite Xb. exact Pwpos.
      * rewrite Xb. exact Pwbase.
    + (* [comment removed for export] *) exact HPOST.
Qed.
End FPX1.
