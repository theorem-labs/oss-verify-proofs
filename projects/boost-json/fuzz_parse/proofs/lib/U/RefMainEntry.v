(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* Modified by Theorem Labs, 2026-11: launch_auxv / vdso_text_base at the entry's stack pointer (LPS b84e73ef); ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, lemmas added for the revision, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk FileSim ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive MemSplit RefLayout StartupTac.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefStartupDefs RefStartup RefStartupFacts.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import SegRead.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefMainEntry () := KReplay.lz_vm "#%X3C47Corelib7Classes9Morphisms6Proper!sI-Program6Basics4flip!sg?:forall_def!sM?Krespectful_per_obligation_1C46Stdlib9micromega5Tauto5eKindK!sE;8GFormula08!si+5Lists4!s+#6nth_ok!td,4Init5Logic8eq_ind_rK!u&,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;defini!uT#s2bv00I!tR19Datatypes4list00C4ELinuxProcessSemantics?!s<23Run:valid_argv!u3G1C!tm@;bv_unsignedC5!vc&6ZArith6BinInt1Z2leK!u8;3nat02C89OSSVerify!yi#ofs:boost_json:fuzz_parse3lib1U?RefStartupFacts<D_main_missbC13~~~C7!sxN8!{+#Exec9u64_range!sl%!x$>Z02!ug<3powI!yN73and!wu#!s^&4Bool!s'$=andb_true_iffC!x^<!sM#!tE<6of_nat!te=ad!wk=3leb!y~<6op!x]#00K!sHC2!un82eq00!xSb@!w^$_disjoint_!xW'!s|aB!s|2djw!s~&!w+<leb_le!~v9iff_refl!#4B5;Zify!#5/%3inj!sIB7rew!xz$!tV;>pow_pos_nonneg!}4>!y$=:!sj#!sf%K!#3j@1!#6E56VarMap1t!xd#!sD>0!sD6=RingM!s4'7!#70&0!t567Env!sT#5PExpr02!sIE1!sIE7!#9+;8B!t[&K!{0;!#9h6:Z!uC+=Z!sn$CheckerC!v8<4find!sqAC!sq0_sound!{WP=SymExec2S!sa#4SX2S7u_small!{M&!#8,?7Z_to_bv!|sR>!|s,Defs6envp_!|f'!#:JI>Riscv!sE+@word!t[#le_bytes!#8/O7Cat!u}#6w!sb%!#3@V!uK3auxv!uK+!sq`4pn!soi:progname!su'!~3B2!t=a8canary!t;,!~b>1!#5EA;!#5E%_rev!#;E;6length!xiXD!sb%_N!y[0!u/$!#:Q8or00!#?+PMemSplit>!y|%_outside!z+h!#@p$!xDCprod!w1#!#BK:fst!sC=s!#3bQ!#<;43!#<++!x\A5mkapp!sKB6!sK$2!sqErel!#8?D3K!#9{K1!#JQE4!sJF5!xba3rbn!vlH6eq!#Dd$!sL@8or_morph!u0F6!#K8<bool!#D6=!sF%1!#G_?1I!sD?!#L\<!#JJ#!#L{=unit!#?$7!uU%4kind!xK8!xv13Op2!yE#!t5@!smJ5!#MzF3I!#;ZI;StackLayout9EntryDraw!wT>!vP$!#6y68!y/#Inst7Inj_Z_Z!#5Z74True!#CE7!#@2,;!#E&$!{E$00!#G=2Peano2ltK!#RDC!#PxA5bv_eq!t,,!#TX$7!s+#Def3nth!#Fd24Znat5Nat2Z9is!#Fe'!{cD3c!}mQ<RefMain!wW$8all_regs!#Jd8!tb-8inj_succ!sJ>6!sJ#!v[#!wc<!|Z?N!#Up<5!#B<#7Prelude5bvmap!wFA4BvWfK!v8O8!#ER&3SX24e!#Hg#!#D2@!td16!x`$bC!tB]ridx!#;y2!#3x53!#94=3P!#4}$!~KB5Psatz!#Kb7!sO84!sOK6K!}3M2!#B`?3!{aF!#;@F:!#VA<!wtS!#Kd5:!wz#!#Yy-!xm]6edenot!sm%!~2_<nth_!~62!}H76!#aL$!uyc>!uy%!s6#trip!u}dsr_get!smV!#PK6!uy#_ok!st&!#_KW4getr!#HH%!uL\3env00!slc!#4D$0!#3&&!|xL1!#?KA2!#>\H1!#A}A2!zt_2p0!{ae2p1!ske5auxvp!sne3rnd!z7WSymDrive9junk_vals!slV3Amb7a_hwcap!~b8!#BT,!#LJ#!#@79seq!#n+6:!#QU%s!#@r=!#=:#!sa=!sE$!ta03Nat!#fs#!vMX;n!s{%!tb$!uh&!tL58app_nth1!sC7=!sC&2_plus!#4r\2ev!yUe7ev!xk-!sp_@!w8&!yf3!wD6sub!#G98ge!#f0<ge!w0?2!#D_Bge!#4,H4!#7fX5v_!yj#!ui&!#au?bv_wrap!#jj<modulo!ud+!uG+divAZ!yJ#_mod_idemp_r!t}Y=!tS&64!sr#!u,G@!#c|%!#u0+!#F-?3Sem5alu6!vnZ7alu!vp,!#5w_sp!#Fn'!u$?5Instr!u&#op!#[u3!#@Z$5proj!sA>!#aqR:!#X&+5me_ra!wO&!#Dz;!|G#!t1`s!#9he2E!#<2e7spx_va!#k7&!uK`gp!slgtp!#6Lhjunk!t^gs!w+&!#fWPArgvEnv5argcN!tUh1!slga0!slh1!|/Cmu!#c|E5C3!#5@$7tac!~_#<f_equal_help!tqb2!w;h!sli3!sl&!#;~52In!t']8!t'#zero!#6V&!#5g52or!#Hy`@!#Ml%_by_inde!#7k'!xMC4!y5>ax!sC<8max_spec!uE<!#8H87and!to#!#5d`r!#o1,!tq+5!tp$8!#AR#Na!#Ar+!#@y<;!#^~$b_max!#cD75False!$54L5State<sp_window_lo!sa\hi!#MG_ev_38!#7Jd!sn$9!|nV!#UP59ke!sy#!#UR'!#aAb2!smc6!t_%05!sok6!soc5sadd!#ck'!t_e7!sok1!#4k=!$9I#!#m969SatDivModCZ!#HT#!#j_$!$35&!$'MX8store!y[#!#78[G!$=A#!zK%!st'!},#!{MV!vK1a_bas!#bTc5a_off!}&i4fla!#`Gi6es!v]#!ss%I!#QH7le!$<RQ!v]2!#eD,!$=}C!$+=B9and!#zL$!#ZCS5a_ui!#[nW!#NO&8wrap_mem!skV!#El&;rea!$GL#c!$4gR!$H3,envp!tLX4w!u4,!tEJ6BvBase8!$5~#le8!vYY>n!$0,%8!#?F#!zzV!~J0D!~J-rdn_abov!}X'!#Tq?C!#Tq&!$J~F7add_0!#V^Q!w1'?!xW'v_ptr!x[,!#[Q4mul!wSR;nat!u>#!wZ#!ufA6b!#Z3$!$50V<cat!u7+!#3th9w!t\#!$Jk#!|QU9Ref!$$r$>!vz,nu!$?X+!|VMA!#8u&ack_imageC!$&IU<!sf%to!~r$!y;W>!z{#!}J#!tY%!#5{2!#ff06F!$Wy#01!wLc7know!#qca3rdn!sf_6!zV$i!uhI2I!#@yc!#ZNe3ke!#W65!se96!yk$s5Ubsan1M?loaded_segment!$+3D!$'g$e!#I[_kp_lo!ume!sn#hi!snia!}bR!#MV$>!|v%!#QS#ize!wDT5phdrs!xoh1!slh2!sle8kn!#3:-!#6GY8!$K3#!#En+!#S|>!$['5!zo-7!zo#!sI/!si7mul!siC!sI#!#8cY!uB'_b!$R,#!z#P!#7}-Abuild!#8k%!$OzT!t`,;lay_bsb_len!x`f!#{t#_!#vr+!uPU=at_random!#=i#!$>\Ved!sh&!sdW?!tN,!vv%!#8F95skipn!sD;6firstn!w[Z9rnd_fact!$T\V3Lib2Nd:and_elimF5!}5`:!$UB$ords!sn`!#AF%!ss'!sr%!$-5M3!$9+J7!sOK5!#aA_!{P%u!u>&!#>:c8!#541!#yd3divide!$:BE7!sj<:mod_!sn%!$hx9x!$kg,!#zn-:!#Y<$mult!$KI<!$T/#0!#E{W!y,$!v##i!}##!#7D&!#~},flat!$+S#!{p`3!#58d<!{$+_at!#<Wg!tcf7kn!|h$!t^h4!sle4ke!#g%grnd!|p'!#L%PStepTac6u_Z2bv!shXeq!}Z#?!#Lk#!$]i$hit8!sqV:!#Uf%Tac@!st-out_Z!su%!$RaJ<MemImageType7S!#Hv$!$R`3;Hexadecimal4uint!$|s-!sH:7!sHD5!sH26!$Ji$!t/&!#V15;of_num_!sG#!}lP!uO#Read7SEGREAD>!$tT$writabl!#Y8'!#4n59!#pC#!$E]S!t?3=wseg_ok!${S8!v>:1!#5n;:comparis!$y:?!sL/2!sLH3!$<r<orb!#6D'!$|V+<or!$|U;!#jn%!s?0!%-/5!%,`+!sM?@subrel!%,y$!$x`$!sS+!%/I1imp!sq@5flip2!sH?F!t;1!tnGI!tb#exive_!s0,proxy!t7@!sR0per!sYEB!tj/p!%2L2!sU4NR!t0,artial_app!#gq$ism!sa5>!sa+_Prop?or!$m]#!sW=!t:,D!sO#!wD#_!tr-!vS@!sW#!wT#!s\F?R!sA'!s6%=!sb#!uS+!#=w67!%4y$b!sB7>!sB&_!s-%!#9H^!%%$2su!%&$h!%0S&cel!$AG+!u\6ex!s2#!%-D=to!%-D6!#Q7$Z2Nat2i!$$P_9!%2E#!un,!sr_;!uk&non!$rFX!#jK,C!#jK,mem_dat!$;l%!#H%d4!#?$XoreOk?!#wL-dow!#C2fimg!#c_+!z6a!wI'self!wIordn!wI-!#n;Bl!u<b>!tH-t!#uU'!sza=!}H'!$}=#!syX!$tA1<!$~0%!%%|\!un4!sx/!%%<Y!%883!vj-guar!$H$e!#53&!$Wp,!tsb?!sx&page!#d\#!#7&n!$WL,!#6$_!#D4#!{k,!#Mla5!sle4ke!$5#&!#`2_kn!#sU%!sq$!#F6+!#o>80!$Ym7!sC%_appI!sE66E!#;-#00!tv_:!#r`#!#gf,!x<`!ss$!#S&h!tg%!va-!#Tib!$>Q,!#`2Y!#fC&nw!snV!#x7&B!#~G'!#hk#s_!#{Hbu_!#}45!thP!#}|%?!sn#struct_!#36,!teY?!so&av!#kK/!ssO!#xp'Ctotal!uY#!#7k%!#~tX!u^'I!su3!#gl$_l!uha<!wI$str!#lS+!tmQFileSim@!$$a+c!st#!}N&".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk14list37Corelib4Init5Logicm02eq46Stdlib6ZArith6BinInt1Zn92lehfbbv_unsignedk14Nonek14boolk16optionk14true01Z3h5LinuxProcessSemanticsfLinuxProcessSem3Runs5avalid_argv3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutve9EntryDraw79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UeRefStartupDefs~~~~~~hje6D_main79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UfRefStartupFacts~~~~~~hobcD_main_missbhf7Z_to_bv69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~hu9ccat_argv_ptrhje6auxv_wvedat_random_ptrk14consk13appk13nil69OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Amb~~~~~~im07a_hwcap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~iq19junk_vals89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcRefMainEntry9MainEntry~~~~~~iu95auxvpiu92p0iu92p1iu93rndhje8canary_w79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~jlc3enviq18blobs_evjlc3Env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~jr57vals_eviu96blobs0iu95vals0jlc4expr3h5LinuxProcessSemantics5Riscv5Instrkh47ALU_ADDjlc4EAlujlc4ELitjlc4EVariu93spxjlc6kentryjlc2SAjlc5KWordjlc6KAlignjlc6KRangejlc3KWrjlc5KDisjjlc4KImgiu97kn_auxviu98kn_imageiu98kn_stackm01Ihf2BVhf4BvWfk13nat37Corelib4Init5Peanoku02lt37Corelib5Lists7ListDefkva3nth89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcRefMainEntry4FPX2~~~~~~lh88all_regsn96of_nat3h5LinuxProcessSemantics5Riscv7Preludeln35bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~lq24getrjlc6edenot79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~luf7regs_okk16lengthn96modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UcRefMainEntry~~~~~~ml13rndm03andn93addk14Some3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsmqch0word_to_le_bytesim05a_uidlq23rdn69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9RefLayout~~~~~~ng8aauxv_wordsml15auxvp69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~nlbfloaded_segmentsnlb5phdrsn93mul37Corelib4InitbHexadecimalnr32D0nr32D1nr32D5nr33Nil37Corelib4Init3Natnu6bof_num_uint37Corelib4Init6Numberog7fUIntHexadecimal69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9StreamSim~~~~~~oif7wseg_okhobh0range_disjoint_bk14prods58valid_spn92ltn93pows5avalid_envpnr32D3" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.
Abbreviation RPH := Ubsan.M.phdrs.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
(* LPS-revision port.  The encoded statement held the pre-revision D_main
   (sp0 av ev hw rdraw tid), which no longer exists: RefStartupDefs.v's Section Defs
   now exports D_main inp sp0 rnd tid, with av/ev read off inp.  A KReplay blob is never
   re-encoded, so the replay is replaced by an explicit proof (rule 11).
   Statement and tactic text: a donor tree
   :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:30-53 (the plain-text twin of
   this encoded file), statement AND proof, with boost-json's own D_cxx for beast's D_cx and
   boost-json's own cell table; the argument list re-threaded to boost-json's own
   RefStartupDefs.v:191 and RefStartup.v:101. *)
Lemma D_main_none : forall (inp : ProcInput) sp0 (rdraw : EntryDraw) tid (i : Z),
  valid_argv (in_argv inp) ->
  (0x7fff80000000 <= bv_unsigned sp0)%Z -> (bv_unsigned sp0 <= 0x800000000000)%Z ->
  D_main_missb i 1 = true ->
  D_main inp sp0 rdraw tid (Z_to_bv 64 i) = None.
Proof.
  intros inp sp0 rdraw tid i Hva Hlo Hhi Hb.
  pose proof (u64_range tid) as Ht.
  unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
  repeat match goal with
         | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
         end.
  repeat match goal with
         | H : range_disjoint_b _ _ _ = true |- _ =>
             apply range_disjoint_djw in H; cbn [fst snd] in H
         | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
         | H : true = true |- _ => clear H
         end.
  assert (Hui : bv_unsigned (Z_to_bv 64 i) = i) by (apply u_small; lia).
  unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
  repeat (rewrite MemSplit.wbytes_outside;
    [ | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite u_small by (cbn; lia); cbn; lia
      | rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Hui; rewrite u_small by (cbn; lia);
        match goal with H : djw _ |- _ => unfold djw in H; clear -H; lia end ]).
  reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
End FPX1.

Section MainEntry.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable ev : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable rdraw : ltac2:(zQ "10!hj2$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!lp9!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : word -> option byte.
  Let av : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8") := ltac2:(zQ "50!l9!h9!jc!ikd!ila@3$3@1$0@1$2@1$1#8?3a0s@3$3@1$0@1$2@1$1#8?4path@1$4@1$0@1$2@1$1#8").
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp ev.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = ev.
  (* LPS-revision port: the encoded/old form held the pre-revision 7-argument
     main_entry sp0 av ev rdraw tid regs mem.  RefStartup.v:101 now reads
     main_entry inp mbase entry sp0 rnd tid regs mem, with av/ev off inp.  Written out
     rather than re-encoded (rule 11).  Shape donor, statement only:
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:94-110. *)
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.

  Let Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let Hal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* LPS-revision port, written out rather than re-encoded (rule 11).  Three tree-local
     signatures moved with the revision and the encoded forms hold the old ones:
       CatExec.v:258-260  cat_argv_ptr (top : word) av ev (execfn : list byte) (k : nat)
                          -- gained execfn; `top` is the DRAWN top, and this tree's own
                          ported CatExec.v:422 and :495 apply it as
                          `cat_argv_ptr (ed_top draw) (in_argv inp) (in_envp inp) (in_execfn inp) k`,
                          which is why the base is `ed_top rdraw` and not sp0;
       RefStartupDefs.v Section Defs exports  auxv_w inp sp0;
       at_random_ptr gained the rseq flag -- RefStartupDefs.v's own rnd_w reads
                          `at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev`.
     Donors, statement only, both ported and in agreement:
       this unit's own RefStartupDefs.v (pn_w / auxv_w / rnd_w) and
       a donor tree
       :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:116-119.
     kb_rseq is taken from the run and never pinned. *)
  Definition p0 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 0.
  Definition p1 : word := cat_argv_ptr (ed_top rdraw) av ev (in_execfn inp) 1.
  Definition auxvp : word := auxv_w inp sp0.
  Definition rnd : word := at_random_ptr sp0 (kb_rseq (in_kernel inp)) av ev.

  (* [comment removed for export] *)
  Definition vals0 : ltac2:(zQ "30!l9!h9!jc@1$0@1$2@1$1#k0") := ltac2:(zQ "c0!h9!jc!ikd!il4!ila!ip6!itc!jj4!jjd!jk3!jk9!jl0@3$3@1$1@1$0#k0@3$2@1$1@1$0#k0?3sp0@3$2@1$1@1$0#k0$8@3$2@1$1@1$0#k0$9@3$2@1$1@1$0#k0$7@3$2@1$1@1$0#k0$a@3$2@1$1@1$0#k0?3tid@1$4@1$1@1$0#k0@3$3@1$1@1$0#k0@1$6?4regs@3$2@1$1@1$0#k0@1$5?3AMB@3$2@1$1@1$0#k0@1$b?5rdraw@1$4@1$1@1$0#k0").
  Definition blobs0 : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8") := ltac2:(zQ "71!h9!jc!ikd!l9!ila!il4!htf&@3$2@1$1@1$0#8@2$6@1$0#8Z@1$4@1$1@1$0#8@3$2@1$3@1$1@1$0#8@3$5@1$1@1$0#8?3a0s~0@3$2@1$3@1$1@1$0#8@3$5@1$1@1$0#8?4path~0@1$4@1$3@1$1@1$0#8").
  Definition E0 : ltac2:(zQ "10!jpb$0") := ltac2:(zQ "50!jq2!jqe!jue!jv9!kg3@2$1@1$2$4@1$0$3").

  Definition spx : ltac2:(zQ "20!s2!kgc>1k$0$1") := ltac2:(zQ "50!s2!kj8!kk3!kkb!kl3\1k$0@3$2$1@1$4N0@1$3^1").

  Definition sr_main : ltac2:(zQ "20!l9!kgc@1$0$1") := ltac2:(zQ "60!kgc!ikd!kkb!kl3!klb!ila@3$1$0@1$2Z@3$1$0@1$2+ttln4@3$1$0@1$4-j0@3$1$0@1$2+hgog0@3$1$0@1$2+hgurv8@3$1$0@1$3Nb@3$1$0@1$3Nc@3$1$0@1$3Nd@3$1$0@1$4+8@3$1$0@1$2+2@3$1$0@1$2+2@3$1$0@1$4+8@3$1$0@1$4+i0@3$1$0@1$3Nh3@3$1$0@1$3Nh4@3$1$0@1$3Nh5@3$1$0@1$3Nh6@3$1$0@1$3Nh7@3$1$0@1$2+kmvu4@3$1$0@1$4+i0@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$2Z@3$1$0@1$3Ni2@3$1$0@1$3Ni3@3$1$0@1$3Ni4@3$1$0@1$3Ni5@1$5$0").

  (* LPS-revision port.  The encoded form claimed the writable stack window as
       KWr (SA (EVar 0) (-8388608)) 8388608
     i.e. everything from sp0 - stack_max_size.  THAT IS FALSE AT THIS REVISION: the model
     certifies writes only from MemSplit.wok_lo sp0 = bv_unsigned sp0 + stack_window_reach
     - stack_max_size (MemSplit.v:137-138), which is 2,244,095 bytes higher.  Measured, not
     inferred: a farm round's UNCLOSED-GOAL probe printed
       (bv_unsigned sp0 + 2244095 - 8*1024*1024 <= bv_unsigned sp0 + -8388608 + d)
     as the obligation main_entry_store_ok_win could not discharge.  8388608 is the
     zero-filled window here, not stack_max_size's other meaning, so it is the occurrence
     that MOVES (rules-broadcast 12h; G3-FINAL section 5).
     Written SYMBOLICALLY rather than as 6144513, so it stays right if either constant moves.
     A KReplay/CDef blob is never re-encoded, so the definition is written out (rule 11).
     SHAPE DONOR, mapped entry-for-entry onto this file's own zQ string before use:
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:134-138.
     RULE 22: every literal below is read from THIS file's encoded string
     (+h0 = 16, +nvvvogggggg0 / +ogggggggggg0 = the two sp bounds, Z/+8/+h0/+h8 = the
     offsets 0/8/16/24, N8 = 8, +2 / N1 / N2 / Z = the four values); only the window moved.
     UNITS: BYTES below sp0.  Not words, not pairs. *)
  Definition kn_stack : list kentry :=
    [KAlign (EVar 0) 16; KRange (EVar 0) 0x7fff80000000 0x800000000000;
     KWr (SA (EVar 0) (stack_window_reach - stack_max_size)) (stack_max_size - stack_window_reach);
     KWord (SA (EVar 0) 0) 8 (ELit 2); KWord (SA (EVar 0) 8) 8 (EVar 1);
     KWord (SA (EVar 0) 16) 8 (EVar 2); KWord (SA (EVar 0) 24) 8 (ELit 0)].

  (* LPS-revision port, MIRROR of the plain twin's kn_auxv in this unit's own
     RefMainEntry.v, which is farm-GREEN.  The two encoded BODIES are byte-identical --
     only the symbol tables differ (km2/kl3 here against klc/kkd there) -- so every
     literal below is this file's own as well as that one's, and RULE 22 is satisfied
     without a second decode.  Checked explicitly: `+a` (AT_PHNUM = 10) is right for the
     Ubsan image too, whose elf-snapshot line reads phdr=0x10040/56/10.
     THE WHOLE TABLE MOVED at this revision: the encoded form claimed the pre-revision
     10-pair vector beginning at AT_PHDR, and the revision inserts ten pairs ahead of
     AT_HWCAP (auxv_entries printed on the farm in 20261106t093733z-232e54; see the plain
     twin for the full vector).  Same facts, new indices; the two KDisj windows become
     symbolic; no terminator is claimed, because AT_NULL's pair index is 26 or 28 and a
     literal one would PIN kb_rseq.  UNITS: BYTES throughout. *)
  Definition kn_auxv : list kentry :=
    [KRange (EVar 3) 0x7fff80000000 0x800000400000;
     KRange (EVar 4) 0x7fff80000000 0x800000400000;
     KDisj (SA (EVar 0) (stack_window_reach - stack_max_size))
           (stack_max_size - stack_window_reach) (SA (EVar 3) 0) 400;
     KDisj (SA (EVar 0) (stack_window_reach - stack_max_size))
           (stack_max_size - stack_window_reach) (SA (EVar 4) 0) 16;
     KAlign (EVar 3) 8; KAlign (EVar 4) 8;
     KWord (SA (EVar 3) 160) 8 (ELit 16);      (* pair 10 AT_HWCAP   key   *)
     KWord (SA (EVar 3) 168) 8 (EVar 38);      (*                    value *)
     KWord (SA (EVar 3) 176) 8 (ELit 6);       (* pair 11 AT_PAGESZ  key   *)
     KWord (SA (EVar 3) 184) 8 (ELit 0x1000);  (*                    value *)
     KWord (SA (EVar 3) 208) 8 (ELit 3);       (* pair 13 AT_PHDR    key   *)
     KWord (SA (EVar 3) 216) 8 (ELit 0x10040); (*                    value *)
     KWord (SA (EVar 3) 224) 8 (ELit 4);       (* pair 14 AT_PHENT   key   *)
     KWord (SA (EVar 3) 232) 8 (ELit 0x38);    (*                    value *)
     KWord (SA (EVar 3) 240) 8 (ELit 5);       (* pair 15 AT_PHNUM   key   *)
     KWord (SA (EVar 3) 248) 8 (ELit 0xa);     (*                    value *)
     KWord (SA (EVar 3) 304) 8 (ELit 0xb);     (* pair 19 AT_UID     key   *)
     KWord (SA (EVar 3) 320) 8 (ELit 0xc);     (* pair 20 AT_EUID    key   *)
     KWord (SA (EVar 3) 368) 8 (ELit 0x17);    (* pair 23 AT_SECURE  key   *)
     KWord (SA (EVar 3) 376) 8 (ELit 0);       (*                    value *)
     KWord (SA (EVar 3) 384) 8 (ELit 0x19);    (* pair 24 AT_RANDOM  key   *)
     KWord (SA (EVar 3) 392) 8 (EVar 4)].      (*                    value *)
  (* [comment removed for export] *)

  Definition kn_image : ltac2:(zQ "20!l9!km2@1$0$1") := ltac2:(zQ "a0!km2!ikd!kpf!kkb!kmc!kn2!kl3!ila!ko5!kof@3$1$0@2$9@2$4@1$3Z+vsgg0+jlgg0@3$1$0@2$2+hggg0+vtgv0@3$1$0@2$2+vtgv1+hgthq0@3$1$0@2$2+hgthqc+hgtki8@3$1$0@2$2+hgtkic+hguri8@3$1$0@2$2+hiusg0+hiusi0@3$1$0@3$5@2$4@1$3Z+hgurj0N8@1$3+hgurj0@3$1$0@3$5@2$4@1$3Z+hgurl0N4@1$6N5@3$1$0@2$2+hgurlc+hgurq8@3$1$0@2$2+hgurr0+hgurs8@3$1$0@2$2+hgurt0+hguru8@3$1$0@3$5@2$4@1$3Z+hguru8N8@1$6Ni7@3$1$0@2$2+hgurv8+hgusg8@3$1$0@2$2+hgush0+hguso0@3$1$0@3$5@2$4@1$3Z+hiusj8N8@1$6Ni7@3$1$0@2$2+hiuun0+hiuun8@3$1$0@2$2+hiuuo9+hiuup0@3$1$0@3$5@2$4@1$3Z+hiuup0N8@1$6N3@3$1$0@2$2+hiuup8+hiuuq0@3$1$0@2$2+hiuur0+hiuur8@3$1$0@3$5@2$4@1$3Z+hiuur8N8@1$3+hgg0@3$1$0@2$2+hiuus0+hiuuv0@3$1$0@3$5@2$4@1$3Z+hiuuv0N8@1$6Ni6@3$1$0@2$2+hivgg0+hjhgg0@3$1$0@3$8@1$6N5+1+jvvvvf@3$1$0@2$2Z+hgg0@1$7$0").

  (* [comment removed for export] *)
  Definition kn_main : ltac2:(zQ "20!l9!km2@1$0$1") := ltac2:(zQ "50!il4!km2!kq7!kr2!kre@3$0$1$4@3$0$1$2$3").
End MainEntry.

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition all_regs : ltac2:(zQ "30!l9!h9!jc@1$0@1$2@1$1#5") := ltac2:(zQ "70!h9!jc!ikd!ksa!kse!kt3!ila@3$2@1$1@1$0#5@3$4@1$0#5ZKv$3@2$5@1$0#5Z@3$2@1$1@1$0#5@3$4@1$0#5+1Kv$3@2$5@1$0#5+1@3$2@1$1@1$0#5@3$4@1$0#5+2Kv$3@2$5@1$0#5+2@3$2@1$1@1$0#5@3$4@1$0#5+3Kv$3@2$5@1$0#5+3@3$2@1$1@1$0#5@3$4@1$0#5+4Kv$3@2$5@1$0#5+4@3$2@1$1@1$0#5@3$4@1$0#5+5Kv$3@2$5@1$0#5+5@3$2@1$1@1$0#5@3$4@1$0#5+6Kv$3@2$5@1$0#5+6@3$2@1$1@1$0#5@3$4@1$0#5+7Kv$3@2$5@1$0#5+7@3$2@1$1@1$0#5@3$4@1$0#5+8Kv$3@2$5@1$0#5+8@3$2@1$1@1$0#5@3$4@1$0#5+9Kv$3@2$5@1$0#5+9@3$2@1$1@1$0#5@3$4@1$0#5+aKv$3@2$5@1$0#5+a@3$2@1$1@1$0#5@3$4@1$0#5+bKv$3@2$5@1$0#5+b@3$2@1$1@1$0#5@3$4@1$0#5+cKv$3@2$5@1$0#5+c@3$2@1$1@1$0#5@3$4@1$0#5+dKv$3@2$5@1$0#5+d@3$2@1$1@1$0#5@3$4@1$0#5+eKv$3@2$5@1$0#5+e@3$2@1$1@1$0#5@3$4@1$0#5+fKv$3@2$5@1$0#5+f@3$2@1$1@1$0#5@3$4@1$0#5+h0Kv$3@2$5@1$0#5+h0@3$2@1$1@1$0#5@3$4@1$0#5+h1Kv$3@2$5@1$0#5+h1@3$2@1$1@1$0#5@3$4@1$0#5+h2Kv$3@2$5@1$0#5+h2@3$2@1$1@1$0#5@3$4@1$0#5+h3Kv$3@2$5@1$0#5+h3@3$2@1$1@1$0#5@3$4@1$0#5+h4Kv$3@2$5@1$0#5+h4@3$2@1$1@1$0#5@3$4@1$0#5+h5Kv$3@2$5@1$0#5+h5@3$2@1$1@1$0#5@3$4@1$0#5+h6Kv$3@2$5@1$0#5+h6@3$2@1$1@1$0#5@3$4@1$0#5+h7Kv$3@2$5@1$0#5+h7@3$2@1$1@1$0#5@3$4@1$0#5+h8Kv$3@2$5@1$0#5+h8@3$2@1$1@1$0#5@3$4@1$0#5+h9Kv$3@2$5@1$0#5+h9@3$2@1$1@1$0#5@3$4@1$0#5+haKv$3@2$5@1$0#5+ha@3$2@1$1@1$0#5@3$4@1$0#5+hbKv$3@2$5@1$0#5+hb@3$2@1$1@1$0#5@3$4@1$0#5+hcKv$3@2$5@1$0#5+hc@3$2@1$1@1$0#5@3$4@1$0#5+hdKv$3@2$5@1$0#5+hd@3$2@1$1@1$0#5@3$4@1$0#5+heKv$3@2$5@1$0#5+he@3$2@1$1@1$0#5@3$4@1$0#5+hfKv$3@2$5@1$0#5+hf@1$6@1$1@1$0#5").

Lemma nth_all_regs : ltac2:(zQ "c0!h9!jc!kta!ksa!n4!kv4!lh1!lle!lma!kse!kt3!htf>1n$2>0@2$5^1Ni0@3$4@1$1@1$0#5@4$6@1$1@1$0#5^2$7@3$9@1$0#5ZKv$3@2$a@1$0#5Z@2$b@1$0#5@1$8^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntry ()) ["FPX2"] "##^Dp'0h02Hnh11Hh22n0h31ni001nh44__p1h54__x1h62b1h72b2h83Hn0h97__arithh:4__ffh;8__varmaph<5__with=4cstrh>1xp%0p;1p;2p;3p;4p;6p;<p;7p;8g0094R0j10Tg010]R1j21Tg004Lj1>Tg007Ij1QTg0051j1c!s/$Oj1;Tg0115j3[Tg00>@R2j1=Tg00OMj2CTg00@^j39!sg$nj2<!sU$Xj3MTg012<j4@Tg00;kj1JTg00FVR3j2I!sr$`j2?Tg00EGj4Y!sU$Xj1XTg008Xj2FTg00GVj1VTg0062j1UTg00H6j2T!s/$Tj1PTg00I2j1OTg00J@j2B!s8$]j2NTg00c7j4G!tr$<j1RTg013=j6STg00KFj2b!s/$hj2DTg00LBj2a!s/$nj3`Tg00MMj4_Tg00`dl<KTg00aol<^!t$$bj7]Tg00bTj3ATg002oj8\Tf4R4f3R5f2R6g013aR7f1R8C@f0R939p=W%=9,C8p=4g00iBR:1<89'Dp=2f5R;P4P5P7P6C@!sM%39p=3P6P8P7P9C@p=51?45/?6/?8/?9p=71D:9p=Hg00i`R<P<P:P:P0P2P2f6g014lR=P;P4P!sA0P5P=!s|$9M<KM<Kp=6!sE$1P2P3g015P!sZ$5!sJ'^p=ZP8g002PR;g00j?R3P3g00j_R2P9g00kfF]p=EAA:45=A:6=A:8=A:9p=8P5P;P3P3P2!su%G\p=L%09#0#0#0p=:g00nRR1#0R=#0R0#0R>#0R?#0R@#0RA#0RB#0RC#0RD#0RE#0RF#0RG#0RH#0RI#0RJ#0RK#0RL#0RM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[,19R\P<g00lmR]#>R^#Q#cR_#;R`P`!uu$hdRag01625[_Rb%=8Rc,C_DW^0\P8111[g016NR\%;9Rd%;8Reg00<f%;6?9891<561<5859:Rf[1<681<6959:%;5?968[Rg%;4?956\fAM689P9n20010!s#$12!s-%0W7W6W3RfPg^7e^6d^3\R\P9P_P`P1P7PbC@14_1R112_1O4b1W0P<%09R1/1[P`P`%08R7PbP_P7E3]0P911=[PfP!sk$A5`=b14_=R=12_=!sf,1!sf-7R=!sf$=!sf'0!sf/0b14_0R012_0!sf9=R0!sf$0!sf'>!sf/>b14_>R>12_>!sf90R>!sf$>!sf'?!sf/?b14_?R?12_?!sf9>R?!sf$?!sf'@!sf/@b14_@R@12_@!sf9?R@!sf$@!sf'A!sf/Ab14_ARA12_A!sf9@RA!sf$A!sf'B!sf/Bb14_BRB12_B!sf9ARB!sf$B!sf'C!sf/Cb14_CRC12_C!sf9BRC!sf$C!sf'D!sf/Db14_DRD12_D!sf9CRD!sf$D!sf'E!sf/Eb14_ERE12_E!sf9DRE!sf$E!sf'F!sf/Fb14_FRF12_F!sf9ERF!sf$F!sf'G!sf/Gb14_GRG12_G!sf9FRG!sf$G!sf'H!sf/Hb14_HRH12_H!sf9GRH!sf$H!sf'I!sf/Ib14_IRI12_I!sf9HRI!sf$I!sf'J!sf/Jb14_JRJ12_J!sf9IRJ!sf$J!sf'K!sf/Kb14_KRK12_K!sf9JRK!sf$K!sf'L!sf/Lb14_LRL12_L!sf9KRL!sf$L!sf'M!sf/Mb14_MRM12_M!sf9LRM!sf$M!sf'N!sf/Nb14_NRN12_N!sf9MRN!sf$N!sf'O!sf/Ob14_ORO12_O!sf9NRO!sf$O!sf'P!sf/Pb14_PRP12_P!sf9ORP!sf$P!sf'Q!sf/Qb14_QRQ12_Q!sf9PRQ!sf$Q!sf'R!sf/Rb14_RRR12_R!sf9QRR!sf$R!sf'S!sf/Sb14_SRS12_S!sf9RRS!sf$S!sf'T!sf/Tb14_TRT12_T!sf9SRT!sf$T!sf'U!sf/Ub14_URU12_U!sf9TRU!sf$U!sf'V!sf/Vb14_VRV12_V!sf9URV!sf$V!sf'W!sf/Wb14_WRW12_W!sf9VRW!sf$W!sf'X!sf/Xb14_XRX12_X!sf9WRX!sf$X!sf'Y!sf/Yb14_YRY12_Y!sf9XRY!sf$Y!sf'Z!sf/Zb14_ZRZ12_Z!sf%%01/1[%0Y!sj%c%J]RZP!s$$D7P!s0h%>^#>!s$$JR^'IS00P11?9ZX>:R1P!s$acO1S01O1S02O1S03O1R\O1RfO1RdO1ReO1RgO1RhO1RiO1RjO1RkO1RlO1RmO1RnO1RoO1RpO1RqO1RrO1RsO1RtO1RuO1RvO1RwO1RxO1RyO1RzO1R{O1R|O1R}O1R~O1P1PYP~P1PXP}P1PWP|P1PVP{P1PUPzP1PTPyP1PSPxP1PRPwP1PQPvP1PPPuP1POPtP1PNPsP1PMPrP1PLPqP1PKPpP1PJPoP1PIPnP1PHPmP1PGPlP1PFPkP1PEPjP1PDPiP1PCPhP1PBPgP1PAPeP1P@PdP1P?PfP1P>P\P1P0Q03P1P=Q02P1P7Q01P1P8Pc%HcF6!s$AP[P^%H^EZP9CYQ00%X6%=6,Fap-0R[g0101Rc#V%Uc1T:8%P:%O:RcP:1B:ag00k?1N:]R]CG,Ec%R3R1PcP:P]1B:ZR]P!s$$D8P!s0hg00lF1B:^!t;$P1Pc!#JC'5ESCLCL1bc2P9P6g00gdRcg00hDR2'D1a96=9c2dA`:a8C_b:b;b<X5:W41Fa9P8P!|$r/I^P5[[^5:^4[P9!}x$:4#:!s$/R`!~-$`E3%=4P8P6O4b9b=b8W0X3<P9O1n0110001020111100X2!s>/0!s>~!s>~!s>~!s>~!s>~!s>~!s>+0!s>~!s>uP9O1!{l$o"). Qed.

Lemma regs_ok_by_index : ltac2:(zQ "h20!h9!jc!lh1!kgc!l9!kta!ksa!n4!kv4!lp9!ltd!kkb!lu5!jpb!mj4!lle!kse!kt3>1E$d>2sr@1$4$3>1R@2$9@1$0#5@1$1@1$0#k0>0>1i$5>0@2$8^1Ni0@3$7@1$1@1$0#k0@2$a^3@4$2@1$1@1$0#5^2$f@3$h0@1$0#5ZKv$6@2$h1@1$0#5Z@2$c^5@4$2$3^2^4@1$bZ@3$e^4^3^2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntry ()) ["FPX2"] "##9pp'0h03Hr0h12Hxh21bi001bh32H0h44__x1h54__x2h62b1h72b2h81nh91rh:1Eh;1Hh<1Rh=7__arithh>4__ffh?8__varmaph@5__withA1ihB2srp;1p;2p;3p;4p;7p;5p;6p;8g0062j1HTg004Lj16Tg007Ij1[Tg0051j1=!s/$Oj14Tg016lj2_Tg0094j12Tg010]j2STg017Xj2LTg0115j3@Tg012<j41Tg018;j1jTg019Bj38Tg00Khj2;Tg00@^j30!sA$oj1:!tL$nj27!sn$Xj3\Tg01;4j1Y!s/$Rj2XTg01<3j2A!s/$\j3WTg01=Ej3V!s/$nj2UTg00GVj1RTg00Vkj3QTg00H6j2OTg00XXj1KTg01>Zj4M!sA$Tj1NTg00I2j1J!s/$]j2>Tg00c7j4P!s/$bj7?Tg01?8j5I!s/$\j6T!u<$<j1iTg002oj8h!uW$Fj2gTg00LBj2f!s/$nj3eTg00MMj4bTg01@@j2aTg00OMj2<Tg003nj7`!sA$]j1DTg01Anj2GTg00>@j1ETg01C5j2^Tg01DDj6F!s/$`j1]Tg01F5j2cTg01G<j3dTg01HJj2BTf0R0#2#2p=Z%2!s0$#2p=5f4R1f3R2f2R3'Bf1R4/G030p=3g00gdR5g00hDR6700p=91B34=020p=Cg01IKg01JQR7#Hg00lmR8#6R9#[#=R:%69#6!s$&=R;#4R<'_g00i`g00nRR=#2R>#2#Z#5!s$/,S0P<P3%4:R?P4g013aR@g00hdRAg0162RB1L:Ad5@:RCC1P1P7P4P2%jARDC1D3[]AA@:ABRB98:0REP51;50A8:4B=050P5A8:2!s1%<f6RFP1f8RGP5!sm$DP7%:1RHf7RIPDC1RJn010!s#$20000D3]0P4A8:3BRK#9g016NRL%40RM%44RNg00<f%43?040g00iBRO1723172430RP[1734173050O%42?034[RQ%41?023\PA\340P0n20!tC'1!tD$000W7W6W8PQ^7N^6M^8LP0P:P1PBg0101RL%Y8,XO1AO>5WO1AO=5VOg01KX'U%RL3Q%HLPO1OO3P4%KOCM%NO%JORLg002PR=g00j?R>P>g00j_RMPLP=P>P>!s-'g01LDRNPO1>O8g01Ld1>O9CPR9g00kfR8F?!sY+NDIET%i!sb+PMP9P8F?Gh1gLMP0P31;561f03#9dAeOA4Cbb>b?b@X4OX5O1a04#9A0O43[^4O^5OP017:Bf5RO,7:P3O3b=O4b3A0?2CP?PB%9EP<PGP4f:REPDD3]0X9?A8:BB#91<;A,;<P<PIPBf9RAPDD3eW0P1P0P4F`b3W0g01MK905KP1%:2RK%D2O2P<POP?PKP@PCC1PIP7PKPFP!y{$P?P?PHP@PBC1!t$$0P7%:ORBPGPDC1,GAR@CCX2?P0%EH,<:RK%D1,^HEFP<PFPKPGPJD3P?%EB,<:!u4$0PEP7%:FPA!t2%!sd$PO%]O!s[$IPOP@CCP0b1b1b1W0n01!y<%20101P0O1b0b2P<P3P0P11c20D3eX9?Ad234eW;W<WBW:o"). Qed.
End FPX2.

Section MainEntryProofs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable rdraw : ltac2:(zQ "10!hj2$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!lp9!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : word -> option byte.
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = envv.
  (* LPS-revision port: the encoded/old form held the pre-revision 7-argument
     main_entry sp0 av ev rdraw tid regs mem.  RefStartup.v:101 now reads
     main_entry inp mbase entry sp0 rnd tid regs mem, with av/ev off inp.  Written out
     rather than re-encoded (rule 11).  Shape donor, statement only:
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:94-110. *)
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.

  Let E := E0 inp sp0 a0s path envv rdraw tid regs.


  (* LPS-revision port.  These six replays applied p0/p1/auxvp/rnd in their pre-revision
     4-argument form from inside the replay program; a KReplay blob is never re-encoded, so
     each replay is REPLACED BY AN EXPLICIT PROOF (rule 11, and this lane's brief).
     Statement AND tactic text: a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:223-250 -- the PLAIN-TEXT
     TWIN of this encoded file, hunk by hunk, with only the argument lists re-threaded to
     each definition's new generalisation set (p0/p1 lost sp0 because their base is now
     `ed_top rdraw`; auxvp lost a0s/path/envv because they come off inp).  Nothing else of
     beast's file is taken: its LATER sections are still pre-revision. *)
  Lemma ev_vals : forall n, ev E n = nth n ([sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] ++ junk_vals regs ++ [a_hwcap; canary_w rdraw]) (Z_to_bv 64 0).
  Proof. intros n. reflexivity. Qed.

  Lemma length_junk_vals : length (junk_vals regs) = 32%nat.
  Proof. unfold junk_vals. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma ev_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr regs (Z_to_bv 5 (Z.of_nat i)).
  Proof.
    intros i Hi. rewrite ev_vals. change (6 + i)%nat with (length [sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] + i)%nat.
    rewrite app_nth2_plus. rewrite app_nth1 by (rewrite length_junk_vals; exact Hi).
    unfold junk_vals. rewrite (nth_map_seq (fun i => getr regs (Z_to_bv 5 (Z.of_nat i)))) by exact Hi. reflexivity.
  Qed.

  Lemma ev_38 : ev E 38 = a_hwcap.
  Proof.
    rewrite ev_vals. change 38%nat with (length [sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] + 32)%nat.
    rewrite app_nth2_plus. rewrite app_nth2 by (rewrite length_junk_vals; lia). rewrite length_junk_vals. reflexivity.
  Qed.

  Lemma ev_39 : ev E 39 = canary_w rdraw.
  Proof.
    rewrite ev_vals. change 39%nat with (length [sp0; p0 inp a0s path envv rdraw; p1 inp a0s path envv rdraw; auxvp inp sp0; rnd inp sp0 a0s path envv; tid] + 33)%nat.
    rewrite app_nth2_plus. rewrite app_nth2 by (rewrite length_junk_vals; lia). rewrite length_junk_vals. reflexivity.
  Qed.

  Lemma spx_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
  Proof. intros k. cbn [spx edenot]. rewrite alu_add. unfold v_add. change (ev E 0) with sp0.
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity. Qed.

End MainEntryProofs.

Section MainRegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable rdraw : ltac2:(zQ "10!hj2$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!lp9!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : ltac2:(zQ "30!h9!jc!r2>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : ltac2:(zQ "10!op2@1$0?3sp0").
  Hypothesis Htid : ltac2:(zQ "50!h9!opd!p6!mp9!oq2@2$3@2$1Z@2$2@1$0#k0?3tid@2$1@2$2@1$0#k0?3tid@2$4+2+h6").
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = envv.
  (* LPS-revision port: the encoded/old form held the pre-revision 7-argument
     main_entry sp0 av ev rdraw tid regs mem.  RefStartup.v:101 now reads
     main_entry inp mbase entry sp0 rnd tid regs mem, with av/ev off inp.  Written out
     rather than re-encoded (rule 11).  Shape donor, statement only:
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:94-110. *)
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.
  Let E := E0 inp sp0 a0s path envv rdraw tid regs.

  (* LPS-revision port: main_entry's register facts are now stated over the ProcInput --
     me_s1/me_a0 give `argcN inp` and me_a2/me_s3 `length (in_argv inp)`, where the
     pre-revision record gave them over `av`.  `Hargv : in_argv inp = av` is what closes the
     gap, so each of those four arms rewrites with it; the remaining arms are beast's text
     with one more underscore (main_entry gained an explicit argument).
     Donor, tactic text: a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:271-289.
     Found with the UNCLOSED-GOAL probe (rule 10), not by reading: the trailing `idtac`
     made every miss silent, and the goal it printed was `getr regs 9 = Z_to_bv 64 2`. *)
  Ltac reg_case :=
    cbn [nth sr_main all_regs];
          first [ unfold E; rewrite (spx_val inp sp0 a0s path envv rdraw tid regs)
                | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
                    change (edenot E (EVar n)) with (ev E n);
                    first [ rewrite (ev_junk inp sp0 a0s path envv rdraw tid regs (n - 6)) by lia; reflexivity | idtac ]
                  | |- _ => cbn [edenot] end ];
          first [ reflexivity
                | exact (me_ra _ _ _ _ _ _ _ _ ME) | exact (me_gp _ _ _ _ _ _ _ _ ME) | exact (me_tp _ _ _ _ _ _ _ _ ME)
                | exact (me_s2 _ _ _ _ _ _ _ _ ME)
                | rewrite (me_sp _ _ _ _ _ _ _ _ ME); apply bv_eq; rewrite !u_small by lia; lia
                | rewrite (me_s0 _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a1 _ _ _ _ _ _ _ _ ME); reflexivity
                | rewrite (me_a2 _ _ _ _ _ _ _ _ ME); rewrite ?Hargv; f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s3 _ _ _ _ _ _ _ _ ME); rewrite ?Hargv; f_equal; subst av; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul Pos.add]; lia
                | rewrite (me_s1 _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite ?Hargv; cbn [length Z.of_nat Pos.of_succ_nat]; reflexivity
                | rewrite (me_a0 _ _ _ _ _ _ _ _ ME); unfold argcN, len_word; rewrite ?Hargv; cbn [length Z.of_nat Pos.of_succ_nat]; reflexivity
                | apply (me_szero _ _ _ _ _ _ _ _ ME); cbn; tauto
                | fail 99 "UNCLOSED-GOAL" ].

  Theorem main_regs_ok : regs_ok E sr_main regs.
  Proof.
    pose proof (proj1 Hvsp) as Hlo. pose proof (proj1 (proj2 Hvsp)) as Hhi. unfold sp_window_lo, sp_window_hi in *.
    apply regs_ok_by_index.
    intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; reg_case.
  Qed.
End MainRegs.

Section KnowProofs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : ltac2:(zQ "30!l9!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable rdraw : ltac2:(zQ "10!hj2$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!h9!lp9!jc@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : ltac2:(zQ "30!h9!jc!r2>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Let av := [a0s; path].
  Hypothesis Hva : valid_argv av.
  Hypothesis Hve : ltac2:(zQ "10!oq8@1$0?4envv").
  Hypothesis Hvsp : ltac2:(zQ "10!op2@1$0?3sp0").
  Hypothesis Htid : ltac2:(zQ "50!h9!opd!p6!mp9!oq2@2$3@2$1Z@2$2@1$0#k0?3tid@2$1@2$2@1$0#k0?3tid@2$4+2+h6").
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = envv.
  (* LPS-revision port.  The revision's auxv_words takes the hwcap OFF THE ProcInput
     (`in_hwcap inp`), where the pre-revision one took the ambient `a_hwcap` directly, so
     the AT_HWCAP value bullet needs the same bridge Hargv/Hve' already give for argv and
     envp.  MEASURED: the UNCLOSED-AUXV probe in a farm round printed
       Some (word_to_le_bytes 8 (in_hwcap inp)) = Some (word_to_le_bytes 8 a_hwcap).
     IT IS NOT A PREMISE THE TOP CANNOT MEET: MainOpen and MainTop build their inp as
     `mkProcInputC [a0s; path] envv fs0 stdin0` (Amb.v:36-40), whose in_hwcap field IS
     a_hwcap, so there it is reflexivity -- the same discharge Hargv and Hve' get. *)
  Hypothesis Hhw : in_hwcap inp = a_hwcap.
  (* LPS-revision port: the encoded/old form held the pre-revision 7-argument
     main_entry sp0 av ev rdraw tid regs mem.  RefStartup.v:101 now reads
     main_entry inp mbase entry sp0 rnd tid regs mem, with av/ev off inp.  Written out
     rather than re-encoded (rule 11).  Shape donor, statement only:
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:94-110. *)
  Hypothesis ME : main_entry inp mbase entry sp0 rdraw tid regs mem.
  (* LPS-revision port.  The stack-reading helpers moved into RefLayout.v's Section Layout
     and ArgvEnv's, which thread the LAUNCH as well as the stack: their exported types, read
     off a farm round's arity probe rather than inferred, are
       read_argc_w    segs v inp mbase ph entry sp brk draw  Hvl Hlau Hhi
       read_argv_ptr_w segs v inp mbase ph entry sp brk draw Hva Hvl Hlau Hlo Hhi k Hk
       read_argv_null segs v inp mbase ph entry sp brk rdraw Hvl Hlau Hhi
       read_auxv_word segs v inp mbase ph entry sp brk rdraw Hvl Hlau Hhi j Hj
       lay_bsb_len         v inp mbase ph entry sp brk rdraw Hvl Hlau
       rnd_facts      segs v inp mbase ph entry sp brk rdraw Hvl Hlau Hlo Hhi Hal
     so this section gains `brk`, `Hvl : valid_launch inp` and `Hlau`.  It does NOT need a
     `v` or a `ph` variable: `v` is Sv48, which valid_input pins (conjunct 11 of 17 at
     75d69e00:Run.v:4590) and which RefStartup.v:167 already uses, and `ph` is RPH, which
     main_entry's own me_mem names (RefStartup.v:118).
     BOTH NEW HYPOTHESES ARE DISCHARGED BY THE LAYER ABOVE, so neither is a premise the top
     cannot meet: `valid_launch inp` is conjunct 13 of valid_input (75d69e00:Run.v:4592), and
     `entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp` is already a Hypothesis of
     this tree's own ref_startup (RefStartup.v:132). *)
  Variable brk : word.
  Hypothesis Hvl : valid_launch inp.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp0 brk mbase rdraw) inp.
  Let E := E0 inp sp0 a0s path envv rdraw tid regs.

  (* LPS-revision port.  These replays applied the pre-revision forms from inside the replay
     program; a KReplay blob is never re-encoded, so each is REPLACED BY AN EXPLICIT PROOF
     (rule 11).  Statement AND tactic text: boost-beast/http_request's
     proofs/lib/RefMainEntry.v:291-327
     -- the PLAIN-TEXT TWIN of this encoded file -- with the argument lists re-threaded to
     each definition's new generalisation set.  Nothing is taken from beast below :327. *)
  (* LPS-revision port.  The stack readers now state their argv premise over the
     ProcInput (`valid_argv (in_argv inp)`), where the pre-revision form took it over the
     section's `av`; `Hargv` is exactly the bridge (a farm round named this
     at line 415).  Stated once rather than inline at each use. *)
  Lemma kva : valid_argv (in_argv inp). Proof. rewrite Hargv. exact Hva. Qed.
  Lemma kp_lo : (0x7fff80000000 <= bv_unsigned sp0)%Z. Proof. exact (proj1 Hvsp). Qed.
  Lemma kp_hi : (bv_unsigned sp0 <= 0x800000000000)%Z. Proof. exact (proj1 (proj2 Hvsp)). Qed.
  Lemma kp_al : (bv_unsigned sp0 mod 16 = 0)%Z. Proof. exact (proj2 (proj2 Hvsp)). Qed.
  Lemma ke0 : ev E 0 = sp0. Proof. reflexivity. Qed.
  Lemma ke1 : ev E 1 = p0 inp a0s path envv rdraw. Proof. reflexivity. Qed.
  Lemma ke2 : ev E 2 = p1 inp a0s path envv rdraw. Proof. reflexivity. Qed.
  Lemma ke3 : ev E 3 = auxvp inp sp0. Proof. reflexivity. Qed.
  Lemma ke4 : ev E 4 = rnd inp sp0 a0s path envv. Proof. reflexivity. Qed.
  Lemma ke5 : ev E 5 = tid. Proof. reflexivity. Qed.
  Lemma ke38 : ev E 38 = a_hwcap. Proof. exact (ev_38 inp sp0 a0s path envv rdraw tid regs). Qed.
  Lemma ke39 : ev E 39 = canary_w rdraw. Proof. exact (ev_39 inp sp0 a0s path envv rdraw tid regs). Qed.

  (* LPS-revision port.  Replay replaced by an explicit proof (rule 11); the STATEMENT is
     untouched.  Tactic text: a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:329-364, the plain-text
     twin, with every argument list taken from the types the arity probe printed in
     a farm round -- not inferred.  v is Sv48 and ph is RPH, as explained
     at the Section header. *)
  Lemma know_stack : know_ok RSEGS E mem kn_stack.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    unfold kn_stack, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot]; rewrite ?ke0, ?ke1, ?ke2;
      unfold flat, estart; cbn [a_base a_off edenot]; rewrite ?ke0.
    - split; [lia | exact Hal].
    - lia.
    (* the KWr bullet's own range side: the window is now symbolic, so lia must be shown
       stack_window_reach and stack_max_size here too (a farm round put the
       first error at this line's `lia`, chars 14-17, after the window fix cleared the one
       below it).  Separate try-unfolds then a tactic that must close. *)
    - split; [try unfold stack_window_reach; try unfold stack_max_size; lia|]. intros d m Hd Hm.
      (* The lower bound moved with the revision: main_entry_store_ok_win now asks
         MemSplit.wok_lo sp0 <= bv_unsigned a, where the pre-revision form asked
         bv_unsigned sp0 - stack_max_size <= bv_unsigned a.  wok_lo is
         bv_unsigned sp0 + stack_window_reach - stack_max_size (MemSplit.v:137-138), so
         stack_window_reach has to be unfolded too or lia is handed a name it cannot see
         through and answers "Cannot find witness" -- which reads as an arithmetic failure
         about the node and is not one (a farm round, line 354 chars
         128-131, i.e. the trailing lia, counted against the line).
         Separate `try unfold`s followed by a tactic that MUST close, so a unfold that
         finds nothing cannot silently become the step. *)
      apply (main_entry_store_ok_win inp mbase entry sp0 rdraw tid regs mem ME);
        rewrite u_small by (try unfold stack_window_reach, stack_max_size in *; lia);
        try unfold MemSplit.wok_lo, stack_window_reach, stack_max_size in *; lia.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by lia.
      pose proof (read_argc_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hr. unfold wmem in Hr.
      rewrite Hr by (unfold sp_window_hi; lia).
      (* argcN is over the ProcInput at this revision, so the goal closes with Hargv
         rather than by reflexivity: a farm round printed
         Unable to unify "Some (word_to_le_bytes 8 (Z_to_bv 64 2))"
                    with "Some (word_to_le_bytes 8 (argcN inp))".
         Same move as reg_case's me_s1/me_a0 arms. *)
      rewrite n_to_le_8_spec. unfold argcN, len_word. rewrite Hargv.
      cbn [length Z.of_nat Pos.of_succ_nat]. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw kva Hvl Hlau
                    ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 0%nat
                    ltac:(rewrite Hargv; subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 0)) with 8%Z in Hr.
      (* read_argv_ptr_w's conclusion is over the ProcInput's own argv/envp at this
         revision, where p0 is stated over the section's av/ev
         (a farm round, line 424: p0 … vs cat_argv_ptr … (in_argv inp)
         (in_envp inp) …).  Hargv/Hve' are the bridge. *)
      rewrite Hargv, Hve' in Hr.
      rewrite Hr. unfold p0. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_ptr_w RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw kva Hvl Hlau
                    ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) 1%nat
                    ltac:(rewrite Hargv; subst av; cbn; lia)) as Hr.
      unfold wmem in Hr. rewrite w_add_nat in Hr. change (Z.of_nat (8 + 8 * 1)) with 16%Z in Hr.
      rewrite Hargv, Hve' in Hr.
      rewrite Hr. unfold p1. rewrite n_to_le_8_spec. reflexivity.
    - split; [lia|]. split; [lia|].
      unfold adenot. cbn [a_base a_off edenot]. rewrite ke0. unfold v_addi.
      rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; lia).
      pose proof (read_argv_null RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                    ltac:(unfold sp_window_hi; lia)) as Hr.
      rewrite w_add_nat in Hr. rewrite Hargv in Hr. subst av.
      change (Z.of_nat (8 + 8 * length [a0s; path])) with 24%Z in Hr.
      rewrite <- (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) in Hr by (try rewrite u_small by lia; lia).
      unfold wmem in Hr. rewrite n_to_le_8_spec in Hr. exact Hr.
  Qed.

  (* LPS-revision port.  Replays replaced by explicit proofs (rule 11); statement and
     tactic text from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:366-387, re-threaded.
     ONE STATEMENT CHANGE, and it is a STALE CONSTANT rather than a port artefact:
     auxvp_u's second conjunct read `auxv_off av envv + 160 <= 2240000`.  The 160 is the
     PRE-REVISION auxv size IN BYTES; at 75d69e00 the block is `auxv_size (kb_rseq …)`,
     16 * 27 or 16 * 29 (StackLayout.v:276-277).  Written parametrically, so kb_rseq -- one
     of recorded_kernel's five FREE fields -- is never pinned.  The bound 2240000 is
     unchanged and has ~2.2e6 of slack, so no consumer loses anything.  auxvp_u is
     file-private to KnowProofs, nothing published is touched, and no hypothesis is
     strengthened.  UNIT: BYTES. *)
  Lemma auxvp_eq : auxvp inp sp0 = Z_to_bv 64 (bv_unsigned sp0 + Z.of_nat (auxv_off av envv)).
  Proof. unfold auxvp, auxv_w, auxv_off. rewrite Hargv, Hve'. subst av. cbn [length]. f_equal. lia. Qed.

  Lemma auxvp_u : bv_unsigned (auxvp inp sp0) = (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
    /\ (Z.of_nat (auxv_off av envv) + Z.of_nat (auxv_size (kb_rseq (in_kernel inp))) <= 2240000)%Z.
  Proof.
    pose proof kp_lo. pose proof kp_hi.
    (* Helper arities read off the arity probe (a farm round), not inferred:
         auxv_off_bound inp mbase ph entry sp brk rdraw
         lay_bsb_len  v inp mbase ph entry sp brk rdraw Hvl Hlau
       and both conclusions are now stated over the ProcInput's own argv/envp, so Hargv and
       Hve' bridge them to this section's av/envv. *)
    pose proof (auxv_off_bound inp mbase RPH entry sp0 brk rdraw) as Hb.
    pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hl.
    rewrite Hargv, Hve' in Hb.
    rewrite auxvp_eq. rewrite u_small by lia. lia.
  Qed.

  (* LPS-revision port.  `rnd` is this section's name for the AT_RANDOM pointer and
     rnd_facts now states every one of its facts over `in_argv inp` / `in_envp inp`;
     the bridge is stated once here rather than at each use. *)
  Lemma krnd : rnd inp sp0 a0s path envv
    = at_random_ptr sp0 (kb_rseq (in_kernel inp)) (in_argv inp) (in_envp inp).
  Proof. unfold rnd. rewrite Hargv, Hve'. subst av. reflexivity. Qed.

  Lemma rnd_u : (bv_unsigned sp0 <= bv_unsigned (rnd inp sp0 a0s path envv))%Z
    /\ (bv_unsigned (rnd inp sp0 a0s path envv) + 16 <= bv_unsigned sp0 + 2240000)%Z
    /\ (bv_unsigned (rnd inp sp0 a0s path envv) mod 8 = 0)%Z.
  Proof.
    pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hl.
    destruct (rnd_facts RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) kp_al)
      as (A & B & C & D & F).
    rewrite krnd. repeat split; try assumption; try lia.
  Qed.

  (* LPS-revision port, MIRROR of the farm-GREEN plain twin in this unit's own
     RefMainEntry.v.  The encoded statement here is the same one, decoded symbol by
     symbol there: `forall j, j < 20 -> rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp sp0
     a0s path envv) + 8 * Z.of_nat j)) 8 = Some (word_to_le_bytes 8 (nth j (auxv_words RPH
     (rnd sp0 a0s path envv) a_uid a_hwcap) (Z_to_bv 64 0)))`.  A CDef blob is never
     re-encoded, so it is written out (rule 11).  Two things moved, both read off the
     the arity probe a farm round: auxvp takes the ProcInput, and auxv_words
     takes a LaunchAuxv and eight arguments (RefLayout.v:110).  The word list is spelled
     exactly as read_auxv_word's own conclusion spells it (RefLayout.v:354).
     THE BOUND GOES 20 -> 50, a WIDENING: the revision's table puts the slots kn_auxv
     claims as far out as word 49, and 50 is still a sound instance of
     `j < 2 * auxv_count (kb_rseq (in_kernel inp))` (54 or 58), discharged below from
     kb_rseq's own case split, so kb_rseq stays free.  UNIT: WORDS for j. *)
  Lemma auxv_word_at : forall j, (j < 50)%nat ->
    rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j)) 8
    = Some (word_to_le_bytes 8
        (nth j (auxv_words (launch_auxv inp sp0 mbase) RPH entry (in_uid inp) (in_gid inp)
                  (in_hwcap inp) (rnd inp sp0 a0s path envv)
                  (at_execfn_ptr (ed_top rdraw) (in_execfn inp)))
           (Z_to_bv 64 0))).
  Proof.
    intros j Hj. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    destruct auxvp_u as [Hu Hb].
    rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME)
      by (rewrite u_small by lia; lia).
    pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw. unfold wmem in Hw.
    rewrite Hw by (rewrite u_small by lia; lia).
    replace (Z_to_bv 64 (bv_unsigned (auxvp inp sp0) + 8 * Z.of_nat j))
      with (sp0 + nat_to_word (auxv_off (in_argv inp) (in_envp inp) + 8 * j))
      by (rewrite Hargv, Hve'; rewrite w_add_nat; f_equal; lia).
    rewrite (read_auxv_word RSEGS Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
               ltac:(unfold sp_window_hi; lia) j
               ltac:(unfold auxv_count; destruct (kb_rseq (in_kernel inp)); cbn; lia)).
    rewrite krnd. rewrite n_to_le_8_spec. reflexivity.
  Qed.

  (* The auxv list the revision builds is a literal 26-pair cons list followed by an
     la_rseq-dependent tail and AT_NULL, so `nth j` reduces through the literal prefix
     for every j this file claims (max 49) WITHOUT touching the rseq branch -- which is
     why kb_rseq stays free.  The cbn list has to name auxv_entries, app and flat_map,
     not just nth, or nothing reduces at all. *)
  Ltac kw_auxv j :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; rewrite ke3; unfold v_addi;
    lazymatch goal with |- rdn _ _ (Z_to_bv 64 (?u + ?k)) 8 = _ =>
      replace k with (8 * Z.of_nat j)%Z by reflexivity end;
    rewrite (auxv_word_at j) by lia;
    cbn [auxv_words auxv_entries flat_map app nth fst snd];
    rewrite ?ke38, ?Hhw;
    reflexivity.

  (* LPS-revision port, MIRROR of the farm-GREEN plain twin.  Same series as know_stack
     (rule 11g).  Statement unchanged; tactic text from
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:411-425, re-threaded,
     with the bullet indices moved onto the revision's auxv table.  The two KDisj entries
     now carry the window symbolically, so the names are unfolded IN HYPOTHESES TOO
     before lia. *)
  Lemma know_auxv : know_ok RSEGS E mem kn_auxv.
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof kp_al as Hal.
    destruct auxvp_u as [Hau Hab]. destruct rnd_u as (Hr1 & Hr2 & Hr3).
    unfold kn_auxv, know_ok.
    repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok a_base a_off edenot];
      rewrite ?ke0, ?ke3, ?ke4, ?ke38;
      unfold flat, estart, elenZ; cbn [a_base a_off edenot]; rewrite ?ke0, ?ke3, ?ke4, ?ke38;
      try rewrite Hau;
      try (unfold stack_window_reach, stack_max_size in *; lia);
      try lia.
    - split; [lia|].
      destruct (proj1 (Z.mod_divide (bv_unsigned sp0) 16 ltac:(lia)) Hal) as [q Hq].
      replace (bv_unsigned sp0 + Z.of_nat (auxv_off av envv))%Z
        with ((2 * q + 5 + Z.of_nat (length envv)) * 8)%Z
        by (unfold auxv_off; subst av; cbn [length]; lia).
      apply Z_mod_mult.
    - kw_auxv 20%nat. - kw_auxv 21%nat. - kw_auxv 22%nat. - kw_auxv 23%nat.
    - kw_auxv 26%nat. - kw_auxv 27%nat. - kw_auxv 28%nat. - kw_auxv 29%nat.
    - kw_auxv 30%nat. - kw_auxv 31%nat. - kw_auxv 38%nat. - kw_auxv 40%nat.
    - kw_auxv 46%nat. - kw_auxv 47%nat. - kw_auxv 48%nat. - kw_auxv 49%nat.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_auxvp : forall segs,
    rdn segs (D_main inp sp0 rdraw tid) (Z_to_bv 64 0x12ee90) 8
    = Some (word_to_le_bytes 8 (auxvp inp sp0)).
  (* LPS-revision port, MIRROR of the farm-GREEN plain twin.  The replay applied
     `envp_w sp0 av`, and RefStartupDefs.v's Section Defs now exports envp_w/auxv_w over
     the ProcInput.  Written out (rule 11); tactic text from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:434-439, with auxv_w in
     the unfold list because auxvp is one indirection deeper here, and with D_cxx -- THIS
     TREE'S NAME; beast says D_cx and boost-json declares no such thing (RefStartupDefs.v
     :181, :191).  The statement, 0x12ee90 included, is untouched. *)
  Proof.
    intros segs. pose proof (u64_range tid). pose proof kp_lo. pose proof kp_hi.
    unfold auxvp, auxv_w, D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.

  (* [comment removed for export] *)

  Lemma wseg_data : ltac2:(zQ "e0!nsd!qb!rb!nt3!nt9!ntf!n4!nv8!ohc!h9!omb!np1!htf!or5@3$6$1@3$a$b@2$c@1$9#k0+vsgg0@1$7@1$8@1$d@1$4@1$0@1$0@1$0$5$2").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntry ()) ["KnowProofs"] "##+7p'0h01Hh11eh21xi001cp;1p;2p;3p;6p;5g004Lj12Tg0051j1<Tg007Ij11Tg00;kj14Tg00OMj2CTg03cTj13Tg03d6j1;!s/$Xj1:Tg03e:j17!s/$Wj16Tg00Khj28!sw$nj29Tg03f6j3ETg00@^j35Tg01DDj6DTg03gHj2BTg00>@j1?!s/$`j2>Tg00<Ij2=Tg008Xj2@!sS$gj5ATf0R0#2#2p=0g033jR1g00lmR2#2R3#2#0#0R4#<R5%12#1!s$&0!s$04'CR2g03i8#3!s$$;#:#7#6R6g00gdR7g00hDR8'81952R2=E16=578dg03iZR8g03j@R7g03jfR135P8P7P8p-0P0g02BS!sg$oUP7n011000003!s+$0X18g0162P1P0EDP71B70b0W2%?6,>2%43%44'='@dDAo"). Qed.   (* [comment removed for export] *)

  Lemma range_disjoint_sub : ltac2:(zQ "a0!s2!qb!kta!rb!n4!on6!mpf!p1!oob!lma>2lo$0>1n$2>1c@2$8$0$2>1i$0>0@3$4$1@3$5^4^3^2$3>0@2$7^5^2>0@2$7@2$6^3+1@2$6^6@1$9^5@3$4$1@3$5^4N1^5$3").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntry ()) ["KnowProofs"] "##Eyp'0h01Hh12b1h22b2h35lemmah41xh52H0h62Hah74__x1h84__x2h94__x3h:4__x4h;4__x5h<1ih=1ni001nh>1yh?1Ah@1BhA3HhihB3HlohC7__arithhD4__ffhE6__sat1hF!s/%2hG8__varmaphH5__withI1chJ2c0hK4cstrhL5cstr0hM2lohN1mhO1wi011pi021zp&0p;2p;3p;1p;4p;8p;<p;6p;=p;7p;;p;Bg03UBR0k202Tg00A8j3ATg008XR1j20Tg00;kj1ITg00>`R2j21!s1$@R3j13Tg0094j1?Tg00^Aj4MTg03kLj2<Tg00[QR4j24!s:$ij2\Tg00?=j26Tg03lIR5j2>!s1$bj4BTg000Sj4yTg03mIj2sTg03n6R6j2p!s1$Tj4kTg03o6j8G!s/$ij3eTg00Cfj2CTg00DFj1_!s/$dj4^Tg00Khj27Tg00aol<ZTg00f2j3Y!s/$Xj6XTg012Xj1LTg004Lj1JTg007Ij1KTg00Enk20!ui$FVj2WTg00<Ik20!v8$G2j3~Tg01<3j2;Tg01=Ej3=!s/$nj2U!sJ$Vj1{Tg00Vkj3TTg0062j1xTg00XXj1wTg00H6j2RTg01>Zj4E!s8$Tj1rTg00I2j1o!s/$]j2:Tg00J@j2nTg00bTj3HTg00@<j1j!ub$Fj2iTg00LBj2l!s/$nj3mTg00MMj4hTg00Y6j4g!wu$aj3fTg00_>j3q!sn$^j3STg040_j4tTg041Rl=dj7uTg042Al;vTg00`dl<c!vp$IlBbTg00c7j4z!s/$bj7aTg00g@j7|Tg002oj8}!s8$dR7f0R8g00hDR93Sp=2p-0R:f1R;P5P8CBp=DP:f4R<P5P5f3R=f2R>P;P8GGp=Q16;8=S79p=5P:P5P;P8Ctp=@P8P;P4g043<R?P>g00kfR@P=P<f5RAf6RBf7RCf8RDf9REM=dp=VP:!si$5P8P5P6g043mGGp=`P=P>P4P?P;P@P8Fup=PP:PCP5PBP4PAP<!sG$;P8M;vp=Ng00i`R4g00iBR?P?P?P3P3!sN0<cp=]!s@$!s$'2!u#$>P2P=P<PAPBPCPDPEMBbp=[P?P;g00k?P8Czp=9!s4$2PR2g00j?R3P3g00j_RFP8P@Fap=8!sp$3P3PFP;P8F|p=OP=!s9+!v]%}p=F202?4P0P?P4AA<=;#210A;g00lmR0#IR2,1>R@%3A,1BRG'0g00nRRH#?RI=A=<#2[[[^<?P8P?P4P>P;CM9ACB#210D;%3D,1ERJ,0@g00<fR@1<;8#2%2>RK%2;RL'4RM[RN%28,4L1<>;#2RL[RO%2=/4K\L1\;8RLP;n20010!s#$12!s-%0X27X17PN^27^17P8f;RKf:RP#3RQ'1/6BRR16GKRGP=O3%2R%2G'4P@PNPO1<=>#2\MPLP8!t%>O!t%'%3IRO,1BRL/6DRM%3C,1DRN/6B%2M10LD'>P:^@:RM^?:R@P:\:!yb'CBRG'DRR!s6&!s>%6CyRSCBRT,DMRUPM1s:5RVPGPT!zA+VP5PSP:P51p8;X>:X4:g044^CkGGDQRS11CORW/5E10WEP815JCRWPWg045T9e:5RX/@WM:VW31CLDf=RLf<#3'1RY/5D10YDRZ'>P@P!tg'6CBR6,DMR5PMPVPGP6%`VDQRVf>RG%3L'1R@!t<$@ER@!t>$GR[P[1@X[!t4&YDP;O215NL,4Z10JC,>WPMPTPM\:RTPRPUPSCP11DORS/0PRU1@XU%3E,1PRE!tc$EDRWP8GNW31CJC10JGRC,>[PMP6PTPRP5PVCPf?RV%3GR5'1/0PRR1@XR15EV10EV!sc+GP8O214@C14UWRC11D2R@/0PRJ/4WPUPWPJPW!}-$1P8X4?RJP110;8#_X>?X4?PSP@PJ!s$$?P?g00o111;8C^,7?XN?X=?PDPD17?DPOP2PJPJ%38,7?X44PIP217?2E]M:[PPPP17?PM<Z17:W9YWWEX%LGg00hdRG/05%LP10GQ%J0RQ#IRW%KQR:#K#J#IRJ+011WGW10GJ200WJRD,WG[[10GWR@g00oURSA~WJ;UW610GD\S^6@g0101R@%?IRS#?RD,;?1;?SRS1;?H5=?5=?g01KXRH'U%?!sE&I9=?S5=?/UH%{@5T@3T%x@P?P?%w?R@P>1R?ACEP;P?1R?<P=P@CECE%r?%o?R@1:?0RH1n?25H?RS1:?:R:%K0R0#J,:?5H?RD'9,8@%j3R3P@19:H,8@P3P@1:?QRQ,9D,8!sm$9H?QR0/9:,8@5O@P319SQ,8@190H!s9%CFCFCF1i@FP8P>17791l8>#2dAm?G;ChbDbGbHX7?X8?X9?X:?X;?118211=<RG'010<;11AB/0=10GA'411=2/0<11<A/0='4[[[^7?^8?^9?^:?^;?P8fC#3fD!}P$LPPPKPAO8bCbEbFbLbKCgPCeb0O2b0O2O3b5b0b511=OP?!#8q$CMR<9f?4RA'6Aq?4<#3,1A/6='<#2eAA=I<#2eWAWBW0X<?XO4XI?P;P8O2n2001101000121102100WJX=4XM?o"). Qed.

  Lemma missb_sub : ltac2:(zQ "90!qb!rb!n4!s2!hsf!mpf!p1!kta!lma>2lo$3>1n$7>1i$3>0@3$2$0@2$4^3^2$1>0@2$6^4^2>0@2$6@2$5^3+1@2$5^5@1$8^4@3$2$0@2$4^4N1$1").
Proof.
ltac2:(KReplay.run1z (kr_t_RefMainEntry ()) ["KnowProofs"] "##G'h01Hh14__x1h24__x2h31xh41nh51mh67__arithh74__ffh86__sat4h9!s/%5h:8__varmaph;5__with<4__x3h=2b1h>2b2h?4cstrh@1AhA2H0hB2H2hC2H3hD2HahE1fhF1lhG2H1hH2HchI3HhihJ3HlohK1chL1ihM2lohN1yp;2p;1p;3p;6p;4p;7p;<p;8p;Bg009Sj2RTg008XR0j22Tg00;kj1CTg00>`R1j21!s1$@R2j13Tg00=bj24Tg00<fR3j2?!s:$Aj2\Tg03UBj2ZTg004Lj1;Tg007Ij1>Tg00?=j26Tg0094j1QTg00Cfj2gTg0062j1OTg046Dj3ATg02:\j3I!s8$`j3MTg00A8j2Ej3LTg01gPj6[Tg012Xj1DTg00Enj2YTg00FVj2K!tl$Ij2XTg00G2j3W!s/$Vj1VTg00H6j2JTg00XXj1UTg01>Zj4@!sA$Tj1TTg00I2j1S!s/$]j2BTg00@<j1rTg00KFj2q!s/$hj2<Tg00LBj2p!s/$nj3oTg00MMj4lTg00J@j2HTg00bTj3GTg047Cj7hTg01<3j2FTg01=Ej3P!s/$nj2fTg00Vkj3eTg02O9j4NTg00DFj1b!s/$dj4cTg00aol<`Tg00Y6j4i!tp$^j3_Tg00c7j4j!s/$bj7kTg002oj8^Tg00`dl<m!se$IlBnTg00gdR4f0R5g00hDR63_p=0f2R7f1R8/E5g048XR93Ap=!sI$dR:/65p=8%;5#;p=:12:5p=9AA859p=]P7g002PR;g00j?R<P<g00j_R=g00iBR>P8g00k?P5Cjg00kfFkp=7f3R?P;P<P<P=P7P8P5G^p=!sY$`R;P>!s$$2P2f5R2f4R@P?!sL%M<mp=d!sF&!s$%1P5P8P7P1P?P@P2f6R1f7RAf8RBf9RCMBnp=a1R78#012?8g00lmRD#CRE,17RF%3?,1@'2P31485#0%07RG%08RH'?RI[RJ%05,?H1478#0RH[RK%0?/?G\H1\85RHP8n20010!s#$12!s-%0X>4X=4RGPJ^>4^=4RLP51Z>;RM?512%81RN'4RO%32,11%;DR2#;RP#>#>#;#:#>#:!s$-CRQ'6RRP?O3%0O%0R'?P3A5MA1%8A'4#0%31,1A/6Q#0g00nRRA#QRR95M1/4N%3RRN,11/6Q'4#0P5A5MCB%8C'4#0f:RB%3C'1!sc$PGPLP5f<RLf;55MRG%8LROP7O3%0G%0O'?P3f=RG=5ML#0%8G#0A5MLR/4O11LN!t0+f?f>55M#0f@#8#0P31685#01278RL[RO1285RG16!vq$S[RT12?7\S1g85RS!vo:5>X4>RUPO^5>^4>RVP5P:fBRWP8O3%9WPUPVP5fDRVfC#3'1RUPQPCO312UQP3PJPK14?7#0\IPHP5!wz>HPK!wz&K!vJ$VR%8V'4RI11VN/6QRV%0I%0VPHPKP5fERK=5MRRH%8KRV%0H%0Vg049jp4p710RVP4\5RH%O8RIP3AA785#0AI@57P@P8O1#0[^3?RJ[AI?58P?!s:+7AA?78#0[RUAA@!u1$JAM785!u49WFWEW@PU^FI^EH^@VP5PMfFRV/ERP9AIM59RHfJRIfIRUP8fHRJ1EIUR@,]M#0fMRWfLRX;L8#0\H^3M[fKRY=LX!s6'A5MYI#0[AMM@9PBP8P5E[%DURB%3U#9R@%C2R9%>2!{%$CRH'YRZ1K:9%9H1X9HR[,K:[[R\%99R]g00oUR^AW9H8UWDRH%9[\^^D]R]g0101R^#VR[%O^R9P>1J>7R_P8%U>R`C@%T>Ra%S>Rb1B>DRc1B>2R257bRd%r<R<PdC=1qb=R=P5P71<461p57#0dAo>:8ClR6b7b:b;X1>X2>12581287[^1>^2>P5PXfNR4PIO3b6b8b9b?PBP@PZP\PHP]P[P9P>P_P81J>?R@C@PaPb1H>E9G>cRB%>D,B>RD9G>!ta$2P<P2C=P=P!tD0X<>115E1187'2R2118E117?Rd'2!tW&^<>P5%3WP4PXPUO4!t['FhWHXKMO4b0P3POPT16!y2$LPS!{=:!|H%SPT!|H&TP5P:PVfGRL#D%3L#9!uS'%QR,F>1F>R1F>A5P>5P>g01KX'f=e^[R!ur%`P8P_!un%A7bDcP<!uw$:R:=7bDP<A7b:cC=!uk5%97R7P7[\G!w2,PIPJPC!uU,O3b0CNO3b0PSPTP511KNRTPQ12TQRS11KERC/2QP>P>P0P5X3>RJP0%bGXN>X3>PTPCPJ!s$$>P>g00o11185Cc,<>!v#%PKPK1<>KPNPEPJPJ%35,<>X3;PRPE1<>EEdM:aPQPQ1<>QM<`%DV%3V!vC,!xp&>P@P?P`C@!v+,1B>P9G>DRD97bB!v5&QRP9!v5'BP!v57X<>12dQ12FQ[\2!xl0IPYPUPVP1O5!v?'CiPSe!vD,bCb0bBb0WBWGP8P5O2!xr0!s/&b0bAWCW0!sHA1R?R#0eWIWJW0XL>X4;XM>o"). Qed.

  (* [comment removed for export] *)
  Lemma kimg_ok : forall lo hi, D_main_missb lo (Z.to_nat (hi - lo)) = true -> (lo <= hi)%Z -> (hi <= 0x131000)%Z ->
    kentry_ok RSEGS E mem (KImg lo hi).
  (* LPS-revision port, MIRROR of the farm-GREEN plain twin.  The replay applied
     `D_main sp0 av envv a_hwcap rdraw tid`, the pre-revision 6-argument form, and
     RefStartupDefs.v:191 now reads `D_main inp sp0 rdraw tid`.  Written out (rule 11);
     tactic text from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:465-474, re-threaded to
     this file's OWN already-ported D_main_none (whose argv premise is over
     `in_argv inp`, hence kva) and to RefStartup.v:351's main_entry_mem_data.
     The statement, including the 0x131000 bound -- this image's own, not the plain
     twin's 0x12d000 -- is untouched. *)
  Proof.
    intros lo hi Hb Hle Hhi. pose proof kp_lo as HLO. pose proof kp_hi as HHI.
    assert (Hlo0 : (0 <= lo)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb _].
      apply andb_true_iff in Hb as [_ Hb]. apply Z.leb_le in Hb. exact Hb. }
    cbn [kentry_ok]. split; [lia|]. split; [lia|]. intros i Hi.
    rewrite (main_entry_mem_data inp mbase entry sp0 rdraw tid regs mem ME)
      by (rewrite u_small by lia; unfold stack_max_size; lia).
    apply (D_main_none inp sp0 rdraw tid i kva); [lia | lia |].
    apply (missb_sub lo (Z.to_nat (hi - lo))); [exact Hb | lia | rewrite Z2Nat.id by lia; lia].
  Qed.

  Ltac kimg := apply kimg_ok; [vm_compute; reflexivity | lia | lia].

  Ltac kw_pre :=
    split; [lia|]; split; [lia|];
    unfold adenot; cbn [a_base a_off edenot]; unfold v_addi; rewrite u_small by lia; rewrite Z.add_0_l.
  Ltac kw_data L :=
    kw_pre;
    rewrite (main_entry_rdn_data inp mbase entry sp0 rdraw tid regs mem ME) by (rewrite u_small by lia; unfold stack_max_size; lia);
    rewrite (L RSEGS); try reflexivity.
  Ltac kw_mem L := kw_pre; rewrite (L RSEGS); try reflexivity.

  Lemma know_image : know_ok RSEGS E mem kn_image.
  (* LPS-revision port.  The replay applies `D_main sp0 av envv a_hwcap rdraw tid`, the
     pre-revision form.  Written out (rule 11), shape from the plain-text twin
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:487-507.  ONLY the
     leading tactic is ported: kn_image is a different list in every image, and THIS
     file's addresses are the Ubsan ones, not the plain twin's -- so the bullets come
     from rule 3o-FINAL's one-round all-goals probe rather than from either donor.
     The nine goals are the ones the probe printed in a farm round, in
     order, at the UBSAN image's OWN addresses (RULE 22 -- the plain twin's are different
     and are not used): 1032192 .. +217088 the writable image window (0xfc000, 0x35000,
     hi 0x131000, which is kimg_ok's bound); 1108784 D_main_self; 1108816 tid;
     1108968 canary; 1240120 guard; 1240720 auxvp (= D_main_auxvp's 0x12ee90);
     1240760 pagesize; 1240816 hwcap; then tid's range.  wseg_data's own encoded literals
     agree: +vsgg0 = 0xfc000 and +jlgg0 = 0x35000. *)
  Proof.
    pose proof kp_lo as Hlo. pose proof kp_hi as Hhi. pose proof (u64_range tid) as Ht.
    unfold kn_image, know_ok.
    repeat apply Forall_cons; try apply Forall_nil;
      try kimg;
      cbn [kentry_ok a_base a_off edenot]; rewrite ?ke3, ?ke5, ?ke38, ?ke39;
      unfold flat, estart, elenZ; cbn [a_base a_off edenot];
      rewrite ?(u_small 0) by lia; cbn [Z.add].
    - split; [lia|]. intros d m Hd Hm.
      eapply (store_ok_window RSEGS mem (Z_to_bv 64 0xfc000) (Z_to_bv 64 (0xfc000 + d))
                0x35000 m 0xfc000 0x131000);
        [reflexivity | reflexivity | cbn; lia | apply wseg_data
        | rewrite u_small by lia; lia | rewrite u_small by lia; lia].
    - kw_data (D_main_self inp sp0 rdraw tid).
    - kw_mem (main_entry_tid inp mbase entry sp0 rdraw tid Hlo regs mem ME).
    - kw_data (D_main_canary inp sp0 rdraw tid); rewrite ?ke39; reflexivity.
    - kw_mem (main_entry_guard inp mbase entry sp0 rdraw tid Hlo regs mem ME);
        rewrite ?ke39, ?(canary_bytes_w rdraw); reflexivity.
    - kw_data D_main_auxvp.
    - kw_data (D_main_pagesize inp sp0 rdraw tid kva).
      (* LPS-revision: the hwcap cell now holds `in_hwcap inp`, where kn_image claims the
         ambient a_hwcap.  Hhw. *)
    - kw_data (D_main_hwcap inp sp0 rdraw tid); rewrite ?Hhw; reflexivity.
    - lia.
  Qed.


  Theorem main_know_ok : know_ok RSEGS E mem kn_main.
Proof.
ltac2:(KReplay.run1 (kr_t_RefMainEntry ()) ["KnowProofs"] "h01Ah11Hh21Ph32l1h42l2p;1p;3p;2p;4g0062j14Tg01THj31Tg04TRj30Tg00<fR0j22Tg04U3j47Tg02G6j36Tg02O9j43Tg02mij45Tg04URp4p710R1f0R2p-0[R3f1R4#4R5f2R6#4R7P0f3R0A1042706f4R8?006A0804'2R9[A0064A0062'2A18649080[R:f5R;A1;06708\9P0P6P4P2C7P2n2001000000120000000W4W3W2W0R4P:^47^35^23^01R1P2g031[R3g033jR5p,1ER7p,3memR:36R6g03=1R0g03ZZR9g04SGR8513R;A0360A036;g04UoP4P1P2P3P6P9P8A0369A0368g04W<g04XHC3O5b1C3O5b1P5P7P:g04YUC5eo"). Qed.

  (* [comment removed for export] *)
  Lemma main_str : forall k, (k < 2)%nat ->
    rdn RSEGS mem (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) (length (nth k av []) + 1) = Some (nth k av [] ++ [Z_to_bv 8 0])
    /\ (bv_unsigned sp0 <= bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k))%Z
    /\ (bv_unsigned (cat_argv_ptr (ed_top rdraw) av envv (in_execfn inp) k) <= bv_unsigned sp0 + 2107576)%Z   (* [comment removed for export] *)
    /\ (Z.of_nat (length (nth k av [])) <= 131071)%Z.
  (* LPS-revision port, MIRROR of the farm-GREEN plain twin.  Written out (rule 11);
     tactic text from a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:521-538, with all seven
     helper argument lists read off the the arity probe a farm round.  They
     do not share a prefix: argv_ptr_bounds_at takes no ph and no entry, struct_av_bound
     no launch hypotheses, argv_str_len only inp and its argv premise.
     THE BRIDGE GOES ON THE GOAL, not on the hypotheses -- `rewrite ?H in H1, H2, …`
     leaves them untouched, which cost two rounds on the plain twin.  The statement, with
     its 2107576 and 131071, is untouched. *)
  Proof.
    intros k Hk. pose proof kp_lo as Hlo. pose proof kp_hi as Hhi.
    assert (Hk' : (k < length (in_argv inp))%nat) by (rewrite Hargv; subst av; cbn; lia).
    pose proof (lay_bsb_nw Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                  ltac:(unfold sp_window_hi; lia)) as Hnw.
    destruct (argv_ptr_bounds_at Sv48 inp mbase sp0 brk rdraw Hlau k Hk') as [B1 B2].
    pose proof (u_cat_argv_ptr Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau
                  ltac:(unfold sp_window_lo; lia) ltac:(unfold sp_window_hi; lia) k Hk') as Hu.
    pose proof (struct_av_bound inp mbase RPH entry sp0 brk rdraw) as Hsb.
    pose proof (total_arg_bytes_firstn_le k (in_argv inp)) as Hf.
    pose proof (argv_str_len inp kva k Hk') as Hlen.
    pose proof (read_argv_cstr_k Sv48 RSEGS inp mbase RPH entry sp0 brk rdraw k Hlau Hk') as Hr.
    rewrite <- Hargv, <- Hve'.
    repeat split.
    (* The first side goal is B1's statement; after the goal-side bridge `lia` fires,
       and before it only `exact B1` could -- so both branches are load-bearing
       (measured on the plain twin, a farm round). *)
    - rewrite (main_entry_rdn_above inp mbase entry sp0 rdraw tid regs mem ME)
        by (first [ exact B1 | lia ]).
      pose proof (rdn_wmem_stack RSEGS inp mbase RPH entry sp0 rdraw) as Hw.
      unfold wmem in Hw. rewrite Hw by lia.
      exact Hr.
    - exact B1.
      (* The span bullet needs the stack image's LENGTH bound: lay_bsb_len
         (RefLayout.v:387, length <= 2101782), which with Hu, Hsb and Hf gives
         cat_argv_ptr <= sp0 + 2101782 <= sp0 + 2107576. *)
    - pose proof (lay_bsb_len Sv48 inp mbase RPH entry sp0 brk rdraw Hvl Hlau) as Hl. lia.
    - exact Hlen.
  Qed.
End KnowProofs.
(* [comment removed for export] *)
