(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb
  PropExec CatExec StepTac StoreOk StartupTac ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  MemSplit ZStores RefLayout RefStartupDefs RefStartupFacts RefStartup LibDiagKn.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_LibDiagKnMain () := KReplay.lz_vm "##b|K47Corelib7Numbers7BinNums8positive01!sKG2!sK=1N02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC79OSSVerify6Proofs:boost_json:fuzz_parse3lib?RefStartupFactsDmain_entry_rdn_imageC13~~~I!tl@2bv00I!uU+4Init9Datatypes4list!sF>6op!sl#00!uyA7Z_to_bvK!snC2!t825Logic2eq!tr?prod00!v]P9LibDiagKn7cell_ok!vJ%!to<3nat!xu@Z!sD/!vd81!sFB!y]B9bv_eq_dec!sN';!s]#_basic!si%!s7%!sK&3!sK%!vx&=!s,%!sC24base:decide_relK!wD;!u2-5Lists7!s+#Def6Forall!sGE2!wfZ8!wf#s!wg+!|3`<D_!|5$missb!svV8PropExec3rdn!yGB!zT%1C4ELinuxProcessSemantics?!s<2>Riscv!sE+@word!|B#le_bytes!|HD1!xB'9!x=$able;bool_!xL%!sD5E!sD-!y,#true_1C!xp78eq_ind_r!}:=!ss#00K!sFA1!w4/!w,96!#4g#s5Plain1M?loaded_segments!#5$&!}=>!#3/<!}z$0!}z@!#8\G3!#3+@1!{PZ:diag_!{U$!zZV!sn,9pf1!sm\>!|A,Defs8canary_w!sq&!#:]:3pow!#:z=t!#7}73an!#7^R!tm2<!tm&!|1$!#3#e@!#<4,guard!szf>!tr/!vg+!v-76!|u%!#8U@C!#<9%_!#?<-!#4sW9u64_ran!#>f&K!wj<!{8[6CANARY!vcV3Amb7a_hwcap!{+e6!#8F$!sofenvp!x2+!soO7Cat!w;#6w!zj[!tY3auxv!tYX!so24pn!smg:progname!#32C6of_nat!#3R<add!#9}8iff_reflC4!sa&9micromega;ZifyClasses3inj!t+<>pow_pos_nonneg!sN<:!sN#!sJ%K!t=56VarMap1t01I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PExpr07!uo65Tauto8B!sm&!sH6:Z!t;+=Z!sT$CheckerC!u0<4f!#46#!sq?C!sq0_sound!u8E1C8!yyN=Sym!|C#2S!t+#4SX2S7u_small!#6E7!#AL,length!}YXD!sb%_N!#B^-!t>%!#Kd8or!x'8!xt,2!v7E!#GEP8MemSplit>!#3U$_outside!#=<BsubK!zOC5Psatz!u&8!sO86K!y>@;!tR%!uH$!s{8!vE,3!vEE4!vEP:!#4Q+C!#=p,mem_data!#5Kd3rb!#9L&!u15!#4A-5mkapp!sKB6!sK$2!sqE!#Nh#!vIC3!x/D!#4%'1!sQ6!#3^%G!sJ'4!sJF5!u1B;rew_!#7k$v!v&Ceq!sP#!sLB8or_morph!tkF3!sJF6!sJF8!#7';5eKind!#M:<unit!#307!se%4kind!wR8!w}13Op2!#KJ=!t5%!smJ!wx78!w##Inst7Inj_Z_Z!#5L74True!#:~7!~[;0!#3/M!#S>K5State>stack_max_siz!#_0P7MmapSimB!sj1_va!#9[%c!stO=!#F{'MainE!#3|,none_belo!#AV%".
Local Ltac2 zQ s := CDef.cdeft "69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~08cells_ok0adiag_cells09pf1_cells37Corelib7Numbers7BinNumsld4Npos09canary_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3libeRefStartupDefs~~~~~~o88canary_w35stdpp9bitvectorbdefinitionst4bbv_unsignedt42bv37Corelib4Init9Datatypeshg44Nonehg46option37Corelib4Init5Logichie3andhie2eqld1Z46Stdlib6ZArith6BinInt1Zhl32lehl32ltt47Z_to_bvhie2or3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutho79EntryDraw3h5LinuxProcessSemantics5Riscv7Preludehs85bvmap3h5LinuxProcessSemanticsfLinuxProcessSem3Runhv78valid_sp69OSSVerify6Proofsaboost_jsonafuzz_parse3libaRefStartup~~~~~~iifamain_entry" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AtMain.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable rnd : ltac2:(zQ "10!hrb$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!n6!hue!vf@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : ltac2:(zQ "30!n6!vf!hi4>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Hypothesis Hvsp : ltac2:(zQ "10!ii3@1$0?3sp0").
  (* LPS-revision port: the encoded form held the pre-revision 7-argument
     main_entry sp0 av ev rnd tid regs mem.  RefStartup.v:101 now reads
     main_entry inp mbase entry sp0 rnd tid regs mem, with av/ev read off inp, so this
     section gains inp/mbase/entry and ties av/ev to inp by hypothesis.  Written out
     rather than re-encoded (rule 11).  Shape donor, statement only:
     a donor tree
     :projects/boost-beast/http_request/proofs/lib/RefMainEntry.v:94-110. *)
  Hypothesis Hargv : in_argv inp = av.
  Hypothesis Hve' : in_envp inp = ev.
  Hypothesis ME : main_entry inp mbase entry sp0 rnd tid regs mem.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* LPS-revision port.  These five replays applied main_entry_rdn_image / main_entry_guard /
     main_entry_mem_data in their pre-revision argument order from inside the replay program.
     A KReplay blob is never re-encoded, so each replay is REPLACED BY AN EXPLICIT PROOF
     (rule 11); the STATEMENTS are untouched and stay encoded, so nothing is restated.
     Tactic text: a donor tree
     :projects/boost-beast/http_request/proofs/lib/LibDiagKnMain.v:37-77 (the plain-text twin),
     with D_cxx for beast's D_cx and the argument lists re-threaded.
     THE EXPORTED ORDER WAS READ OFF A FARM ROUND, NOT GUESSED --
     a farm round printed it in full:
       main_entry_rdn_image : forall AMB inp mbase entry sp0 rnd tid,
         (140735340871680 <= bv_unsigned sp0)%Z -> forall regs mem,
         main_entry inp mbase entry sp0 rnd tid regs mem -> forall segs a n, ...
     main_entry_lib_pristine has no counterpart in beast and follows
     main_entry_none_below's shape, which is the twin of its own statement. *)
  Lemma cells_ok_main_entry : ltac2:(zQ "20!jc!k6@2$0?3mem$1").
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_entry_rdn_image inp mbase entry sp0 rnd tid Hlo regs mem ME RSEGS) as HI.
    unfold diag_cells, cells_ok.
    repeat (apply Forall_cons); [ .. | apply Forall_nil ]; unfold cell_ok;
      rewrite HI by (vm_compute; reflexivity); vm_refl_bv.
  Qed.

  Lemma pf1_cells_main_entry : ltac2:(zQ "20!jc!l2@2$0?3mem$1").
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_entry_rdn_image inp mbase entry sp0 rnd tid Hlo regs mem ME RSEGS) as HI.
    unfold pf1_cells, cells_ok.
    repeat (apply Forall_cons); [ .. | apply Forall_nil ]; unfold cell_ok;
      rewrite HI by (vm_compute; reflexivity); vm_refl_bv.
  Qed.

  (* [comment removed for export] *)
  Lemma canary_ok_main_entry : ltac2:(zQ "40!n6!nd!s9!v1@2$1?3mem@2$3@1$0#k0@1$2?3rnd").
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    split.
    - unfold CANARY. rewrite Z_to_bv_bv_unsigned, <- (canary_bytes_w rnd).
      exact (main_entry_guard inp mbase entry sp0 rnd tid Hlo regs mem ME RSEGS).
    - apply u64_range.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_none_below : ltac2:(zQ "a0!n6!vf!hhc!hi4!hk2!hk9!hkf!hmb!hn1!hn7>1i$6>0@2$4@2$7Z^1@2$8^1+vprr0@3$5@1$3@1$1@1$0#8@1?3mem@2$9@1$0#k0^2@1$2@1$1@1$0#8").
  Proof.
    intros i Hi. pose proof SPlo as Hlo. pose proof (u64_range tid).
    rewrite (main_entry_mem_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite stack_max_size_val, u_small by lia; lia).
    unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite wbytes_outside by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u_small by lia; lia)).
    reflexivity.
  Qed.

  Corollary main_entry_ro_none : ltac2:(zQ "a0!n6!vf!hhc!hi4!hk2!hk9!hkf!hmb!hn1!hn7>1i$6>0@2$4@2$7+hggg0^1@2$8^1+vhgg0@3$5@1$3@1$1@1$0#8@1?3mem@2$9@1$0#k0^2@1$2@1$1@1$0#8").
Proof.
ltac2:(KReplay.run1z (kr_t_LibDiagKnMain ()) ["AtMain"] "##-_h04__x1h12Hih27__arithh34__ffh48__varmaph55__with61ip;1p;2p;4p;8p;3p;7g009Aj16Tg002Bj27Tg0000j10!s/$Uj11Tg00M^j29Tg00N:j28Tg009_j1@Tg004Yj1?Tg00i[j2>Tg00aUj1=Tg00b3j1<Tg00e`j25Tg00j9j2LTg013nj43Tg006Aj1KTg018bj8JTg00cAj2ITg00<aj2C!s8$cj2B!sS$cj3ATg00dOj3D!s/$nj4ETg01A6j2FTg014Yj7GTg015=j7HTf0R0#1!s$%p=2%10#1p=:f1R1g019FR2g019eR3P3g01:ER4P0g01;LFGp=4f2R5P2P3P3P4P1P0FHp=;g00GHR6g00HcR7#2!s$&6R8/70%07#0#0R9#1#:#0!sB+:,90'8R;g01=SR<#@%?<1>61%=6%<6R<!t4+61568g01:eR81L67R7C3,4<P6P7g01;lR2156:!s:$5;<%K3P!tX$ER3,56P8P!sU,P2%09!tS$0#1!s+$!s-'2#6R9,56!sl'GJ1I<4P0P5g00EAR<g00EaR4'C1B05=A<4dAD631CEb3b4b5X0617311919'8\;^06P0P5P1O2b2,F1W1W6o"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_lib_pristine : ltac2:(zQ "b0!hk2!hmb!hn1!ho1!n6!vf!hhc!hi4!hk9!hkf!hn7>1i$9>0@2$3@2$0@2$1+vonn8^1@2$2^1+vons8@2$3@2$0@2$1+vpnv0^1@2$2^1+vpnv8@2$3@2$0@2$1+vpoq8^1@2$2^1+vpos0@2$3@2$0@2$1+vpov8^1@2$2^1+vppg8@2$3@2$0@2$1+hgpsmc^1@2$2^1+hgpuu8@2$0@2$1+hgrlu0^1@2$2^1+hgrlu8@3$8@1$7@1$5@1$4#8@1?3mem@2$a@1$4#k0^2@1$6@1$5@1$4#8").
  Proof.
    intros i Hi. pose proof SPlo as Hlo. pose proof (u64_range tid).
    rewrite (main_entry_mem_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite stack_max_size_val, u_small by lia; lia).
    unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite wbytes_outside by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u_small by lia; lia)).
    reflexivity.
  Qed.
End AtMain.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
