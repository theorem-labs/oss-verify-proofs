(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs written out as text, statements written out as text, the launch input as a ProcInput. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb PropExec CatExec StepTac StoreOk StartupTac ArgvEnv SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemSplit ZStores RefLayout.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefStartupDefs RefStartupFacts RefStartup LibDiagKn.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_LibDiagKnMain () := KReplay.lz_vm "##cJK47Corelib7Numbers7BinNums8positive01!sKG2!sK=1N02C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC89OSSVerify6Proofs:boost_json:fuzz_parse3lib1U?RefStartupFactsDmain_entry_rdn_imageC13~~~I!tn@2bv00I!uW+4Init9Datatypes4list!sF>6op!sl#00!u{A7Z_to_bvK!snC2!t825Logic2eq!tr?prod00!v_R9LibDiagKn7cell_ok!vL%!tq<3nat!xy@Z!sD/!vf81!sFB!yaB9bv_eq_dec!sN';!s]#_basic!si%!s7%!sK&3!sK%!vz&=!s,%!sC24base:decide_relK!wF;!u2-5Lists7!s+#Def6Forall!sGE2!wh\8!wh#s!wi+!|9b<D_!|;$missb!sx&7!sxN8PropExec3rdn!yKB!zZ%1C4ELinuxProcessSemantics?!s<2>Riscv!sE+@word!|H#le_bytes!|ND1!xF'9!xA$able;bool_!xP%!sD5E!sD-!y1#true_1C!xt78eq_ind_r!}@=!ss#00K!sFA1!w4/!w,96!#4m#s5Ubsan1M?loaded_segments!#5-&!}A>!#35<!}~$0!}~@!#8dG3!#30@1!{T\:diag_!{Y$!{VX!sp,9pf1!so^>!|G,Defs8canary_w!ss&!#:k:3pow!#;0=t!#8173an!#7jT!to2<!to&!|9$!#31g@!#<D,guard!s|h>!tv/!vm+!v476!}%%!#8e@C!#<K%_!#?P-!#5#W9u64_ran!#>x&K!wp<!{D]6CANARY!#6vU3Amb7a_hwcap!{6g6!#8V$!sqhenvp!x8+!uKO7Cat!wA#6w!zt]!t[3auxv!t[+!sq`4pn!soi:progname!#3DC6of_nat!#3d<add!#:=8iff_reflC4!sa&9micromega;ZifyClasses3inj!t+<>pow_pos_nonneg!sN<:!sN#!sJ%K!t=56VarMap1t01I!sD?0!sD6=RingM!s4'7Formula00!t567Env!sT#5PExpr07!uo65Tauto8B!sm&!sH6:Z!t;+=Z!sT$CheckerC!u0<4f!#4B#!sq?C!sq0_sound!u8E!#3\P=Sym!|I#2S!t+#4SX2S7u_small!#6Q7!#Ad,length!}_XD!sb%_N!#Bv-!t>%!#L&8or!x'8!xt,2!v7E2!#7vPMemSplit>!#3[$_outside!#=NBsubK!zOC5Psatz!u&8!sO86K!y>@;!tR%!uH$!s{8!vE,3!vEE4!#4SQ:!#4S+C!#>$,mem_data!#5Of3rb!#9X&!u55!#4E-5mkapp!sKB6!sK$2!sqE!#O0#!vMC3!x3D!#4,'1!sQ6!#3b%G!sJ'4!sJF5!u1B;rew_!#7o$v!v&Ceq!sP#!sLB8or_morph!tkF3!sJF6!sJF8!#7/;5eKind!#MV<unit!#347!se%4kind!wR8!w}13Op2!#Kf=!t5%!smJ!wx78!w##Inst7Inj_Z_Z!#5P74True!#;&7!~_;0!#33M!#SZK5State>stack_max_size!#8IPMmapSimB!sj1_va!#9_%c!#3%P=!#G3'MainE!#4$,none_belo!#A\%".
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9LibDiagKn~~~~~~08cells_ok0adiag_cells09pf1_cells37Corelib7Numbers7BinNumslf4Npos09canary_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UeRefStartupDefs~~~~~~oa8canary_w35stdpp9bitvectorbdefinitionst8bbv_unsignedt82bv37Corelib4Init9Datatypeshg84Nonehg86option37Corelib4Init5Logichj23andhj22eqlf1Z46Stdlib6ZArith6BinInt1Zhl72lehl72ltt87Z_to_bvhj22or3h5LinuxProcessSemanticsfLinuxProcessSembStackLayouthob9EntryDraw3h5LinuxProcessSemantics5Riscv7Preludehsc5bvmap3h5LinuxProcessSemanticsfLinuxProcessSem3Runhvb8valid_sp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UaRefStartup~~~~~~ij3amain_entry" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section AtMain.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {AMB : Amb}.
  Variable inp : ProcInput.
  Variable mbase entry : word.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variable rnd : ltac2:(zQ "10!hrf$0").
  Variable tid : word.
  Variable regs : ltac2:(zQ "30!n8!hv2!hg3@2$1@1$0#5@1$2@1$0#k0").
  Variable mem : ltac2:(zQ "30!n8!hg3!hi8>0@1$1@1$0#k0@1$2@1$1@1$0#8").
  Hypothesis Hvsp : ltac2:(zQ "10!ii7@1$0?3sp0").
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
  Lemma cells_ok_main_entry : ltac2:(zQ "20!je!k8@2$0?3mem$1").
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_entry_rdn_image inp mbase entry sp0 rnd tid Hlo regs mem ME RSEGS) as HI.
    unfold diag_cells, cells_ok.
    repeat (apply Forall_cons); [ .. | apply Forall_nil ]; unfold cell_ok;
      rewrite HI by (vm_compute; reflexivity); vm_refl_bv.
  Qed.

  Lemma pf1_cells_main_entry : ltac2:(zQ "20!je!l4@2$0?3mem$1").
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    pose proof (main_entry_rdn_image inp mbase entry sp0 rnd tid Hlo regs mem ME RSEGS) as HI.
    unfold pf1_cells, cells_ok.
    repeat (apply Forall_cons); [ .. | apply Forall_nil ]; unfold cell_ok;
      rewrite HI by (vm_compute; reflexivity); vm_refl_bv.
  Qed.

  (* [comment removed for export] *)
  Lemma canary_ok_main_entry : ltac2:(zQ "40!n8!nf!sd!v5@2$1?3mem@2$3@1$0#k0@1$2?3rnd").
  Proof.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    split.
    - unfold CANARY. rewrite Z_to_bv_bv_unsigned, <- (canary_bytes_w rnd).
      exact (main_entry_guard inp mbase entry sp0 rnd tid Hlo regs mem ME RSEGS).
    - apply u64_range.
  Qed.

  (* [comment removed for export] *)
  Lemma main_entry_none_below : ltac2:(zQ "a0!n8!hg3!hi0!hi8!hk6!hkd!hl3!hmf!hn5!hnb>1i$6>0@2$4@2$7Z^1@2$8^1+vtgv0@3$5@1$3@1$1@1$0#8@1?3mem@2$9@1$0#k0^2@1$2@1$1@1$0#8").
  Proof.
    intros i Hi. pose proof SPlo as Hlo. pose proof (u64_range tid).
    rewrite (main_entry_mem_data inp mbase entry sp0 rnd tid regs mem ME) by (rewrite stack_max_size_val, u_small by lia; lia).
    unfold D_main, D_cxx, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite wbytes_outside by
      (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite !u_small by lia; lia)).
    reflexivity.
  Qed.

  Corollary main_entry_ro_none : ltac2:(zQ "a0!n8!hg3!hi0!hi8!hk6!hkd!hl3!hmf!hn5!hnb>1i$6>0@2$4@2$7+hggg0^1@2$8^1+vkgg0@3$5@1$3@1$1@1$0#8@1?3mem@2$9@1$0#k0^2@1$2@1$1@1$0#8").
Proof.
ltac2:(KReplay.run1z (kr_t_LibDiagKnMain ()) ["AtMain"] "##-[h04__x1h12Hih27__arithh34__ffh48__varmaph55__with61ip;1p;2p;4p;8p;3p;7g009Ej16Tg002Bj29Tg0000j10!s/$Uj12Tg00Mlj28Tg00NHj27Tg009cj1?Tg004[j1>Tg00j;j2=Tg00b5j1<!s/$Sj1;Tg00f@j23!sJ$Yj2LTg014Rj44Tg006Cj1JTg019Fj8DTg00caj2CTg00<ej2BTg00dCj2A!sS$ej3@!s8$oj3ETg00eNj4FTg01AZj2GTg015=j7H!s/$aj7ITf0R0#2!s$%p=1%20#2p=Kf1R1g019jR2g01:IR3P3g01:iR4P0g01<0FHp=5f2R5P2P3P3P4P1P0FIp=:g00GPR6g00HkR7#1!s$&6R8/90%07#0#0R9#2#0#K!sB+:,80'7R;g01>7R<#?%><1=61%<6%;6R<!t4+61368g01;IR81L67R7C4,5<P6P7g01<PR2136:!s:$5:<%J3P!tX$MR3,36P8P!sU,P2%09#0!tW$1#0!s$&1#6R9,36!sh'GD1C<4P0P5g00EIR<g00EiR4'B1A05=@<4dAE631CFb3b4b5X0619311819'7\;^06P0P5P1O2b2,G1W1W6o"). Qed.

  (* [comment removed for export] *)
  Lemma main_entry_lib_pristine : ltac2:(zQ "b0!hk6!hmf!hn5!ho5!n8!hg3!hi0!hi8!hkd!hl3!hnb>1i$9>0@2$3@2$0@2$1+vrso0^1@2$2^1+vrst0@2$3@2$0@2$1+vssv8^1@2$2^1+vstg0@2$3@2$3@2$0@2$1+vstn0^1@2$2^1+vstn8@2$0@2$1+vstg0^1@2$2^1+vsth0@2$3@2$0@2$1+vsuj8^1@2$2^1+vsuk8@2$3@2$0@2$1+hgthqc^1@2$2^1+hgtki8@2$0@2$1+hguri0^1@2$2^1+hguri8@3$8@1$7@1$5@1$4#8@1?3mem@2$a@1$4#k0^2@1$6@1$5@1$4#8").
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
