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
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require U0Gc6. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame ShapeLaws SpecConsts MmapSim AllocSim FileSim AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 LibKnowFrame Spec LibWritev RefMemcpyLib LibTail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefExitBase RefStdioDefs RefExit LibStdioCall RefMemcpyBase RefMemcpy RefMemchr RefStrnlen.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefOpenFailCS_defs RefOpenFailCS_tail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefOpenFailCS_tail2 () := KReplay.lz_vm "#%ioC47Corelib7Program6Basics4flipC46Stdlib5Lists4!s+#8nil_cons!sa,4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?!s<22Fs2F!sr-!t8%7!s+#Def3map!t686!t6%!to8map!to&!sC5:firstn_nilK!uq,Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!u419Datatypes4list00!tTG1!vk;5Riscv7Prelude5bvmap!t?<6op!te#00C!sH<lengthK!sF;3nat!uk#!wV62eq00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun7vals_evC13~~~C8!shN1UBRefOpenFailCS_tail3ENV!srV=SymExec2Sound4SX2S7regs_ok!stjknow!st,!yO@;bv_unsignedC5!{'&6ZArith6BinInt1Z2leK!tbO8!tb'3SX24expr02!t[%!{J>Z03!t3c1!t3F2K!|4A1!tS]5sadd!tT,!sn\6sentry!soe!v4%4!t^dk!t^%6!sok1!sok5!sok7!sok!w3d9sym_state!vEe7scripts!sp'!#63O8Prop!sq#7seg_rom!sjV4Spec9exit_code!#4?&!#=EH5S!u|#4m_fs!u/QShapeAlg6t_!tI#!tD%!#;c<prod!#;c-!sF81K!#:%:1C!wf\8!xZ#exec!v7&!#4$]_log!sldcarry!slV!#9z58sc_deno!wD&K!#BS96Forall!vc_6s_regs!u,i9mem!u-/!#<'@7Z_to_bv!|fY4mks!v=+!{yI3Run6config01!}@U1W!uLG6bv_and!}&]mi!v\+!#G<49nth_error!t/P9SymDriveX8!#@l#nth!x`j!#7_$!#Ae,!#4LN8m_haltedK!#G1B2!t#Q9m_vm_lazy!#E~Q;RefExitBase:file_clean!#5[7!#4s&x!#JZ3!s@%3and00I!tOQ<RefStdioDefs>stdout_pending00!w'W5m_fds!v^Rfd_lookupK!s^P7FdE!#@2$!vJ9or00!#GN;3sub!#4w\2!#K`&K!#OQC!#6,_r_get!#8zb6e!#5|-!sm]a!sm/!vv<add!#34Y>!tv%_add_l!#4F'!#7VXgetr!sgV!#Q4&reg_val!ubB6of_nat!sF34Znat5Nat2Z7inj_iff!#WS77iff_sym!#6y'9micromega;ZifyClasses7rew!sj$!t5=9is_nonnegK!sr56VarMap1!#TR#!sD>0!sD6=RingM!s4'7Formula00!t567Env!sT#5PE!#PS#!sIE4!uo65Tauto8B!t8&!sH6:Z!t^+=Z!sT$CheckerC!uS<4f!#[Z-!sq8C!sq0_soun!#Sj<>pow_po!w:'!#T:=t!|6=pow!sC<:!t/#!x?<!ve21!sIE7!#WMcu_small!#8aP>!#\v#!sE+8store_ok!zc@1!#aw8!|:#refl!|;B3inj!sIB;!|^&_rev!#4XY<kwr_!uD'!#8W&!|KK1!#U{b7!#>_8Peano2le00!uwB9and_morph!y,c4fla!#9Nc7ext!#6k,!#<??C!#I<%_!#^I,K!#3L;G!w9'3!#8SV=!tf&_zx_id!{``@word!u0#le_bytes!#]oA2!#EyC!y[Q!#Cp1;!#U<%mm!sp#!z~'!#EE9!#ST8!#EE#!#So9or!#A'Q1U7!#G0%:ref!#U_#_Z!x}G5bv_eq!#LlX4t!sa#!zzU!t{,?!#MV$_nil!#Wc,!t\Y8!t\#!#>K#!wT%!skYrealizes03!}Kc4s_p!#X9%I!tZb!#Jf%!#5Lb!uI&I!{^k0!vAc6a_base!smc5a_off!{T'!#7_?5mkrel!#5FE4!sJF8!sJF5!t_Eapp!sKB6!sK$!#D>E3!#IbX3rdn!}1X!#=d%5kread!wGH!#yU#ff!t6Y9!t6$_!t|Y!#?b+;!#NE$_lit0!um_6rz_run!#8L&!#y@>5Instr5aluop01I!~#b0!~#V!#Ru1!#l-$!soek!so0!#t:?!#Vb,!sD6!#}f<!#{c#0!#LX;5eKind!#ig<unit!#N,7!se%4ki!#<v$!#ESA3Op203K!t5A1!tU=bool!#k>>!sF$!tUJ5!zn/!wp96images5Ubsan1M?loaded_segment!#gf&!#Rn<6inj_le!#eLQcfg=hunspell_scf!#kkV!$#c3defs4FUEL!ssk5STOPS!tilscr0!tilsrI3!stmkn!st+!}Q=!$/5+!{E=!}:$!#4f]8sidecond!#3yd!#y%,!srd!#y%'!sp'!#dlX0!#I<74True!~q#!~14!#Y+,;!}0%!u+$!#hf9!sn%!#5W68ZifyInst7Inj_Z_Z!#3EH1!#44A2!#7O=N!ts#!#iEOeven!#7##!s\V2!$5h;3!#Al#!sC;fst!#GSb!$&Kc!{Y,1!~-X<Lib!#HF#Call:s!s0#_c!#\/+!ss^6sc_r!#j3W!so24sc_f!sme5!sm#d!sniwb!snjp!v=is!smi!xd'!#E~W8blob!$=a,!#3k67f_equal!$Dj;trans!{t]3env!$0g`5v_add!shV7StepTac6u_Z2bv!shWLibTail7vadd_wZ!si^6ed_var!shb!#r:X!sh/!vi+!#\o;2!|Qcs!|Q'!#M0?3Sem5alu64!y,Y7alu!y/Z9!#Y`#Laws>!$5R$_has_ni!|{`9junk_vals!||83Nat!#x/]@!t++_!$J1$!t3'!#>6%!$Mg-!sG%_!#;o4!#i^&t!tSZ=!$J8%!t%#!#4H&c!yCQC!$J>428of_segI3!#61d!z=$r!snikn!sne@!#=U+!#uo%!syU3Lib2Nd:and_elimF7!yw8!#A<,snd!#LMfrH!wXY!ss7kn!ss+!#Q2Bt!#Lne!u2#!#Mdn!stn3rG3!#7$&!#\$D;branch_!#D~#6!#\ZGmulop!#m]S!tx62PX!tw%I!{h^9!{h%r!#iD+!zYhG!zYo!ssnsc!ssm3!}7oscH!tgnI!srnF4!{uZ4!y`h!tM'!y`h!ssnsc!ssm3rG!srnH!u[n!ssokn!thocH!vQnI!srl?itinerary_63_6!s~'!#f,Ppec?msg_cannot_ope!#reW!#N`,mu!$=HB3mul!#twD5!sf=ltb!$k<H6bv_ltu!#M9Xltu_Z!#OO^!#P:$!sibmul!sia6ed!wZ-!#NGC<!#6V%taken!$W+B2!wj=opp!xRE6!uHP:!#KE&H46win!$Q8+!skZ9log_out_!#[w%!$;X?3!t4[Ardn_!$Xt'!t>#!u+V!#N8+:flat_intro!y'^9!tc#app_Z!t[`8kimg!#|{+!x_>3P!#u2G5Psatz!$F67!sO84!sOK6K!#kJL2!#R$l!#BHW!#OM3!sk'!#U959!x3#assoc!#9G`!u'#4atG!$Vn'!#m5:negb!~T+5!vT$8!#VK#Na!#X$+!$NJA!sI#!t|d9PRE17_le!#TKX!#<?55sc!#JlnsrG!#LVlknG!#wl'!$,<K2!tGe6BUF_LO!u>k!su$HI!suk3I!sri!yf#5!yf$!stk;!z\%words!szk6nl_img!#6j;!#4~:1!$CF@D!$IE&obliga!s:#_!$Of9!#m8%2!|zgrI4!$$to!st'!#bem4!#7c\;!#7c'!yji!vR&H!vRpH!vRn7NL!{T$!tm&!#J\W9u64_rang!$CV&!$a&;ltb_lt!zc85proj2!#J>Ns!|-A9bv_!%1fA:!t^#ir!$Xi#!#DUY!$eN,w0_!#r|V!ss-<!ss&exts!{''!#IA:!%;{$!#nb6sub!#?Y;nil_r!#>F?!sd#!sF>8sub_diag!#nw7!%=`%all!sE@!#o>-7!$DM%?Rel!#4s#!s6&>eq_equivalence!sWE?E!sT,_PER!sX59Morphisms:respectful!t#E<eq_Reflexive!s|?Jr!sL'_eq_dom_r!s]GI!s],!s0,proxy!tjISymmetric!sUE8s!sR%y!t^?@!tT0per!sS?N!$#D#_sym_co_inv_impl!$^`$ism!#LTPSeqExec:rdn_!{F&!|^U!#xj0m!#xj3!#4K;to!$nO6!#XM,ax!sC<8max_!yi#!$\IQ=RefMemcpyBase3mcH!$&I&I!sod!#J2'!#5|>4BvW!$NRP5Hoare;ret_ok_ev!#I?Y9!u#+!$]N#m!s1$!x]V7Cat!yK#6w!$aS#!v[&!shO6CatSim6mstep!#oK+!siO<!uC+Lib5keeps!slV!$dj%:sr_vars_l!#Vq`@!%GS#after_!ta[!$%S'?sr!sq&!#{Q#j!#:<2!#=`,6!$_s%!u+Z!%-u#!t9%!$m<#!vg^kn!vgh<en!$%h$!ti#!sp%!#Vim4!w]X!$a`%9rz_!zv%!};V!#Fr42!tZWAgentLib:!#6m%ap!$2]'!#>B47map!sH#!$_#E6!$Fv>@!$~}$_!#7[$_eq!#HvgG!#Hvo!stosc!#u>nsrF!$%ElknE!tgl!vS#!zBV!#6~/;callee_kep!~Va?!so-_no!vPW!$J}0ridx!|%=2In!#6N73no!#?|<;le_gt_cases!#WQd7!#4B$F!#5;r!#`,h!#Z?#!tp&_g!#?^&!ttf9!s{&!#|Rh!#ej%!|pi!ss#!vc&BC!{4V!#xy#5t_die!#3DmB!#dPn!ss'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~k1floaded_segments37Corelib4Init5Logico92eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1Uh2RefOpenFailCS_tail~~~~~~q23ENV37Corelib4Init9Datatypesv06lengthv04listv03natv06option3h5LinuxProcessSemanticsfLinuxProcessSem3Runhi75mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statehlc4m_fs3h5LinuxProcessSemantics5Riscv7Preludehp25bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hs14mksths17seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~igfdhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~il78realizesil76t_exit69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~iq89exit_code79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~iuc7know_okiuc7regs_ok69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~jk77vals_ev79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1Uh2RefOpenFailCS_defs~~~~~~job5knI30job5srI30hf7Z_to_bvjob5knH30job5srH3001Zil76t_emitiq81Wiq8fmsg_cannot_openq24atG046Stdlib6ZArith6BinInt1Zkid6of_natv04consv03nil3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsklch0word_to_le_bytesjob5knI40job5srI40job5knH40job5srH40kid3addkid2lehfbbv_unsignedv04Somev03appo93and37Corelib4Init3Natkva3addhs13rdnjob3knEjob4srF0o93notiq85t_diejob4knB0job4srB036Stdlib5Lists4Listlk82Inhlc5Modelhi78valid_spv04Nonehlc8m_haltedv04prodhlc9m_vm_lazyhlc7FdEntryhlc9FdChannelhlc9fd_lookuphlc5m_fds" s.   (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* LPS 75d69e00: ref_exit_Z takes the launch's channel reader as a separate premise, so
   the tactic takes the hypothesis that carries it. *)
Ltac close_exit HR HK P0 Hh Hlazy Hrdr sp0 :=
  lazymatch type of HK with know_ok ?segs ?E ?M ?kn =>
  lazymatch goal with |- realizes _ (mkCfg _ ?model) _ =>
    apply (rz_conseq segs _ (t_emit (W 1 []) (t_exit (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) (m_fs model))));
    [ | cbn [W map];
        replace (bv_and (Z_to_bv 64 2) (Z_to_bv 64 255)) with (exit_code 2) by (apply bv_eq; reflexivity);
        apply t_eq_sym; apply t_emit_nil_exit ];
    apply ref_exit_Z; [| exact Hrdr];
    let Ktid := fresh "Ktid" in
    pose proof (know_nth segs _ _ kn ltac:(let i := kidx kn (is_krange (EVar 5)) in exact i) _ HK eq_refl)
      as Ktid; cbn [kentry_ok edenot ev ENV] in Ktid;
    lazymatch type of HR with regs_ok _ _ ?Rc =>
    exists (Z_to_bv 64 (bv_unsigned sp0 - 128)), (Z_to_bv 64 0x10ebf8), (bv_unsigned (ev E 5)),
           (Z_to_bv 64 0), (Z_to_bv 64 0);
    split; [|split; [exact Hh|split; [exact Hlazy|]]];
    [ constructor;
      [ regv HR (2 : reg); rewrite edenot_add_lit; unfold adenot, v_addi; cbn [a_base a_off edenot ev ENV];
        rewrite P0; f_equal; lia
      | regv HR (4 : reg); reflexivity
      | regv HR (10 : reg); reflexivity
      | rewrite u_small by lia; lia
      | rewrite u_small by lia; lia
      | rewrite u_small by lia;
        let Hst := fresh "Hst" in
        pose proof (kwr_store_ok segs E _ kn ltac:(let i := kidx kn (is_kwr_cov (EVar 0) (-272) 144) in exact i)
                      _ _ _ (-272) 144 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst;
        unfold adenot, v_addi in Hst; cbn [a_base a_off edenot ev ENV] in Hst; rewrite P0 in Hst;
        replace (bv_unsigned sp0 - 128 - 144)%Z with (bv_unsigned sp0 + -272)%Z by lia; exact Hst
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | lit_u; cbn [ev ENV] in Ktid |- *; lia
      | cbn [ev ENV] in Ktid |- *; lia
      | lit_u; change (1108984 - 168)%Z with 0x10eb50%Z;
        let Htc := fresh "Htc" in
        krd HK 0x10eb50%Z 4%nat Htc; rewrite Htc; cbn [ev ENV] in Ktid |- *;
        rewrite ext_val_zx_id by (change (2 ^ (8 * Z.of_nat 4))%Z with 4294967296%Z; lia);
        rewrite Z_to_bv_bv_unsigned; reflexivity
      | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK | krd_solve HK
      | repeat split; krd_solve HK
      | repeat split; krd_solve HK ]
    | left; split; [reflexivity|]; exists (Z_to_bv 64 0), (Z_to_bv 64 0); repeat split; krd_solve HK ]
  end end end.

Section Tail2.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.
  Variable BL : ltac2:(zQ "30!hh1!h9!jc@1$0@1$0@1$2@1$1#8").
  Variable model : ltac2:(zQ "10!lm1$0").
  Hypothesis Hvsp : ltac2:(zQ "10!lma@1$0?3sp0").
  Hypothesis Hh : ltac2:(zQ "60!h9!jc!ln6!hhe!pd!lnd@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!h9!jc!lo9!hh1!kl6!pd!lp0&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd2 : ltac2:(zQ "90!h9!lpd!ju5!ku7!hhe!pd!lq8!lr5!ls2@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+2@2$3$1@1$6@2$2@1$0#k0+2").
  (* LPS 75d69e00: the stderr writes and the exit flush need the launch's channel
     reader (stdio_call_sound / ref_exit_Z premise), constant over the run. *)
  Hypothesis Hrdr : m_channel_reader model = true.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma of_segI3 : ltac2:(zQ "h80!h9!jc!n7!pd!ua!hg8!hh1!hh8!hhe!hl3!hoa!hr8!hvc!ig4!ik6!ip2!ipe!itf!jj1!jjc!jo0!jt3!jtc!ju5>4vals@1$6@1$1@1$0#k0>1R@2$b@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$8@1$1@1$0#8>0@3$3$7@2$5@1$1@1$0#k0^3Nhg7>0@3$3@1$1@1$0#k0@2$h4^4N0?3sp0>0@3$h3@2$4?2BL^5$h6^4>0@4$h2$2@2$4?2BL^6^4$h5@4$f$2$e@2$9@5$c?2fx^6@2$h7@1$0#k0+ujrp4^5@1$d$2?5model@2$h0@1$h1+2@1$a?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy Hrdr sp0.
  Qed.

  Lemma of_segH3 : ltac2:(zQ "h80!h9!jc!n7!pd!ua!hg8!hh1!hh8!hhe!hl3!hoa!hr8!hvc!ig4!ik6!ip2!ipe!itf!jj1!jjc!jo0!juf!jv8!ju5>4vals@1$6@1$1@1$0#k0>1R@2$b@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$8@1$1@1$0#8>0@3$3$7@2$5@1$1@1$0#k0^3Nu7>0@3$3@1$1@1$0#k0@2$h4^4N0?3sp0>0@3$h3@2$4?2BL^5$h6^4>0@4$h2$2@2$4?2BL^6^4$h5@4$f$2$e@2$9@5$c?2fx^6@2$h7@1$0#k0+ujtm4^5@1$d$2?5model@2$h0@1$h1+2@1$a?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    apply (rz_conseq RSEGS _ (t_emit (map (WriteEv (Z_to_bv 64 2)) ([] ++ [])) (t_exit (exit_code 2) (m_fs model)))).
    2:{ cbn [map app]. apply t_eq_sym. apply t_emit_nil_exit. }
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH3 knH3 Rc Mc model scH3 [] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH3 knH3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH3 length Z.of_nat] end.
    - lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - lia.
    - cbn [edenot]. apply u_small. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - reflexivity.
    - reflexivity.
    - exact Hfd2.
    - exact Hrdr.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Lemma of_segG3 : ltac2:(zQ "e0!h9!jc!hg8!hh1!pd!kg1!hoa!kg4!ipe!kge!itf!kh3!ki6!kk5>4path@1$3@1$1@1$0#8>0@3$4$5@1$d@2$2@1$1@1$0#8^1+jf@7$c?2fx?3sp0?2BL?5model^2+jf@2$7@2$9+2@1$b^2@2$8@1$a+2@1$6?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros path HP vals R M HL P0 P113 HR HK SBp.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk_keep scrG3 199%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113).
      replace (-1 * 63 + 63)%Z with 0%Z by lia.
      rewrite ltu_ZZ by lia. reflexivity. }
    assert (WOK : win_ok (ENV BL vals) 0 BUF_LO BUF_HI IHI).
    { unfold win_ok, BUF_LO, BUF_HI, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (SBp' : rdn RSEGS M0 (Z_to_bv 64 (bv_unsigned sp0 - 543)) (length path) = Some path).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 BUF_LO BUF_HI IHI);
        [exact SBp | vm_compute; reflexivity | exact WOK | cbn [ev ENV]; rewrite P0; unfold BUF_LO; rewrite u_small by lia; lia
        | cbn [ev ENV]; rewrite P0; unfold BUF_HI; rewrite u_small by lia; lia]. }
    clear EQM SBp. rename M0 into M'.
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    assert (B80 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) (17 + length path) = Some (PRE17 ++ path)).
    { apply rdn_app_Z; [exact H17 | | lia | lia].
      replace (bv_unsigned sp0 + -560 + Z.of_nat 17)%Z with (bv_unsigned sp0 - 543)%Z by lia. exact SBp'. }
    assert (Hnl : rdn RSEGS M' (Z_to_bv 64 0x1326f) 1 = Some [Z_to_bv 8 10]).
    { rewrite (kimg_rdn RSEGS (ENV BL vals) _ knG3 ltac:(let i := kidx knG3 (is_kimg_cov 0x1326f 1) in exact i)
                 _ _ 0x1326f 1 HK eq_refl) by (cbn; lia). apply nl_img. }
    (* [comment removed for export] *)
    unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W.
    pose proof itinerary_63_64 as (_ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srG3 knG3 Rc Mc model scG3 (PRE17 ++ path) [Z_to_bv 8 10]
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srG3 knG3) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scG3];
      rewrite ?length_app, ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - cbn [edenot length]. apply u_small. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0, ?P113). unorm.
      replace (17 + length path)%nat with (17 + length path)%nat by lia. exact B80.
    - cbn [edenot]. exact Hnl.
    - exact Hfd2.
    - exact Hrdr.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R2 M2 HR HK.
      eapply (of_segH3 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma NL_word : ltac2:(zQ "80!h9!jc!ju5!kkf!hh1!kl6!pd!kp3@3$6@1$4@1$1@1$0#8@2$7N1@2$2@1$0#k0+a@3$3@1$1@1$0#8@2$2@1$0#8+a@1$5@1$1@1$0#8").
Proof.
ltac2:(KReplay.run1 (kr_t_RefOpenFailCS_tail2 ()) ["Tail2"] "h02b1h12b2h21nh31Hp;1p;2p;3p;:g003kj10Tg004Pj14Tg004nj12Tg005Qj17Tg01MPj1Bj3?Tg0061j1=Tg00AYj1<Tg0429j2;Tg00lYj3:Tg00B7j18Tg008cj31Tg00=gj23Tg01R9j39Tg00Rnj26Tg042ll:ATg008Dj1@Tg00Zdj25Tg01LHj2>Tg02:@#0R0#0#0R1#4R2#2R3%73R4P4%B3%=0#0#<R01;205:2R5P5%83R6P6g02BlR7f0R8#2R9f1R:#2R;g00fMf2R<#2?1:8g01lCR=f3R>/3<13>:31R?[13<:13<851=%2>?1<:[R@f4#2?1><\?A9<:8P8n2001000000120000000W1W0W2P@^1;^09^27P8P2P5P51325,6=O4b31646M:Ag02:e#@%01#0#0#4/50'>1520=?36514do"). Qed.

  Lemma of_segI4 : ltac2:(zQ "h80!h9!jc!n7!pd!ua!hg8!hh1!hh8!hhe!hl3!hoa!hr8!hvc!ig4!ik6!ip2!ipe!itf!jj1!jjc!jo0!kq8!kr1!ju5>4vals@1$6@1$1@1$0#k0>1R@2$b@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$8@1$1@1$0#8>0@3$3$7@2$5@1$1@1$0#k0^3Nhg7>0@3$3@1$1@1$0#k0@2$h4^4N0?3sp0>0@3$h3@2$4?2BL^5$h6^4>0@4$h2$2@2$4?2BL^6^4$h5@4$f$2$e@2$9@5$c?2fx^6@2$h7@1$0#k0+ujrp4^5@1$d$2?5model@2$h0@1$h1+2@1$a?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    run_blk scr0 263%nat.
    close_exit HR HK P0 Hh Hlazy Hrdr sp0.
  Qed.

  Lemma of_segH4 : ltac2:(zQ "hc0!h9!jc!n7!pd!ua!ju5!kkf!hg8!hh1!hh8!kl6!hhe!hl3!hoa!hr8!hvc!ig4!ik6!ip2!kg4!ipe!kge!itf!jj1!jjc!jo0!kra!ks3>4vals@1$8@1$1@1$0#k0>1R@2$e@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@3$3$9@2$7@1$1@1$0#k0^3Nu7>0@3$3@1$1@1$0#k0@2$h9^4N0?3sp0>0@3$h8@2$4?2BL^5$hb^4>0@4$h7$2@2$4?2BL^6^4$ha@4$h2$2$h1@2$c@5$f?2fx^6@2$5@1$0#k0+ujms4^5@1$h0$2?5model@2$h3@2$h5+2@3$6@1$1@1$0#8@2$5@1$0#8+a@1$a@1$1@1$0#8@2$h4@1$h6+2@1$d?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros vals R M HL P0 HR HK.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi.
    (* [comment removed for export] *)
    run_blk scr0 231%nat.
    krdv HK 0%nat (-560)%Z 1%nat Hb. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    rewrite NL_word in Hb.
    unfold adenot, v_addi in Hb. cbn [a_base a_off edenot ev ENV] in Hb. rewrite P0 in Hb.
    replace (W 2 [Z_to_bv 8 10]) with (map (WriteEv (Z_to_bv 64 2)) ([Z_to_bv 8 10] ++ [])) by reflexivity.
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srH4 knH4 Rc Mc model scH4 [Z_to_bv 8 10] []
             (t_exit (exit_code 2) (m_fs model)) HR HK (eq_trans (f_equal (fun n => stdio_call n srH4 knH4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scH4 length Z.of_nat] end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. apply u_small. lia.
    - lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - left. cbn [edenot]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot]. unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hb.
    - reflexivity.
    - exact Hfd2.
    - exact Hrdr.
    - exact Hh.
    - exact Hlazy.
    - apply t_exit_has_nil.
    - clear HR HK. intros R2 M2 HR HK.
      eapply (of_segI4 (vals ++ junk_vals R2));
        [ rewrite length_app, junk_vals_length, HL; reflexivity
        | rewrite vals_ev_app_l by (rewrite HL; lia); exact P0
        | exact HR | exact HK ].
  Qed.

  (* [comment removed for export] *)
  Lemma of_segFG4 : ltac2:(zQ "i70!h9!jc!pd!ksc!kt3!kt9!hh1!n7!hg8!jo0!ju5!hhe!kg1!ua!ku7!kue!kkf!hh8!kl6!kv4!lgc!hl3!hoa!hr8!hvc!lh3!ig4!ik6!ip2!kg4!ipe!kge!itf!kh3!jj1!jjc!lha!li1!kk5>4path@1$6@1$1@1$0#8>2pp@1$1@1$0#k0>1P$c>4vals@1$6@1$1@1$0#k0>1R@2$h7@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@3$2$c@1$i6@2$8@1$1@1$0#8^6^4>0@2$h3@2$4+k0^5@2$4^5+hvvvf>0@3$2$h1@2$8@1$1@1$0#k0^5Nq7>0@3$2@1$1@1$0#k0@2$9^6N0?3sp0>0@3$2@1$1@1$0#k0@2$9^7N2^9>0@3$2@1$1@1$0#k0@2$9^8Nn1@2$a@1$0#k0^9>0@2$4@2$5@1$0#k0?3sp0@2$5@1$0#k0^b>0@2$4@2$3@2$3@2$5@1$0#k0^c^b+8@2$3@2$5@1$0#k0?3sp0+kgggg0>0@2$4@2$3@2$3@2$5@1$0#k0^d^c+8+ogggggggggg0>0@3$i3@2$d?2BL^c$i5^b>0@4$i2$7@2$d?2BL^d^b$i4>0@3$2@1$b@1$6@1$1@1$0#8@4$h9$7^c^h0@2$h4@2$8@1$1@1$0#8^h1N1@2$e@1$6@1$1@1$0#8@3$f@1$1@1$0#8^h1@3$h0@1$1@1$0#8@2$a@1$0#8Z@1$h2@1$1@1$0#8@4$hc$7$hb@2$h5@5$h8?2fx^e@2$a@1$0#k0+ujms4^d@1$ha$7?5model@2$hd@2$hf+2@1$i1^h2@2$he@1$i0+2@1$h6?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros path pp P vals R M HP HPr HL P0 P2 P113 Hpp1 Hpp2 Hpp3 HR HK Hstr.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    assert (Psmall : (bv_unsigned (edenot (ENV BL vals) (EVar 113)) < 2 ^ 31)%Z).
    { cbn [edenot ev ENV]. rewrite P113, u_small by lia. lia. }
    (* [comment removed for export] *)
    run_blk_keep scrF4 167%nat.
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken]. ed_lin ltac:(cbn [ev ENV]; rewrite ?P113).
      rewrite ltu_ZZ by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
    { (* [comment removed for export] *)
      unfold sc_denot. cbn [branch_taken].
      rewrite (edenot_exts4 _ _ Psmall), !(edenot_addw0_r _ _) by (rewrite ?edenot_addw0_r by exact Psmall; exact Psmall).
      unfold bv_lts. rewrite Z.ltb_irrefl. reflexivity. }
    assert (WOKS : win_ok (ENV BL vals) 0 0 4194304 IHI).
    { unfold win_ok, IHI. cbn [ev ENV]. rewrite P0. lia. }
    assert (Hstr' : rdn RSEGS M0 pp (length path + 1) = Some (path ++ [Z_to_bv 8 0])).
    { rewrite EQM, (rdn_mem_denot_out RSEGS (ENV BL vals) M _ 0 0 4194304 IHI);
        [exact Hstr | vm_compute; reflexivity | exact WOKS | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia]. }
    clear EQM Hstr. rename M0 into M'.
    assert (Hsrc : rdn RSEGS M' pp (length path) = Some path).
    { replace path with (firstn (length path) (path ++ [Z_to_bv 8 0])) at 2
        by (rewrite firstn_app, firstn_all, Nat.sub_diag; cbn [firstn]; apply app_nil_r).
      eapply rdn_firstn; [exact Hstr' | lia]. }
    krdv HK 0%nat (-560)%Z 8%nat Hw0. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-552)%Z 8%nat Hw1. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    krdv HK 0%nat (-544)%Z 1%nat Hw2. { apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    unfold adenot, v_addi in Hw0, Hw1, Hw2. cbn [a_base a_off edenot ev ENV] in Hw0, Hw1, Hw2.
    rewrite P0 in Hw0, Hw1, Hw2.
    assert (H17 : rdn RSEGS M' (Z_to_bv 64 (bv_unsigned sp0 + -560)) 17 = Some PRE17).
    { rewrite <- PRE17_words. change 17%nat with (8 + (8 + 1))%nat.
      apply rdn_app_Z; [exact Hw0 | | lia | lia].
      apply rdn_app_Z; [ | | lia | lia].
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -552)%Z by lia. exact Hw1.
      + replace (bv_unsigned sp0 + -560 + Z.of_nat 8 + Z.of_nat 8)%Z with (bv_unsigned sp0 + -544)%Z by lia. exact Hw2. }
    (* [comment removed for export] *)
    apply (rz_conseq RSEGS _ (t_emit (W 2 (PRE17 ++ path)) (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))))).
    2:{ unfold msg_cannot_open. change (s2b _) with PRE17. rewrite app_assoc. unfold W. rewrite (map_app _ (PRE17 ++ path)).
        apply t_eq_sym. apply t_emit_app. }
    unfold W at 1.
    pose proof itinerary_63_64 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC & _).
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ ?Mc _) _) _ =>
    apply (stdio_call_sound vals (blobs_ev BL) srF4 knF4 Rc Mc model scF4 PRE17 path
             (t_emit (W 2 [Z_to_bv 8 10]) (t_exit (exit_code 2) (m_fs model))) HR HK
             (eq_trans (f_equal (fun n => stdio_call n srF4 knF4) HL) SC));
      cbn [sc_f sc_fd sc_ret sc_wb sc_wp sc_bufp sc_bufsz sc_s sc_l sc_sp sc_sr sc_kn scF4];
      rewrite ?PRE17_len end.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P113. rewrite u_small by lia. lia.
    - cbn [length Z.of_nat]. lia.
    - right. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - right. cbn [edenot ev ENV PX]. rewrite P2. ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm. lia.
    - cbn [edenot ev ENV PX]. rewrite P2, P113. rewrite u_small by lia. lia.
    - ed_lin ltac:(cbn [ev ENV]; rewrite ?P0). unorm.
      replace (bv_unsigned sp0 + -560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact H17.
    - cbn [edenot ev ENV PX]. rewrite P2. exact Hsrc.
    - exact Hfd2.
    - exact Hrdr.
    - exact Hh.
    - exact Hlazy.
    - apply t_emit_has_nil.
    - (* [comment removed for export] *)
      clear HR HK. intros R1 M1 HR HK.
      clear Hstr' Hsrc Hw0 Hw1 Hw2 H17 Psmall.
      lazymatch type of HK with know_ok _ _ _ ?k => change k with knG40 in HK end.
      lazymatch type of HR with regs_ok _ ?sr _ => change sr with srG40 in HR end.
      set (vals0 := vals) in P2, P113.
      set (vals1 := vals ++ junk_vals R1) in *.
      assert (HL1 : length vals1 = 199%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals1 vals0. clear HL P0 WOKS. clear vals. rename HL1 into HL. rename Q0 into P0.
      change (Env (vals_ev vals1) (blobs_ev BL)) with (ENV BL vals1) in HR, HK.
      run_blk scr0 199%nat.
      lazymatch goal with |- realizes _ (mkCfg (mkst _ _ ?Mc _) _) _ => rename Mc into MG end.
      (* [comment removed for export] *)
      set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
      assert (Hnl : rdn RSEGS MG (Z_to_bv 64 0x1326f) 1 = Some [Z_to_bv 8 10]).
      { rewrite (kimg_rdn RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kimg_cov 0x1326f 1) in exact i)
                   _ _ 0x1326f 1 HK eq_refl) by (cbn; lia). apply nl_img. }
      assert (Hdst : store_ok RSEGS MG dst 1 = true).
      { pose proof (kwr_store_ok RSEGS (ENV BL vals1) _ knG4 ltac:(let i := kidx knG4 (is_kwr_cov (EVar 0) (-560) 1) in exact i)
                      _ _ _ (-560) 1 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
        unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
        subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
      assert (MC : mcH MG dst (Z_to_bv 64 0x1326f) 1 [Z_to_bv 8 10]).
      { constructor; cbn [length Z.to_nat Z.of_nat Pos.to_nat]; subst dst; rewrite ?u_small by lia; try lia.
        - exact Hnl.
        - exact Hdst. }
      lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
        assert (A1 : getr Rc 1 = (0xe36c4 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
        assert (A10 : getr Rc 10 = dst)
          by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
        assert (A11 : getr Rc 11 = Z_to_bv 64 0x1326f) by (regv HR (11 : reg); reflexivity);
        assert (A12 : getr Rc 12 = Z_to_bv 64 1) by (regv HR (12 : reg); reflexivity);
        destruct (ref_memcpy MG dst (Z_to_bv 64 0x1326f) 1 _ (seg_rom RSEGS) MC Rc (0xe36c4 : word)
                    ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
        clear A1 A10 A11 A12
      end.
      replace (Z_to_bv 64 975440) with (0xee250 : word) by (apply bv_eq; reflexivity).
      eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
      replace (0xe36c4 : word) with (Z_to_bv 64 0xe36c4) by (apply bv_eq; reflexivity).
      lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
        pose proof (regs_after_keeps vals1 (blobs_ev BL) sr Rc R2 callee_kept
                      ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
      rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
      (* [comment removed for export] *)
      pose proof (know_after_store RSEGS (ENV BL vals1) MG knG4 (SA (EVar 0) (-560)) 1 (ELit 10) [Z_to_bv 8 10]
                    knH40 [] [] ltac:(vm_compute; reflexivity) eq_refl HK ltac:(lia)
                    ltac:(apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia)
                    ltac:(cbn [edenot]; symmetry; apply NL_word)) as HK2.
      clear HK.
      assert (Edst : adenot (ENV BL vals1) (SA (EVar 0) (-560)) = dst).
      { unfold adenot, v_addi. cbn [a_base a_off edenot ev ENV]. rewrite P0. subst dst. f_equal; lia. }
      rewrite Edst in HK2.
      pose proof (env_app_know RSEGS vals1 (junk_vals R2) (blobs_ev BL) (wbytes MG dst [Z_to_bv 8 10]) knH40
                    ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
      clear HK2.
      set (vals2 := vals1 ++ junk_vals R2) in *.
      assert (HL2 : length vals2 = 231%nat) by (subst vals2; rewrite length_app, junk_vals_length, HL; reflexivity).
      assert (Q0 : vals_ev vals2 0 = sp0) by (subst vals2; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
      clearbody vals2.
      change (Env (vals_ev vals2) (blobs_ev BL)) with (ENV BL vals2) in HR, HK.
      eapply (of_segH4 vals2); [exact HL2 | exact Q0 | exact HR | exact HK].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem of_tail : ltac2:(zQ "i40!h9!jc!hh1!hg8!ksc!kt9!pd!n7!kt3!kk5!ju5!hhe!ku7!lh3!jo0!ua!kue!kkf!hh8!kl6!li9!lgc!hl3!hoa!hr8!hvc!ig4!ik6!ip2!kh3!lif!jj1!jjc!lj8!lk0!llb>4path@1$2@1$1@1$0#8>2pp@1$1@1$0#k0>2t8@1$2@1$1@1$0#8>4vals@1$2@1$1@1$0#k0>1R@2$h8@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@1$h4@3$i3@1$1@1$0#8@2$a@1$0#8Z^6>0@2$8@1$9@2$3@1$1@1$0#8^7+hvvvf>0@3$6$h2@2$3@1$1@1$0#k0^5Ni7>0@3$6@1$1@1$0#k0@2$e^6N0?3sp0>0@3$6@1$1@1$0#k0@2$e^7N2^9>0@2$8@2$5@1$0#k0?3sp0@2$5@1$0#k0^a>0@2$8@2$4@2$4@2$5@1$0#k0^b@1$9@2$3@1$1@1$0#8^c+8@2$4@2$5@1$0#k0?3sp0+kgggg0>0@2$8@2$4@2$4@2$5@1$0#k0^c@1$9@2$3@1$1@1$0#8^d+8+ogggggggggg0>0@3$i0@2$f?2BL^b$i2^a>0@4$hf$7@2$f?2BL^c^a$i1>0@3$6@1$b@1$2@1$1@1$0#8@4$d$7^b^f@2$h5@2$3@1$1@1$0#8^h0N1@2$c@1$2@1$1@1$0#8@3$h0@1$1@1$0#8^h0@3$h1@1$1@1$0#8@2$a@1$0#8Z@1$h3@1$1@1$0#8>0@3$6@1$b@1$2@1$1@1$0#8@4$d$7^c@2$a@1$0#k0@2$4@2$5@1$0#k0^h0@1$9@2$3@1$1@1$0#8^h1N8@2$c@1$2@1$1@1$0#8^f@4$hc$7$hb@2$h6@5$h9?2fx^e@2$a@1$0#k0+knin4^d@1$ha$7?5model@2$he@1$hd^h2@1$h7?5model").
Proof.
    (* LPS 75d69e00: replay replaced; proof text from boost-beast http_request (branch
       a donor branch), constants mapped to boost-json's own (see the commit). *)
    intros path pp t8 vals R M Hnonul HPl HL P0 P2 Hpp1 Hpp2 Hpp3 HR HK Hstr Ht8.
    unfold t_die.
    eapply (of_segBC sp0 BL model Hvsp Hh Hlazy path pp (Z.of_nat (length path)) _ t8 vals);
      try eassumption; try lia.
    intros vals' R' M' HL' Q0 Q2 Q113 HR' HK' Hstr'.
    destruct (Z.le_gt_cases (Z.of_nat (length path)) 62) as [Hle | Hgt].
    - eapply (of_segF sp0 BL model Hvsp Hh Hlazy Hfd2 Hrdr path pp _ vals'); try eassumption; lia.
    - destruct (Z.le_gt_cases (Z.of_nat (length path)) 63) as [Hle2 | Hgt2].
      + assert (E63 : Z.of_nat (length path) = 63%Z) by lia. rewrite E63 in Q113.
        eapply (of_segF_gen sp0 BL model Hvsp Hh Hlazy path pp 63 _ vals'); try eassumption; try lia.
        apply of_segG3. exact E63.
      + eapply (of_segFG4 path pp _ vals'); try eassumption; lia.
  Qed.

End Tail2.
