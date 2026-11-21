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
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Ubsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame AgentLib SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4 Spec LibTail RefMemcpyLib.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefExitBase LibDiagKn RefPrintfBufBase RefMemcpyBase RefMemcpy RefOpenFailCS_defs RefOpenFailCS_tail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.U Require Import RefUsageCS_defs RefUsageCS_tail.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefUsageCS () := KReplay.lz_vm "#$iyC46Stdlib5Lists4!s+#6nth_okC47Corelib4Init5Logic8eq_ind_rK!sD+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!tR19Datatypes4list!sF>6op!sl#00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun7vals_evC13~~~I!u~72eq00!uU>Z02C!uU@;bv_unsignedC5!wK&6ZArith6BinInt1Z2leK!uX;3nat!t3C7Z_to_bvC4ELinuxProcessSemantics?!s<2>Riscv!sE+@word!sh#le_bytesC8!vkN1U?RefUsageCS_tail3ENV!vr%!soP=SymExec2Sound4SX2S9mem_denot!sv&!v`;3sub!xqP7Cat!t;#6w!uh%!t,$!xW@3!tK=addK!yT;1K!uzO8!uz'3SX24expr02!tj&!sm\5saddr01!wYV!sn06a_base!smde!x?/!uL]a_off!v:c!w%%!v9f!uJ/!xy76!#6O$!#6MF1!sKG3!#37@1!}y^defs7u_logM!v7W!~n54PRE7!sph9!sp#_word!w1'!#5G85!#57#7Prelude5bvmap!#;I62In!wt83!x;#!#9j;length!~m<6of_nat!#5Rb7regs_ok!#6Hh7know!st,!uR13Nat!#4s5!#<u21!sFB2!vQ<3appK!#=ZB1!#7gO8Prop!u[#9u64_range!#8rBpow!#<q=t!#>?73and00!#3g\6sentry!#3i&!so^k!so%5!sok6!sok7!sok4!sok!w3d9sym_state!sre7scripts!#9\'!{LX7seg_rom!sjV4Spec9msg_u!#6I#!#68?!#DY25S!u|#4m_fs!tCU5t_di!t?&!#IY<prod!#H3-!sF81!#=3\8!x;#exec!#6HU!#B#1_log!sldcarry!#7|h8sc!#GE-!vb,!#;&$7!s+#Def6Forall!vc_6s_regs!z=V9SymDriveX;log_below_b!so&!#7514Znat5Nat2Z7inj_iff!#=677iff_sym!sf>9is_nonneg!#8B;>pow_po!sND:!sN#!sJ&!#?'&9micromega9SatDivModCZ_mod!sP&!s{C6moduloK!sw56VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!|l#!sQ47Env!sT#5PE!#K,#!#=6C2!skE7!v>65Tauto8B!tZ&!sH6:Z!u$+=Z!sT$CheckerC!uu<4find!sqAC!sq0_s!|C#!{f]2!#U}&!ww@1K!wYC5Psatz02!|QZ?!#Ro'_abov!#7s'!tD&!#FY,9nth_error!#[#8!|P#refl!vc6;ZifyClasses3inj!sIB;rew_!su%v!uMZ8kimg_rdn!#3f_<kwr_store!#Fg'!zqE4!sIE1!}{=to!#Ia#!#EI;max!sC<8max_spec!#\h8or!}m@3Pol!z-M4!#J^cu_small!#ADU1U=RefMemcpyBase3mcH!#AC&I!sod0!#<~b6sr_ge!#Tj'!#_N>5bv_eq!#CGX4getr!{EV!#c2&reg_val!tuG4BvWfK!#eLC!#N-Y5v_add!u@V7LibTail7vadd_wZ!si^6ed_var!shblit!shb!v#Y5Hoare;ret_ok_even!{&V1U9!{s+:ref_m!s1$!t]V!za,mks!v0&I!zaPCatSim6msteps!}H+!siO<!uB+Lib5keep!#EA%!#k\9x00K!#L0I3Run6config!{YS!#9P&8blob!#m@+!}vW:sr!zp#s_l!z2W!#;&+@!#[\#after_!vE-!uNY9junk_val!#iv&!#6C[3env!#R?'!#KL93map!tvY?sr!ui&call_j!y19Peano2le00!#;3b4fla!wma:!sh#_intro!vy&!#\K;1!#Okclog_!u$Z!z\&;!#QJ#!w&%!sl%c!#4:P:!#f#+>u!#48$1!#qo/!|AWkn!|Ah<env_app_know!}3a!|>+_!#g&%!{W&!#HM4:!sG%!tF#C!zf9t!tSZ=!#zT%!uI$l!tP2!#Hp87!#Hp%!t@Z9rdn_agree!t<H8or_morph!#<EPStepTac6u_Z2b!#6hV!#wy&>!t}#!#w}$_ou!#soV!#n747us!s-$!#6lWhapeAlg9rz_!#;i$!taV!#6l/4s_pc!tYW!#>$&3!#N%'!#v9b3!y%H5mkrel!#KsC!#WV'!#LF6!#VF%G!sJ'4!sJF8!#T\?3!#MTJ6!sO6!#Vh,;!#O?$!v\$02!v%E!~r$!sK@6!sK$!#YgE3!$'yY8!#S,&!vcF5!sJF3!sJF6I!|EX8realize!#E/X!#?&'6rz_ru!{\&!#h[;!#|'#!$2k/!t%96images5Ubsan1M?loaded_segment!$+}F1K!#zZ?5Instr5aluop01I!}\b!vX&I!#S']!#ph$!soek!so1!#ld;bool!#m+>!sF$1I!w%?0!#bl;5eKind!tK=unit!#Yt7!se%4kind!#YsE3Op2!$'0=!t5%1I!#3cL0!#47M!tmJ!sMJ5!vj68Zify!zf#@!$%$$_!#^L$_eq!#<\a8!$'m#l!#Rv&!#Gb74True!#O7Q4Scfg=hunspell_scfg!#>\cdefs6u_knB!#4M&!#nR<6inj_le!sHD!#b/+5!sG$8!#Da#Na!$'/'!#pFB!sI#!uIQBRefOpenFail!uL&4FUEL!v>X!ss65STOPS!w4kscrA!srh5srUS0!sqikn!sq+!#5v\8sidecond!#6id!$$S,!srd!$$S'!#7^8!}I/0!~[cpre7_im!}Qi5!}Q#!yB'!#4q=7Inj_Z_Z!#9G=N!$JDQ!#]j/;callee_kep!#R+`?!so-_no!#iuc4ridx!sk%!#UJ\6valsU!~='!#[F:nth!sB<s!#jvR!v/';nth_map_!sh#!xU1!#T=,=app_nth2_plus!$L|Abv_wr!$>/,!#6c'divAZ!sg#!#}~#idemp_r!#N@X=!t3&64!sr#!u/'!te?@!$Nc%!$Ou+!#Do?3Sem5alu64!toY7alu!#iV,!#8Oc3sp!y}d9spxUS!#om,!spQ@RefPrintfBufBase>!$AY%_by_!{l+!s{c9all!s~#3!$N7%!#=B=8inj_succ!tBR9LibDiagKn8kn_cell!#VQV!$S66!#Hl$!$Cn+!yQO!#`E%<kalign!#d'-!smY!$Br#!sm0!uTb6estart!zDdevUS_junk!yGX;RefExit!yB#=!#T5&_data!vK]:!$%v#!vI[!yg/;canary!#dZ-!sq[?diag!z\%!sug;!$KH%!#e%#!vH\;k!$]C#!#k`7!$;;82!#F,bUS_STK!utb6CANARY!slb:!wY,!{ld!wU&!#>4&!sp]:!#e2%_c!tcd:!#?n$!#PI+!uV^!#8j%!uV'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option37Corelib4Init5Logicm22eqk14list69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~o26wbytes79OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~s59mem_denot69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~hh67vals_ev79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UfRefUsageCS_defs~~~~~~hla7u_logM179OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UfRefUsageCS_tail~~~~~~hq93ENVhq94PRE746Stdlib6ZArith6BinInt1Zhvc3subhf7Z_to_bvhfbbv_unsignedk16lengthhvc3add69OSSVerifyaboost_jsonafuzz_parse6images5Ubsan1M~~~~~~ik3floaded_segmentshvc2lehvc6of_natk14Some69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~iq33rdnk13appk14consk13natk13nilm23not37Corelib4Init3Natjg43add3h5LinuxProcessSemanticsfLinuxProcessSem3Runjhd5mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statejl24m_fs3h5LinuxProcessSemantics5Riscv7Preludejo85bvmapiq34mkstiq37seg_rom69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jsadhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~kh28realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~kl99msg_usagekl95t_dies57know_oks57regs_okhla5knUS0hla5srUS036Stdlib5Lists4Listksc2In69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~ku59junk_vals89OSSVerify6Proofsaboost_jsonafuzz_parse3lib1UaRefUsageCS7UsageCS~~~~~~lid6valsUSjl25Modeljhd8valid_spk14Nonejl28m_haltedk14prodjl29m_vm_lazyjl27FdEntryjl29FdChanneljl29fd_lookupjl25m_fdsm21Iiq34getrhf2BVhf4BvWfhh66stk_okhla6US_STKm23and01Zhvc2lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib1U9LibDiagKn~~~~~~mi38cells_okmi3adiag_cells3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsmnbh0word_to_le_byteshvc3powmi39canary_ok" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section UsageCS.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.                 (* [comment removed for export] *)
  Variable model : ltac2:(zQ "10!lne$0").
  Hypothesis Hvsp : ltac2:(zQ "10!lo7@1$0?3sp0").
  Hypothesis Hh : ltac2:(zQ "60!h9!jc!lp3!l9!n6!lpa@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!h9!jc!lq6!nb!iv8!n6!lqd&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd2 : ltac2:(zQ "90!h9!lra!ihb!ipc!l9!n6!ls5!lt2!ltf@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+2@2$3$1@1$6@2$2@1$0#k0+2").
  (* LPS 75d69e00: the launch's channel reader, constant over the run; us_tail_cs hands it
     to RefUsageCS_tail.us_tail (its stdio_call_sound / ref_exit_Z premise). *)
  Hypothesis Hrdr : m_channel_reader model = true.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Lemma umemcpy1_denot : ltac2:(zQ "e1!h9!jc!l9!n6!nb!rc!hga!hkf!hpe!hud!hv4!ih4!ihb!ii5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4vals@1$4@1$1@1$0#k0>1M~0>0@3$3@1$1@1$0#k0@2$7^2N0?3sp0@3$3~0@3$6@1$9^3^2$8@3$5^2@2$c@1$0#k0@2$b@2$d@1$0#k0?3sp0+ij0$a").
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "##0;h01Hh12H0h21Mh32P0h41bh51lh64valsp;1p;2p;3p;6p10000p4p710g000KR!s3&p8g000ij10Tg001Nj1A!s/$lj1?Tg002Oj1G!s/$oj1STg003Qj2BTg004Sj35!s/$mj19Tg005Kj2<Tg0065j2F!s/$Qj14Tg0070j2:!s/$Vj2ETg008^j1DTg009gj3CTg00;7j2R!s/$Tj36Tg00<Vj1QTg00=4j2@!s/$Qj2PTP0j6O!s5$kj1NTg00?2j2LTg00@:j1KTg00AAj2>Tg00BHj1JTg00CNj1ITg00DUj2MTg00E\j6HTg00F8j1;Tf0R0#0#0p=8%;0#;p=1%;!s6$7%0!s@$#0p==!s2+!s$'p=3%0!sV$2g00F]R1#0#8R2!s+$3#AR4#?R5#G%A2#?R6#S\5R7f1g00GBR8'Bp,3sp0R9555p,4SPlo%11#!s$/7#8#=#3!s$$91<49R1'F!sR$hi%03R!s@%!sF&,F1%G6R6%48#4!s$,R:%13#7#7#2!s&$2!s-&1!s-$8!s6$1#8!s6$1!s4$9R3,:4'ER;f5#Df4R<g00GaR=3C%12#=R2#9,R1,:4R1=6<0557X56P5P91<40%Q2R2'@,:4=6<;A6<1;557X45f3R5?61;R1,P71B<8f2EO%D<R<%N8/L2R2#K'>,<4%J!sf%%I3,><,E:R:565=571e1M<2=65:!s3$AC<5=!s0$g00Hng00J8EHb1b0W3W2W6o"). Qed.

  (* [comment removed for export] *)
  Theorem us_tail_cs : ltac2:(zQ "i40!h9!jc!nb!ij3!ijc!ii5!n6!in9!ioc!ip2!ihb!l9!ipc!ite!hkf!hud!iu5!iub!iv2!iv8!ive!jh6!jk9!jo0!jqe!jr7!jrf!kg1!kkd!kp0!kpd!kq6!kr0!kra!ks3!ktf>3a0s@1$2@1$1@1$0#8>2pp@1$1@1$0#k0>2t8@1$2@1$1@1$0#8>4vals@1$2@1$1@1$0#k0>1R@2$h8@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@1$h4@3$i3@1$1@1$0#8@2$a@1$0#8Z^6>0@2$8@1$9@2$3@1$1@1$0#8^7+hvvvf>0@3$6$h2@2$3@1$1@1$0#k0^5Ni6>0@3$6@1$1@1$0#k0@2$e^6N0?3sp0>0@3$6@1$1@1$0#k0@2$e^7N1^9>0@2$8@2$5@1$0#k0?3sp0@2$5@1$0#k0^a>0@2$8@2$4@2$4@2$5@1$0#k0^b@1$9@2$3@1$1@1$0#8^c+8@2$4@2$5@1$0#k0?3sp0+kgggg0>0@2$8@2$4@2$4@2$5@1$0#k0^c@1$9@2$3@1$1@1$0#8^d+8+ogggggggggg0>0@3$i0@1$f^b$i2^a>0@4$hf$7@1$f^c^a$i1>0@3$6@1$b@1$2@1$1@1$0#8@4$d$7^b^f@2$h5@2$3@1$1@1$0#8^h0N1@2$c@1$2@1$1@1$0#8@3$h0@1$1@1$0#8^h0@3$h1@1$1@1$0#8@2$a@1$0#8Z@1$h3@1$1@1$0#8>0@3$6@1$b@1$2@1$1@1$0#8@4$d$7^c@2$a@1$0#k0@2$4@2$5@1$0#k0^h0@1$9@2$3@1$1@1$0#8^h1N8@2$c@1$2@1$1@1$0#8^f@4$hc$7$hb@2$h6@5$h9?2fx^e@2$a@1$0#k0+knhnc^d@1$ha$7?5model@2$he@1$hd^h2@1$h7?5model").
Proof.
    (* LPS 75d69e00: replay replaced (it applied RefUsageCS_tail.us_tail at the old arity,
       before Hrdr).  Proof text from boost-beast http_request RefUsageCS.v us_tail_cs
       (a donor branch), constants boost-json's own: PRE7 at 0x11470 (pre7_img's
       statement), memcpy return 0xe36c4 (us_tail's start pc), memcpy entry 0xee250
       (BJU/BJIface.RMEMCPY), image high 0x131000 (U/RefOpenFailCS_defs.IHI). *)
    intros a0s pp t8 vals R M Hnonul HL0 HL P0 P1 Hpp1 Hpp2 Hpp3 HR HK Sr Ht8.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    run_blk_keep u_scrA 38%nat.
    assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M0 x = M x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) M _ 0%nat 0x131000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    clear EQM. rename M0 into M1. rename M into M0. rename M1 into M.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x11470) 7 = Some PRE7).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kimg_cov 0x11470 7) in exact i)
                 _ _ 0x11470 7 HK eq_refl) by (cbn; lia). apply pre7_img. }
    assert (Hdst : store_ok RSEGS M dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                    _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x11470) 7 PRE7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?PRE7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0xe36c4 : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11470) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x11470) 7 _ (seg_rom RSEGS) MC Rc (0xe36c4 : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 975440) with (0xee250 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0xe36c4 : word) with (Z_to_bv 64 0xe36c4) by (apply bv_eq; reflexivity).
    lazymatch type of HR with regs_ok ?E ?sr ?Rc =>
      pose proof (regs_after_keeps vals (blobs_ev []) sr Rc R2 callee_kept
                    ltac:(rewrite HL; vm_compute; reflexivity) HR Hkeep callee_kept_no0) as HR2 end.
    rewrite HL in HR2. clear HR Hkeep. rename HR2 into HR.
    assert (HK2 : know_ok RSEGS (ENV vals) (wbytes M dst PRE7) u_knB0).
    { subst dst. rewrite <- (umemcpy1_denot vals M P0).
      eapply (carry_after RSEGS (ENV vals) M u_logM1 u_knA [] u_knB0 [] []);
        [vm_compute; reflexivity | | exact HK | constructor].
      cbn [log_flat u_logM1]. split; [lia|]. split; [|exact I].
      apply flat_intro; cbn [edenot ev ENV]; rewrite ?P0; lia. }
    clear HK.
    pose proof (env_app_know RSEGS vals (junk_vals R2) (blobs_ev []) (wbytes M dst PRE7) u_knB0
                  ltac:(rewrite HL; vm_compute; reflexivity) HK2) as HK.
    clear HK2.
    set (vals1 := vals ++ junk_vals R2) in *.
    assert (HL1 : length vals1 = 70%nat) by (subst vals1; rewrite length_app, junk_vals_length, HL; reflexivity).
    assert (Q0 : vals_ev vals1 0 = sp0) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P0).
    assert (Q1 : vals_ev vals1 1 = pp) by (subst vals1; rewrite vals_ev_app_l by (rewrite HL; lia); exact P1).
    clearbody vals1.
    change (Env (vals_ev vals1) (blobs_ev [])) with (ENV vals1) in HR, HK.
    eapply (us_tail sp0 model Hvsp Hh Hlazy Hfd2 Hrdr a0s pp t8 vals1); try eassumption.
    - rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Sr. apply rdn_agree. intros j Hj. apply Habove. rewrite u_small by lia. lia.
    - rewrite rdn_wbytes_out; [ | | |]; subst dst; rewrite ?PRE7_len; unorm; try lia.
      rewrite <- Ht8. apply rdn_agree. intros j Hj. apply Habove. unorm. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Variables (pp : word) (tid can : Z) (s0v : word) (R : bvmap 5 word) (M : word -> option byte).
  (* [comment removed for export] *)
  Hypothesis Rsp : ltac2:(zQ "a0!h9!lu8!n6!luc!ih4!lv4!lv9!ihb!jc!ii5@3$2@1$8@1$0#k0@2$3?1R@3$5@1$0#5+2Kv$1@2$6@1$0#5+2@2$7@1$0#k0@2$4@2$9@1$0#k0?3sp0+o0").
  Hypothesis Rtp : ltac2:(zQ "80!h9!lu8!n6!luc!lv4!lv9!ihb!jc@3$2@1$7@1$0#k0@2$3?1R@3$4@1$0#5+4Kv$1@2$5@1$0#5+4@2$6@1$0#k0+hgurv8").
  Hypothesis Rs0 : ltac2:(zQ "80!h9!lu8!n6!luc!lv4!lv9!ihb!jc@3$2@1$7@1$0#k0@2$3?1R@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@2$6@1$0#k0+2").
  Hypothesis Ra1 : ltac2:(zQ "a0!h9!lu8!n6!luc!ijc!lv4!lv9!ihb!jc!ii5@3$2@1$8@1$0#k0@2$3?1R@3$5@1$0#5+bKv$1@2$6@1$0#5+b@2$7@1$0#k0@2$4@2$9@1$0#k0?3sp0+8").
  (* [comment removed for export] *)
  Hypothesis Mstack : ltac2:(zQ "70!h9!mg0!mga!in9!ih4!ihb!ii5@4$1$3?1M@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+j0$2").
  (* [comment removed for export] *)
  Hypothesis Mro : ltac2:(zQ "a0!h9!jc!lp3!l9!mh4!n6!mha!ioc!mhd!ihb>1i$6>0@2$4@2$7+hggg0^1@2$8^1+vkgg0@3$5@1$3@1$1@1$0#8@1?1M@2$9@1$0#k0^2@1$2@1$1@1$0#8").
  (* [comment removed for export] *)
  Hypothesis Mcells : ltac2:(zQ "20!mm1!mmd@2$0?1M$1").
  (* [comment removed for export] *)
  Hypothesis Mtid : ltac2:(zQ "a0!h9!nb!ihb!jc!ipc!l9!n6!mr2!ite!in9@3$6@1$5@1$1@1$3@1$0#8@4$8$9?1M@2$2@1$0#k0+hgurl0N4@2$4@1$1@1$3@1$0#8@2$7N4@2$2@1$0#k0?3tid").
  Hypothesis Htid : ltac2:(zQ "30!mhd!mh4!ms7@2$1@2$0Z?3tid@2$0?3tid@2$2+2+h6").
  (* [comment removed for export] *)
  Hypothesis Mcan : ltac2:(zQ "10!mse@2$0?1M?3can").
  (* [comment removed for export] *)
  Hypothesis Margv : ltac2:(zQ "c0!h9!nb!jc!ipc!l9!n6!mr2!ite!in9!ijc!ihb!ii5@3$5@1$4@1$1@1$2@1$0#8@4$7$8?1M@2$a@1$0#k0@2$9@2$b@1$0#k0?3sp0+8N8@2$3@1$1@1$2@1$0#8@2$6N8?2pp").
  Hypothesis Hpp1 : ltac2:(zQ "30!h9!ii5!ioc@2$2@2$1@1$0#k0?3sp0@2$1@1$0#k0?2pp").
  (* [comment removed for export] *)
  Hypothesis Mra : ltac2:(zQ "c0!h9!nb!ihb!jc!ipc!l9!n6!mr2!ite!in9!ih4!ii5@3$6@1$5@1$1@1$3@1$0#8@4$8$9?1M@2$2@1$0#k0@2$a@2$b@1$0#k0?3sp0+j8N8@2$4@1$1@1$3@1$0#8@2$7N8@2$2@1$0#k0+ttln4").
  Hypothesis Ms0 : ltac2:(zQ "c0!h9!nb!jc!ipc!l9!n6!mr2!ite!in9!ih4!ihb!ii5@3$5@1$4@1$1@1$2@1$0#8@4$7$8?1M@2$a@1$0#k0@2$9@2$b@1$0#k0?3sp0+k0N8@2$3@1$1@1$2@1$0#8@2$6N8?3s0v").
  Hypothesis Ms1 : ltac2:(zQ "h00!h9!nb!jc!ipc!l9!lu8!n6!mr2!luc!ite!in9!ih4!lv4!lv9!ihb!ii5@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+k8N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+9Kv$5@2$d@1$0#5+9").
  Hypothesis Ms2 : ltac2:(zQ "h00!h9!nb!jc!ipc!l9!lu8!n6!mr2!luc!ite!in9!ih4!lv4!lv9!ihb!ii5@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+l0N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h2Kv$5@2$d@1$0#5+h2").
  Hypothesis Ms3 : ltac2:(zQ "h00!h9!nb!jc!ipc!l9!lu8!n6!mr2!luc!ite!in9!ih4!lv4!lv9!ihb!ii5@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+l8N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h3Kv$5@2$d@1$0#5+h3").
  Hypothesis Ms4 : ltac2:(zQ "h00!h9!nb!jc!ipc!l9!lu8!n6!mr2!luc!ite!in9!ih4!lv4!lv9!ihb!ii5@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+m0N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h4Kv$5@2$d@1$0#5+h4").
  Hypothesis Ms5 : ltac2:(zQ "h00!h9!nb!jc!ipc!l9!lu8!n6!mr2!luc!ite!in9!ih4!lv4!lv9!ihb!ii5@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+m8N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h5Kv$5@2$d@1$0#5+h5").
  Hypothesis Ms6 : ltac2:(zQ "h00!h9!nb!jc!ipc!l9!lu8!n6!mr2!luc!ite!in9!ih4!lv4!lv9!ihb!ii5@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+n0N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h6Kv$5@2$d@1$0#5+h6").
  Hypothesis Ms7 : ltac2:(zQ "h00!h9!nb!jc!ipc!l9!lu8!n6!mr2!luc!ite!in9!ih4!lv4!lv9!ihb!ii5@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+n8N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h7Kv$5@2$d@1$0#5+h7").

  Definition valsUS : ltac2:(zQ "30!nb!h9!jc@1$0@1$2@1$1#k0") := ltac2:(zQ "70!h9!jc!iub!ihb!iu5!iv8!li0@3$4@1$1@1$0#k0@3$2@1$1@1$0#k0?3sp0@3$2@1$1@1$0#k0?2pp@3$2@1$1@1$0#k0@2$3@1$0#k0?3can@3$2@1$1@1$0#k0?3s0v@3$2@1$1@1$0#k0@2$3@1$0#k0Z@3$2@1$1@1$0#k0@2$3@1$0#k0?3tid@1$5@1$1@1$0#k0@1$6?1R").
  Let E : env := ENV valsUS.

  Lemma valsUS_len : ltac2:(zQ "60!ij3!iv2!n6!h9!ln4!jc@3$2$1@2$0@1$5@1$3#k0$4Ni6").
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "##'Ph01np;1p;2p;3p;6g000ij13Tg001Nj1A!s/$lj1<Tg0070j25Tg00PVj1@Tg00Q6j31Tg00Lcj24Tg01WPj1;!sJ$?j27Tg004Sj36Tg00=Qj2:Tg01d?j1?Tg000Kj68!sn$Vj3>Tg01eMj3=Tg006Qj12Tf0R0#2!s$%p=0%20#2p=9g02<?R1g00F]#3!s$-AR2#<R3p,3sp0p,2ppp,3can,52p,3s0vg02=e!s4%tid,52%@351!s%3R2'4R4p,1RR5#;R6,43R7'7g00GB#0!s$1R8#9#0R99610X01P1P81740=619X011:19P7%?5E8A>326,43A=326E8g02`U,43=619eo"). Qed.

  Lemma evUS_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "##-\h01ih12Hih21bp;2p;1p;4p;3p;6p;5g01elj2DTg000ij14Tg001Nj19!s/$lj1?Tg01WPj1JTg0070j25Tg02a\j48Tg00F8j1ATg00MCj16Tg01E<j27Tg004Sj32Tg00=Qj2NTg02b8j2MTg01Y\j4L!s8$Tj6K!tL$Kj6=Tg00PVj1:Tg00Q6j31Tg00Lcj2I!sA$?j2<!sA$Vj3CTg02c\j5ETg003Qj2;j1BTg002Oj1FTg01T8j1GTg01XVj2HTg0147j2>Tg006Qj13Tf0R0#3#3p=@%3!s0$#3p=0g02<?R1g00GBR2#@#0R3#@#0!s$,R4,D0g00F]#4R5#4#4R6#4!s$$9R7#?R8P8f1R9p,1RR:#JR;g02=e,57R<C8R=%A5#9R5f2#6'5,7:9280X28R>P8%69,55,7:R?P>1N8?P8P9P1P8%60!s?%X01R11M24CLP<C8P8P1P9P4P<P0EKE=A28=?eP8p,3sp0p,2ppp,3can,57p,3s0vp,3tid,57%:8518918<518!s%+R7,I8/<9R=AC87;R0!t4&7P;P<P9DEE=1;0==28?eg02`UR01<39R9';!s:$%B0%96#?#F#:#G'H/>9!s>$p,1E!s2'W1W0o"). Qed.

  Lemma spxUS_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
Proof.
ltac2:(KReplay.run1 (kr_t_RefUsageCS ()) ["UsageCS"] "h01zh12b1h22b2h31nh41Hh51bh61kp;1p;2p;3p;6g000ij17Tg001Nj1HTg001lj18Tg0147j2?Tg0070j29Tg01HEj2ETg005Kj20Tg00=4j22Tg004Sj36Tg01DXj3>Tg02d>j24Tg004mj1<Tg00S[j2GTg00mij23Tg00=Qj2FTg02ddj3DTg02eKj1;Tg02fUj2:Tg02gDj3CTg02glj2BTg000Kj6=Tg02i0j1ATg00AAj2@Tg02CHR0f1R1f0R236p=1P0f4R3f3R4f2R5P1P2E=p=5g00F]#7R6#7#7#7#7#7R7#HR8#8R9p,1ER:g00GB'?R;1982R<'ER=p,3sp0,08R>/21R?,98R@9692X59g02\YRA%82RB%81RCg00TT%85?61210451041'1RD[10511052'1%84?651[RE%83?645\DA>512P2n2001000000120000000W2W1W3PE^2C^1B^3AP2P81981,08RA,2>RB,98RCP@148B12>5RE,98,08RD,12X001481R412>2R3,48/1DX00148?RD1485,2>,48/12X0012>4RF%<6%<7'GR7'3148ER6,12X001317RG1337/16X0013?7R61357,2>/37/12X00P613E7,12X001F0612>G/37AD1>7D5PD%;?D5P4%;1D5148F%;FD5108@1:8?D5PA1:81D5108C1:8BD5O4b41983R3969=eg02>C?C;<1B;<E=%A2,@:=693eX60o"). Qed.

  Ltac reg_caseUS :=
    cbn [nth srUS0 allregs32];
    first [ rewrite spxUS_val
          | lazymatch goal with |- _ = edenot _ (EVar ?n) =>
              change (edenot E (EVar n)) with (ev E n);
              first [ rewrite (evUS_junk (n - 6)) by lia; reflexivity | idtac ]
            | |- _ => cbn [edenot] end ];
    first [ reflexivity
          | exact Rtp | exact Rs0 | exact Ra1
          | rewrite Rsp; f_equal; lia
          | idtac ].

  Lemma regs_okUS : regs_ok E srUS0 R.
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "##e?p'0h02Hih11ni001nh21bh32Hah44__p1h54__x1h61ih71Hh82H0h93Hi0h:7__arithh;4__ffh<7__sat10h=6!s0$8h>!s/%9h?8__varmaph@5__withA4cstrhB1xp%0p;1p;2p;3p;4p;6p;<p;7p;8g00F8j18Tg000ij14Tg004mj17Tg001Nj1RTg005Kj2]Tg0065j2I!s/$QR0j10Tg01elR1j21!sW$lj1XTg01Gbj3@Tg00CNj1KTg0070j2FTg00=Qj2?Tg00AAj2=Tg02a\j4DTg00<Vj1_!sJ$4j2>Tg01E<j2L!tb$Sj3ATg00;7j2^!t}$Kj6JTg02i0j1PTg02j<j1OTg00MCR2j1HTg00T8R3j2CTg01gOj4[Tg00kGj1Z!s/$lj2YTg00S[j2vTg00lTj3uTg00m8j2t!s/$ij2sTg00PVj1rTg002Oj1pTg015:j1oTg00nIj2nTg023hj4Q!s8$gj1kTg00oEj1jTg01<Kj2MTg0100j2hTg0225j4U!s8$Sj1gTg028mj6fTg011Xj2eTg012:j2d!s/$fj3cTg013Ej4iTg02kFj4bTg0147j2mTg025[l<VTg021Pl<a!t1$`j7`Tg026fj3G!tp$Dj8qTf0R4#8#8p=N%8!s0$#8p=E%44#4p=W!s-$#!s2$l!s2+!s$'p=9f7R5f6R6f5R7f4R8g02l[R9f3R:CD'Lf2R;g02>oR<f1R=g02SIR>P4CD'=3Ap=21L;==A:4p=B1m=4,?;p=31>8:/>;/>=/>4p=5g02<?R?P?g02CHR@P@P0P2P2P6g02mkR6P7P8P?P?P!sA,:P6P;P=P4M<VM<Vp=6!sE$1P2P3g02N=!sZ$:!sJ'ap=\g02=eR3/I4p=;P=g02CfR2g02DER1P1g02DeR6P4g02ElF`p=TAG@8:=G@;=G@==G@4p=:P:P2P1P1!tN'Gqp=S%04#0#0#0p=<p,4SPlog00F]R0#8#N#E!s$$4#W#l#9!s$$7%40RA#4RB#4RC#4RD#4RE#4RF#RRGp,3sp0']RH'I!su$hi%4FRF!sc&!sg$,IHp,1ERIP>p,1RRJg00GBRK#0RL#0RM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk,14RlP?%XGRmPJ%8ARn#RRo#XRp!w:$JmRq9@o3RrPIP=%K3RsG2^0lP=11Kk1FG3,?mPmPJPr1=IsCBe!s3$pPKP9PrCDP<PKP>PsCD,=ICBeW0P?%04R>/1k!sP%%0=RKPrPIPKPsG2]0P411LkA3mIR!sr&L!sE$LPsG2!sg&>!sg0KR!sH-!sg%MkPm%_FR<,>H,FGR9%7ARA=@oq,LJRl=Am4X2mPm%7F,^H,FGAAm49X2m1?m9Plp,3RspEJ%P<,=I%O<EJ!tZ&M!t8$M!tZ<LR!sH-!tZ%N!uC$T!sg&N!sE$N!sg<MR!sH-!sg%Okp,3RtpPmPJ%7B=@oq%8D#N#4#8!s&$N!zn&7#K!w,%!t:&O!sp$O!t:<NR!sH-!t:%P!t{$V!sg&P!sE$P!sg<OR!sH-!sg%Q!sg$W!sg&Q!sE$Q!sg<PR!sH-!sg%R!sg$X!sg&R!sE$R!sg<QR!sH-!sg%S!vM$s0!vM%CRC!vO$KA!v90S!s\$S!s~<RR!sH-!s~%T!tg$Z!sg&T!sE$T!sg<SR!sH-!sg%U!sg$[!sg&U!sE$U!sg<TR!sH-!sg%VkPm1>HC,FG!uS$8nRG#7=@oqP4CBX2mp,3Ra1%PC!zt$C!zt+V!sp$V!t:<UR!sH-!t:%W!t{$]!sg&W!sE$W!sg<VR!sH-!sg%X!sg$^!sg&X!sE$X!sg<WR!sH-!sg%Y!sg$_!sg&Y!sE$Y!sg<XR!sH-!sg%Z!sg$`!sg&Z!sE$Z!sg<YR!sH-!sg%[!sg$a!sg&[!sE$[!sg<ZR!sH-!sg%\!sg$b!sg&\!sE$\!sg<[R!sH-!sg%]!sg$c!sg&]!sE$]!sg<\R!sH-!sg%^!sg$d!sg&^!sE$^!sg<]R!sH-!sg%_!sg$!|E'_!sE$_!sg<^R!sH-!sg%`!sg$f!sg&`!sE$`!sg<_R!sH-!sg%a!sg$g!sg&a!sE$a!sg<`R!sH-!sg%b!sg$h!sg&b!sE$b!sg<aR!sH-!sg%c!sg$i!sg&c!sE$c!sg<bR!sH-!sg%d!sg$j!sg&d!sE$d!sg<cR!sH-!sg%e!sg$!sH&Pe!sE$e!sg<dR!sH-!sg%fk%0kRC93mI!sk&f!sI$f!sk<eR!sH-!sk%gk%0C!sk0g!sI$g!sk<fR!sH-!sk%h!sk4h!sI$h!sk<gR!sH-!sk%i!sk4i!sI$i!sk<hR!sH-!sk%jk%0!si/j!sG$j!si&%0>/1k%0i!sm$%H=Rj%70R0P!s$$D5P!s0h%7ERE'CS00P>1>40XB@R>P!s$ajO1S01O1S02O1S03O1S04O1S05O1S06O1S07O1S08O1S09O1S0:O1S0;O1S0<O1RCO1RqO1RoO1RBO1R<O1RlO1R9O1RFO1RtO1RuO1RvO1RwO1RxO1RyO1RzO1R{O1R|O1R}O1R~O1P>PiP~P>PhP}P>PgP|P>PfP{P>PePzP>PdPyP>PcPxP>PbPwP>PaPvP>P`PuP>P_PtP>P^PFP>P]P9P>P\PlP>P[P<P>PZPBP>PYPoP>PXPqP>PWPCP>PVQ0<P>PUQ0;P>PTQ0:P>PSQ09P>PRQ08P>PQQ07P>PPQ06P>POQ05P>PNQ04P>PMQ03P>PLQ02P>PKQ01P>P=Pj1?@jF6!s$APkPE1?@EE\P4C[Q00%Z;%H;#;%4G#7RG,YA1C3A%;G1vAGRk,C3[[%;ARjg02Y@R>AuAG=UW3%;k\>^3j%7DRD,tH%;H%;D1sHD#;[[p-0RDg02FLRH#r%pHP@%o@RHP=P@1n@=P=PHCQCQ%k@%j@RHP@1M@3g02EE1h@nRnCU,TH%g1RjPHP@Pn1M@0RnP!s$$D:P!s0hg02HK1M@E!t;$PjPH!#NJ':EfCSCS1eH6P4P;g02BHRHg02BhR6'?1d4;=AH6dAc@3=Cib;b?b@X5@W4%;4P=P!};r/CEP:[[^5@^4DP4!~m%%<5#<!s$/Rp!~~$pPsG2%H5P8P7O4b:b=b>b<bAb9W0X6?P4O1n0110001020111100X1!s>G0!s>~!s>~!s>~!s>50!s>~!s>W!tv~!s>~!uN{P4O1!{l$Cbb8b7o"). Qed.

  (* [comment removed for export] *)
  Ltac kslot HYP :=
    eapply (kword_intro RSEGS E M (EVar 0) sp0);
      [ reflexivity | | lia | lia | lia | lia | exact HYP ].

  Lemma know_okUS : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knUS0.
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "#$Osh04__x1h17__arithh24__ffh38__varmaph45__with57__sat10h6!s0&1h7!s0&2h86!s0$8h9!s/%9h:4__x2h;1zh<1bh=4cstrh>4__x3h?!sL%0h@!s/%1hA1mhB2HahC1dhD2HshE1xhF2HdhG2HmhH1HhI2H0hJ2H1hK2H2hL4Hpp2hM1nhN1yp%0p%1p&0p;1p;2p;3p;4p;7p;8p;6p;5p;<p;Bp;@g000ij13Tg001Nj1wTg005Kj2CTg004mj1:Tg00=4R0j20Tg00F8j1@Tg0065R1j22Tg00mik20r!sX$Sj3BTg00RUk10^Tg00S[k20G!sl$kj1JTg00V8k20TTg00WAj3{Tg00<Vj1STg00;7j2XTg00?2j2yTg00XJk20?!tA$Qj18Tg00CNk107Tg00YSk20PTg00PVk104Tg02nOk10MTg00QVk30LTg02oWk30Kk40!uF$2Ok10DTg015:k10qTg00ngk10jTg00oEk10eTg01<Kk201Tg011Xk20]!u<$Qj2ATg012:k20[!s0$fk30YTg013Ek40!u5$T8R2j2<Tg030gk70WTg00klk20FTg00lTk30E!v[$8k20V!tP$Ij2~Tg0100j2v!s/$Sk10U!su$Tj2lTg031nj7|Tg01[^k30!w2$MCR3j1;Tg0335k20!tl$;hj3zTg00AAj2d!u9$5k30@Tg01\ik80>Tg0070j2!vy$kGj1uTg01@1j2!v-$E\k60=!vB$Xk20<Tg024oj2p!vw$6j3kTg023hj4tTg00@:k10;Tg00BHk108Tg01^1k409!yr$lk106!u,$DR4j2sTg018mj4HTg017lk10O!s9$Jk40NTg01G?j2`!s/$bj3!w+$E<j2!ss$P?j2cTg0147j2aTg01elR5j2hTg034Bj2fTg000Kj6LTg035Lk50JTg036[k80!u6$2ok10nTg01oIk40i!v&$Vk20h!z{$3k20fTg037`k60dTg00gVk20cTg038kk30bTg03::k60HTg00O1k40aTg00Z\k30`Tg0225j4n!s/$`j7mTg028Ik70I!vU$Dj8oTg027Ik40_Tg026fk300!w+$Fk30gTg021Pm<02Tg025[m<0\!sN$@mB0kTg03;Em@0!y'$<Kk60mTf0R6#3#3p=E%3!s0$!s$,p=K!s:+p=}f2R7f1R8'0/26p=4%@6#@p=N!sJ':p=Vg02=eR9!sG$11<86,l7p=^%86#8p=if3R:/y7@0`86p=I%@6#3p=D%36#:p>0Q%36#@p>05g02A?S00?k86p=>g02CHR;0016p=7P7g02CfR<g02DER=P=g02DeR>P;P8g02HKR?P6Cng02ElR@Fmp=Ug02BHRAg02BhRB7B6p>0ZP7P<P=P=P!s`'EERCP6CnP!s[$5!sF-8P6K0Ip>0Sf6RD!s='f5REf4RFP:!sO+7P8P6GoGop=Z1086,?7p=Yg02<^RG!sD%H0_=BABp=WB00;86p=QPE!sg+FP:!tf1P!ta+Gop=F!s9$!uV$p=bPF!sP+:!t'$!s4'6!sV&>0RP!t}+PEP!ty/;B00;7!t-2G!uB2!sw0K0Ip=]20<;6p=jB0g!u4$\1A;6p=6g02<?R@P;P4P3P1g02M[!tA&!un$N<02p=rP@P;!s$$3P3!sE2\p>0C!sD&!s$%0P6P8P7P0P:PFPEPDf7R0f8S01f9S02NB0kp=M!sQ$1P0P1PD!t@5O12EF12:!s9$CHp=TPG!s}&!s{&P0Q01Q02f:S03f;S04f<S05f=S06f>N@0lp=R201;6:00;8p=P!w_,p>03!xn5p=xg02JmS079[86p=_!um$5P3P2g02N=!tu5eP;P9!s9'ELp=g12F!s5&CHp>0oQ00!s[,J0mp==g00F]R2#3R3#3S08#3S09#3R5#3S0:#3R<#wRCp,2ppR1'CS0;Q09#:R4p,3sp0R?,CCRH%E<#KRI#E#}RJ#:S0<'034p,4SPloS0=%@2S0>#@RK#@RL#NRM#N!s$'RN#}#K!s$$VRO/2H!s]$hiRP%EJRJ!sC&VRQ,!sA&alRR%:5RS-0rHRT=B;9&0^1Q0;#1Q0;%:3RU%:<RV+0GRW3^p,1ERXp,1MRYg00GBS0?#JRZ00TSR[A{ZOQR\Q0>#3S0@#3#ER]#SR^g03<lR_'XR`,yZRa00?_S0APZP4Q0?#8Rb#8S0B#8S0C#8Rc#8S0D#8Rd#iRe%JbS0ECIS0FQ0E%DJ#E!u=%S0G7{OS0HPZ%3K#ERK#SRJPeQ0@#@Rf#@#D!s$&N#D#D$0QS0I$07S0JCIS0KPZ%S<R<PeQ0C#JS0LCIS0MPZQ08#@S0N#3S0O#E#SS0PPe%8eRg#i#i#iRh#JS0QCIS0RPZ%@3S0S#3S0T#3S0U!sX%VPe%8h!sR$8Ri#8Rj#8S0W#8S0X#8S0Y#8Rk#JS0ZCIS0[PZQ0S#@S0\#3S0]!sj%^Pe%8k!sM%_CIS0`PZ%3]#SS0a!sA-bCIS0cPZ%3fRf!s`%d!sE-eCIS0f!vB%SS0g!sA-hCIS0iPZ%3LRL!s`%j!sE$S0!sF$lCIS0m&079S0n%3M!w@$VRM'yS0o%Df!s4$f+0?S0p%:IS0q%DL!sK%S0r+0PS0sQ0n%@5R5#N$05$05!wY&VS0tPcQ0D#JS0uCIS0vQ0ng03>8PeQ0B#!wj$wQ00$04S0x'>S0y'>S0z'>S0{'>S0|'>S0}'>S0~'>S10'>S11'>S12'>S13'>S14'>S15'>S16'>S17'>RL'>RI'>Rk'>Q00g03?>$0MS18Q0u%:2RK%N!|\%:S193{S1:Q!tL$1;40LB0KGXYRNP[PkPGPXPYPZPSg02FLRk$04R[&0DkRl&0q;Rm&0j;Rn&0e;Ro201;9Rp%7S3U20]o>R>P6P71AAB20[67$0ZdB0Y;98H0XRBb2b3b41<9SP6b1PRK0WPNP\PI!tD+OPQ20FUVRI1<9UR\%1V1<9WS1<[[RR%1URAg02Y@RqB0EUV8UWBRV%1W\q^BARrQ0]#:Rs-0FURt%1s20GUsS1=,<9[\\R\B0EUs8VqXBARuQ1=#1!s_%A20VHSRq%1H%1S%1T[[RTP[Pl1~;8RSPnPo1v;2R2%7QS1>55oRv&0U=R=Po%7OS1?=5o2RwP=B0SowvFZP>P!ue&X0;126QRx12O8S1@12O7S1A127Q'l[[^0;P6PHPPQ0=O3S1Bb1b8b9b5b6b7F|PNQ0APLB0BXa_%18RL%;8,07S1C/2_S1D20AXa=YC:=WY7S1E[[^A@^C;PXPZP`P_PIPRPVPrPtP\PuPAPqP!uP$P!uL$PwP=PoPp%7^%35#D#VR5#7Ry5z;,Q2S1FEF!u@2O6Rz1X^5S1G,08R^#1!u9'Q0=O2R{!u6/10H`R|#1e1dXZ,CC/0`R`#1e!tO$mPnA5opy!t/,%15P6b1129_R}eP}e!u3BvP=PoQ1F%7US1H>0@;CRU'bI0R!u'1<^W\x!w/+O2RP!ts0<|We1<`W!t=KPyPUFG!t10A4^5!t2&!t&0A4|_WeA4`_WeL0>Q1Dp,6MstackAYC|:R`P7O2%:]R],XHR},?C,CCR~/X_1CC`'2AYC|F,CCS1I%;:S1J;4~10|ER`,?CS1K=WYF[[P;P~1X6_Q1K!sR$K'210|DS1L!sL$M,CC%;ES1N;48AYC|0=WYDS1O[[X;;P6P}%u:Q1J#1!uxG!yJ%%7]9z;2R~95opPo1b~UC]!{^2Q1@1X7]S1P#1Q1P;^W[!vB$Q!{L1b=%1}?^}We,q}J0=1X}_R_Q1I'2Q1K%;FS1I;4}Q1M=WYE[[P;Q1K12_6%;D=48}Q019YC|=WY0!uG'`%uFQ1I!uG9%jcS1I%jbS1KQ0?-0<;S0?'\'\g02G8S1M'p%jdQ0D#jQ0C#jQ0?'\S0C'\S0D'\Q1M'p=kk[5kkPlP;P;PmP71~;:S1BCtP8PmCtS1@PnPoQ0@,v;S0@95opS1PP=Po1v;3R3Q0@'Q=5oyP=PoA5op3S1Q!v~$!w+-!s+%Q1F/Q3R|!w1'|!w1$FZ!w52X:;X>;%17S1FA47:5%1:12:Q12OFS1R12OES1SQ1G,0D/00S1G#1Q1G;^W[!s#$^0;^:;^>;P6Q04#;Q05PHPDQ02Q03f?f@Q0=O9!x$3`?^`We,q`J0=12_`Q1LQ1N;4}S1GQ1O[[P6%uES1OQ1N#1R}!yy<;1~;7R`!v]'N!v]$!v1%Az;~yP|!#4;1X:;1X8]R]/X510^7R^'2\L!u<%P6Q06PHQ04O3!u$1Q1L,2_eQ1OP!tZ>P`P8Q!x<$!x3$>,v;R`,Q3!ww'P|P`P~!~d2!wG%A4875A4^:]!vp15#;!tb&3O4!tb3GeO2bDbDbD&0;a,dX,CC&08a'0!#8&&eQ1EeWGXFLXA@XC;H09!#;}$Q0AH0:ePNQ0FQ17!#<8%?P4PeQ0EP1&06CRa/A?R^1Aa1Q0E,dX=Ba1e1sbe12K4R1PbPK%6KS17PeP4%64S0FEr!#7M&%7KS0A%74R]55o!ui,P1P6b1CHR11see1244R5PeP4Q0F!s,&!sj,A5o]]!sa-5!sa&5!#:?H1Q2]S1D!xp21084S1E#1\z^0;P!#9r24R~%;eR`'0R|PW10~4RyPWP6XE;R}1286$0OXN;XE;R_P|PyP}!s$$;P;g02\51086H0N#6XA;XM;RyP~P~%6~P`P4P}P}%;6#6XE@S1G!ue&J0CR~M:MPWPW%6WR|GO!#9JHDP]!#9J3Q1E?44!#9L6ETp,5MargvM?RPNQ0HQ16!x{'EPOQ0G!tE7Q0DQ1M'pQ1KQ0B!#5,%!#4}2Q!}/'>95o3!tl%?=5o3S1?!tz&Q0<,P355o!#4h%32!sM&!#4`%oQ0G#7-032C]Cx!#4U6128QQ1AQ0<,0:947412F:Q1SQ1SQ0G,2E'l!#4@,!#?C$;!#SH$Q03p,4Hpp1Q0=O7!#Ad4KQ15!{j+JPeQ0JQ0I,?CREP^1AaEQ0J!{g%EeP1P!z>KP2JS0J!z>5JR!z=<JRJ/0`RQPW10J4ROPWP}P_PQPO!z#&yPJPJ%6J!yg$!yN'P!yKK0J!yK6A4E!yI<3Mra!yG&MQ14!vC+<PeQ0Lp,3s0v!vC,L!vCX<RE!vB5<RJ!vB;<R</0`ROPW10<4RQ!vB&OPQ!vB+<P<%6<!vBXPE!vA8J!vA>s0!vA&RQ13!vA'Q0PPeQ0Qp,1RRJQ0S#wREQ0N#:R<Q071`E<d3['9P^Pa%;g,?E,9J1_E<,9JRQ9Ba6X<a1AaQ1cdg,aXQ0k#8#iRQ,hgQ0:#:RO,<<S0:Pg!uc%QPO%6OS0kE!#GR'%7<%7OR<5U!#7$,Q0:!#6F$,fgEL!wpMQ0P,P2S0:!ws2Q0P,08S0S!wv8!sD$HRg/0`S0PPW10g4S0!wz&Q0PQ0!w|,gPg%6g!{@Z:!w}6Q0S!#5e=3Ms1!x#&[Q12!x#,VPeQ0ZQ0O#:Rg!wr%gd5[E,9J!wt%h!wt+g,9JS0O!wu&Q0O,Aa1cdh,aX1hhQ1<gOS0OPh!uP%QPOQ!wf1g=Uo<!wb/O!wb'h!wbQV!wb$O!wb4V,08Rh!wa:V!wa,V!wa'Z!wa'VQ0Z!waiO!|`8h!w_?2!w_&`Q11!w_,^PeQ0_Q0N!#],$:Rh!wd%h!wd0i!wd+h,9JRg!|Z,g1cdi!wa$iQ1<hORgPiPh%6h!w`6h!w`1Pg!w_'i!w_Q^!w_$_!w_4^,08Ri!w_:^!w_,^!w_%Rh!w^'^Ph!w]i_!w]8i!w]?3!w]&cQ10!w],aPeQ0bQ0U#:Ri!wX%i!wX0j!wX+i!wX6j!wX$jQ1<iORgPjPi%6i!wX6i!wX;j!wXQa!wX$U!wX4a,08Rj!wX:a!wX'Ri!wW1Pi!wVkU!wV8j!wV?4!wV&fQ0~!wV,dPeQ0eQ0T#@#:Rj!wX%j!wX-Q0W#;!wZ+j!wZ3Q0W,cd,aXQ0WQ0W/hQ1<jORgQ0WPj%6j!wb6j!wb9'f!waQd!wa$W!wa4d,08Rg!wa:d,0HRj/0`RhPW10j4Ri!wa&hPi!wa+j!u1%!waYW!wa8g!wa?5!wa&iQ0}!wa,gPeQ0!#4d%sd9[Es!wY+X!wY-s!wY5X!wY'XQ0X!wY$s!wY$XPs%6s!wY6s!wYig,P2Rg!wX4g,08Rs!wX:g!wX+i!wX&!|;7!wX^Pg!wW8s!wW?6!wW&mQ0|!wW,jPeQ0lQ0\!|:$?!w`%?!|:0Y!w_-?,9JRJ!w_,JQ0Y!w_'YQ0Y!w_$?ORdQ0YP?%6?!w_6?!w_2d!w_Yj,P2Rw!w_4j,08R5!w_:j,0HR{/0`RzPW10{4R1!w_&zP1!w_+{P{%6{!w_Yw!w_85!w_?7!w_&pQ0{Q0o>0BXfQ1C/2fRPQ0o-0AX!#Ww&Rx[\L!#h{&Q0nPMPf106MR5#1X;;!w&,MRw,QpRv95op!tZ,109MR~#1P6b11?C9R`,CCR{!uO+!se&!#_B$pPo1bpUC!#W$,1299Q1<'lP6b1b?b@,q9R1CgQ0n!#Yu$/0MRz!#h{,%7fRd!tR1%1fR<P6b1P<e1<5WX;;!tN3AUovU!tD-<~W!t?'P{P1Cg1<zWeA45f!sd71Qvd=5o!sg-A4~f!sh2A4zfWeL0>AYC5F=WY:X;;PY10~:R5,?CRzP7P;P512M6X;;%u7R<%;7#1R?!xuAA5op2RO!xz%1Qv2Rv!za2%1610~8Rw,2M!#lv$Q03Q01O2!#]w01CCzRzP<P!t@8Q1IQ0C!#W0,PlQ!#dm%!#d`$Q0@,Q2=5od!tZ$O!#Vn,A5opvPo1bv!#dC%!#_x5Q1FA48:fQ1FQ1R10~FR~#1?^~W!#c}32#;R~PHQ03!$';'!#Vd1b=,q5RDELP;P5Q1JQ0N#3#E#D#K#VR5546X;;!u`;P[!#YX'1Q23!uH+vP3%75!#b,4A468fA4w75!#XZ+~Q03P0!#c]2PzPDELI0J!y&%Q0o$0;!{/%!s2$8!#b$,PxeXGP!#b$6p!#b$&sQ0z!s;'qQ0!zO+Q0q#7!{k1Q0q!}<%!z{3Q0r#7!z|1Q0r/2!z}+p,3MroL0pPNQ0vQ0y!t>%nP`Q!#|6$up,3tidR@,?CRP1Aa`1AaP1sbcQ08#:R`,2KRxPbPKQ17PcP`%6`RbE!tP-A%7`R7!#c<0x!#7J$1sce12`4RxPcP`Pb!#c967]!s^5Q0t,06Rx!#4T/Q0t,PpR]!v93t,09R4!v>&!w`$%;cRe=4xWX;;104eR:PW104`RD/2WRzP}P_P:PD!#7g'4P4%64PeP`P}P}Q1G!t|%J0C!#7u6!#3>']!w@2Pz!w<'I0o!y:'9#w$06$0DRz$0nPGPY1?CxPcH0i20hcP-0fz3BX;;p,4Mtid!s^%!#81%wQ0x!ww%Bp,3canR11?C1,Aap,4McanJ0dQ0000cNRaD=!s$E!ss$18Q1;p,6Mcells:0bXYPNQ1:Q0x!zN'uPKQ19P;P@12K6Q19,26'l!#6<-!#:s8oAUop2PoQ1HQ0]#w60@;,b2C]Rp!#3k$A=5o!sF$9!#cE+!#y@196Q1=7^6R912K8!tJ$8'l!#{I%@p,4HtidO2R6!}T/1CCP!tjB!tP$POPo1b2U!tF4A^L8W\9!t4$!t#/,q@ELF|PaD=J0HJ0H!vA%g02TTH0aebKbJbIbHWLo"). Qed.

  (* [comment removed for export] *)
  Theorem ref_usage_cs : ltac2:(zQ "hc0!h9!jc!nb!ijc!ij3!in9!ip2!ihb!ii5!ioc!ipc!l9!n6!ite!iu5!iub!iv8!ive!jh6!jk9!jo0!jr7!jrf!kg1!kkd!kp0!kpd!ktf>3a0s@1$2@1$1@1$0#8>2t8@1$2@1$1@1$0#8>0@1$h1@3$hb@1$1@1$0#8@2$7@1$0#8Z^2>0@2$9@1$6@2$4@1$1@1$0#8^3+hvvvf>0@2$9@2$3@2$3@2$8@1$0#k0?2pp@1$6@2$4@1$1@1$0#8^4+8@2$3@2$8@1$0#k0?3sp0+kgggg0>0@2$9@2$3@2$3@2$8@1$0#k0?2pp@1$6@2$4@1$1@1$0#8^5+8+ogggggggggg0>0@3$c@1$b@1$2@1$1@1$0#8@4$d$5?1M?2pp@2$h2@2$4@1$1@1$0#8^6N1@2$a@1$2@1$1@1$0#8@3$e@1$1@1$0#8^6@3$f@1$1@1$0#8@2$7@1$0#8Z@1$h0@1$1@1$0#8>0@3$c@1$b@1$2@1$1@1$0#8@4$d$5?1M@2$7@1$0#k0@2$3@2$8@1$0#k0?2pp@1$6@2$4@1$1@1$0#8^7N8@2$a@1$2@1$1@1$0#8^6@4$h8$5$h7@2$h3@5$h5?2fx?1R@2$7@1$0#k0+knhnc?1M@1$h6$5?5model@2$ha@1$h9^8@1$h4?5model").
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "##8dh02Hah14__x1h24__x2h34__x3h43HPlh56Hnonulh64Hpp2h74Hpp3h84Hstrh93Ht8h:7__arithh;4__ffh<7__sat10h=!s0&1h>6!s0$9h?8__varmaph@5__withA3a0shB4cstrhC2t8p;1p;2p;3p;4p;Bp;7p;8g000ij10Tg001Nj1J!s/$lj1GTg002Oj1PTg0070j2NTg00L3j3]!s/$Jj1[!s/$cj27Tg00MCj1:Tg00F8j19Tg004mj14Tg0065j26Tg005Kj2OTg00=4j21!t1$oj1_!sJ$Qj13Tg00P?j2\Tg01oIj4M!s8$Vj1LTg00Q6j3K!s/$Vj3ZTg00R3j2I!t:$Sj3@!t$$Qj2?Tg00kGj1Y!s/$lj2XTg00T8j2HTg00S[j2WTg00lTj3VTg00m8j2U!s/$ij2STg015Xj2BTg024Fj3E!s/$oj2RTg00nIj2F!sJ$:j1TTg023hj4Q!sA$gj1kTg00oEj1jTg01<Kj2;Tg0100j2A!s/$Sj1iTg026fj3<Tg011Xj2cTg012:j2`!s/$fj3aTg013Ej4bTg03@Hj1^Tg03ARlBeTg0225j4f!s/$`j7g!tU$Dj8hTf0R0#0#0p=D%90#9p=8%0!s8$!s$,p=2g02=eR1/60p=5g02CHR2f1R3g02EEP0Cfp=>P3g02CfR4g02DER5P5g02DeR6P0g02ElFgp==!t'+p=df3R7P4P5P5P6f2R4P3P0Ghp=Cg00F]R8#0R9#DR:#JR;#GR<#PR=1N;1R;=]<3#[17<4#:%98#!s$0R>#9#4'6%0:R?#DR@#JRAp,2ppRB'ORC17<7#:'1%4:R:'1p,3sp0RD,OARE%2@#2R@#4RF'1'6f4RG,7<#:,1C/1:%0@#2!s$$4'6%_=R@g02<^RHp,1MRIPBf5RJ,7<g00GBRK#3RL'\CM%L<9K<;9Z<J,I=3@PHPIf6RH!t$',NA%3LRL#3R;#3!s$'CM1I=J5@@f7R@PBPHg02`Up,1RPIPJPGg03B]%GARA/?D1?ABp,4Hpp1P7P4g03Ch17<@R@#Y%:@#5%49R@%99RA#9#0#4RB'X1H1@%5B1W@BRD,H1[[%5@RJg02Y@RIAV@B3UW0%5D\I^0J%4?R?,UE%5E%5?1SE?#5[[g02FLR?1B2;1B2L1B2K5E25E2g02G8'R%L?3K%P?P21F24P3!s-$7P7%T2CQCQ%k2%j2R?1;211A2ARA'>,=?%i5R5P?1A28R8=<2A1;2:RA5<21A29R91;2F5<2RK!sT$P5P?%0>#D#d!we'R>,;2/>9!sD$A<28A/>K,=?C!s#$1c?6P0P4g02BHR?g02BhR6'?1`04=@?6dAa213Cbb;b?b@X12X22X32%541137/1:114F'616>7117:11GF'6[[[^12^22^32P0f<!xL$PEPCPGf8p,4SPloO6b:b>b<b=bB#^P3P0MBeW9W8W7W6W4W5XC=WAo"). Qed.
End UsageCS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
