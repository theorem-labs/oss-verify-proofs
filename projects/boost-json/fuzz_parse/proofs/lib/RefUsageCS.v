(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.boost_json.fuzz_parse.images Require Import Plain.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Hoare Frame AgentLib
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymDriveH4
  Spec RefExitBase LibTail LibDiagKn RefPrintfBufBase RefMemcpyLib RefMemcpyBase RefMemcpy
  RefOpenFailCS_defs RefOpenFailCS_tail.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RefUsageCS_defs RefUsageCS_tail.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_RefUsageCS () := KReplay.lz_vm "#$i1C46Stdlib5Lists4!s+#6nth_okC47Corelib4Init5Logic8eq_ind_rK!sD+7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00I!tR19Datatypes4list!sF>6op!sl#00C79OSSVerify6Proofs:boost_json:fuzz_parse3lib6SymRun7vals_evC13~~~I!u~72eq00!uU>Z02C!uU@;bv_unsignedC5!wK&6ZArith6BinInt1Z2leK!uX;3nat!t3C7Z_to_bvC4ELinuxProcessSemantics?!s<2>Riscv!sE+@word!sh#le_bytes!vkP?RefUsageCS_tail3ENV!vp%C8!smN=SymExec2Sound4SX2S9mem_denot!sv&!v^;3sub!u&P7Cat!t;#6w!uf%!t,$!xU@3!tK=addK!yR;1K!uzO8!uz'3SX24expr02!tj&!sm\5saddr01!wYV!sn06a_base!smde!x?/!uL]a_off!v:c!w%%!v9f!uJ/!xy76!#6M$!#6KF1!sKG3!#35@1!}w\defs7u_logM!v5'!~j_4PRE7!snf9!sn#_word!w''!#5?85!#5/#7Prelude5bvmap!#;A62In!wn83!x5#!#9b;length!~g<6of_nat!#5Lb7regs_ok!#6Bh7know!st,!uR13Nat!#4m5!#<m21!sFB2!vQ<3appK!#=RB!zlQ8Prop!u[#9u64_range!#8lBpow!#<i=t!#>773and00!#3a\6sentry!#3c&!so^k!so%5!sok6!sok7!sok4!sok!w3d9sym_state!sre7scripts0!#6GV!{L+7seg_rom!sjV4Spec9msg_u!#6I#!#68?!#DQ25S!u|#4m_fs!tCU5t_di!t?&!#IQ<prod!#H'-!sF81!#=,\8!x;#exec!#6HU!#Ay1_log!sldcarry!#7|h8sc!#G?-!vb,!#;&$7!s+#Def6Forall!vc_6s_regs!z=V9SymDriveX;log_below_b!so&!#7514Znat5Nat2Z7inj_iff!#=677iff_sym!sf>9is_nonneg!#8B;>pow_po!sND:!sN#!sJ&!#?'&9micromega9SatDivModCZ_mod!sP&!s{C6moduloK!sw56VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!|l#!sQ47Env!sT#5PE!#K##!#=6C2!skE7!v>65Tauto8B!tZ&!sH6:Z!u$+=Z!sT$CheckerC!uu<4find!sqAC!sq0_s!|C#!{f]2!#Uu&!ww@1K!wYC5Psatz02!|QZ?!#Ri'_abov!#7s'!tD&!#FY,9nth_error!#Zw8!|P#refl!vc6;ZifyClasses3inj!sIB;rew_!su%v!uMZ8kimg_rdn!#3f_<kwr_store!#Fg'!zqE4!sIE1!}{=to!#Ia#!#EI;max!sC<8max_spec!#\`8or!}m@3Pol!z-M4!#J^cu_small!vu&!wgO=RefMemcpyBase3mcH!#AA&I!smb0!#<zb6sr_ge!#T`'!#_B>5bv_eq!#CCX4getr!{AV!#b~&reg_val!tuG4BvWfK!#e@C!#N&Y5v_add!u@V7LibTail7vadd_wZ!si^6ed_var!shblit!shb!v#Y5Hoare;ret_ok_eve!#5IW!{q+:ref_m!s1$!snV!z_,mkst!}JV6CatSim6msteps!}F+!siO<!uB+Lib5keep!#E;%!#kN9x00K!#L&I3Run6config!{WS!#9J&8blob!#m2+!}tW:sr!zn#s_l!z0W!#:|+@!#[V#after_!vE-!uNY9junk_val!#ij&!#6A[3env!#R9'!#KF93map!tvY?sr!ui&call_j!y19Peano2le00!#;,b4fla!wma:!sh#_intro!vy&!#\E;1!#Oeclog_!u$Z!z\&;!#QD#!w&%!sl%c!slO:!#ew+>u!#46$1!#qa/!|?Wkn!|?h<env_app_know!}1a!|<+_!#fz%!{U&!#HE4:!sG%!tF#C!zd9t!tSZ=!#zD%!uI$l!tP2!#Hh87!#Hh%!t@Z9rdn_agree!t<H8or_morph!t=P7StepTac6u_Z2b!#6fV!#wk&>!t}#!#wo$_ou!yRW!#n,27us!s-$!#6hWhapeAlg9rz_!#;e$!sl&!#6h[4s_pc!tYW!#=|&3!#Mw'!#v%b3!y#H5mkrel!#KiC!#WL'!#L<6!#V<%G!sJ'4!sJF8!#TR?3!#MJJ6!sO6!#V^,;!#O5$!v\$02!v%E!~p$!sK@6!sK$!#Y]E3!$'gY8!#R{&!vcF5!sJF3!sJF6I!|EX8realize!#E'X!#>~'6rz_ru!{\&!#hQ;!#{s#!$2Y/!t%96images5Plain1M?loaded_segment!$+mF1K!#zP?5Instr5aluop01I!}\b!vX&I!#R}]!#p^$!soek!so1!#lZ;bool!#lz>!sF$1I!w%?0!#bb;5eKind!tK=unit!#Yj7!se%4kind!#YiE3Op2!$&x=!t5%1I!#3cL0!#47M!tmJ!sMJ5!vj68Zify!zf#@!$$v$_!#^B$!#XkR!#<Z28!$'a#l!#Rn&!#G\74True!#O1Q4Scfg=hunspell_scfg!#>Xadefs6u_knB!#4I&!#nD<6inj_le!sHD!#ay+5!sG$8!#D[#Na!$&y'!#p8B!sI#!uGOBRefOpenFail!uJ&4FUEL!v:V!sq65STOPS!w-iscrA!spf5srUS0!sogkn!so+I!#z3]idecond!#6[d!$$;,!srd!$$;'!#7P8!}=/0!~Mapre7_im!}Cg5!}C#!y:'!#4_=7Inj_Z_Z!#95=N!uMR!#]T/;callee_kep!#Qp`?!so-_no!#i]c4ridx!sk%!#U4Z6valsU!~1'!#[-:nth!sB<s!#j\R!v,';nth_map_!sh#!xS1!#T#,=app_nth2_plus!$LVAbv_wr!$=i,!#6S'divAZ!sg#!#}`#idemp_r!#N+X=!t3&64!sr#!u/'!te?@!$N=%!$OO+!#D[?3Sem5alu64!toY7alu!#i<Y!#8A53sp!yyb9spxUS!#oO,!snO@RefPrintfBufBase>!$A5%_by_!{d+!sya9all!s|#3!$Mc%!#=&=8inj_succ!~`QLibDiagKn8kn_cell!#V3V!$R`6!#HN$!$CF+!tdO!#_}%<kalign!#ca-!smY!$BJ#!sm0!uTb6estart!z<bevUS_jun!vAW;RefExit!y<#=!#Sk&_data!vG]:!$%J#!w4[!ya,;canary!#d4[!so+?diag!zT%!sse;!$Jn%!#dW#!vB\;k!$\a#!#k47!$:a8!$0GP!#Ee3US_STK!up`6CANARY!sj`:!wQ,!{\b!wM&!#=p&!sn[:!#dX%_c!t_b:!#?N$!#Oo+!uP\!#8N%!uP'".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option37Corelib4Init5Logicm22eqk14list69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~o26wbytes69OSSVerify6Proofsaboost_jsonafuzz_parse3libfRefUsageCS_defs~~~~~~s57u_logM169OSSVerify6Proofsaboost_jsonafuzz_parse3libfRefUsageCS_tail~~~~~~hh13ENVhh14PRE779OSSVerify6Proofsaboost_jsonafuzz_parse3libdSymExec2Sound4SX2S~~~~~~hm29mem_denot69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~hr47vals_ev46Stdlib6ZArith6BinInt1Zhv83subhf7Z_to_bvhfbbv_unsignedk16lengthhv83add69OSSVerifyaboost_jsonafuzz_parse6images5Plain1M~~~~~~ijffloaded_segmentshv82lehv86of_natk14Some69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ipf3rdnk13appk14consk13natk13nilm23not37Corelib4Init3Natjg03add3h5LinuxProcessSemanticsfLinuxProcessSem3Runjh95mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statejke4m_fs3h5LinuxProcessSemantics5Riscv7Preludejo45bvmapipf4mkstipf7seg_roms55knUS0s55srUS069OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~jt6dhunspell_scfg69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8ShapeAlg~~~~~~khe8realizes69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec~~~~~~km59msg_usagekm55t_diehm27know_okhm27regs_ok36Stdlib5Lists4Listks82In69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymDrive~~~~~~ku19junk_vals79OSSVerify6Proofsaboost_jsonafuzz_parse3libaRefUsageCS7UsageCS~~~~~~li96valsUSjke5Modeljh98valid_spk14Nonejke8m_haltedk14prodjke9m_vm_lazyjke7FdEntryjke9FdChanneljke9fd_lookupjke5m_fdsm21Iipf4getrhf2BVhf4BvWfs56US_STKhr46stk_okm23and01Zhv82lt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib9LibDiagKn~~~~~~mhc8cells_okmhcadiag_cells3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsmn2h0word_to_le_byteshv83powmhc9canary_ok" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Import SX2. Import SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section UsageCS.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Variable sp0 : word.                 (* [comment removed for export] *)
  Variable model : ltac2:(zQ "10!ln8$0").
  Hypothesis Hvsp : ltac2:(zQ "10!lo1@1$0?3sp0").
  Hypothesis Hh : ltac2:(zQ "60!h9!jc!lod!l9!n6!lp4@3$4@1$3@1$1@1$0#k0@1$5?5model@1$2@1$1@1$0#k0").
  Hypothesis Hlazy : ltac2:(zQ "71!h9!jc!lq0!nb!iv4!n6!lq7&@2$2@1$1@1$0#k0@1$1@1$0#k0@3$5@1$3~0@1$6?5model@1$4~0").
  Hypothesis Hfd2 : ltac2:(zQ "90!h9!lr4!ih7!ip8!l9!n6!lrf!lsc!lt9@3$5@1$4$1@2$7@1$8?5model@2$2@1$0#k0+2@2$3$1@1$6@2$2@1$0#k0+2").
  (* LPS 75d69e00: the launch's channel reader, constant over the run; us_tail_cs hands it
     to RefUsageCS_tail.us_tail (its stdio_call_sound / ref_exit_Z premise). *)
  Hypothesis Hrdr : m_channel_reader model = true.

  Let SPlo : (0x7fff80000000 <= bv_unsigned sp0)%Z := proj1 Hvsp.
  Let SPhi : (bv_unsigned sp0 <= 0x800000000000)%Z := proj1 (proj2 Hvsp).
  Let SPal : (bv_unsigned sp0 mod 16 = 0)%Z := proj2 (proj2 Hvsp).

  (* [comment removed for export] *)
  Lemma umemcpy1_denot : ltac2:(zQ "e1!h9!jc!l9!n6!nb!rc!hg7!hl3!hla!hq7!hud!ih0!ih7!ii1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4vals@1$4@1$1@1$0#k0>1M~0>0@3$3@1$1@1$0#k0@2$a^2N0?3sp0@3$3~0@3$9@1$7^3^2$6@3$5^2@2$c@1$0#k0@2$b@2$d@1$0#k0?3sp0+ij0$8").
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "##0;h01Hh12H0h21Mh32P0h41bh51lh64valsp;1p;2p;3p;6p10000p4p710g000KR!s3&p8g000ij10Tg001Nj1A!s/$lj1?Tg002Oj1G!s/$oj1STg003Qj2BTg004Sj35!s/$mj19Tg005Kj2<Tg0065j2F!s/$Qj14Tg0070j2:!s/$Vj2ETg008^j1DTg009ej3CTg00;5j2R!s/$Rj36Tg00<Tj1QTg00=2j2@!s/$Oj2PTP0j6O!s5$ij1NTg00?0j2LTg00@8j1KTg00A?j2>Tg00BFj1JTg00CLj1ITg00DSj2MTg00EZj6HTg00F6j1;Tf0R0#0#0p=8%;0#;p=1%;!s6$7%0!s@$#0p==!s2+!s$'p=3%0!sV$2g00F[R1#0#8R2!s+$3#AR4#?R5#G%A2#?R6#S\5R7f1g00G@R8'Bp,3sp0R9555p,4SPlo%11#!s$/7#8#=#3!s$$91<49R1'F!sR$hi%03R!s@%!sF&,F1%G6R6%48#4!s$,R:%13#7#7#2!s&$2!s-&1!s-$8!s6$1#8!s6$1!s4$9R3,:4'ER;f5#Df4R<g00G_R=3C%12#=R2#9,R1,:4R1=6<0557X56P5P91<40%Q2R2'@,:4=6<;A6<1;557X45f3R5?61;R1,P71B<8f2EO%D<R<%N8/L2R2#K'>,<4%J!sf%%I3,><,E:R:565=571e1M<2=65:!s3$AC<5=!s0$g00Hjg00J2EHb1b0W3W2W6o"). Qed.

  (* [comment removed for export] *)
  Theorem us_tail_cs : ltac2:(zQ "i40!h9!jc!nb!iif!ij8!ii1!n6!in5!io8!ioe!ih7!l9!ip8!ita!hl3!hud!iu1!iu7!iue!iv4!iva!jh2!jk5!jnc!jqa!jr3!jrb!js6!jse!kgd!kl9!kpc!kq9!kr2!krd!ktb>3a0s@1$2@1$1@1$0#8>2pp@1$1@1$0#k0>2t8@1$2@1$1@1$0#8>4vals@1$2@1$1@1$0#k0>1R@2$h8@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@1$h4@3$i3@1$1@1$0#8@2$a@1$0#8Z^6>0@2$8@1$9@2$3@1$1@1$0#8^7+hvvvf>0@3$6$h2@2$3@1$1@1$0#k0^5Ni6>0@3$6@1$1@1$0#k0@2$f^6N0?3sp0>0@3$6@1$1@1$0#k0@2$f^7N1^9>0@2$8@2$5@1$0#k0?3sp0@2$5@1$0#k0^a>0@2$8@2$4@2$4@2$5@1$0#k0^b@1$9@2$3@1$1@1$0#8^c+8@2$4@2$5@1$0#k0?3sp0+kgggg0>0@2$8@2$4@2$4@2$5@1$0#k0^c@1$9@2$3@1$1@1$0#8^d+8+ogggggggggg0>0@3$i2@1$e^b$hc^a>0@4$i1$7@1$e^c^a$hb>0@3$6@1$b@1$2@1$1@1$0#8@4$d$7^b^f@2$h5@2$3@1$1@1$0#8^h0N1@2$c@1$2@1$1@1$0#8@3$h0@1$1@1$0#8^h0@3$h1@1$1@1$0#8@2$a@1$0#8Z@1$h3@1$1@1$0#8>0@3$6@1$b@1$2@1$1@1$0#8@4$d$7^c@2$a@1$0#k0@2$4@2$5@1$0#k0^h0@1$9@2$3@1$1@1$0#8^h1N8@2$c@1$2@1$1@1$0#8^f@4$he$7$hd@2$h6@5$h9?2fx^e@2$a@1$0#k0+knlm8^d@1$ha$7?5model@2$i0@1$hf^h2@1$h7?5model").
Proof.
    (* LPS 75d69e00: replay replaced (it applied RefUsageCS_tail.us_tail at the old arity,
       before Hrdr).  Proof text from boost-beast http_request RefUsageCS.v us_tail_cs
       (a donor branch), constants boost-json's own: PRE7 at 0x11457 (pre7_img's
       statement), memcpy return 0xe021c (us_tail's start pc), memcpy entry 0xeada8
       (BJIface.RMEMCPY), image high 0x12d000 (RefOpenFailCS_defs.IHI). *)
    intros a0s pp t8 vals R M Hnonul HL0 HL P0 P1 Hpp1 Hpp2 Hpp3 HR HK Sr Ht8.
    pose proof SPlo as Hlo. pose proof SPhi as Hhi. pose proof (u64_range pp) as Hppr.
    run_blk_keep u_scrA 38%nat.
    assert (Habove : forall x : word, (bv_unsigned sp0 <= bv_unsigned x)%Z -> M0 x = M x).
    { intros x Hx. rewrite EQM. apply (mem_denot_above (ENV vals) M _ 0%nat 0x12d000);
        [vm_compute; reflexivity | cbn [ev ENV]; rewrite P0; lia | cbn [ev ENV]; rewrite P0; lia | lia]. }
    clear EQM. rename M0 into M1. rename M into M0. rename M1 into M.
    set (dst := Z_to_bv 64 (bv_unsigned sp0 - 560)).
    assert (Hsrc : rdn RSEGS M (Z_to_bv 64 0x11457) 7 = Some PRE7).
    { rewrite (kimg_rdn RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kimg_cov 0x11457 7) in exact i)
                 _ _ 0x11457 7 HK eq_refl) by (cbn; lia). apply pre7_img. }
    assert (Hdst : store_ok RSEGS M dst 7 = true).
    { pose proof (kwr_store_ok RSEGS (ENV vals) _ u_knA ltac:(let i := kidx u_knA (is_kwr_cov (EVar 0) (-560) 7) in exact i)
                    _ _ _ (-560) 7 HK eq_refl ltac:(lia) ltac:(cbn; lia)) as Hst.
      unfold adenot, v_addi in Hst. cbn [a_base a_off edenot ev ENV] in Hst. rewrite P0 in Hst.
      subst dst. replace (bv_unsigned sp0 - 560)%Z with (bv_unsigned sp0 + -560)%Z by lia. exact Hst. }
    assert (MC : mcH M dst (Z_to_bv 64 0x11457) 7 PRE7).
    { constructor; subst dst; rewrite ?u_small by lia; rewrite ?PRE7_len; try (cbn; lia).
      - exact Hsrc.
      - exact Hdst. }
    lazymatch goal with |- realizes _ (mkCfg (mkst ?Rc _ _ _) _) _ =>
      assert (A1 : getr Rc 1 = (0xe021c : word)) by (regv HR (1 : reg); apply bv_eq; reflexivity);
      assert (A10 : getr Rc 10 = dst)
        by (regv HR (10 : reg); subst dst; ed_lin ltac:(cbn [ev ENV]; rewrite ?P0); f_equal; lia);
      assert (A11 : getr Rc 11 = Z_to_bv 64 0x11457) by (regv HR (11 : reg); reflexivity);
      assert (A12 : getr Rc 12 = Z_to_bv 64 7) by (regv HR (12 : reg); reflexivity);
      destruct (ref_memcpy M dst (Z_to_bv 64 0x11457) 7 _ (seg_rom RSEGS) MC Rc (0xe021c : word)
                  ltac:(apply ret_ok_even; reflexivity) A1 A10 A11 A12) as (R2 & Hms & Hkeep);
      clear A1 A10 A11 A12
    end.
    replace (Z_to_bv 64 961960) with (0xeada8 : word) by (apply bv_eq; reflexivity).
    eapply rz_msteps; [exact Hh | exact Hlazy | exact Hms |]. clear Hms.
    replace (0xe021c : word) with (Z_to_bv 64 0xe021c) by (apply bv_eq; reflexivity).
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
  Hypothesis Rsp : ltac2:(zQ "a0!h9!lu2!n6!lu6!ih0!lue!lv3!ih7!jc!ii1@3$2@1$8@1$0#k0@2$3?1R@3$5@1$0#5+2Kv$1@2$6@1$0#5+2@2$7@1$0#k0@2$4@2$9@1$0#k0?3sp0+o0").
  Hypothesis Rtp : ltac2:(zQ "80!h9!lu2!n6!lu6!lue!lv3!ih7!jc@3$2@1$7@1$0#k0@2$3?1R@3$4@1$0#5+4Kv$1@2$5@1$0#5+4@2$6@1$0#k0+hgrmr8").
  Hypothesis Rs0 : ltac2:(zQ "80!h9!lu2!n6!lu6!lue!lv3!ih7!jc@3$2@1$7@1$0#k0@2$3?1R@3$4@1$0#5+8Kv$1@2$5@1$0#5+8@2$6@1$0#k0+2").
  Hypothesis Ra1 : ltac2:(zQ "a0!h9!lu2!n6!lu6!ij8!lue!lv3!ih7!jc!ii1@3$2@1$8@1$0#k0@2$3?1R@3$5@1$0#5+bKv$1@2$6@1$0#5+b@2$7@1$0#k0@2$4@2$9@1$0#k0?3sp0+8").
  (* [comment removed for export] *)
  Hypothesis Mstack : ltac2:(zQ "70!h9!lva!mg3!in5!ih0!ih7!ii1@4$2$3?1M@2$5@1$0#k0@2$4@2$6@1$0#k0?3sp0+j0$1").
  (* [comment removed for export] *)
  Hypothesis Mro : ltac2:(zQ "a0!h9!jc!lod!l9!mgd!n6!mh3!io8!mh6!ih7>1i$6>0@2$4@2$7+hggg0^1@2$8^1+vhgg0@3$5@1$3@1$1@1$0#8@1?1M@2$9@1$0#k0^2@1$2@1$1@1$0#8").
  (* [comment removed for export] *)
  Hypothesis Mcells : ltac2:(zQ "20!ml8!mm4@2$0?1M$1").
  (* [comment removed for export] *)
  Hypothesis Mtid : ltac2:(zQ "a0!h9!nb!ih7!jc!ip8!l9!n6!mq9!ita!in5@3$6@1$5@1$1@1$3@1$0#8@4$8$9?1M@2$2@1$0#k0+hgrmh0N4@2$4@1$1@1$3@1$0#8@2$7N4@2$2@1$0#k0?3tid").
  Hypothesis Htid : ltac2:(zQ "30!mh6!mgd!mre@2$1@2$0Z?3tid@2$0?3tid@2$2+2+h6").
  (* [comment removed for export] *)
  Hypothesis Mcan : ltac2:(zQ "10!ms5@2$0?1M?3can").
  (* [comment removed for export] *)
  Hypothesis Margv : ltac2:(zQ "c0!h9!nb!jc!ip8!l9!n6!mq9!ita!in5!ij8!ih7!ii1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?1M@2$a@1$0#k0@2$9@2$b@1$0#k0?3sp0+8N8@2$3@1$1@1$2@1$0#8@2$6N8?2pp").
  Hypothesis Hpp1 : ltac2:(zQ "30!h9!ii1!io8@2$2@2$1@1$0#k0?3sp0@2$1@1$0#k0?2pp").
  (* [comment removed for export] *)
  Hypothesis Mra : ltac2:(zQ "c0!h9!nb!ih7!jc!ip8!l9!n6!mq9!ita!in5!ih0!ii1@3$6@1$5@1$1@1$3@1$0#8@4$8$9?1M@2$2@1$0#k0@2$a@2$b@1$0#k0?3sp0+j8N8@2$4@1$1@1$3@1$0#8@2$7N8@2$2@1$0#k0+tqgsc").
  Hypothesis Ms0 : ltac2:(zQ "c0!h9!nb!jc!ip8!l9!n6!mq9!ita!in5!ih0!ih7!ii1@3$5@1$4@1$1@1$2@1$0#8@4$7$8?1M@2$a@1$0#k0@2$9@2$b@1$0#k0?3sp0+k0N8@2$3@1$1@1$2@1$0#8@2$6N8?3s0v").
  Hypothesis Ms1 : ltac2:(zQ "h00!h9!nb!jc!ip8!l9!lu2!n6!mq9!lu6!ita!in5!ih0!lue!lv3!ih7!ii1@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+k8N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+9Kv$5@2$d@1$0#5+9").
  Hypothesis Ms2 : ltac2:(zQ "h00!h9!nb!jc!ip8!l9!lu2!n6!mq9!lu6!ita!in5!ih0!lue!lv3!ih7!ii1@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+l0N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h2Kv$5@2$d@1$0#5+h2").
  Hypothesis Ms3 : ltac2:(zQ "h00!h9!nb!jc!ip8!l9!lu2!n6!mq9!lu6!ita!in5!ih0!lue!lv3!ih7!ii1@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+l8N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h3Kv$5@2$d@1$0#5+h3").
  Hypothesis Ms4 : ltac2:(zQ "h00!h9!nb!jc!ip8!l9!lu2!n6!mq9!lu6!ita!in5!ih0!lue!lv3!ih7!ii1@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+m0N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h4Kv$5@2$d@1$0#5+h4").
  Hypothesis Ms5 : ltac2:(zQ "h00!h9!nb!jc!ip8!l9!lu2!n6!mq9!lu6!ita!in5!ih0!lue!lv3!ih7!ii1@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+m8N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h5Kv$5@2$d@1$0#5+h5").
  Hypothesis Ms6 : ltac2:(zQ "h00!h9!nb!jc!ip8!l9!lu2!n6!mq9!lu6!ita!in5!ih0!lue!lv3!ih7!ii1@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+n0N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h6Kv$5@2$d@1$0#5+h6").
  Hypothesis Ms7 : ltac2:(zQ "h00!h9!nb!jc!ip8!l9!lu2!n6!mq9!lu6!ita!in5!ih0!lue!lv3!ih7!ii1@3$6@1$4@1$1@1$2@1$0#8@4$9$a?1M@2$e@1$0#k0@2$b@2$f@1$0#k0?3sp0+n8N8@2$3@1$1@1$2@1$0#8@2$7N8@2$8?1R@3$c@1$0#5+h7Kv$5@2$d@1$0#5+h7").

  Definition valsUS : ltac2:(zQ "30!nb!h9!jc@1$0@1$2@1$1#k0") := ltac2:(zQ "70!h9!jc!iu7!ih7!iu1!iv4!lhc@3$4@1$1@1$0#k0@3$2@1$1@1$0#k0?3sp0@3$2@1$1@1$0#k0?2pp@3$2@1$1@1$0#k0@2$3@1$0#k0?3can@3$2@1$1@1$0#k0?3s0v@3$2@1$1@1$0#k0@2$3@1$0#k0Z@3$2@1$1@1$0#k0@2$3@1$0#k0?3tid@1$5@1$1@1$0#k0@1$6?1R").
  Let E : env := ENV valsUS.

  Lemma valsUS_len : ltac2:(zQ "60!iif!iue!n6!h9!lme!jc@3$2$1@2$0@1$5@1$3#k0$4Ni6").
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "##'Ph01np;1p;2p;3p;6g000ij13Tg001Nj1A!s/$lj1<Tg0070j25Tg00PNj1@!s/$nj31Tg00L[j24Tg01WBj1;!sA$7j27Tg004Sj36Tg00=Oj2:Tg01coj1?Tg000Kj68Tg00QNj3>Tg01e=j3=Tg006Qj12Tf0R0#2!s$%p=0%20#2p=9g02;mR1g00F[#3!s$-AR2#<R3p,3sp0p,2ppp,3can,52p,3s0vg02=S!s4%tid,52%@351!s%3R2'4R4p,1RR5#;R6,43R7'7g00G@#0!s$1R8#9#0R99610X01P1P81740=619X011:19P7%?5E8A>326,43A=326E8g02`1,43=619eo"). Qed.

  Lemma evUS_junk : forall i, (i < 32)%nat -> ev E (6 + i) = getr R (Z_to_bv 5 (Z.of_nat i)).
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "##-\h01ih12Hih21bp;2p;1p;4p;3p;6p;5g01e\j2DTg000ij14Tg001Nj19!s/$lj1?Tg01WBj1JTg0070j25Tg02a6j48Tg00F6j1ATg00M;j16Tg01E0j27Tg004Sj32Tg00=Oj2N!s\$Rj2MTg01YNj4L!s8$nj6K!tL$Kj6=Tg00PNj1:!s/$nj31Tg00L[j2I!s8$7j2<Tg00QNj3CTg02c6j5ETg003Qj2;j1BTg002Oj1FTg01Sjj1GTg01XHj2HTg013oj2>Tg006Qj13Tf0R0#3#3p=@%3!s0$#3p=0g02;mR1g00G@R2#@#0R3#@#0!s$,R4,D0g00F[#4R5#4#4R6#4!s$$9R7#?R8P8f1R9p,1RR:#JR;g02=S,57R<C8R=%A5#9R5f2#6'5,7:9280X28R>P8%69,55,7:R?P>1N8?P8P9P1P8%60!s?%X01R11M24CLP<C8P8P1P9P4P<P0EKE=A28=?eP8p,3sp0p,2ppp,3can,57p,3s0vp,3tid,57%:8518918<518!s%+R7,I8/<9R=AC87;R0!t4&7P;P<P9DEE=1;0==28?eg02`1R01<39R9';!s:$%B0%96#?#F#:#G'H/>9!s>$p,1E!s2'W1W0o"). Qed.

  Lemma spxUS_val : forall k, edenot E (spx k) = Z_to_bv 64 (bv_unsigned sp0 + k).
Proof.
ltac2:(KReplay.run1 (kr_t_RefUsageCS ()) ["UsageCS"] "h01zh12b1h22b2h31nh41Hh51bh61kp;1p;2p;3p;6g000ij17Tg001Nj1HTg001lj18Tg013oj2?Tg0070j29Tg01H9j2ETg005Kj20Tg00=2j22Tg004Sj36Tg01DLj3>Tg02cXj24Tg004mj1<Tg00SSj2GTg00maj23Tg00=Oj2FTg02d>j3DTg02dej1;Tg02eoj2:Tg02f^j3CTg02gFj2BTg000Kj6=Tg02hJj1ATg00A?j2@Tg02C6R0f1R1f0R236p=1P0f4R3f3R4f2R5P1P2E=p=5g00F[#7R6#7#7#7#7#7R7#HR8#8R9p,1ER:g00G@'?R;1982R<'ER=p,3sp0,08R>/21R?,98R@9692X59g02\5RA%82RB%81RCg00TL%85?61210451041'1RD[10511052'1%84?651[RE%83?645\DA>512P2n2001000000120000000W2W1W3PE^2C^1B^3AP2P81981,08RA,2>RB,98RCP@148B12>5RE,98,08RD,12X001481R412>2R3,48/1DX00148?RD1485,2>,48/12X0012>4RF%<6%<7'GR7'3148ER6,12X001317RG1337/16X0013?7R61357,2>/37/12X00P613E7,12X001F0612>G/37AD1>7D5PD%;?D5P4%;1D5148F%;FD5108@1:8?D5PA1:81D5108C1:8BD5O4b41983R3969=eg02>1?C;<1B;<E=%A2,@:=693eX60o"). Qed.

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
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "##e=p'0h02Hih11ni001nh21bh32Hah44__p1h54__x1h61ih71Hh82H0h93Hi0h:7__arithh;4__ffh<7__sat10h=6!s0$8h>!s/%9h?8__varmaph@5__withA4cstrhB1xp%0p;1p;2p;3p;4p;6p;<p;7p;8g00F6j1<Tg000ij13Tg004mj17Tg001Nj1WTg005Kj2^Tg0065j2H!s/$QR0j10Tg01e\R1j21!sW$lj1NTg01GVj3CTg00CLj1MTg0070j2FTg00=Oj2@Tg00A?j2>Tg02a6j4GTg00<Tj1a!sJ$2j2?Tg01E0j2J!tb$Sj3ATg00;5j2]!t}$Kj6ITg02hJj1QTg02iTj1PTg00M;R2j1KTg00T0R3j2ETg01g?j4[Tg00k?j1Z!s/$dj2YTg00SSj2XTg00lLj3tTg00m0j2s!s/$aj2rTg00PNj1qTg002Oj1pTg0152j1oTg00nAj2mTg023Vj4U!s8$_j1lTg00o=j1jTg01<Cj2L!s8$hj2iTg021cj4TTg010Kj1gTg028[j6fTg011Pj2eTg0122j2d!s/$^j3hTg013=j4cTg02j\j4k!s8$oj2bTg025Il<V!t$$>l<nTg022Nj7`Tg026Tj3D!tp$2j8_Tf0R4#<#<p=8%34#3p=O!s-$#3#3p=u!s2+!s$'p==f7R5f6R6f5R7f4R8g02koR9f3R:CG'Jf2R;g02>]R<f1R=g02RmR>P4CG'>3Ap=21J;==A:4p=B1b=4,@;p=41?8:/?;/?=/?4p=5g02;mR?P?g02C6R@P@P0P2P2P6g02m=R6P7P8P?P?P!sA,:P6P;P=P4M<VM<Vp=6!sE$1P2P3g02Mg!sZ$:!sJ'np=\g02=SR3/H4p=:P=g02CTR2g02D3R1P1g02DSR6P4g02EZF`p=SAD@8:=D@;=D@==D@4p=;P:P2P1P1!tN'G_p=R%04#0#0#0p=9p,4SPlog00F[R0#<#8!s$03#O#u#=!s$$7%30RA#3RB#3RC#3RD#3RE#3RF#WRGp,3sp0'^RH'H!s{$hi%3FRF!sc&!sg$,HHp,1ERIP>p,1RRJg00G@RK#0RL#0RM#0RN#0RO#0RP#0RQ#0RR#0RS#0RT#0RU#0RV#0RW#0RX#0RY#0RZ#0R[#0R\#0R]#0R^#0R_#0R`#0Ra#0Rb#0Rc#0Rd#0Re#0Rf#0Rg#0Rh#0Ri#0Rj#0Rk,14RlP?%NGRmPJ%<ARn#WRo#NRp!w@$JYRq9Co3RrPIP=%M3RsG2^0lP=11Kk1FG3,@mPmPJPr1>IsCBe!s3$pPKP9PrCGP<PKP>PsCG,>ICBeW0P?%04R>/1k!sP%%0=RKPrPIPKPsG2]0P411LkA4mIR!sr&L!sE$LPsG2!sg&>!sg0KR!sH-!sg%MkPm%aFR<,?H,FGR9%7ARA=Coq,JJRl=Am4X2mPm%7F,]H,FGAAm49X2m1@m9Plp,3RspEI%Q<,>I%P<EI!tZ&M!t8$M!tZ<LR!sH-!tZ%N!uC$T!sg&N!sE$N!sg<MR!sH-!sg%Okp,3RtpPmPJ%7B=Coq%<D#3!zd$8#3#<!s&$!zr%7#M!w1%!t>&O!st$O!t><NR!sH-!t>%P!u#$V!sg&P!sE$P!sg<OR!sH-!sg%Q!sg$W!sg&Q!sE$Q!sg<PR!sH-!sg%R!sg$X!sg&R!sE$R!sg<QR!sH-!sg%S!vQ$s0!vQ%CRC!vS$MA!v90S!s\$S!s~<RR!sH-!s~%T!tg$Z!sg&T!sE$T!sg<SR!sH-!sg%U!sg$[!sg&U!sE$U!sg<TR!sH-!sg%VkPm1?HC,FG!uS$<nRG#7=CoqP4CBX2mp,3Ra1%QC!zx$C!zx+V!sp$V!t:<UR!sH-!t:%W!t{$]!sg&W!sE$W!sg<VR!sH-!sg%X!sg$^!sg&X!sE$X!sg<WR!sH-!sg%Y!sg$_!sg&Y!sE$Y!sg<XR!sH-!sg%Z!sg$`!sg&Z!sE$Z!sg<YR!sH-!sg%[!sg$a!sg&[!sE$[!sg<ZR!sH-!sg%\!sg$b!sg&\!sE$\!sg<[R!sH-!sg%]!sg$c!sg&]!sE$]!sg<\R!sH-!sg%^!sg$d!sg&^!sE$^!sg<]R!sH-!sg%_!sg$!|E'_!sE$_!sg<^R!sH-!sg%`!sg$f!sg&`!sE$`!sg<_R!sH-!sg%a!sg$g!sg&a!sE$a!sg<`R!sH-!sg%b!sg$h!sg&b!sE$b!sg<aR!sH-!sg%c!sg$i!sg&c!sE$c!sg<bR!sH-!sg%d!sg$j!sg&d!sE$d!sg<cR!sH-!sg%e!sg$!sH&Pe!sE$e!sg<dR!sH-!sg%fk%0kRC94m!~r'f!sI$f!sk<eR!sH-!sk%gk%0C!sk0g!sI$g!sk<fR!sH-!sk%h!sk4h!sI$h!sk<gR!sH-!sk%i!sk4i!sI$i!sk<hR!sH-!sk%jk%0!si/j!sG$j!si&%0>/1k%0i!sm$%K=Rj%70R0P!s$$D5P!s0h%7ERE'ES00P>1?40XB@R>P!s$ajO1S01O1S02O1S03O1S04O1S05O1S06O1S07O1S08O1S09O1S0:O1S0;O1S0<O1RCO1RqO1RoO1RBO1R<O1RlO1R9O1RFO1RtO1RuO1RvO1RwO1RxO1RyO1RzO1R{O1R|O1R}O1R~O1P>PiP~P>PhP}P>PgP|P>PfP{P>PePzP>PdPyP>PcPxP>PbPwP>PaPvP>P`PuP>P_PtP>P^PFP>P]P9P>P\PlP>P[P<P>PZPBP>PYPoP>PXPqP>PWPCP>PVQ0<P>PUQ0;P>PTQ0:P>PSQ09P>PRQ08P>PQQ07P>PPQ06P>POQ05P>PNQ04P>PMQ03P>PLQ02P>PKQ01P>P=Pj1@@jF6!s$APkPE1@@EE\P4C[Q00%Z;%K;#:%3G#7RG,YA1E3A%:G1XAGRk,E3[[%:ARjg02X`R>AtAG=UW3%:k\>^3j%7DRD,sH%:H%:D1rHD#:[[p-0RDg02F:RH#q%pHP@%o@RHP=P@1m@=P=PHCUCU%l@%j@RHP@1L@3g02E31i@nRnCT,SH%g1RjPHP@Pn1L@0RnP!s$$D;P!s0hg02H91L@E!t;$PjPH!#NT':EfCRCR1eH6P4P;g02B6RHg02BVR6'@1d4;=AH6dAh@3=Ccb;b?b@X5@W4%:4P=P!};r/EEP:[[^5@^4DP4!~m%%95#9!s$/Rp!~~$pPsG2%K5P8P7O4b:b=b>b<bAb9W0X6?P4O1n0110001020111100X1!s>G0!s>~!s>~!s>~!s>50!s>~!s>W!tv~!s>~!uN{P4O1!{l$Ckb8b7o"). Qed.

  (* [comment removed for export] *)
  Ltac kslot HYP :=
    eapply (kword_intro RSEGS E M (EVar 0) sp0);
      [ reflexivity | | lia | lia | lia | lia | exact HYP ].

  Lemma know_okUS : (bv_unsigned pp + 8 <= bv_unsigned sp0 + 4194304)%Z -> know_ok RSEGS E M knUS0.
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "#$Oih04__x1h17__arithh24__ffh38__varmaph45__with57__sat10h6!s0&1h7!s0&2h86!s0$8h9!s/%9h:4__x2h;1zh<1bh=4cstrh>4__x3h?!sL%0h@!s/%1hA1mhB2HahC1dhD2HshE1xhF2HdhG2HmhH1HhI2H0hJ2H1hK2H2hL4Hpp2hM1nhN1yp%0p%1p&0p;1p;2p;3p;4p;7p;8p;6p;5p;<p;Bp;@g000ij13Tg001Nj1yTg005Kj2CTg004mj1:Tg00=2R0j20Tg00F6j1>Tg0065R1j22Tg00mak20r!sX$Sj3BTg00RMk10^Tg00SSk20G!sl$ij1HTg00V0k20TTg00W9j3}Tg00<Tj1STg00;5j2WTg00?0j2{Tg00XBk20@!tA$Qj18Tg00CLk107Tg00YKk20OTg00PNk105Tg02mak10MTg00QNk30LTg02ngk30Kk409Tg002Ok10DTg0152k10qTg00n_k10jTg00o=k10eTg01<Ck202Tg011Pk20]!u<$Oj2ATg0122k20[!s0$^k30YTg013=k40XTg00T0R2j2<Tg0307k70!uJ$kdk20FTg00lLk30E!v[$0k20V!tP$Ak20!w'$ohj2xTg010Kk10U!sv$Lj2kTg031>j7~Tg01[Pk30!wn$M;R3j1;Tg032Ek20BTg01;`j3|Tg00A?j2d!ss$mk30!u1$\[k80?Tg0070j2!vz$k?j1wTg01?ij2!v/$EZk60>!vC$Pk20=Tg024]j2p!w4$nj3jTg023Vj4vTg00@8k10<Tg00BFk10;Tg01]ck40!yX$1lk108!u,$6R4j2tTg018ej4!wL$7dk10P!s9$Bk40NTg01G3j2`!s/$Vj3\Tg01E0j2!x,$P7j2b!w5$oj2cTg01e\R5j2hTg033Rj2fTg000Kj6NTg034Zk50JTg035gk80!u6$2ok10nTg01o7k40i!v&$Vk20h!yN$kk20fTg036lk60dTg00gNk20cTg0385k30bTg039Bk60!{9$Nik40aTg00ZTk30`Tg021cj4nTg022Nj7mTg0287k70I!vU$2j8oTg0277k40_Tg026Tk301!w+$4k30g!si$>m<03Tg025Im<0\!s0$nmB0!xy$:Km@0lTg03;Qk60mTf0R6#3#3p=I%3!s0$!s$,p=J!s:+p=rf2R7f1R8'0/26p=4%>6#>p=Y!sJ':p!x_$=SR9!sG$11<86,k7p=^%86#8p=lf3R:/{7@0`86p=G%>6#3p=U%3!sp$u%36#:p>0Qg02@mS00?j86p=?g02C6R;0026p=7P7g02CTR<g02D3R=P=g02DSR>P;P8g02H9R?P6Cng02EZR@Fmp=Qg02B6RAg02BVRB7B6p>0ZP7P<P=P=P!s`'E3RCP6CnP!s[$5!sF-8P6K0Ip>0Sf6RD!s='f5REf4RFP:!sO+7P8P6GoGop=Z1086,@7p=Xg02<LRG!sD%H0_=BABp=VB01;86p=KPE!sg+FP:!tf1P!ta+Gop=E!s9$!uV$p=aPF!sP+:!t'$!s4'6!sV&>0RP!t}+PEP!ty/;B01;7!t-2!uB3!sw0K0Ip=]20=;6p=iB0g!u4$[1A;6p=6g02;mR@P;P4P3P1g02ME!tA&!un$N<03p=sP@P;!s$$3P3!sE2\p>06!sD&!s$%0P6P8P7P0P:PFPEPDf7R0f8S01f9S02NB0kp=M!sQ$1P0P1PD!t@5O12EF12:!s9$CDp=RPG!s}&!s{&P0Q01Q02f:S03f;S04f<S05f=S06f>N@0lp=P202;6:01;8p=L!w_,p>04!xn5p=zg02JYS079\86p=_!um$5P3P2g02Mg!tu5eP;P9!s9'ENp=g12F!s5&CDp>0oQ00!s[,J0mp==g00F[R2#3R3#3S08#3S09#3R5#3S0:#3R<#yRCp,2ppR1'CS0;Q09#:R4p,3sp0R?,CCRH%I<#JRI#I#rRJ#:S0<'034p,4SPloS0=%>2S0>#>RK#>RL#>RM#>#Y!s$'RN#r#J!s$$TRO/2H!s_$hiRP%IJRJ!sC&TRQ,!sA&alRR%:5RS-0rHRT=B;9&0^1Q0;#1Q0;%:3RU%:<RV+0GRW3^p,1ERXp,1MRYg00G@S0?#HRZ00TSR[A}ZOQR\Q0>#3S0@#3#IR]#SR^g03<2R_'WR`,{ZRa00@_S0APZP4Q0?#8Rb#8S0B#8S0C#8Rc#8S0D#8Rd#lRe%HbS0ECGS0FQ0E%UJ#I!u=%S0G7}OS0HPZ%3K#IRK#SRJPeQ0@#>Rf#>#u#r#u#U#u#U$0QS0I$07S0JCGS0KPZ%S<R<PeQ0C#HS0LCGS0MPZQ08#>S0N#3S0O#I#SS0PPe%8eRg#l#l#lRh#HS0QCGS0RPZ%>3S0S#3S0T#3S0U!sX%VPe%8h!sR$8Ri#8Rj#8S0W#8S0X#8S0Y#8Rk#HS0ZCGS0[PZQ0S#>S0\#3S0]!sj%^Pe%8k!sM%_CGS0`PZ%3]#SS0a!sA-bCGS0cPZ%3f#IRf#SS0d!sE-eCGS0f!v@%SS0g!sA-hCGS0iPZ%3L#IRL#SS0j!sE$S0!sF$lCGS0m&079S0n%IM#U!yS$M'{S0o%Jf#TRf+0@S0p%:IS0q%UL!w]%r+0OS0sQ0n%>5#uR5#U#Y#r#U#TS0tPcQ0D#HS0uCGS0vQ0ng03=!wO$B#HCGS0wQ00$05S0x'?S0y'?S0z'?S0{'?S0|'?S0}'?S0~'?S10'?S11'?S12'?S13'?S14'?S15'?S16'?S17'?RL'?RI'?Rk'?Q00g03>@$0MS18Q0u%:2RK%YN!|R$:S193}S1:Q!tL$1;40LB0KGXYRNP[PkPGPXPYPZPSg02F:Rk$05R[&0DkRl&0q;Rm&0j;Rn&0e;Ro202;9Rp%7S3Q20]o>R>P6P71AAB20[67$0ZdB0Y;98H0XRBb2b3b41<9SP6b1PRK0WPNP\PI!tD+OPQ20FUVRI1<9UR\%1V1<9WS1<[[RR%1URAg02X`RqB0EUV8UWBRV%1W\q^BARrQ0]#:Rs-0FURt%1s20GUsS1=,<9[\\R\B0EUs8VqXBARuQ1=#1!s_%A20VHSRq%1H%1S%1T[[RTP[Pl200;8RSPnPo1x;2R2%7QS1>55oRv&0U=R=Po%7OS1?=5o2RwP=B0SowvFZP>P!uf&X0;126QRx12O8S1@12O7S1A127Q'k[[^0;P6PHPPQ0=O3S1Bb1b8b9b5b6b7F~PNQ0APLB0CXa_%18RL%;8,07S1C/2_S1D20BXa=XC:=VY7S1E[[^A@^C;PXPZP`P_PIPRPVPrPtP\PuPAPqP!uQ$P!uL$PwP=PoPp%7^%35#TR5#7Ry5|;,K2S1FEE!u>2O6Rz1W^5S1G,08R^#1!u7'Q0=O2R{!u4/10H`R|#1e1dXZ,CC/0`R`#1e!tM$mPnA5opy!t/,%15P6b1129_R}eP}e!u1BvP=PoQ1F%7US1H>0A;CRU'aI0R!u'1<^W\x!w,+O2RP!ts0<|We1<`W!t=KPyPUFF!t10A4^5!t2&!t&0A4|_WeA4`_WeL0?Q1Dp,6MstackAXC|:R`P7O2%:]R],WHR},@C,CCR~/W_1CC`'2AXC|F,CCS1I%;:S1J;4~10|ER`,@CS1K=VYF[[P;P~1W6_Q1K!sR$K'210|DS1L!sL$M,CC%;ES1N;48AXC|0=VYDS1O[[X;;P6P}%w:Q1J#1!uxG!yH%%7]9|;2R~95opPo1a~UC]!{\2Q1@1W7]S1P#1Q1P;^W[!vB$Q!{J1b=%1}?^}We,q}J0>1W}_R_Q1I'2Q1K%;FS1I;4}Q1M=VYE[[P;Q1K12_6%;D=48}Q019XC|=VY0!uG'`%wFQ1I!uG9%icS1I%ibS1KQ0?-0=;S0?'['[g02FfS1M'p%idQ0D#iQ0C#iQ0?'[S0C'[S0D'[Q1M'p=jk[5jkPlP;P;PmP7200;:S1BCvP8PmCvS1@PnPoQ0@,x;S0@95opS1PP=Po1x;3R3Q0@'K=5oyP=PoA5op3S1Q!w#$!w,-!s+%Q1F/K3R|!w2'|!w2$FZ!w62X:;X>;%17S1FA47:5%1:12:Q12OFS1R12OES1SQ1G,0D/00S1G#1Q1G;^W[!s#$^0;^:;^>;P6Q04#;Q05PHPDQ02Q03f?f@Q0=O9!x%3`?^`We,q`J0>12_`Q1LQ1N;4}S1GQ1O[[P6%wES1OQ1N#1R}!yz<;200;7R`!v^'N!v^$!v2%A|;~yP|!#4=1X:;1W8]R]/W510^7R^'2\L!u=%P6Q06PHQ04O3!u%1Q1L,2_eQ1OP!t[>P`P8Q!x=$!x4$>,x;R`,K3!wx'P|P`P~!~f2!wH%A4875A4^:]!vq15#;!tb&3O4!tb3GeO2bDbDbD&0<a,dX,CC&0;a'0!#8&&eQ1EeWGXFLXA@XC;H0:!#;~$Q0AH09ePNQ0FQ17!#<9%?P4PeQ0EP1&08CRa/A?R^1Aa1Q0E,dX=Ba1e1tbe12K4R1PbPK%6KS17PeP4%64S0FEs!#7O&%7KS0A%74R]55o!ui,P1P6b1CDR11tee1244R5PeP4Q0F!s,&!sj,A5o]]!sa-5!sa&5!#:?H1K2]S1D!xp21084S1E#1\z^0;P!#9t24R~%;eR`'0R|PW10~4RyPWP6XE;R}1286$0PXN;XE;R_P|PyP}!s$$;P;g02[Q1086H0N#6XA;XM;RyP~P~%6~P`P4P}P}%;6#6XE@S1G!ue&J06R~M:MPWPW%6WR|GO!#9LHDP]!#9L3Q1E?44!#9N6ERp,5MargvM?PPNQ0HQ16!x{'EPOQ0G!tE7Q0DQ1M'pQ1KQ0B!#5/%!#5#2Q!}/'>95o3!tl%?=5o3S1?!tz&Q0<,L355o!#4i%32!sM&!#4a%oQ0G#7-042C]Cz!#4V6128QQ1AQ0<,0:947412F:Q1SQ1SQ0G,2E'k!#4A,!#?E$;!#SA$Q03p,4Hpp1Q0=O7!#Ad4KQ15!{j+JPeQ0JQ0I,@CREP^1AaEQ0J!{g%EeP1P!z>KL2JS0J!z>5JR!z=<JRJ/0`RQPW10J4ROPWP}P_PQPO!z#&yPJPJ%6J!yg$!yN'P!yKK0J!yK6A4E!yI<3Mra!yG&MQ14!vC+<PeQ0Lp,3s0v!vC,L!vCX<RE!vB5<RJ!vB;<R</0`ROPW10<4RQ!vB&OPQ!vB+<P<%6<!vBXPE!vA8J!vA>s0!vA&RQ13!vA'Q0PPeQ0Qp,1RRJQ0S#yREQ0N#:R<Q071`E<d3\'9P^Pa%;g,@E,9J1_E<,9JRQ9Ba6X<a1AaQ1bdg,cXQ0k#8#lRQ,hgQ0:#:RO,<<S0:Pg!uc%QPO%6OS0kE!#GT'%7<%7OR<5Q!#7$,Q0:!#6F$,fgEN!wpMQ0P,L2S0:!ws2Q0P,08S0S!wv8!sD$HRg/0`S0PPW10g4S0!wz&Q0PQ0!w|,gPg%6g!{@Z:!w}6Q0S!#5e=3Ms1!x#&[Q12!x#,VPeQ0ZQ0O#:Rg!wr%gd5\E,9J!wt%h!wt+g,9JS0Z!wu&Q0Z,Aa1bdh,cX1hhQ1<gOS0ZPh!uP%QPOQ!wf1g=Qo<!wb/Z!wb'h!wbQV!wb$Z!wb4V,08Rh!wa:V!wa,V!wa&12!wa'VQ12!waiZ!|`8h!w_?2!w_&`Q11!w_,^PeQ0_Q0N#>#:Rh!wa%h!wa0i!wa+h,9JRg!|W,g1bdi!w^$iQ1<hORgPiPh%6h!w]6h!w]1Pg!w\'i!w\Q^!w\$N!w\4^,08Ri!w\:^!w\,^!w\%Rh!w['^Ph!wZiN!wZ8i!wZ?3!wZ&cQ10!wZ,aPeQ0bQ0U#:Ri!wX%i!wX0j!wX+i!wX6j!wX$jQ1<iORgPjPi%6i!wX6i!wX;j!wXQa!wX$U!wX4a,08Rj!wX:a!wX'Ri!wW1Pi!wVkU!wV8j!wV?4!wV&fQ0~!wV,dPeQ0eQ0T!|2$j!wX%j!wX-Q0W#;!wZ+j!wZ3Q0W,bd,cXQ0WQ0W/hQ1<jORgQ0WPj%6j!wb6j!wb9'f!waQd!wa$W!wa4d,08Rg!wa:d,0HRj/0`RhPW10j4Ri!wa&hPi!wa+j!u1%!waYW!wa8g!wa?5!wa&iQ0}!wa,gPeQ0!#4d%sd9\Es!wY+X!wY-s!wY5X!wY'XQ0X!wY$s!wY$XPs%6s!wY6s!wYig,L2Rg!wX4g,08Rs!wX:g!wX+i!wX&!|;7!wX^Pg!wW8s!wW?6!wW&mQ0|!wW,jPeQ0lQ0\!|:$?!w`%?!|:0Y!w_-?,9JRJ!w_,JQ0Y!w_'YQ0Y!w_$?ORdQ0YP?%6?!w_6?!w_2d!w_Yj,L2Rw!w_4j,08R5!w_:j,0HR{/0`RzPW10{4R1!w_&zP1!w_+{P{%6{!w_Yw!w_85!w_?7!w_&pQ0{Q0o>0CXfQ1C/2fRPQ0o-0BX!#Wt&Rx[\L!#hx&Q0nPMPf106MR5#1X;;!w&,MRw,KpRv95op!tZ,109MR~#1P6b11@C9R`,CCR{!uO+!se&!#_@$pPo1apUC!#V},1299Q1<'kP6b1b?b@,q9R1CgQ0n!#Yr$/0MRz!#hz,%7fRd!tR1%1fR<P6b1P<e1<5WX;;!tN3AQovU!tD-<~W!t?'P{P1Cg1<zWeA45f!sd71Kvd=5o!sg-A4~f!sh2A4zfWeL0?AXC5F=VY:X;;PY10~:R5,@CRzP7P;P512M6X;;%w7R<%;7#1R?!xuAA5op2RO!xz%1Kv2Rv!za2%1610~8Rw,2M!#lu$Q03Q01O2!#]t01CCzRzP<P!t@8Q1IQ0C!#W,,PlQ!#dk%!#d^$Q0@,K2=5od!tZ$O!#Vk,A5opvPo1av!#dA%!#_u5Q1FA48:fQ1FQ1R10~FR~#1?^~W!#c{32#;R~PHQ03!$'1'!#Va1b=,q5RDENP;P5Q1JQ0O#>#U!#y2%5546X;;!u`;P[!#YU'1K23!uH+vP3%75!#b&4A468fA4w75!#XW+~Q03P0!#cZ2PzPDENI0J!y&%Q0o$0<!{/%!s2$;!#a},PxeXGP!#a}6p!#a}&sQ0z!s;'qQ0!zO+Q0q#7!{k1Q0q!}<%!z{3Q0r#7!z|1Q0r/2!z}+p,3MroL0pPNQ0vQ0y!t>%nP`Q!#|4$up,3tidR@,@CRP1Aa`1AaP1tbcQ08#:R`,2KRxPbPKQ17PcP`%6`Rb!#bP+Q0A%7`R7!#c90x!#7J$1tce12`4RxPcP`Pb!#c667]!s^5Q0t,06Rx!#4T/Q0t,LpR]!v93t,09R4!v>&!w`$%;cRe=4xWX;;104eR:PW104`RD/2WRzP}P_P:PD!#7g'4P4%64PeP`P}P}Q1G!t|%J06!#7u6!#3>']!w@2Pz!w<'I0o!y:'9#y$08$0DRz$0nPGPY1@CxPcH0i20hcP-0fz3BX;;p,4Mtid!s^%!#81%wQ0x!ww%Bp,3canR11@C1,Aap,4McanJ0dQ0000cNRaD=!s$E!ss$18Q1;p,6Mcells:0bXYPNQ1:Q0x!zN'uPKQ19P;P@12K6Q19,26'k!#6<-!#:s8oAQop2PoQ1HQ0]#y60A;,a2C]Rp!#3k$A=5o!sF$9!#cB+!#y?196Q1=7^6R912K8!tJ$8'k!#{H%@p,4HtidO2R6!}T/1CCP!tjB!tP$POPo1a2U!tF4A^L8W\9!t4$!t#/,q@ENF~PaD=J0HJ0H!vA%g02T6H0aebKbJbIbHWLo"). Qed.

  (* [comment removed for export] *)
  Theorem ref_usage_cs : ltac2:(zQ "hc0!h9!jc!nb!ij8!iif!in5!ioe!ih7!ii1!io8!ip8!l9!n6!ita!iu1!iu7!iv4!iva!jh2!jk5!jnc!jr3!jrb!kgd!kl9!kpc!kq9!ktb>3a0s@1$2@1$1@1$0#8>2t8@1$2@1$1@1$0#8>0@1$h1@3$hb@1$1@1$0#8@2$7@1$0#8Z^2>0@2$9@1$6@2$4@1$1@1$0#8^3+hvvvf>0@2$9@2$3@2$3@2$8@1$0#k0?2pp@1$6@2$4@1$1@1$0#8^4+8@2$3@2$8@1$0#k0?3sp0+kgggg0>0@2$9@2$3@2$3@2$8@1$0#k0?2pp@1$6@2$4@1$1@1$0#8^5+8+ogggggggggg0>0@3$c@1$b@1$2@1$1@1$0#8@4$d$5?1M?2pp@2$h2@2$4@1$1@1$0#8^6N1@2$a@1$2@1$1@1$0#8@3$e@1$1@1$0#8^6@3$f@1$1@1$0#8@2$7@1$0#8Z@1$h0@1$1@1$0#8>0@3$c@1$b@1$2@1$1@1$0#8@4$d$5?1M@2$7@1$0#k0@2$3@2$8@1$0#k0?2pp@1$6@2$4@1$1@1$0#8^7N8@2$a@1$2@1$1@1$0#8^6@4$h8$5$h7@2$h3@5$h5?2fx?1R@2$7@1$0#k0+knlm8?1M@1$h6$5?5model@2$ha@1$h9^8@1$h4?5model").
Proof.
ltac2:(KReplay.run1z (kr_t_RefUsageCS ()) ["UsageCS"] "##8dh02Hah14__x1h24__x2h34__x3h43HPlh56Hnonulh64Hpp2h74Hpp3h84Hstrh93Ht8h:7__arithh;4__ffh<7__sat10h=!s0&1h>6!s0$9h?8__varmaph@5__withA3a0shB4cstrhC2t8p;1p;2p;3p;4p;Bp;7p;8g000ij10Tg001Nj1J!s/$lj1GTg002Oj1PTg0070j2NTg00Kkj3]Tg00LBj1[!s/$[j27Tg00M;j1:Tg00F6j19Tg004mj14Tg0065j26Tg005Kj2OTg00=2j21!t1$oj1_!sJ$Qj13Tg00P7j2\Tg01o7j4M!s8$Nj1L!s/$nj3KTg00QNj3Z!s/$kj2I!t:$Sj3@!t$$Oj2?Tg00k?j1Y!s/$dj2XTg00T0j2HTg00SSj2WTg00lLj3VTg00m0j2U!s/$aj2STg015Pj2BTg0244j3E!s/$]j2RTg00nAj2F!sJ$2j1TTg023Vj4Q!sA$_j1kTg00o=j1jTg01<Cj2;!s8$hj2ATg010Kj1iTg026Tj3<Tg011Pj2cTg0122j2`!s/$^j3aTg013=j4bTg03?Hj1^Tg03@PlBeTg021cj4fTg022Nj7g!tU$2j8hTf0R0#0#0p=D%90#9p=8%0!s8$!s$,p=2g02=SR1/60p=5g02C6R2f1R3g02E3P0Cfp=>P3g02CTR4g02D3R5P5g02DSR6P0g02EZFgp==!t'+p=df3R7P4P5P5P6f2R4P3P0Ghp=Cg00F[R8#0R9#DR:#JR;#GR<#PR=1N;1R;=]<3#[17<4#:%98#!s$0R>#9#4'6%0:R?#DR@#JRAp,2ppRB'ORC17<7#:'1%4:R:'1p,3sp0RD,OARE%2@#2R@#4RF'1'6f4RG,7<#:,1C/1:%0@#2!s$$4'6%_=R@g02<LRHp,1MRIPBf5RJ,7<g00G@RK#3RL'\CM%L<9K<;9Z<J,I=3@PHPIf6RH!t$',NA%3LRL#3R;#3!s$'CM1I=J5@@f7R@PBPHg02`1p,1RPIPJPGg03AY%GARA/?D1?ABp,4Hpp1P7P4g03Bb17<@R@#Y%:@#5%49R@%99RA#9#0#4RB'X1H1@%5B1W@BRD,H1[[%5@RJg02X`RIAV@B3UW0%5D\I^0J%4?R?,UE%5E%5?1SE?#5[[g02F:R?1B2;1B2L1B2K5E25E2g02Ff'R%L?3K%P?P21F24P3!s-$7P7%T2CQCQ%k2%j2R?1;211A2ARA'>,=?%i5R5P?1A28R8=<2A1;2:RA5<21A29R91;2F5<2RK!sT$P5P?%0>#D#d!we'R>,;2/>9!sD$A<28A/>K,=?C!s#$1c?6P0P4g02B6R?g02BVR6'?1`04=@?6dAa213Cbb;b?b@X12X22X32%541137/1:114F'616>7117:11GF'6[[[^12^22^32P0f<!xL$PEPCPGf8p,4SPloO6b:b>b<b=bB#^P3P0MBeW9W8W7W6W4W5XC=WAo"). Qed.
End UsageCS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
