(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Mem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsClsKit CXXRep CXXLib CXXLib2 AsObj AsStack0 AsWalk N8Kit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AXpres BJIface BJKitRoom AKitChk BJKitVS BJKitPA BJKitPV W_afail W_asuspend.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bvhfbbv_unsigned46Stdlib6ZArith6BinInt1Zkf2le01Z37Corelib4Init5Logicmf2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~o85asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~sb2wz37Corelib4Init9Datatypeshgb4listmf3and3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshj1dmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhn95mkCfg3h5LinuxProcessSemanticsfLinuxProcessSem5Statehqe5Model79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB5BJRep~~~~~~hu56ps_endhu55ps_vs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~ij45blockij43mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~io14cellkf3addkf2ltkf3powhgb4Nonehgb3apphgb4conshgb3nil3h5LinuxProcessSemantics5Riscv7Preludeiv45bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB6AXpres~~~~~~ji37inframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7BJIface~~~~~~jmb6A_FAILjmbh0parse_value_postjmb8parser_Xjmb7pv_costhu5abj_staticshu59blocks_vshu59parser_athu56pstate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsConst~~~~~~kh16ACONSTij43ATPij48as_AKRELij48as_MPRESij46as_RFSij48as_RHEAPij45as_SRij45as_Stij46as_VISij4bas_rauxv_okij46fframe79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~ks25aceilks2baddressable79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsStack0~~~~~~lh86stack079OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6CXXRep~~~~~~lm05xpresio12C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib2FP~~~~~~lqb4frm079OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~luc3mkRluc3stk79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~mj62MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~mn97mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~mre7seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ng88rw_cellskf6modulokf3subhgb4boolhgb5falsemf3notjmbaA_MSUSPENDhu57ps_moreij43asrij4casan_rt_hyps" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!noe$0").
  Hypothesis RT : ltac2:(zQ "10!np5@2$0?5HCEIL?1H").

  (* [comment removed for export] *)
  Lemma tail_fail : ltac2:(zQ "jc0!h9!jc!k1!m7!mc!o3!s3!hg6!hi3!hib!hm8!hq5!htc!ii1!iib!in1!ina!ird!is5!isb!it0!it6!ite!iu5!iud!jha!jm0!jq9!jr3!js8!jt4!jtf!jud!jva!kg7!kke!kl8!klf!kmb!kn7!ko1!kod!kp6!kpf!kq9!kr8!lg0!lg9!ll6!lpc!lq5!lu4!mi8!mif!mn3!mr3!mvd!nk3!nkf!nl8>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$h9@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$a>1m$h0>2mc$h0>1s@1$ia?1H>4REST@1$8$f>2LF@1$8$id>2ps$i2>2lo$4>1B$4>4errv@1$1@1$0#k0>2mo$c>3mo1$c>1p$4>0@3$5$a@3$ib?1H^a^d@7$j6@hf$j4^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3@1$7+1^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f@1$7$hb^e@1$h5@1$1@1$0#k0^b@1$j8$6>0@3$i5?1H^b@2$b^e^3>0@3$i6?1H^5^4>0@4$i8?1H^d@3$h6$f@1$i0@1$e^a^c^e>0@3$i7?1H^c^f>0@2$j7$6^h0>0@4$j5$6^h1^c@2$2@1$0#k0^j2>0@2$3@1$ie?5HCEIL^d>0@2$3@2$h2^e+j0@2$2@1$0#k0^j4>0@2$9@2$3@2$2@1$0#k0^j5^e@2$h3^e@2$h4+2+k0>0@3$ic?1H^h5^f>0@4$j9$6^h6@2$h2@2$2@1$0#k0^j5-q4@3$h7$h1@1$j2^f@1$h8$h1>0@3$5@1$1@1$0#k0^j6@1$7$i4>0@1$hf^h8>0@1$i3^h9>0@4$j0?5HCEIL^ha^h5@2$2@1$0#k0^jb>0@1$j3^he>0@4$i1?5HCEIL^hc@2$2@1$0#k0^j5^h8>0@3$ha^ha@2$2@1$0#k0^j6+hh8>0@3$if^he@2$2@1$0#k0^j7+hh8>0@3$5$4@2$ja@2$2@1$0#k0^j8+h0Z>0@7$j1?5HCEIL?1H^he@2$2@1$0#k0^k1@1$hd@2$2@1$0#k0^j9^i1^i0>0@2$9@2$3+2@2$2@1$0#k0^j8@2$h3@2$2@1$0#k0^j8@2$h4+2+if>0@3$5$4^h8@2$2@1$0#k0^ja>0@2$3^h9@1$d^hf>0@2$3Z@3$he?1H@1$e^i0@2$jb@1$d^i0^ha@3$i9?1H@he$hc?5HCEIL?1H^k7^k6^k5^k4^k0^jf^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^i9^i8^i4^i3^i2@2$2@1$0#k0^je^i1^hb^i0^hf^i6^hd@2$b^i7^hc").
  Proof.
    intros until p. intros VIS AK MP HP RF MI ST CEIL ROOM SPB AUX ERR TP BS AC STK0 FRM PA IFR PAD PA16 XP A3 -> PLE CNN.
    pose proof (bv_unsigned_in_range _ sp) as RSP. unfold bv_modulus in RSP; cbn in RSP.
    pose proof (bv_unsigned_in_range _ a0) as RA0. unfold bv_modulus in RA0; cbn in RA0.
    pose proof (bv_unsigned_in_range _ a1) as RA1. unfold bv_modulus in RA1; cbn in RA1. acb.
    pose proof (inframe_range H RT _ _ _ _ RF IFR) as (IR1 & IR2 & IR3 & IR4 & IR5).
    pose proof (inframe_aapp H RT _ _ _ _ RF IFR ltac:(lia)) as APP.
    pose proof PA as PA0. apply parser_at_split in PA. ndestruct PA as (VS & PC & DR).
    ndestruct PC as (NUM & ECC & STZ & SCR & MOREC & ENDC & NB & NBP & OPT & DEPC & LITC).
    ndestruct ECC as (e1 & e2 & e3 & Re & Hiff & Hne1).
    eapply (ahh_evt H RT). { exact AK. } { exact VIS. }
    { eapply (fail_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (wz 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mc lo);
        [exact MI| exact ST| exact CEIL| unfold AFAIL_STACK; lia| exact BS| exact ENDC| exact Re| unfold wz; rewrite unsigned_lit by lia; lia| lia
        | exact APP| clear - PA16; Z.div_mod_to_equations; lia| exact PAD| exact AC]. }
    intros msF2 mo2 AK2 MP2 POST. cbn beta in POST.
    ndestruct POST as (a1' & a2' & a3' & m' & ev64 & lcf & E & MU & WM & MI' & ST' & BS' & END' & EC' & EV & LCF & AC').
    unfold AFAIL_STACK in MU.
    (* [comment removed for export] *)
    assert (WOK : Forall (aclient_write_ok H (blocks_vs (ps_vs ps) ++ REST)) [(bv_unsigned sp + -48, bv_unsigned sp); (bv_unsigned a0 + 184, bv_unsigned a0 + 192); (bv_unsigned a0 + 88, bv_unsigned a0 + 112)]%Z
              /\ Forall (afs_write_ok H LF) [(bv_unsigned sp + -48, bv_unsigned sp); (bv_unsigned a0 + 184, bv_unsigned a0 + 192); (bv_unsigned a0 + 88, bv_unsigned a0 + 112)]%Z).
    { pose proof (stack_window_ok' H RT _ _ _ LF (bv_unsigned sp + -48) (bv_unsigned sp) HP ltac:(lia)) as (W1 & W2 & _).
      pose proof (inframe_window_ok H RT _ _ _ _ _ _ _ (bv_unsigned a0 + 184) 8 HP RF IFR ltac:(lia) ltac:(lia)) as (W3 & W4 & _).
      pose proof (inframe_window_ok H RT _ _ _ _ _ _ _ (bv_unsigned a0 + 88) 24 HP RF IFR ltac:(lia) ltac:(lia)) as (W5 & W6 & _).
      replace (bv_unsigned a0 + 184 + 8) with (bv_unsigned a0 + 192) in * by lia. replace (bv_unsigned a0 + 88 + 24) with (bv_unsigned a0 + 112) in * by lia.
      split; (repeat apply Forall_cons; [..| apply Forall_nil]); assumption. }
    destruct WOK as [WOK1 WOK2].
    assert (HP' : as_RHEAP H s (blocks_vs (ps_vs ps) ++ REST) m') by (eapply (ah_RHEAP_frame H RT); [exact HP| exact MU| exact WM| exact WOK1]).
    assert (RF' : as_RFS H LF m') by (eapply (ah_RFS_frame H RT); [exact RF| exact MU| exact WM| exact WOK2]).
    assert (AUX' : as_rauxv_ok H m' B) by (eapply (ah_rauxv_frame H RT); [exact AUX| exact MU| exact WM| exact WOK1]).
    (* [comment removed for export] *)
    assert (XPF : xpres H (blocks_vs (ps_vs ps) ++ REST) (bv_unsigned sp) [(bv_unsigned a0 + 184, bv_unsigned a0 + 192); (bv_unsigned a0 + 88, bv_unsigned a0 + 112)]%Z mc m').
    { eapply (xpres_of_munch H); [exact RT| exact HP| exact MU| exact WM|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; lia|]. apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; lia| apply Forall_nil]. }
    assert (BB : blocks_below H (blocks_vs (ps_vs ps) ++ REST)).
    { split; [exact (RFS_fsb H RT _ _ RF)| intros b Hb; exact (ah_blocks H RT _ _ _ _ HP Hb)]. }
    assert (HX : X_above_hceil H [(bv_unsigned a0 + 184, bv_unsigned a0 + 192); (bv_unsigned a0 + 88, bv_unsigned a0 + 112)]%Z).
    { unfold X_above_hceil. apply Forall_cons; [cbn; right; right; left; lia|]. apply Forall_cons; [cbn; right; right; left; lia| apply Forall_nil]. }
    assert (XC64 : xclient_range H (blocks_vs (ps_vs ps) ++ REST) (bv_unsigned sp) [(bv_unsigned a0 + 184, bv_unsigned a0 + 192); (bv_unsigned a0 + 88, bv_unsigned a0 + 112)]%Z (bv_unsigned a0) 64).
    { split. { right; right; right; right; left. lia. } apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (VS' : vs_at m' (bv_unsigned a0) (ps_vs ps)).
    { eapply (vs_at_xpres H); [exact XPF| exact HX| exact BB| intros b Hb; apply in_or_app; left; exact Hb| exact XC64| exact VS]. }
    assert (TR : forall A cs, rw_cells asegs mc A cs -> bv_unsigned a0 + 64 <= A ->
                 (A + Z.of_nat (cells_size cs) <= bv_unsigned a0 + 88 \/ bv_unsigned a0 + 112 <= A) ->
                 (A + Z.of_nat (cells_size cs) <= bv_unsigned a0 + 184 \/ bv_unsigned a0 + 192 <= A) ->
                 A + Z.of_nat (cells_size cs) <= bv_unsigned a0 + 280 -> rw_cells asegs m' A cs).
    { intros A cs R H1 H2 H3 H4. eapply rw_cells_transport; [exact R| exact MU| exact WM|]. cbn. lia. }
    unfold parse_value_post.
    neexists 15. nexists m', s, (mkPS (ps_vs ps) (bv_unsigned a1) (ps_depth ps) true (ps_more ps)), F, fc, [].
    split. { rewrite E. unfold wz. reflexivity. }
    split; [exact FRM|]. split; [exact AK2|]. split. { cbn [cfg_model]. eapply (ah_mpres_trans H RT); [exact MP| exact MP2]. }
    split; [exact HP'|].
    split.
    { apply parser_at_split. cbn [ps_vs ps_end ps_depth ps_ecset ps_more]. split; [exact VS'|]. split; [| exact DR].
      split. { ndestruct NUM as (num & Ln & Rn). exists num. split; [exact Ln|]. apply TR; [exact Rn| lia| cbn; lia| cbn; lia| cbn; lia]. }
      split. { nexists ev64, (wz BJ_ERRCAT), lcf. split; [exact EC'|].
               pose proof (Z.add_lor_land (bv_unsigned a3) 1) as AL0.
               assert (LU : Z.land (bv_unsigned a3) 1 = (bv_unsigned a3) mod 2) by exact (zb_land_mask (bv_unsigned a3) 1 ltac:(lia)).
               pose proof (Z.mod_pos_bound (bv_unsigned a3) 2 ltac:(lia)) as LN.
               split; [| rewrite LCF; lia]. split; [intros X; discriminate X|]. intros EQ. exfalso.
               apply (f_equal bv_unsigned) in EQ. rewrite LCF in EQ. unfold wz in EQ. rewrite unsigned_lit in EQ by lia. lia. }
      split. { apply TR; [exact STZ| lia| cbn; lia| cbn; lia| cbn; lia]. }
      split. { ndestruct SCR as (sc & Ls & Rs). exists sc. split; [exact Ls|]. apply TR; [exact Rs| lia| cbn; lia| cbn; lia| cbn; lia]. }
      split. { ndestruct MOREC as (dn & cl & p5 & Lp & Rm). nexists dn, cl, p5. split; [exact Lp|]. apply TR; [exact Rm| lia| cbn; lia| cbn; lia| cbn; lia]. }
      split. { unfold wz. rewrite Z_to_bv_bv_unsigned. exact END'. }
      split. { ndestruct NB as (nb & Lb & Rb). exists nb. split; [exact Lb|]. apply TR; [exact Rb| lia| cbn; lia| cbn; lia| cbn; lia]. }
      split. { apply TR; [exact NBP| lia| cbn; lia| cbn; lia| cbn; lia]. }
      split. { destruct OPT as (pd2 & Ro). exists pd2. apply TR; [exact Ro| lia| cbn; lia| cbn; lia| cbn; lia]. }
      split. { apply TR; [exact DEPC| lia| cbn; lia| cbn; lia| cbn; lia]. }
      ndestruct LITC as (j8 & Lj & Rl). exists j8. split; [exact Lj|]. apply TR; [exact Rl| lia| cbn; lia| cbn; lia| cbn; lia]. }
    cbn [ps_vs ps_end ps_depth ps_ecset ps_more].
    split; [reflexivity|]. split; [reflexivity|].
    split. { right. exists []. unfold wz. rewrite unsigned_lit by lia. split; [reflexivity|]. split; [lia|]. split; [symmetry; apply app_nil_r|]. split; [constructor|].
             eapply (pv_spent_fail0 H RT); [exact HP| exact (vs_at_shape _ _ _ VS)| lia]. }
    assert (SOK : Forall stack0_ok [(bv_unsigned sp + -48, bv_unsigned sp); (bv_unsigned a0 + 184, bv_unsigned a0 + 192); (bv_unsigned a0 + 88, bv_unsigned a0 + 112)]%Z).
    { pose proof (aapp_bounds _ _ APP ltac:(lia)) as (APB1 & APB2 & APB3 & APB4 & APB5).
      assert (SLO : ALOWSH_LO < sh aceil) by (unfold sh, ALOWSH_LO; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      unfold stack0_ok. unfold aapp, aapp_lo, aapp_hi in APP.
      apply Forall_cons; [cbn; left; unfold AHI_LO; lia|]. apply Forall_cons; [cbn; lia|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    split.
    { split; [exact AUX'|]. split; [exact ST'|].
      split. { exists errv. pose proof aceil_range as ACR. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. rewrite TP. unfold ATP, wz. rewrite unsigned_lit by lia. cbn. clear - IR1 CEIL ROOM ACR. unfold AIMG_TOP, AFS_HDR in IR1. lia. }
      split; [exact MI'|]. split; [exact BS'|]. split; [exact AC'|].
      eapply stack0_transport; [exact STK0| exact MU| exact WM| exact SOK]. }
    split; [exact RF'|]. split; [constructor|].
    split. { rewrite app_nil_r. eapply xpres_trans; [exact XP|].
      eapply (xpres_weaken H (blocks_vs (ps_vs ps) ++ REST) REST (bv_unsigned sp) (bv_unsigned sp) (parser_X (bv_unsigned a0)) (parser_X (bv_unsigned a0))); [eapply (xpres_of_munch H); [exact RT| exact HP| exact MU| exact WM|] | lia| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha].
      unfold parser_X. apply Forall_cons; [left; cbn; lia|]. 
      apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; lia|]. apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; lia| apply Forall_nil]. }
    eapply (AsWalk.addressable_transport_hi); [exact PAD| exact MU| exact WM| unfold AAPP_HI; lia|]. hiw_tac.
  Qed.

  (* [comment removed for export] *)
  Lemma tail_susp : ltac2:(zQ "k00!h9!jc!k1!m7!o3!mc!s3!is5!hi3!hib!hm8!hq5!htc!ii1!iib!in1!ina!ird!hg6!it6!ite!nle!iu5!nm6!iud!nmf!jha!jm0!nn5!jr3!js8!jt4!jtf!jud!jva!no3!kg7!kke!kl8!klf!kmb!kn7!ko1!kod!kp6!kpf!kq9!kr8!lg0!lg9!ll6!lpc!lq5!lu4!mi8!mif!mn3!mr3!mvd!nk3!isb!nkf!it0!nl8>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a1@1$1@1$0#k0>2a2@1$1@1$0#k0>2a3@1$1@1$0#k0>2a4@1$1@1$0#k0>2a5@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$ha@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>3msF$a>1m$h0>2mc$h0>1s@1$ic?1H>4REST@1$8$f>2LF@1$8$if>2ps$i4>2lo$5>1B$5>4errv@1$1@1$0#k0>2mo$c>3mo1$c>1p$5>0@3$4$a@3$id?1H^a^d@7$j8@hf$j6^ie^id^ic^ib^ia^i9^i8^i7^i6^i5^i4^i3^i2^i1^i0^hf^he^hd^hc^hb^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f@1$h2$hc^e@1$h3@1$1@1$0#k0^b@1$ja$6>0@3$i7?1H^b@2$b^e^3>0@3$i8?1H^5^4>0@4$ia?1H^d@3$h4$f@1$i1@1$e^a^c^e>0@3$i9?1H^c^f>0@2$j9$6^h0>0@4$j7$6^h1^c@2$2@1$0#k0^j3>0@2$3@1$j0?5HCEIL^d>0@2$3@2$7^e+k0@2$2@1$0#k0^j5>0@2$9@2$3@2$2@1$0#k0^j6^e@2$jc^e@2$je+2+k0>0@3$ie?1H^h5^f>0@4$jb$6^h6@2$7@2$2@1$0#k0^j6-q4@3$h6$h1@1$j4^f@1$h8$h1>0@3$4@1$1@1$0#k0^j7@1$h2$i6>0@1$i0^h8>0@1$i5^h9>0@4$j2?5HCEIL^ha^h5@2$2@1$0#k0^jc>0@1$j5^he>0@4$i2?5HCEIL^hc@2$2@1$0#k0^j6^h8>0@3$4$h5@1$i3^h9$h7>0@3$hb^hb@2$2@1$0#k0^j8+hh8>0@3$j1^hf@2$2@1$0#k0^j9+hh8>0@3$4$5@2$jd@2$2@1$0#k0^ja+h0Z>0@7$j3?5HCEIL?1H^hf@2$2@1$0#k0^k3@1$he@2$2@1$0#k0^jb^i2^i1>0@2$9@2$3^h8@2$2@1$0#k0^jb@2$3@2$2@1$0#k0^jb@1$d^he>0@1$h9@3$4$5@2$2@1$0#k0^jc@2$7@2$2@1$0#k0^jd+1>0@2$3Z@3$hf?1H@1$e^i0@2$jf@1$d^i0^ha@3$ib?1H@he$hd?5HCEIL?1H^k8^k7^k6^k5^k1^k0^j7^j6^j5^j4^j3^j2^j1^j0^if^ie^i9^i8^i4^i3^i2@2$2@1$0#k0^jf^i1^hb^i0^hf^i6^hd@2$b^i7^hc").
  Proof.
    intros until p. intros VIS AK MP HP RF MI ST CEIL ROOM SPB AUX ERR TP BS AC STK0 FRM PA MORE IFR PAD PA16 XP PLE NE CNN.
    pose proof (bv_unsigned_in_range _ sp) as RSP. unfold bv_modulus in RSP; cbn in RSP.
    pose proof (bv_unsigned_in_range _ a0) as RA0. unfold bv_modulus in RA0; cbn in RA0.
    pose proof (bv_unsigned_in_range _ a1) as RA1. unfold bv_modulus in RA1; cbn in RA1. acb.
    pose proof (inframe_range H RT _ _ _ _ RF IFR) as (IR1 & IR2 & IR3 & IR4 & IR5).
    pose proof (inframe_aapp H RT _ _ _ _ RF IFR ltac:(lia)) as APP.
    pose proof PA as PA0. apply parser_at_split in PA. ndestruct PA as (VS & PC & DR).
    ndestruct PC as (NUM & ECC & STZ & SCR & MOREC & ENDC & NB & NBP & OPT & DEPC & LITC).
    ndestruct MOREC as (dn & cl & p5 & Lp & Rm).
    assert (M7 : rw_cells asegs mc (bv_unsigned a0 + 176) [C1 (b8 0); CB 7 (dn :: cl :: p5)]).
    { pose proof (rw_cells_merge asegs mc (bv_unsigned a0 + 176) [C1 (b8 0)] [C1 dn; C1 cl; CB 5 p5] [] ) as MG.
      ndestruct Lp as (Lp5 & _ & _). destruct p5 as [|q1 [|q2 [|q3 [|q4 [|q5 [|]]]]]]; try discriminate.
      cbn [app cells_size csize cells_bytes cbytes Nat.add] in MG. apply MG. rewrite MORE in Rm. exact Rm. }
    eapply (ahh_evt H RT). { exact AK. } { exact VIS. }
    { eapply (msuspend_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mc lo (wz (ps_end ps)) (dn :: cl :: p5));
        [exact MI| exact ST| exact CEIL| unfold AMSUSPEND_STACK; lia| exact M7| exact ENDC| exact NE
        | exact APP| clear - PA16; Z.div_mod_to_equations; lia| exact PAD| exact AC]. }
    intros msF2 mo2 AK2 MP2 POST. cbn beta in POST.
    ndestruct POST as (a1' & a3' & a4' & m' & E & MU & WM & MI' & ST' & END' & M7' & AC').
    unfold AMSUSPEND_STACK in MU.
    (* [comment removed for export] *)
    assert (WOK : Forall (aclient_write_ok H (blocks_vs (ps_vs ps) ++ REST)) [(bv_unsigned sp + -64, bv_unsigned sp); (bv_unsigned a0 + 184, bv_unsigned a0 + 192)]%Z
              /\ Forall (afs_write_ok H LF) [(bv_unsigned sp + -64, bv_unsigned sp); (bv_unsigned a0 + 184, bv_unsigned a0 + 192)]%Z).
    { pose proof (stack_window_ok' H RT _ _ _ LF (bv_unsigned sp + -64) (bv_unsigned sp) HP ltac:(lia)) as (W1 & W2 & _).
      pose proof (inframe_window_ok H RT _ _ _ _ _ _ _ (bv_unsigned a0 + 184) 8 HP RF IFR ltac:(lia) ltac:(lia)) as (W3 & W4 & _).
      replace (bv_unsigned a0 + 184 + 8) with (bv_unsigned a0 + 192) in * by lia.
      split; (repeat apply Forall_cons; [..| apply Forall_nil]); assumption. }
    destruct WOK as [WOK1 WOK2].
    assert (HP' : as_RHEAP H s (blocks_vs (ps_vs ps) ++ REST) m') by (eapply (ah_RHEAP_frame H RT); [exact HP| exact MU| exact WM| exact WOK1]).
    assert (RF' : as_RFS H LF m') by (eapply (ah_RFS_frame H RT); [exact RF| exact MU| exact WM| exact WOK2]).
    assert (AUX' : as_rauxv_ok H m' B) by (eapply (ah_rauxv_frame H RT); [exact AUX| exact MU| exact WM| exact WOK1]).
    assert (XPF : xpres H (blocks_vs (ps_vs ps) ++ REST) (bv_unsigned sp) [(bv_unsigned a0 + 184, bv_unsigned a0 + 192)]%Z mc m').
    { eapply (xpres_of_munch H); [exact RT| exact HP| exact MU| exact WM|].
      apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; lia| apply Forall_nil]. }
    assert (BB : blocks_below H (blocks_vs (ps_vs ps) ++ REST)).
    { split; [exact (RFS_fsb H RT _ _ RF)| intros b Hb; exact (ah_blocks H RT _ _ _ _ HP Hb)]. }
    assert (HX : X_above_hceil H [(bv_unsigned a0 + 184, bv_unsigned a0 + 192)]%Z).
    { unfold X_above_hceil. apply Forall_cons; [cbn; right; right; left; lia| apply Forall_nil]. }
    assert (XC64 : xclient_range H (blocks_vs (ps_vs ps) ++ REST) (bv_unsigned sp) [(bv_unsigned a0 + 184, bv_unsigned a0 + 192)]%Z (bv_unsigned a0) 64).
    { split. { right; right; right; right; left. lia. } apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    assert (VS' : vs_at m' (bv_unsigned a0) (ps_vs ps)).
    { eapply (vs_at_xpres H); [exact XPF| exact HX| exact BB| intros b Hb; apply in_or_app; left; exact Hb| exact XC64| exact VS]. }
    assert (TR : forall A cs, rw_cells asegs mc A cs -> bv_unsigned a0 + 64 <= A ->
                 (A + Z.of_nat (cells_size cs) <= bv_unsigned a0 + 184 \/ bv_unsigned a0 + 192 <= A) ->
                 A + Z.of_nat (cells_size cs) <= bv_unsigned a0 + 280 -> rw_cells asegs m' A cs).
    { intros A cs R H1 H2 H3. eapply rw_cells_transport; [exact R| exact MU| exact WM|]. cbn. lia. }
    unfold parse_value_post.
    neexists 15. nexists m', s, (mkPS (ps_vs ps) (bv_unsigned a1) (ps_depth ps) (ps_ecset ps) (ps_more ps)), F, fc, [].
    split. { rewrite E. unfold wz. reflexivity. }
    split; [exact FRM|]. split; [exact AK2|]. split. { cbn [cfg_model]. eapply (ah_mpres_trans H RT); [exact MP| exact MP2]. }
    split; [exact HP'|].
    split.
    { apply parser_at_split. cbn [ps_vs ps_end ps_depth ps_ecset ps_more]. split; [exact VS'|]. split; [| exact DR].
      split. { ndestruct NUM as (num & Ln & Rn). exists num. split; [exact Ln|]. apply TR; [exact Rn| lia| cbn; lia| cbn; lia]. }
      split. { ndestruct ECC as (e1 & e2 & e3 & Re & Hiff & Hne1). nexists e1, e2, e3. split; [| split; [exact Hiff| exact Hne1]]. apply TR; [exact Re| lia| cbn; lia| cbn; lia]. }
      split. { apply TR; [exact STZ| lia| cbn; lia| cbn; lia]. }
      split. { ndestruct SCR as (sc & Ls & Rs). exists sc. split; [exact Ls|]. apply TR; [exact Rs| lia| cbn; lia| cbn; lia]. }
      split. { nexists dn, cl, p5. split; [exact Lp|]. apply TR; [exact Rm| lia| cbn; lia| cbn; lia]. }
      split. { unfold wz. rewrite Z_to_bv_bv_unsigned. exact END'. }
      split. { ndestruct NB as (nb & Lb & Rb). exists nb. split; [exact Lb|]. apply TR; [exact Rb| lia| cbn; lia| cbn; lia]. }
      split. { apply TR; [exact NBP| lia| cbn; lia| cbn; lia]. }
      split. { destruct OPT as (pd2 & Ro). exists pd2. apply TR; [exact Ro| lia| cbn; lia| cbn; lia]. }
      split. { apply TR; [exact DEPC| lia| cbn; lia| cbn; lia]. }
      ndestruct LITC as (j8 & Lj & Rl). exists j8. split; [exact Lj|]. apply TR; [exact Rl| lia| cbn; lia| cbn; lia]. }
    cbn [ps_vs ps_end ps_depth ps_ecset ps_more].
    split; [reflexivity|]. split; [reflexivity|].
    split. { right. exists []. unfold wz. rewrite unsigned_lit by lia. split; [reflexivity|]. split; [lia|]. split; [symmetry; apply app_nil_r|]. split; [constructor|].
             eapply (pv_spent_fail0 H RT); [exact HP| exact (vs_at_shape _ _ _ VS)| lia]. }
    assert (SOK : Forall stack0_ok [(bv_unsigned sp + -64, bv_unsigned sp); (bv_unsigned a0 + 184, bv_unsigned a0 + 192)]%Z).
    { pose proof (aapp_bounds _ _ APP ltac:(lia)) as (APB1 & APB2 & APB3 & APB4 & APB5).
      assert (SLO : ALOWSH_LO < sh aceil) by (unfold sh, ALOWSH_LO; rewrite ASHADOW_BASE_val; Z.div_mod_to_equations; lia).
      unfold stack0_ok. unfold aapp, aapp_lo, aapp_hi in APP.
      apply Forall_cons; [cbn; left; unfold AHI_LO; lia|]. apply Forall_cons; [cbn; lia| apply Forall_nil]. }
    split.
    { split; [exact AUX'|]. split; [exact ST'|].
      split. { exists errv. pose proof aceil_range as ACR. eapply rw_cells_transport; [exact ERR| exact MU| exact WM|]. rewrite TP. unfold ATP, wz. rewrite unsigned_lit by lia. cbn. clear - IR1 CEIL ROOM ACR. unfold AIMG_TOP, AFS_HDR in IR1. lia. }
      split; [exact MI'|].
      split. { eapply bj_statics_frame; [exact BS| exact MU| exact WM|]. pose proof aceil_range as ACR.
               apply Forall_cons; [cbn; clear - CEIL ROOM ACR; unfold AIMG_TOP; lia|]. apply Forall_cons; [cbn; clear - IR1; unfold AIMG_TOP, AFS_HDR in *; lia| apply Forall_nil]. }
      split; [exact AC'|].
      eapply stack0_transport; [exact STK0| exact MU| exact WM| exact SOK]. }
    split; [exact RF'|]. split; [constructor|].
    split. { rewrite app_nil_r. eapply xpres_trans; [exact XP|].
      eapply (xpres_weaken H (blocks_vs (ps_vs ps) ++ REST) REST (bv_unsigned sp) (bv_unsigned sp) (parser_X (bv_unsigned a0)) (parser_X (bv_unsigned a0))); [eapply (xpres_of_munch H); [exact RT| exact HP| exact MU| exact WM|] | lia| intros b Hb; apply in_or_app; right; exact Hb| intros a Ha; exact Ha].
      unfold parser_X. apply Forall_cons; [left; cbn; lia|].
      apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; lia| apply Forall_nil]. }
    eapply (AsWalk.addressable_transport_hi); [exact PAD| exact MU| exact WM| unfold AAPP_HI; lia|]. hiw_tac.
  Qed.

End W.
