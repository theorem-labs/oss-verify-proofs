(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_bson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
     PmLayout PnLayoutS PmModel PmModelFacts PmStatics PmSpecs PnSpecsS PmStep PmKeep PnKitS
     PgSrc PgV8 PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun PnRunS PnTopS PnSHarnessStmts PnSHarnessKit PnSHarnessP.
From OSSVerify.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNH5.
Import PMS. Import PNH.
Local Ltac lia := PMK.alia.     (* [comment removed for export] *)

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ra n : Z).
Variable LB0 : list (Z * Z).
Variable cr0 : credit.
Variable g : PNST.st.
Hypothesis Hn : 0 <= n < 2 ^ 26.
Hypothesis Hcr0 : PMSP.credit_le (PNTS.TOPK, PNTS.TOPB n) cr0.
Hypothesis Hgp : getr R0 (reg 3) = Z_to_bv 64 (pa_gp AD).
Hypothesis Htp : getr R0 (reg 4) = Z_to_bv 64 (pa_tp AD).

Lemma stage5 :
  PNRS.parse_spec L HI ->
  forall (fx : FPState) R M model cr s s2 sm qc b K,
    PNH.H4 L HI R0 M0 model0 sp ra n LB0 cr0 g R M model cr s s2 sm qc b -> K [] ->
    (forall (fx1 : FPState) R1 M1 model1 cr1 p sm1 ax,
        PNH.H5 L HI R0 M0 model0 sp ra n LB0 cr0 g R1 M1 model1 cr1 s s2 p sm1 ax ->
        srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx1 R1 0x34490 M1 model1) K) ->
    srealizes RSEGS SCFG (@PMSP.cfg RSEGS fx R 0x34480 M model) K.
Proof using All.
  intros PARSE fx R M model cr s s2 sm qc b K (CORE & VS & SZ & IA & SZ2 & SG & ST0 & PA & VV & HST & HH & CK & EC & VREF) K0 KONT.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R M model CORE) as (Hsp & Rsp & Rng & A16 & WR & STK).
  pose proof STK as (A16f & SLO & SHI & STOP & _).
  pose proof CORE as (_ & Hcs & _ & _ & _ & _ & SPT & _ & _ & BASE & _ & (Mh & Ml & Mm)).
  set (p0 := PNR.bparser_init qc b) in *.
  set (LBX := PM.vs_own s2 ++ PM.vs_own s ++ LB0) in *.
  set (LBc := PNM.bparser_own p0 ++ LBX) in *.
  assert (VREF' : L5.u64_at RSEGS M (sp - 328) (sp - 320)).
  { unfold PNH.fb, FRAME in VREF. replace (sp - 784 + 456) with (sp - 328) in VREF by lia. replace (sp - 784 + 464) with (sp - 320) in VREF by lia. exact VREF. }
  LeanFeed.pfeed P (PNSHP.bhnF_conc fx R M (fun j => match j with 2%nat => sp | 40%nat => sp - 320 | _ => 0 end)) ltac:(first [PMK.sc]).
  PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & A1 & A10 & A11 & A12)); PMK.pvz_clrT.
  unfold PMSP.cfg.
  apply (PMK.spiece RSEGS L HI KL HIok LBc cr M model fx fx1 R 0x34480 R1 0x35fb4 M1 (fun _ => False) K HH Mh Ml ltac:(lia) MS MG).
  { intros a Ha _. apply FRZ. exact Ha. }
  { intros a []. }
  { intros a. right. tauto. }
  intros HH1.
  assert (CORE1 : PNH.hcore L R0 M0 model0 sp ra LB0 R1 M1 model).
  { apply (PNHK.hcore_piece L LY R0 M0 model0 sp ra LB0 R M model R1 M1 (fun _ => False) CORE MG); [intros a Ha _; apply FRZ; exact Ha| intros a []| rewrite (KS 2%nat) by PMK.inl; exact Rsp|].
    intros k Hk. apply KS. revert k Hk. apply PNH.CSK_in. vm_compute. reflexivity. }
  assert (EM : M1 = M) by (apply functional_extensionality; exact FR). subst M1.
  pose proof (PNHK.hcore_facts L R0 M0 model0 sp ra LB0 R1 M model CORE1) as (_ & Rsp1 & _ & _ & _ & _).
  pose proof CORE1 as (_ & Hcs1 & _).
  pose proof (ly_kpm L LY) as HK. pose proof (ly_bov L LY) as HB. pose proof (PNTS.pot_callB_le L n LY Hn) as (PC1 & PC2).
  assert (SC10 : 0 <= PMSP.pm_scr 10) by (unfold PMSP.pm_scr; lia).
  assert (STKc : L5C.stk (hl_sptop L) M (sp - 784) (PMSP.pm_scr 10)).
  { apply (PMK.stk_call L M (sp - 784) (65536 - 784) (sp - 784) (PMSP.pm_scr 10) STK); [lia| unfold PMSP.pm_scr; lia| unfold PMSP.pm_scr; lia| exact A16f]. }
  destruct HST as (SLOC & SSYS & SERR).
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IAE & _).
  unfold PNRS.parse_spec, PNR.parse_spec in PARSE.
  apply (PARSE fx1 R1 M model K LBX cr (sp - 784) 214160 (sp - 784) (pa_syscat_obj AD) 0 p0 s2 sm (PNST.st_ax g) HH1).
  - repeat split; assumption.
  - exact K0.
  - unfold PMSP.entry. rewrite L5K.rl1, L5K.rl2, L5K.rl3, L5K.rl4. split; [exact A1|]. split; [split; [lia| reflexivity]|]. split; [exact Rsp1|].
    split; [rewrite (Hcs1 3%nat) by (unfold CSK; cbn; auto); exact Hgp|]. split; [rewrite (Hcs1 4%nat) by (unfold CSK; cbn; auto); exact Htp|]. exact STKc.
  - unfold PMSP.frame_ok. cbn [pa_frame AD]. split; [lia|]. split; [lia| exact A16f].
  - unfold PNR.bargs3, PNR.o_p, PNR.o_v, PNR.o_ec, PMSP.o_p, PMSP.o_v, PMSP.o_ec. cbn [pa_off_p pa_off_v pa_off_ec AD]. rewrite L5K.rl10, L5K.rl11, L5K.rl12.
    split; [replace (sp - 784 + 40) with (sp - 744) by lia; exact A10|]. split; [replace (sp - 784 + 464) with (sp - 320) by lia; exact A11|].
    replace (sp - 784 + 16) with (sp - 768) by lia. exact A12.
  - unfold PNR.brun_pre, PMSP.visitor_at, PNR.o_p, PNR.o_is, PNR.o_v, PMSP.o_p, PMSP.o_is, PMSP.o_v, PNM.PSIZE. cbn [pa_off_p pa_off_is pa_off_v AD].
    split; [exact PA|]. split; [exact IA|]. split; [exact VV|].
    split; [unfold PNH.fb, FRAME in VREF; replace (sp - 784 + 40 + 416) with (sp - 784 + 456) by lia; exact VREF|].
    split; [exact BASE|]. split; [exact SERR|].
    unfold PNM.bgrow_ok, PM.tb_ok, PGV8.v8_ok. cbn. repeat split; lia.
  - unfold LBX. apply incl_appl. apply incl_refl.
  - unfold PNR.binv, p0, PNR.bparser_init. cbn [PNM.b_done PNM.b_stk].
    split; [reflexivity|].
    unfold PNR.bstack_shape. cbn [length nth]. split; [lia|]. split; [unfold PNM.MAX_DEPTH; lia|]. split; [left; reflexivity|].
    split; [intros i Hi; lia|]. intros i Hi. assert (i = 0%nat) by lia. subst i. cbn [nth]. unfold PNM.bstate_ok, PNM.bs_root. cbn. lia.
  - unfold PNR.o_ec, PMSP.o_ec. cbn [pa_off_ec AD]. exact EC.
  - lia.
  - unfold PM.unread, p0, PNR.bparser_init. cbn [PNM.b_src PM.sr_rem]. unfold PNH.fb, FRAME in IAE, SG. rewrite IAE, SG, SZ2.
    replace (sp - 784 + 472 + 80) with (sp - 784 + 552) by lia. lia.
  - unfold PNR.bb_room, p0, PNR.bparser_init. cbn [PNM.b_bb PGV8.v8_room]. exact I.
  - destruct CK as (CK1 & CK2). destruct Hcr0 as (C6 & C7). unfold p0, PNR.bparser_init. cbn [PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg].
    clear - CK1 CK2 C6 C7 PC1 PC2 HK HB Hn. PNHK.cred_norm. lia.
  - intros fx2 R2 M2 model2 p sm2 ax cr2 RP (RPRE & SSTEP & EMONO & ECD) HP CK2 MB HH2.
    destruct RPRE as (PA2 & IA2 & _ & _ & _ & SERR2 & _).
    set (W' := PNR.W_brun AD AN (sp - 784)) in *.
    unfold PNR.o_p, PNR.o_is, PMSP.o_p, PMSP.o_is in PA2, IA2. cbn [pa_off_p pa_off_is AD] in PA2, IA2.
    apply (KONT fx2 R2 M2 model2 cr2 p sm2 ax). unfold PNH.H5.
    assert (WC : forall a, PMK.inW W' a -> (sp - 784 + 16 <= a < sp - 784 + 664) \/ (PMK.inW WF a /\ PNHK.err_dom a)).
    { intros a (r & Hin & Hr). unfold W', PNR.W_brun, PGS.W_srcfG, PNST.berr_W, PNST.cat_W, PNST.dec_W, PNR.o_src, PNR.o_bb, PNR.o_nb, PNR.o_tb, PNR.o_stk, PNR.o_ec, PNR.o_is, PNR.o_p,
        PMSP.o_is, PMSP.o_ec, PMSP.o_p, PNM.OFF_SRC, PNM.OFF_BB, PNM.OFF_NB, PNM.OFF_TB, PNM.OFF_STK in Hin.
      cbn [pa_off_p pa_off_is pa_off_ec pa_errcat_guard pa_atexit PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AD AN app] in Hin.
      unfold L5.in_rng in Hr. unfold PNHK.err_dom.
      destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]]]; cbn [fst snd] in Hr;
        first [left; lia
              | right; split; [|lia]; match type of Hr with ?lo <= _ < ?lo + ?len => exists (lo, len) end;
                split; [unfold WF, PNST.pn_foot, pm_foot; cbn; auto 12| unfold L5.in_rng; cbn [fst snd]; lia]]. }
    assert (EKc : PMK.ek L LBX (sp - 784) (PMSP.pm_scr 10) W' M M2) by (apply (PMK.ek_of_hpres L); exact HP).
    assert (BRx : PNHK.brange L LBX) by (apply (PNHK.brange_of_heap L HI LY HIok LBc LBX cr M _ HH); unfold LBc; apply incl_appr; apply incl_refl).
    assert (WSTD : forall a, PMK.inW W' a -> PNH.fb sp <= a \/ 65536 <= a < 958464).
    { intros a I. destruct (WC a I) as [F|(_ & F)]; [left; unfold PNH.fb, FRAME; lia| right; unfold PNHK.err_dom in F; lia]. }
    split. { apply (PNHK.hcore_call L LY R0 M0 model0 sp ra LB0 R1 M model R2 M2 model2 LBX (PMSP.pm_scr 10) W' CORE1 RP HP);
               [unfold LBX; apply incl_appr; apply incl_appr; apply incl_refl| unfold PMSP.pm_scr, SCR, FRAME; lia| |exact MB].
             intros a I. destruct (WC a I) as [F|(F & _)]; [left; unfold PNH.fb, FRAME; lia| right; exact F]. }
    split. { eapply (PNHK.vstr_keep L LY sp LBX (PMSP.pm_scr 10) W' M M2 EKc STKc SC10 BRx WSTD); [unfold PNH.fb, FRAME; lia|unfold PNH.fb, FRAME; lia| | |exact VS].
             - intros i Hi I. unfold PNH.fb, FRAME in Hi. destruct (WC i I) as [F|(_ & F)]; [lia| unfold PNHK.err_dom in F; lia].
             - unfold LBX. apply incl_appr. apply incl_appl. apply incl_refl. }
    split; [exact SZ|].
    split; [unfold PNH.fb, FRAME; exact IA2|].
    split; [unfold PNH.fb, FRAME; exact PA2|].
    split. { split; [|split; [|exact SERR2]].
             - apply (PNHK.loc_keep L LY LBX (sp - 784) (PMSP.pm_scr 10) W' M M2 EKc); [|exact SLOC].
               intros a I D. unfold PNHK.loc_dom in D. destruct (WC a I) as [F|(_ & F)]; [lia| unfold PNHK.err_dom in F; lia].
             - apply (PNHK.sys_keep L LY LBX (sp - 784) (PMSP.pm_scr 10) W' M M2 EKc); [|exact SSYS].
               intros a I D. unfold PNHK.sys_dom in D. destruct (WC a I) as [F|(_ & F)]; [lia| unfold PNHK.err_dom in F; lia]. }
    split; [exact EMONO|].
    split; [exact HH2|].
    destruct CK as (CKa & CKb). destruct CK2 as (CK3 & CK4). unfold p0, PNR.bparser_init in CK3, CK4. cbn [PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg] in CK3, CK4.
    clear - CKa CKb CK3 CK4 HK HB Hn. PNHK.cred_norm. lia.
Qed.

End Stage.
End PNH5.
