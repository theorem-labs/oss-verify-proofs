(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StreamSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout PnLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u PnCertKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u
     PnSMakeEcP_u Bs0_code_r363e8_363ec_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSME.
Import PMS.
Abbreviation AN := PnLayoutS_u.NADDR_S.

Lemma wseg_errg : wseg_ok RSEGS (Z_to_bv 64 820608) (Z.to_nat 2) = true. Proof. vm_compute. reflexivity. Qed.
Lemma wseg_atexit : wseg_ok RSEGS (Z_to_bv 64 958472) (Z.to_nat 544) = true. Proof. vm_compute. reflexivity. Qed.
Lemma cs_erA : forall k, In k PMK.cs_all -> In k PNSMEP.KS_erA. Proof. PMCK.cs_all_tac. Qed.
Lemma cs_erB : forall k, In k PMK.cs_all -> In k PNSMEP.KS_erB. Proof. PMCK.cs_all_tac. Qed.
Lemma cs_erC : forall k, In k PMK.cs_all -> In k PNSMEP.KS_erC. Proof. PMCK.cs_all_tac. Qed.

(* [comment removed for export] *)
Definition dec_dom (a : Z) : Prop := 0xc8588 <= a < 0xc85c8.
Lemma bdec_keep M M' d : (forall a, 0 <= a < 2 ^ 64 -> dec_dom a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
  PNST.bdec_ok RSEGS AN M d -> PNST.bdec_ok RSEGS AN M' d.
Proof.
  intros AG. unfold PNST.bdec_ok, dec_dom in *. cbn [PNL.pn_inf_guard PNL.pn_nan_guard PNL.pn_inf_obj PNL.pn_nan_obj AN] in *.
  assert (AGR : forall a n, 0xc8588 <= a -> a + n <= 0xc85c8 -> L5C.agree_on M M' a n) by (intros a n Ha Hn i Hi; apply AG; lia).
  destruct d.
  - intros (G1 & G2 & S1 & S2). split; [|split; [|split]].
    + apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; lia|lia|lia|exact G1].
    + apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; lia|lia|lia|exact G2].
    + destruct S1 as (S1a & S1b). unfold PNST.sso_lit. split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; lia|lia|lia|exact S1a]|].
      apply (L5C.defined_agree M M'); [apply AGR; lia| exact S1b].
    + destruct S2 as (S2a & S2b). unfold PNST.sso_lit. split; [apply (L5C.u8_at_agree RSEGS M M'); [apply AGR; lia|lia|lia|exact S2a]|].
      apply (L5C.defined_agree M M'); [apply AGR; lia| exact S2b].
  - intros (C1 & C2 & C3 & C4). repeat split; intros i Hi; rewrite AG by lia; [apply C1| apply C2| apply C3| apply C4]; exact Hi.
Qed.

Section Stage.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.

Theorem make_ec_ok : PNRS.make_ec_spec L HI.
Proof.
  unfold PNRS.make_ec_spec, PNR.make_ec_spec.
  intros fx R M model K LB cr o v sp r ax HH (Mh & Ml & Mm) K0 ENT A10 A11 Hv Hspo Hotop Ho8 DEFO BASE ERR KONT.
  destruct ENT as (Rra & (RA1 & RA2) & Rsp & Rgp & Rtp & STK).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11.
  pose proof (L5C.stk_floor _ _ _ _ STK) as FL. pose proof (L5C.stk_writable RSEGS _ M sp _ STK) as WR0.
  pose proof STK as (S16 & SB & SC & SD & SW). unfold PMSP.pm_scr in *.
  assert (WRO : L5.writable RSEGS M o 16) by (apply (L5C.writable_of_defined RSEGS M o 16 DEFO); lia).
  pose proof (PMCK.lb_hi L HI HIok LB cr M _ HH) as LBhi.
  destruct BASE as (RO0 & _ & NL & _).
  cbn [pa_rw_lo pa_need_locks AD PnLayoutS_u.ADDR_S] in RO0, NL.
  destruct ERR as (EG & EDEC & EA). unfold PNST.batexit_st in EA. cbv zeta in EA.
  unfold PMSP.cfg. cbn [pa_make_ec AD PnLayoutS_u.ADDR_S].
  destruct (PNST.bax_cat ax) eqn:ECAT; cbn [pa_errcat_guard AD PnLayoutS_u.ADDR_S] in EG.
  - (* [comment removed for export] *)
    assert (EADD : PNST.bax_add_cat ax = ax) by (destruct ax; cbn in ECAT |- *; congruence).
    rewrite EADD in KONT.
    LeanFeed.pfeed P (PNSMEP.erA_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | _ => 0 end)) ltac:(first [ PMK.sc | exact EG ]).
    destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & C8 & C0).
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x36ee4 R1 0x36f38 M1 (fun a => sp - 32 <= a < sp - 32 + 32 \/ o + 0 <= a < o + 0 + 16) K HH Mh Ml ltac:(lia) MS MG).
    { intros a Ha NP. apply FRZ; [exact Ha| |]; intros X; apply NP; [left|right]; exact X. }
    { intros a Ha. apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 1) a STK). lia. }
    { intros a. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH1.
    assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 32 <= a < sp) -> ~ (o <= a < o + 16) -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha N1 N2. apply FRZ; [exact Ha| lia| lia]. }
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x36f38 W_36244 r F_36244 ltac:(reflexivity) D_36244)|].
    + rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
    + exact RA1.
    + exact RA2.
    + apply (KONT fx1 R1 M1).
      * apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_erA. exact Hk.
      * split; [apply PMCK.u32_of_u64; exact C0|]. split; [exact C8|]. apply (L5.defined_grows M M1 _ _ MG). exact DEFO.
      * apply (PNKP.berr_agree RSEGS AD AN PNRS.addrs_wf_B M M1); [| split; [rewrite ECAT; exact EG| split; [exact EDEC| exact EA]]].
        intros a Ha D. apply AG; [exact Ha| |]; unfold PNKP.edep, PNL.pn_d128_foot in D; cbn in D;
          (destruct D as [D|[D|(iv & Hin & D)]]; [lia|lia| destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in D; lia]).
      * apply PMK.hpres_of.
        -- apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 1) [(o, 16)] M M1 (fun a => sp - 32 <= a < sp \/ o <= a < o + 16)).
           ++ intros a Ha NP. apply AG; [exact Ha| |]; intros X; apply NP; [left|right]; exact X.
           ++ exact STK.
           ++ exact LBhi.
           ++ intros a [X|X]; [left; lia| right; apply PMK.inW_here; exact X].
        -- apply (L5.defined_grows M M1 _ _ MG). exact SW.
        -- apply PMK.dk_grows. exact MG.
      * exact HH1.
  - (* [comment removed for export] *)
    pose proof (PMCK.writable_img M 820608 2 wseg_errg ltac:(lia) ltac:(lia) ltac:(lia)) as W1.
    pose proof (PMCK.writable_img M 958472 544 wseg_atexit ltac:(lia) ltac:(lia) ltac:(lia)) as W2.
    destruct ax; cbn in ECAT; try discriminate ECAT; clear ECAT;
      cbn [PNST.bax_add_cat PNST.bax_list PNST.bax_dec length Z.of_nat Pos.of_succ_nat Pos.succ pa_atexit pa_errcat_dtor pa_errcat_obj AD PnLayoutS_u.ADDR_S PNL.pn_str_dtor PNL.pn_inf_obj PNL.pn_nan_obj AN PNST.slots_at] in EA |- *.
    + (* [comment removed for export] *)
      destruct EA as (X0 & XN & X12 & XH & X24 & (XF0 & XA0 & _) & XCF & XCA).
      LeanFeed.pfeed P (PNSMEP.erB_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | _ => 0 end)) ltac:(first [ PMK.sc | exact EG | exact W1 | exact W2 | exact X0 | exact XN | exact X12 | exact XH ]).
      destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B11 & B12 & B13 & C8 & C0 & G1 & G0 & SLOT & A1 & F1).
      set (P7 := fun a => (sp - 128 <= a < sp \/ o <= a < o + 16) \/ 820608 <= a < 820610 \/ 958480 <= a < 958484 \/ 958512 <= a < 958520 \/ 958768 <= a < 958776).
      assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ P7 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha NP. unfold P7 in NP. apply FRZ; [exact Ha| | | | | |]; intros X; apply NP; lia. }
      apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x36ee4 R1 0x36f38 M1 P7 K HH Mh Ml ltac:(lia) MS MG AG).
      { intros a [[Ha|Ha]|Ha].
        - apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 1) a STK). lia.
        - apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 1) a STK). lia.
        - destruct (PMK.rng_dec a 820608 820610) as [G|NG].
          + apply (PMKS.cwr_foot_S L LY LB (0xc8580, 0xc8582) a); [unfold pm_foot; cbn; auto| cbn [fst snd]; lia].
          + apply (PMKS.cwr_foot_S L LY LB (0xea008, 0xea008 + 544) a); [unfold pm_foot; cbn; auto 10| cbn [fst snd]; lia]. }
      { intros a. unfold P7. repeat apply PMK.or_dec; apply PMK.rng_dec. }
      intros HH1.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x36f38 W_36244 r F_36244 ltac:(reflexivity) D_36244)|].
      * rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
      * exact RA1.
      * exact RA2.
      * assert (CLRk : forall lo hi, 0 <= lo -> hi <= 2 ^ 47 -> (forall i, lo <= i < hi -> ~ P7 i) -> L5.img_clear M lo hi -> L5.img_clear M1 lo hi).
        { intros lo hi Hlo Hhi NP C i Hi. rewrite AG; [apply C; exact Hi| lia| apply NP; exact Hi]. }
        assert (U64k : forall a w, 0 <= a -> a + 8 <= 2 ^ 47 -> (forall i, a <= i < a + 8 -> ~ P7 i) -> L5.u64_at RSEGS M a w -> L5.u64_at RSEGS M1 a w).
        { intros a w Ha Ha' NP U. apply (L5C.u64_at_agree RSEGS M M1); [|lia|lia|exact U]. intros i Hi. apply AG; [lia| apply NP; exact Hi]. }
        apply (KONT fx1 R1 M1).
        -- apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_erB. exact Hk.
        -- split; [apply PMCK.u32_of_u64; exact C0|]. split; [exact C8|]. apply (L5.defined_grows M M1 _ _ MG). exact DEFO.
        -- split; [exact G0|]. split; [apply (bdec_keep M M1); [intros a Ha D; unfold dec_dom in D; apply AG; [exact Ha| unfold P7; lia]| exact EDEC]|].
           unfold PNST.batexit_st. cbv zeta.
           cbn [PNST.bax_add_cat PNST.bax_list length Z.of_nat Pos.of_succ_nat Pos.succ pa_atexit pa_errcat_dtor pa_errcat_obj AD PnLayoutS_u.ADDR_S PNST.slots_at PNL.pn_str_dtor PNL.pn_inf_obj PNL.pn_nan_obj AN].
           split; [apply CLRk; [lia|lia|intros i Hi; unfold P7; lia| exact X0]|]. split; [exact SLOT|].
           split; [apply CLRk; [lia|lia|intros i Hi; unfold P7; lia| exact X12]|]. split; [apply U64k; [lia|lia|intros i Hi; unfold P7; lia| exact XH]|].
           split; [apply CLRk; [lia|lia|intros i Hi; unfold P7; lia| exact X24]|].
           split. { split; [apply U64k; [lia|lia|intros i Hi; unfold P7; lia| exact XF0]|]. split; [apply U64k; [lia|lia|intros i Hi; unfold P7; lia| exact XA0]|].
                    split; [exact F1|]. split; [exact A1| exact I]. }
           split.
           ++ intros i Hi. rewrite AG; [apply XCF; lia| lia| unfold P7; lia].
           ++ intros i Hi. rewrite AG; [apply XCA; lia| lia| unfold P7; lia].
        -- apply PMK.hpres_of.
           ++ apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 1) ((o, 16) :: PNST.cat_W AD) M M1 P7 AG STK LBhi).
              intros a [[X|X]|X]; [left; lia| right; apply PMK.inW_here; exact X| right; apply PMK.inW_next].
              destruct (PMK.rng_dec a 820608 820610) as [G|NG].
              ** exists (820608, 2). split; [cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
              ** exists (958472, 544). split; [cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
           ++ apply (L5.defined_grows M M1 _ _ MG). exact SW.
           ++ apply PMK.dk_grows. exact MG.
        -- exact HH1.
    + (* [comment removed for export] *)
      destruct EA as (X0 & XN & X12 & XH & X24 & (XF0 & XA0 & XF1 & XA1 & XF2 & XA2 & _) & XCF & XCA).
      LeanFeed.pfeed P (PNSMEP.erC_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => o | 34%nat => v | _ => 0 end)) ltac:(first [ PMK.sc | exact EG | exact W1 | exact W2 | exact X0 | exact XN | exact X12 | exact XH ]).
      destruct P as (fx1 & R1 & M1 & MG & FR & FRZ & MS & KS & B11 & B12 & B13 & C8 & C0 & G1 & G0 & SLOT & A3 & F3).
      set (P7 := fun a => (sp - 128 <= a < sp \/ o <= a < o + 16) \/ 820608 <= a < 820610 \/ 958480 <= a < 958484 \/ 958528 <= a < 958536 \/ 958784 <= a < 958792).
      assert (AG : forall a, 0 <= a < 2 ^ 64 -> ~ P7 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
      { intros a Ha NP. unfold P7 in NP. apply FRZ; [exact Ha| | | | | |]; intros X; apply NP; lia. }
      apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x36ee4 R1 0x36f38 M1 P7 K HH Mh Ml ltac:(lia) MS MG AG).
      { intros a [[Ha|Ha]|Ha].
        - apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 1) a STK). lia.
        - apply (PMK.cwr_stack L LB M sp (12288 + 2048 * 1) a STK). lia.
        - destruct (PMK.rng_dec a 820608 820610) as [G|NG].
          + apply (PMKS.cwr_foot_S L LY LB (0xc8580, 0xc8582) a); [unfold pm_foot; cbn; auto| cbn [fst snd]; lia].
          + apply (PMKS.cwr_foot_S L LY LB (0xea008, 0xea008 + 544) a); [unfold pm_foot; cbn; auto 10| cbn [fst snd]; lia]. }
      { intros a. unfold P7. repeat apply PMK.or_dec; apply PMK.rng_dec. }
      intros HH1.
      eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| apply (PMK.ret_to RSEGS fx1 R1 M1 0x36f38 W_36244 r F_36244 ltac:(reflexivity) D_36244)|].
      * rewrite (KS 1%nat) by (apply L5K.In_of_mem; vm_compute; reflexivity). exact Rra.
      * exact RA1.
      * exact RA2.
      * assert (CLRk : forall lo hi, 0 <= lo -> hi <= 2 ^ 47 -> (forall i, lo <= i < hi -> ~ P7 i) -> L5.img_clear M lo hi -> L5.img_clear M1 lo hi).
        { intros lo hi Hlo Hhi NP C i Hi. rewrite AG; [apply C; exact Hi| lia| apply NP; exact Hi]. }
        assert (U64k : forall a w, 0 <= a -> a + 8 <= 2 ^ 47 -> (forall i, a <= i < a + 8 -> ~ P7 i) -> L5.u64_at RSEGS M a w -> L5.u64_at RSEGS M1 a w).
        { intros a w Ha Ha' NP U. apply (L5C.u64_at_agree RSEGS M M1); [|lia|lia|exact U]. intros i Hi. apply AG; [lia| apply NP; exact Hi]. }
        apply (KONT fx1 R1 M1).
        -- apply PMK.preserved_by_index. intros k Hk. apply KS. apply cs_erC. exact Hk.
        -- split; [apply PMCK.u32_of_u64; exact C0|]. split; [exact C8|]. apply (L5.defined_grows M M1 _ _ MG). exact DEFO.
        -- split; [exact G0|]. split; [apply (bdec_keep M M1); [intros a Ha D; unfold dec_dom in D; apply AG; [exact Ha| unfold P7; lia]| exact EDEC]|].
           unfold PNST.batexit_st. cbv zeta.
           cbn [PNST.bax_add_cat PNST.bax_list length Z.of_nat Pos.of_succ_nat Pos.succ pa_atexit pa_errcat_dtor pa_errcat_obj AD PnLayoutS_u.ADDR_S PNST.slots_at PNL.pn_str_dtor PNL.pn_inf_obj PNL.pn_nan_obj AN].
           split; [apply CLRk; [lia|lia|intros i Hi; unfold P7; lia| exact X0]|]. split; [exact SLOT|].
           split; [apply CLRk; [lia|lia|intros i Hi; unfold P7; lia| exact X12]|]. split; [apply U64k; [lia|lia|intros i Hi; unfold P7; lia| exact XH]|].
           split; [apply CLRk; [lia|lia|intros i Hi; unfold P7; lia| exact X24]|].
           split. { split; [apply U64k; [lia|lia|intros i Hi; unfold P7; lia| exact XF0]|]. split; [apply U64k; [lia|lia|intros i Hi; unfold P7; lia| exact XA0]|].
                    split; [apply U64k; [lia|lia|intros i Hi; unfold P7; lia| exact XF1]|]. split; [apply U64k; [lia|lia|intros i Hi; unfold P7; lia| exact XA1]|].
                    split; [apply U64k; [lia|lia|intros i Hi; unfold P7; lia| exact XF2]|]. split; [apply U64k; [lia|lia|intros i Hi; unfold P7; lia| exact XA2]|].
                    split; [exact F3|]. split; [exact A3| exact I]. }
           split.
           ++ intros i Hi. rewrite AG; [apply XCF; lia| lia| unfold P7; lia].
           ++ intros i Hi. rewrite AG; [apply XCA; lia| lia| unfold P7; lia].
        -- apply PMK.hpres_of.
           ++ apply (PMK.ek_piece_in RSEGS L KL LB sp (12288 + 2048 * 1) ((o, 16) :: PNST.cat_W AD) M M1 P7 AG STK LBhi).
              intros a [[X|X]|X]; [left; lia| right; apply PMK.inW_here; exact X| right; apply PMK.inW_next].
              destruct (PMK.rng_dec a 820608 820610) as [G|NG].
              ** exists (820608, 2). split; [cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
              ** exists (958472, 544). split; [cbn; auto| unfold L5.in_rng; cbn [fst snd]; lia].
           ++ apply (L5.defined_grows M M1 _ _ MG). exact SW.
           ++ apply PMK.dk_grows. exact MG.
        -- exact HH1.
Qed.

End Stage.
End PNSME.
