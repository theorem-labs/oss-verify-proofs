(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PgSrcKitA_b PnASrcRead1_b PnASrcReadK_b PnASrcReadP_b Ba0PgSrcReadK16_b Ba0PgSrcReadC16_b.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import L5DefsA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B.asan Require Import L5CoreA_b L5StepAR_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PmSpecsAX_b PnSpecsAa_b
     PmModelFactsA_b PnStepA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmParStep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnASrcKit_b PnASrcReadK_b PnASrcRead1_b PnASrcReadP_b Ba0_code_raf314_af318_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgSrc. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PgSrcA_b PgSrcKitA_b PnRunA_b PmAUarK_b PmAUar_b PnAReadCsK_b.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := first [ L5FastLia.plia | Lia.lia ].

Module PGSRDCD16.
Import PGSRDC16.
Ltac sdx Hi Y E1 E2 KB := first [ clear - Hi Y E1 E2 KB; lia | match goal with D : _ \/ _ |- _ => clear - Hi Y E1 E2 KB D; lia end ].
Ltac carry_with Ms AG KB fin :=
  lazymatch goal with
  | |- L5.u64_at ?s ?Mt ?a ?v => apply (L5C.u64_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| fin]
  | |- L5.u32_at ?s ?Mt ?a ?v => apply (PMF.u32_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| fin]
  | |- L5.u8_at ?s ?Mt ?a ?v => apply (L5C.u8_at_agree s Ms Mt a v); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| fin]
  | |- L5.defined ?Mt ?a ?n => apply (L5C.defined_agree Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| fin]
  | |- L5.writable ?s ?Mt ?a ?n => apply (L5C.writable_agree s Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| sd KB| sd KB| fin]
  | |- L5KA.zeros_at ?Mt ?a ?n => apply (L5KA.zeros_at_agree1 Ms Mt a n); [let ii := fresh in let Hii := fresh in intros ii Hii; apply AG; sdi Hii KB| fin]
  | |- L5.img_clear ?Mt ?lo ?hi => let ii := fresh in let Hii := fresh in intros ii Hii; rewrite (AG ii) by sdi Hii KB; revert ii Hii;
      change (L5.img_clear Ms lo hi); fin
  end.
Ltac sfind := match goal with
  | H : ?a <= ?x <= ?b |- ?a <= ?x <= ?b => exact H
  | H : ?a <= ?x < ?b |- ?a <= ?x < ?b => exact H
  | H : ?a <= ?b \/ ?c <= ?d |- ?a <= ?b \/ ?c <= ?d => exact H
  | H : ?a < ?b \/ ?c <= ?d |- ?a < ?b \/ ?c <= ?d => exact H
  | H : ?a <= ?b \/ ?c < ?d |- ?a <= ?b \/ ?c < ?d => exact H
  | H : ?a < ?b \/ ?c < ?d |- ?a < ?b \/ ?c < ?d => exact H
  | H : ?a mod ?b = ?c |- ?a mod ?b = ?c => exact H
  | H : getr ?R ?r = ?v |- getr ?R ?r = ?v => exact H
  | H : L5.u64_at ?s ?m ?a ?v |- L5.u64_at ?s ?m ?a ?v => exact H
  | H : L5.u32_at ?s ?m ?a ?v |- L5.u32_at ?s ?m ?a ?v => exact H
  | H : L5.u8_at ?s ?m ?a ?v |- L5.u8_at ?s ?m ?a ?v => exact H
  | H : L5.defined ?m ?a ?n |- L5.defined ?m ?a ?n => exact H
  | H : L5.writable ?s ?m ?a ?n |- L5.writable ?s ?m ?a ?n => exact H
  | H : L5KA.zeros_at ?m ?a ?n |- L5KA.zeros_at ?m ?a ?n => exact H
  | H : L5.img_clear ?m ?a ?n |- L5.img_clear ?m ?a ?n => exact H
  end.
Ltac feed P tac :=
  lazymatch type of P with
  | ?A -> _ =>
      let H := fresh "FD" in
      assert (H : A) by (first [ tac | fail 100 "feed: premise" A ]);
      specialize (P H); clear H; feed P tac
  | _ => idtac
  end.
Ltac dsp LIA MEM :=
  lazymatch goal with
  | |- PMASRP.aligned _ _ => unfold PMASRP.aligned; sfind
  | |- 0 <= bv_unsigned _ < 2 ^ 64 => exact (bv_unsigned_in_range _ _)
  | |- _ <= _ <= _ => first [ sfind | LIA ]
  | |- _ <= _ < _ => first [ sfind | LIA ]
  | |- getr _ _ = Z_to_bv 64 (bv_unsigned _) => symmetry; apply Z_to_bv_bv_unsigned
  | |- _ => first [ sfind | MEM ]
  end.
Ltac fin3 MG3 MV AG3 KB :=
  first [ sfind | (eapply L5.writable_grows; [exact MG3| sfind]) | (eapply L5.defined_grows; [exact MG3| sfind])
        | carry_with MV AG3 KB ltac:(idtac; sfind) ].
Ltac fin4 DF128 M3v AG43 KB MG3 MV AG3 :=
  first [ sfind | (eapply L5.defined_sub; [exact DF128| clear; lia| clear; lia]) | carry_with M3v AG43 KB ltac:(idtac; fin3 MG3 MV AG3 KB) ].

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma srd_cnz : PGSRDK16.srd_exit_T L ar HI 16 -> PGSRDC16.srd_fill_ret_case L ar HI (fun c => c <> 0).
Proof using All.
  intros EXIT. unfold PGSRDC16.srd_fill_ret_case.
  intros O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 FR
         fx R M model LKc Ac V BI V2 V36 V37 V38 V50 V51 VSV X3 X4 len1 c g2 st2 STC V39 V34 R10 HC PA IA BASE Hl1 Hl1k Hl1k' Hc Hg2 Hg2e Hst2 Hc0 DP.
  change (c <> 0) in HC.
  pose proof CTX as (OK & HH & AM & K0 & ENT & FRM & FRS & OFR & A10 & SP32 & ARGS & WX & PA0 & IA0 & BASE0 & INCS & KONT).
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH).
  destruct ARGS as (p' & k' & A11 & A12 & Hk & DST). destruct WX as (p'' & k'' & A11' & A12' & Hp'' & Hk'' & WE).
  rewrite L5SAR.r11 in A11, A11'. rewrite L5SAR.r12 in A12, A12'.
  pose proof (PGSA.oo_lay _ _ _ _ _ _ OK) as (LY1 & LY2 & LY3 & LY4 & LY5 & O8 & I8 & LY6 & LYD).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M0 _ OB PA0) as (PSRC & PNI & SDEF0).
  pose proof (PMASK.fs_above_img L ar C HI LY HIok _ _ _ _ _ _ _ HH) as FSI.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _).
  pose proof (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as FRB. pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH) as BRB.
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP).
  set (os := PGS.ow_os O) in *. set (ois := PGS.ow_ois O) in *. set (lo := PGS.ow_lo O) in *. set (hi := PGS.ow_hi O) in *.
  set (LB := PM.src_own (PM.SRC qc de rem) ++ OB ++ LBX) in *.
  assert (AO : PMSPA.aobjA FF os 296) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY1| exact LY2]).
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply (PGSKA.aobjA_sub FF lo hi); [exact OFR| exact LY3| exact LY4]).
  pose proof (PGSKA.src_visG L ar C HI LY HIok LB FF LK cr Aw M0 model0 os _ _ _ sp (PMSPA.pm_scr 4) HH AO O8 PSRC PNI ASTK)
    as ((O1 & _ & OBIG) & _ & _ & OCE & _ & _ & OFS1 & OFS2).
  pose proof (PGSKA.iss_visG L ar C HI LY HIok LB FF LK cr Aw M0 model0 ois str _ sp (PMSPA.pm_scr 4) HH AOI I8 IA0 ASTK)
    as ((I1 & _ & IBIG) & _ & _ & ICE & _ & _).
  cbn [PM.sr_qc PM.sr_de PM.sr_rem PM.sm_g PM.sm_eg PM.sm_st] in *.
  pose proof PSRC as (S240 & S248 & SD256 & S264 & S272 & S280 & S288 & G1 & G2 & G3 & G16 & DCH & ACH & ACC240).
  assert (QIN : In (qc, PM.CHUNK) LB) by (unfold LB, PM.src_own; cbn; left; reflexivity).
  assert (OBIN : forall B m, In (B, m) OB -> In (B, m) LB) by (intros B m Hin; unfold LB, PM.src_own; cbn; right; apply in_or_app; left; exact Hin).
  assert (SOWN : incl (PM.vs_own str) LB) by (unfold LB; intros x Hx; apply in_or_app; right; apply in_or_app; right; exact (INCS x Hx)).
  assert (STb : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LB).
  { intros c1 n1 q1 E. apply SOWN. rewrite E. cbn. left. reflexivity. }
  assert (STbX : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> In (q1, c1) LBX).
  { intros c1 n1 q1 E. apply INCS. rewrite E. cbn. left. reflexivity. }
  assert (ND : NoDup (map fst LB)) by exact (PMASK.lb_nodup L ar C HI HIok _ _ _ _ _ _ _ HH).
  destruct (WB _ QIN) as ((Q0 & QI & Q16 & _ & Q4 & QAPP) & _). cbn [fst snd] in Q0, QI, Q16, Q4, QAPP.
  unfold app_mem in QAPP, FSAPP. destruct FSAPP as (FSA0 & FSAs & FSA47). destruct QAPP as (QA0 & QAs & QA47).
  assert (DF : 0 <= p' /\ p' + k' <= 2 ^ 47 /\ L5.defined M0 p' k' /\ aacc M0 p' k' /\ app_rng ar p' k'
     /\ (forall a, p' <= a < p' + k' -> in_block LB a \/ in_fframe FF a)
     /\ (forall a, p' <= a < p' + k' -> ~ (sp - PMSPA.pm_scr 4 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
           /\ ~ (qc <= a < qc + PM.CHUNK) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1)))
     /\ (p' + k' <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p')
     /\ (PMSPA.aobjA FF p' k' \/ exists q m, In (q, m) LB /\ q <= p' /\ p' + k' <= q + m)
     /\ (p' + k' <= qc \/ qc + PM.CHUNK <= p')).
  { assert (OBJ : forall (APo : p' + k' <= os \/ os + 296 <= p') (APi : p' + k' <= ois \/ ois + 272 <= p'),
      PMSPA.aobjA FF p' k' -> L5.defined M0 p' k' -> aacc M0 p' k' ->
      0 <= p' /\ p' + k' <= 2 ^ 47 /\ L5.defined M0 p' k' /\ aacc M0 p' k' /\ app_rng ar p' k'
      /\ (forall a, p' <= a < p' + k' -> in_block LB a \/ in_fframe FF a)
      /\ (forall a, p' <= a < p' + k' -> ~ (sp - PMSPA.pm_scr 4 <= a < sp) /\ ~ (ois <= a < ois + 272) /\ ~ (os <= a < os + 296)
            /\ ~ (qc <= a < qc + PM.CHUNK) /\ (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> ~ (q1 <= a < q1 + c1)))
      /\ (p' + k' <= BIGSHADOW_LO \/ BIGSHADOW_HI <= p')
      /\ (PMSPA.aobjA FF p' k' \/ exists q m, In (q, m) LB /\ q <= p' /\ p' + k' <= q + m)
      /\ (p' + k' <= qc \/ qc + PM.CHUNK <= p')).
    { intros APo APi AOD DD AD.
      pose proof AOD as (f & Hf & X1 & X2). destruct (WF f Hf) as (Y1 & Y2 & _).
      pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ qc PM.CHUNK p' k' HH QIN AOD) as APQ.
      split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia|]. split; [exact DD|]. split; [exact AD|].
      split; [apply (L5SAR.app_rng_fs L ar C HI HIok LB FF LK cr Aw M0 _ p' k' HH); clear - X1 X2 Y1 Y2; lia|].
      split; [intros a Ha; right; apply (PMASR1.in_fframe_of_aobjA FF p' k' a AOD Ha)|].
      split; [|split; [destruct FSAs as [Z|Z]; [left|right]; clear - Z X1 X2 Y1 Y2; lia| split; [left; exact AOD| clear - APQ; lia]]].
      intros a Ha. split; [clear - Ha X2 Y2 FSCEIL SLO; lia|]. split; [clear - Ha APi; lia|]. split; [clear - Ha APo; lia|].
      split; [clear - Ha APQ; lia|].
      intros c1 n1 q1 E. destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ q1 c1 p' k' HH (STb c1 n1 q1 E) AOD) as [Z|Z]; clear - Ha Z; lia. }
    destruct DST as [(AOD & Hk8 & DD & AD & APF)|DW].
    - apply OBJ; [clear - APF LY1 LY2; lia| clear - APF LY3 LY4; lia| exact AOD| exact DD| exact AD].
    - destruct (PGSA.oo_win _ _ _ _ _ _ OK M0 (PM.SRC qc de rem) OB p' k' PA0 DW) as (W0 & WD & [(B & m & BIN & WB1 & WB2)|(W1 & W2 & WL1 & WL2 & WL3 & WL4 & WL5)] & WACC).
      + pose proof (OBIN B m BIN) as TIN.
        destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & TAPP) & _). cbn [fst snd] in T0, T4, TAPP.
        unfold app_mem in TAPP. destruct TAPP as (TA0 & TAs & TA47).
        assert (NQ : B <> qc).
        { intros E. apply (PMASK.fst_neq_appA [(qc, PM.CHUNK)] (OB ++ LBX) qc PM.CHUNK B m); [exact ND| left; reflexivity| apply in_or_app; left; exact BIN| symmetry; exact E]. }
        pose proof (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m qc PM.CHUNK HH TIN QIN NQ) as APQ.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m os 296 HH TIN AO) as APP.
        pose proof (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m ois 272 HH TIN AOI) as API.
        split; [clear - WB1 T0; lia|]. split; [clear - WB2 T4 SLO SHI SPT; lia|]. split; [exact WD|]. split; [exact WACC|].
        split; [apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M0 _ B m p' k' HH TIN); clear - WB1 WB2; lia|].
        split; [intros a Ha; left; apply (PMASR1.in_block_of LB B m a TIN); clear - Ha WB1 WB2; lia|].
        split; [|split; [destruct TAs as [Z|Z]; [left|right]; clear - Z WB1 WB2; lia|
                 split; [right; exists B, m; split; [exact TIN|]; split; [exact WB1| exact WB2]| clear - APQ WB1 WB2; lia]]].
        intros a Ha. split; [clear - Ha WB1 WB2 T4 SLO; lia|]. split; [clear - Ha WB1 WB2 API; lia|]. split; [clear - Ha WB1 WB2 APP; lia|].
        split; [clear - Ha WB1 WB2 APQ; lia|].
        intros c1 n1 q1 E.
        assert (NS : B <> q1) by (apply (PMASK.fst_neq_appA ((qc, PM.CHUNK) :: OB) LBX B m q1 c1); [exact ND| right; exact BIN| exact (STbX c1 n1 q1 E)]).
        destruct (PMASK.blk_apart L ar C HI HIok LB FF LK cr Aw M0 _ B m q1 c1 HH TIN (STb c1 n1 q1 E) NS) as [Z|Z]; clear - Ha WB1 WB2 Z; lia.
      + apply OBJ; [exact WL4| exact WL5| apply (PGSKA.aobjA_sub FF lo hi p' k' OFR WL1 WL2)| exact WD| exact WACC]. }
  destruct DF as (DP0 & DP1 & DDP & DAP & DAPP & DCL & DX & DSH & DLOC & DQA).
  assert (P37 : 0 <= p < 2 ^ 64) by (rewrite <- V37; pick_st STC; assumption).
  assert (P38 : 0 <= k < 2 ^ 64) by (rewrite <- V38; pick_st STC; assumption).
  assert (EP : p' = p).
  { rewrite R11 in A11. apply (f_equal bv_unsigned) in A11. rewrite !L5.unsigned_lit in A11 by (clear - P37 DP0 DP1 Hk; unfold PM.CHUNK in Hk; lia). lia. }
  assert (EK : k' = k).
  { rewrite R12 in A12. apply (f_equal bv_unsigned) in A12. rewrite !L5.unsigned_lit in A12 by (clear - P38 Hk; unfold PM.CHUNK in Hk; lia). lia. }
  assert (EP2 : p'' = p).
  { rewrite R11 in A11'. apply (f_equal bv_unsigned) in A11'. rewrite !L5.unsigned_lit in A11' by (clear - P37 Hp''; lia). lia. }
  assert (EK2 : k'' = k).
  { rewrite R12 in A12'. apply (f_equal bv_unsigned) in A12'. rewrite !L5.unsigned_lit in A12' by (clear - P38 Hk''; lia). lia. }
  subst p' k' p'' k''.
  assert (WAPP : PMKA.wapp (PGS.W_srcG os ois (PM.SRC qc de rem) ++ Wextra)).
  { rewrite WE. unfold PGS.W_srcG, PGS.W_srcfG. cbn [PM.sr_qc app].
    apply PMKA.wapp_cons; [cbn [fst snd]; clear - OBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; clear - IBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; clear - IBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI; lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; clear - QAs; lia|].
    apply PMKA.wapp_cons; [cbn [fst snd]; clear - DSH; lia| apply PMKA.wapp_nil]. }
  assert (AGSHP : forall Ma Mb W, L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb -> PMKA.wapp W -> PMFA.agsh Ma Mb p k).
  { intros Ma Mb W E WP. destruct DLOC as [AOD|(q & m & Hq & X1 & X2)].
    - exact (PMKA.agsh_obj L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb E WP FRB p k AOD).
    - destruct (BRB _ Hq) as (Y1 & Y2). cbn [fst snd] in Y1, Y2.
      intros x Hx. apply (PMASK.agsh_blk L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb q m E WP Hq ltac:(clear - Y1; lia) ltac:(clear - Y2; lia)). clear - Hx X1 X2; lia. }
  assert (AGSHQ : forall Ma Mb W, L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb -> PMKA.wapp W -> PMFA.agsh Ma Mb qc PM.CHUNK).
  { intros Ma Mb W E WP. apply (PMASK.agsh_blk L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb qc PM.CHUNK E WP QIN); clear - Q0 Q4 SLO SHI SPT; lia. }
  assert (CLP : forall a sp0 scr0, p <= a < p + k -> aclient L ar LB FF sp0 scr0 a) by (intros a sp0 scr0 Ha; apply PMASR1.cl_of_bf; exact (DCL a Ha)).
  assert (CLQ : forall a sp0 scr0, qc <= a < qc + PM.CHUNK -> aclient L ar LB FF sp0 scr0 a).
  { intros a sp0 scr0 Ha. apply PMASR1.cl_of_bf. left. exact (PMASR1.in_block_of LB qc PM.CHUNK a QIN Ha). }
  assert (CALLF : forall M3 model3 LK3 Ac3 len2,
      PGSRDK16.srd_body L ar HI 16 O R0 M0 model0 OB LBX FF LK Aw sp (PM.SRC qc de rem) Wextra F M3 model3 LK3 cr Ac3 ->
      0 <= len1 -> 1 <= len2 -> len1 + len2 <= k -> len2 <= PM.CHUNK ->
      aacc M3 (p + len1) len2 /\ L5.defined M3 (p + len1) len2 /\ aacc M3 qc len2 /\ L5.defined M3 qc len2).
  { intros M3 model3 LK3 Ac3 len2 BI3 H1 H2 H3 H4. unfold PGSRDK16.srd_body in BI3. pose proof BI3 as (_ & _ & _ & _ & _ & _ & EK3 & DK3 & _).
    split; [intros a Ha; apply (PMFA.accA_agree M0 M3 p k (AGSHP M0 M3 _ EK3 WAPP) DAP a); clear - Ha H1 H2 H3; lia|].
    split.
    { apply (L5.defined_sub M3 p k); [| clear - H1; lia| clear - H1 H3; lia].
      apply (PMASK.defined_dk L ar LB FF sp (PMSPA.pm_scr 4) M0 M3 p k DK3); [intros i Hi; apply CLP; exact Hi| exact DP0| clear - DP1; lia| exact DDP]. }
    split; [intros a Ha; apply (PMFA.accA_agree M0 M3 qc PM.CHUNK (AGSHQ M0 M3 _ EK3 WAPP) ACH a); clear - Ha H4; lia|].
    apply (L5.defined_sub M3 qc PM.CHUNK); [| clear; lia| clear - H4; lia].
    apply (PMASK.defined_dk L ar LB FF sp (PMSPA.pm_scr 4) M0 M3 qc PM.CHUNK DK3); [intros i Hi; apply CLQ; exact Hi| clear - Q0; lia| clear - Q4 SLO SHI SPT; lia| exact DCH]. }
  assert (ISSC : forall (M' : mem) (W : list L5.range), L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) W M M' -> PMKA.wapp W ->
      (forall a, ois <= a < ois + 272 -> L5.outside W a) ->
      (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> forall a, q1 <= a < q1 + c1 -> L5.outside W a) ->
      forall sm0, PM.iss_at RSEGS PMA.AD PMSPA.accA M ois str sm0 -> PM.iss_at RSEGS PMA.AD PMSPA.accA M' ois str sm0).
  { intros M' W E WP OI OS sm0 IS.
    apply (PMFA.iss_at_agreeA RSEGS PMA.AD M M' ois str sm0); [clear - I1; lia| clear - I1; lia| split| | exact IS].
    - intros i Hi. apply E. split; [clear - Hi I1; lia|].
      split; [apply PMASR1.cl_of_bf; right; exact (PMASR1.in_fframe_of_aobjA FF ois 272 i AOI Hi)| exact (OI i Hi)].
    - exact (PMKA.agsh_obj L ar LB FF sp (PMSPA.pm_scr 4) W M M' E WP FRB ois 272 AOI).
    - intros c1 n1 q1 Es. pose proof (STb c1 n1 q1 Es) as TIN. destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & _) & _).
      cbn [fst snd] in T0, T4. split.
      + intros i Hi. apply E. split; [clear - Hi T0 T4 SLO SHI SPT; lia|].
        split; [apply PMASR1.cl_of_bf; left; exact (PMASR1.in_block_of LB q1 c1 i TIN Hi)| exact (OS c1 n1 q1 Es i Hi)].
      + apply (PMASK.agsh_blk L ar LB FF sp (PMSPA.pm_scr 4) W M M' q1 c1 E WP TIN); clear - T0 T4 SLO SHI SPT; lia. }
  assert (WOS : PMKA.wapp [(PGS.ow_os O + 256, 40)]).
  { apply PMKA.wapp_cons; [cbn [fst snd]; clear - OBIG; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; lia| apply PMKA.wapp_nil]. }
  assert (OI_os : forall a, ois <= a < ois + 272 -> L5.outside [(PGS.ow_os O + 256, 40)] a).
  { intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. clear - Ha LYD. lia. }
  assert (OS_os : forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> forall a, q1 <= a < q1 + c1 -> L5.outside [(PGS.ow_os O + 256, 40)] a).
  { intros c1 n1 q1 Es a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd].
    destruct (PMASK.blk_obj_apart L ar C HI HIok LB FF LK cr Aw M0 _ q1 c1 os 296 HH (STb c1 n1 q1 Es) AO) as [Z|Z]; clear - Ha Z; lia. }
  specialize (EXIT O R0 M0 model0 K OB LBX FF LK Aw cr sp r str Wextra qc de rem g eg sst p k CTX R11 R12 F fl LK2 M2 model2 FR).
  pose proof (PGSA.oo_src _ _ _ _ _ _ OK M _ OB PA) as (PSRC1 & _ & _).
  pose proof PSRC1 as (_ & _ & _ & F264 & F272 & _). cbn [PM.sr_qc] in F264.
  set (MV := mrestrict (ahid Ac model) M) in *.
  pick_st STC.
  match goal with
  | H2 : _ <= V 2%nat <= _, H36 : _ <= V 36%nat <= _, H50 : _ <= V 50%nat <= _, H51 : 4096 <= V 51%nat <= _ |- _ =>
      pose proof (conj H2 (conj H36 (conj H50 H51))) as KB
  end.
  assert (V39r : 0 <= len1) by (rewrite <- V39; match goal with H : 0 <= V 39%nat < _ |- _ => exact (proj1 H) end).
  assert (CN : 1 <= c) by (clear - HC Hc; lia).
  assert (SCRv : 16384 <= PMSPA.pm_scr 4) by (vm_compute; intro X; discriminate X).
  assert (CHv : PM.CHUNK = 16384) by reflexivity.
  set (len2 := Z.min c (k - len1)).
  assert (L2R : 1 <= len2 <= k - len1 /\ len2 <= c /\ (len2 = k - len1 \/ len2 = c)).
  { unfold len2. clear - CN Hl1k. destruct (Z.min_spec c (k - len1)) as [[X1 X2]|[X1 X2]]; rewrite X2; lia. }
  assert (DFX : 4096 <= p /\ p + k <= ahl_ceil ar /\ (forall a, p <= a < p + k -> ~ (65536 <= a < 6905856))).
  { destruct DLOC as [(f & Hf & X1 & X2)|(q & m & Hq & X1 & X2)].
    - destruct (WF f Hf) as (Y1 & Y2 & _).
      split; [clear - X1 Y1 FSI; lia|]. split; [clear - X2 Y2 FSCEIL SLO SHI SPT; lia|].
      intros a Ha. clear - Ha X1 Y1 FSI. lia.
    - destruct (WB _ Hq) as ((T0 & TI & _ & _ & T4 & _) & _). cbn [fst snd] in T0, TI, T4.
      rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in TI.
      split; [clear - X1 T0; lia|]. split; [clear - X2 T4; lia|].
      intros a Ha. clear - Ha X1 X2 TI T0. lia. }
  destruct DFX as (P4096 & PCEIL & IMX).
  assert (NDP : forall a, p + len1 <= a < p + len1 + len2 -> p <= a < p + k) by (intros a Ha; clear - Ha L2R V39r; lia).
  assert (ISSG : forall (Ma Mb : mem) (W : list L5.range), L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb -> PMKA.wapp W ->
      (forall a, ois <= a < ois + 272 -> L5.outside W a) ->
      (forall c1 n1 q1, str = PM.VLong c1 n1 q1 -> forall a, q1 <= a < q1 + c1 -> L5.outside W a) ->
      forall sm0, PM.iss_at RSEGS PMA.AD PMSPA.accA Ma ois str sm0 -> PM.iss_at RSEGS PMA.AD PMSPA.accA Mb ois str sm0).
  { intros Ma Mb W E WP OI OS sm0 IS.
    apply (PMFA.iss_at_agreeA RSEGS PMA.AD Ma Mb ois str sm0); [clear - I1; lia| clear - I1; lia| split| | exact IS].
    - intros i Hi. apply E. split; [clear - Hi I1; lia|].
      split; [apply PMASR1.cl_of_bf; right; exact (PMASR1.in_fframe_of_aobjA FF ois 272 i AOI Hi)| exact (OI i Hi)].
    - exact (PMKA.agsh_obj L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb E WP FRB ois 272 AOI).
    - intros c1 n1 q1 Es. pose proof (STb c1 n1 q1 Es) as TIN. destruct (WB _ TIN) as ((T0 & _ & _ & _ & T4 & _) & _).
      cbn [fst snd] in T0, T4. split.
      + intros i Hi. apply E. split; [clear - Hi T0 T4 SLO SHI SPT; lia|].
        split; [apply PMASR1.cl_of_bf; left; exact (PMASR1.in_block_of LB q1 c1 i TIN Hi)| exact (OS c1 n1 q1 Es i Hi)].
      + apply (PMASK.agsh_blk L ar LB FF sp (PMSPA.pm_scr 4) W Ma Mb q1 c1 E WP TIN); clear - T0 T4 SLO SHI SPT; lia. }
  pose proof FR as G'. unfold PGSRDK16.srd_frame in G'.
  destruct G' as [_ GSPT GSLO GSHI GSPC GOCR GOWN GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 1) with 128 in GFR, GNCF.
  set (VC := fun j : nat => match j with 33%nat => c | _ => V j end).
  assert (HEADC : exists fx3 R3 M3v,
      msteps RSEGS (st fx R 0xaef9c MV) (st fx3 R3 0x77c94 M3v) /\ mem_grows MV M3v
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (4 * V 50%nat + 2147450888 <= i < 4 * V 50%nat + 2147450888 + 1) -> ~ (32 * V 50%nat + 64 <= i < 32 * V 50%nat + 64 + 8)
            -> ~ (V 36%nat + 288 <= i < V 36%nat + 288 + 8) -> M3v (Z_to_bv 64 i) = MV (Z_to_bv 64 i))
      /\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27]%nat -> getr R3 (reg x) = getr R (reg x))
      /\ getr R3 (reg 1) = Z_to_bv 64 716828 /\ getr R3 (reg 10) = Z_to_bv 64 (V 37%nat + V 39%nat)
      /\ getr R3 (reg 11) = Z_to_bv 64 (V 34%nat) /\ getr R3 (reg 12) = Z_to_bv 64 len2 /\ getr R3 (reg 24) = Z_to_bv 64 len2
      /\ L5.u64_at RSEGS M3v (V 36%nat + 288) c /\ L5.u8_at RSEGS M3v (4 * V 50%nat + 2147450888) 248
      /\ L5.u64_at RSEGS M3v (32 * V 50%nat + 64) (V 38%nat - V 39%nat)
      /\ L5.defined M3v (32 * V 50%nat) 64 /\ L5.defined M3v (32 * V 50%nat + 72) 56 /\ L5.defined M3v (32 * V 50%nat + 40) 24).
  { destruct (Z_le_gt_dec c (k - len1)) as [CLE|CGT].
    - assert (E2 : len2 = c) by (unfold len2; clear - CLE; lia).
      pose proof (PMASRP.asrCge16_conc fx R MV VC) as P3. unfold VC in P3. cbn beta iota in P3.
      feed P3 ltac:(idtac; dsp ltac:(idtac; clear - CN Hc CLE Hl1k Hl1k' V37 V38 V39 V39r P4096 PCEIL SPT KB; lia) ltac:(idtac; fail)).
      destruct P3 as (fx3 & R3 & M3v & MG3 & _ & AG3 & MS3 & KS3 & T1 & T10 & T11 & T12 & T21 & T24 & U288 & U8 & U64 & UD1 & UD2 & UD3 & _).
      exists fx3, R3, M3v. split; [exact MS3|]. split; [exact MG3|]. split; [exact AG3|].
      split.
      { intros x Hx. cbn in Hx. repeat destruct Hx as [<-|Hx]; try destruct Hx;
          first [solve [apply KS3; inl] | (rewrite T21; symmetry; sfind)]. }
      rewrite E2. split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|]. split; [exact T24|].
      split; [exact U288|]. split; [exact U8|]. split; [exact U64|]. split; [exact UD1|]. split; [exact UD2| exact UD3].
    - assert (E2 : len2 = k - len1) by (unfold len2; clear - CGT; lia).
      pose proof (PMASRP.asrClt16_conc fx R MV VC) as P3. unfold VC in P3. cbn beta iota in P3.
      feed P3 ltac:(idtac; dsp ltac:(idtac; clear - CN Hc CGT Hl1k Hl1k' V37 V38 V39 V39r P4096 PCEIL SPT KB; lia) ltac:(idtac; fail)).
      destruct P3 as (fx3 & R3 & M3v & MG3 & _ & AG3 & MS3 & KS3 & T1 & T10 & T11 & T12 & T24 & U288 & U8 & U64 & UD1 & UD2 & UD3 & _).
      exists fx3, R3, M3v. split; [exact MS3|]. split; [exact MG3|]. split; [exact AG3|].
      split.
      { intros x Hx. cbn in Hx. repeat destruct Hx as [<-|Hx]; try destruct Hx; apply KS3; inl. }
      rewrite E2, <- V38, <- V39. split; [exact T1|]. split; [exact T10|]. split; [exact T11|]. split; [exact T12|]. split; [exact T24|].
      split; [exact U288|]. split; [exact U8|]. split; [exact U64|]. split; [exact UD1|]. split; [exact UD2| exact UD3]. }
  destruct HEADC as (fx3 & R3 & M3v & MS3 & MG3 & AG3 & KS3 & T1 & T10 & T11 & T12 & T24 & U288 & U8 & U64 & UD1 & UD2 & UD3).
  apply (PGSRDC16.srd_piece L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2
           M model LKc Ac fx fx3 R R3 _ _ M3v
           (fun a => (4 * V 50%nat + 2147450888 <= a < 4 * V 50%nat + 2147450888 + 1) \/ (32 * V 50%nat + 64 <= a < 32 * V 50%nat + 64 + 8)
                     \/ (V 36%nat + 288 <= a < V 36%nat + 288 + 8)) CTX FR BI MS3 MG3).
  { intros a Ha NW. cbn beta in NW.
    apply AG3; [exact Ha| intros Y; apply NW; left; exact Y| intros Y; apply NW; right; left; exact Y| intros Y; apply NW; right; right; exact Y]. }
  { intros a Wa. cbn beta in Wa. destruct Wa as [Y|[Y|Y]].
    - right; left. clear - Y V50. unfold SB. lia.
    - left. clear - Y V50. lia.
    - right; right; left. clear - Y V36. lia. }
  intros M1 model1 BI1 HID1 MRT1 MGM1 FR1 VIS1 EK1.
  pose proof (CALLF M1 model1 LKc Ac len2 BI1 V39r ltac:(clear - L2R; lia) ltac:(clear - L2R; lia) ltac:(clear - L2R Hl1k' CHv; lia))
    as (CF1 & CF2 & CF3 & CF4).
  apply (PGSRDC16.srd_call L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2
           M1 model1 LKc Ac fx3 R3 716828 (p + len1) qc len2 CTX FR BI1).
  - exact T1.
  - split; [clear; lia| reflexivity].
  - rewrite KS3 by inl. match goal with H : getr R (reg 2) = _ |- _ => rewrite H end. rewrite V2. f_equal. clear; lia.
  - rewrite KS3 by inl. rewrite X4. exact Rtp.
  - rewrite T10, V37, V39. reflexivity.
  - rewrite T11, V34. reflexivity.
  - exact T12.
  - clear - L2R Hl1k' CHv. lia.
  - exact CF1.
  - exact CF2.
  - clear - DP0 V39r. lia.
  - clear - DP1 L2R V39r. lia.
  - unfold app_rng in DAPP |- *. clear - DAPP L2R V39r. lia.
  - intros i Hi. apply DCL. clear - Hi L2R V39r. lia.
  - intros i Hi. destruct (DX (p + len1 + i) ltac:(clear - Hi L2R V39r; lia)) as (DX1 & _). split; [exact DX1|].
    intros OUT. apply (OUT (p, k)); [rewrite WE; apply in_or_app; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Hi L2R V39r; lia].
  - exact CF3.
  - exact CF4.
  - clear - Q0. lia.
  - clear - Q4 SPT L2R Hl1k' CHv. lia.
  - apply (L5SAR.app_rng_block L ar C HI HIok LB FF LK cr Aw M0 _ qc PM.CHUNK qc len2 HH QIN); clear - L2R Hl1k' CHv; lia.
  - intros i Hi. apply (PMASR1.in_block_of LB qc PM.CHUNK (qc + i) QIN). clear - Hi L2R Hl1k' CHv. lia.
  - clear - DQA L2R V39r Hl1k' CHv. lia.
  - intros fx4 R4 M4 model4 RP4 DEF4 BI4 HP4.
    assert (RP4' : forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg x) = getr R3 (reg x)).
    { intros x Hx. apply RP4. cbn in Hx. repeat destruct Hx as [<-|Hx]; try destruct Hx; vm_compute; repeat (first [left; reflexivity| right]). }
    assert (NDST : forall i, (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
                      \/ (os <= i < os + 296) \/ ((os + 8) / 8 + SB <= i < (os + 8) / 8 + SB + 36) -> ~ (p + len1 <= i < p + len1 + len2)).
    { intros i RGi Y. pose proof (NDP i Y) as Yp. destruct (DX i Yp) as (D1 & _ & D3 & _).
      destruct RGi as [Z|[Z|[Z|[Z|Z]]]].
      - apply D1. clear - Z SCRv. lia.
      - apply (GNCF i); [left; clear - Z; lia| apply PMASR1.cl_of_bf; exact (DCL i Yp)].
      - clear - Z Yp DSH GFR. unfold BIGSHADOW_LO, BIGSHADOW_HI, SB in *. lia.
      - apply D3. exact Z.
      - clear - Z Yp DSH KB V36. unfold BIGSHADOW_LO, BIGSHADOW_HI, SB in *. lia. }
    assert (AG43 : forall i, 0 <= i < 2 ^ 64 ->
        (V 2%nat - 160 <= i < V 2%nat + 16) \/ (32 * V 50%nat <= i < 32 * V 50%nat + 120 /\ ~ (32 * V 50%nat + 24 <= i < 32 * V 50%nat + 32))
        \/ (4 * V 50%nat + SB <= i < 4 * V 50%nat + SB + 16) \/ (V 36%nat <= i < V 36%nat + 296)
        \/ ((V 36%nat + 8) / 8 + SB <= i < (V 36%nat + 8) / 8 + SB + 36) ->
        mrestrict (ahid Ac model4) M4 (Z_to_bv 64 i) = M3v (Z_to_bv 64 i)).
    { intros i Hi RGi.
      assert (RG' : (sp - 160 - 16 <= i < sp) \/ (F <= i < F + 120 /\ ~ (F + 24 <= i < F + 32)) \/ (F / 8 + SB <= i < F / 8 + SB + 16)
                    \/ (os <= i < os + 296) \/ ((os + 8) / 8 + SB <= i < (os + 8) / 8 + SB + 36)) by (clear - RGi V2 V50 V36; lia).
      rewrite (PGSRDC16.srd_call_ag L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2
                 M1 model1 LKc Ac M4 model4 LKc Ac (p + len1) len2 i CTX FR BI1 BI4 HP4 Hi RG' (NDST i RG')).
      rewrite HID1, MRT1. reflexivity. }
    unfold SB in AG43.
    pose proof BI4 as BI4'. unfold PGSRDK16.srd_body, PMAUK.binv in BI4'. destruct BI4' as (HH4 & _ & _ & _ & _ & _ & EK4 & _).
    assert (OUTIMG : forall a, 65536 <= a < 6905856 -> L5.outside (PGS.W_srcG os ois (PM.SRC qc de rem) ++ Wextra) a).
    { intros a Ha r0 Hr. rewrite WE in Hr. unfold PGS.W_srcG, PGS.W_srcfG in Hr. cbn [PM.sr_qc app] in Hr. unfold L5.in_rng.
      pose proof QI as QI'. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in QI'.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd].
      - clear - Ha O1. lia.
      - clear - Ha I1. lia.
      - clear - Ha I1. lia.
      - clear - Ha QI' Q0 CHv. lia.
      - intros Y. exact (IMX a Y Ha). }
    pose proof (PMASK.base_keep L ar C LY LB FF sp (PMSPA.pm_scr 4) _ M0 M4 EK4 OUTIMG BASE0) as BASE4.
    pose proof (PMASK.mach_vis L ar C HI LY HIok _ _ _ _ _ M4 model4 HH4 BASE4) as (IM40 & IM41 & IM42).
    pose proof (PMAUK.vis_facts L ar C HI LYa HIok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FR _ _ _ _ _ _ _ BI4)
      as (_ & _ & (VF1 & VF2 & _ & VF4 & VF5) & _).
    change (ff_bytes 1) with 128 in VF1, VF2, VF4.
    set (M4v := mrestrict (ahid Ac model4) M4) in *.
    assert (DF128 : L5.defined M4v (32 * V 50%nat) 128) by (rewrite V50; exact VF1).
    assert (WF128 : L5.writable RSEGS M4v (32 * V 50%nat) 128) by (rewrite V50; exact VF2).
    assert (U120 : L5.u64_at RSEGS M4v (32 * V 50%nat + 120) (V 51%nat)).
    { rewrite V50, V51. replace (F + 120) with (F + 128 - 8) by (clear; lia). exact VF4. }
    assert (WFL : L5.writable RSEGS M4v (V 51%nat) 1) by (rewrite V51; exact VF5).
    set (VD := fun j : nat => match j with 33%nat => c | 35%nat => qc | 40%nat => len2
       | 61%nat => bv_unsigned (getr R4 (reg 1)) | 62%nat => bv_unsigned (getr R4 (reg 5)) | 63%nat => bv_unsigned (getr R4 (reg 6))
       | 64%nat => bv_unsigned (getr R4 (reg 7)) | 65%nat => bv_unsigned (getr R4 (reg 12)) | 66%nat => bv_unsigned (getr R4 (reg 13))
       | 67%nat => bv_unsigned (getr R4 (reg 14)) | 68%nat => bv_unsigned (getr R4 (reg 15)) | 69%nat => bv_unsigned (getr R4 (reg 16))
       | 70%nat => bv_unsigned (getr R4 (reg 17)) | 71%nat => bv_unsigned (getr R4 (reg 28)) | 72%nat => bv_unsigned (getr R4 (reg 29))
       | 73%nat => bv_unsigned (getr R4 (reg 30)) | 74%nat => bv_unsigned (getr R4 (reg 31)) | _ => V j end).
    pose proof (PMASRP.asrD16_conc fx4 R4 M4v VD) as P5. unfold VD in P5. cbn beta iota in P5.
    feed P5 ltac:(idtac; dsp ltac:(idtac; clear - CN Hc Hl1k Hl1k' V37 V38 V39 V39r V34 P4096 PCEIL Q0 Q4 CHv SPT L2R KB; lia)
                      ltac:(idtac; first [ (rewrite RP4' by inl; first [sfind | (rewrite KS3 by inl; sfind)])
                                  | (eapply L5.defined_sub; [exact DF128| clear; lia| clear; lia])
                                  | carry_with M3v AG43 KB ltac:(idtac; fin3 MG3 MV AG3 KB) ])).
    destruct P5 as (fx5 & R5 & M5v & MG5 & _ & AG5 & MS5 & KS5 & D1 & D2 & D8 & D9 & D10 & D12 & D18 & D19 & D20 & D21 & D22 & D23 & D24 & D288 & D280).
    apply (PGSRDC16.srd_piece L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2
             M4 model4 LKc Ac fx4 fx5 R4 R5 _ _ M5v
             (fun a => (V 36%nat + 256 <= a < V 36%nat + 256 + 8) \/ (V 36%nat + 280 <= a < V 36%nat + 280 + 16)) CTX FR BI4 MS5 MG5).
    { intros a Ha NW. cbn beta in NW. apply AG5; [exact Ha| intros Y; apply NW; left; exact Y| intros Y; apply NW; right; exact Y]. }
    { intros a Wa. cbn beta in Wa. right; right; left. clear - Wa V36. lia. }
    intros M5 model5 BI5 HID5 MRT5 MGM5 FR5 VIS5 EK5.
    pose proof BI5 as BI5'. unfold PGSRDK16.srd_body, PMAUK.binv in BI5'. destruct BI5' as (HH5 & _ & _ & _ & _ & _ & EK5' & _).
    pose proof (PMASK.base_keep L ar C LY LB FF sp (PMSPA.pm_scr 4) _ M0 M5 EK5' OUTIMG BASE0) as BASE5.
    pose proof (PMASK.mach_vis L ar C HI LY HIok _ _ _ _ _ M5 model5 HH5 BASE5) as (IM50 & IM51 & IM52).
    rewrite HID5, MRT5 in IM50, IM51, IM52.
    assert (SV5 : forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> vx V R5 i = bv_unsigned (getr R0 (reg i))).
    { intros i Hi. rewrite <- (VSV i Hi). cbn in Hi. repeat destruct Hi as [<-|Hi]; first [reflexivity | destruct Hi]. }
    assert (X3' : getr R5 (reg 3) = getr R0 (reg 3)) by (rewrite KS5 by inl; rewrite RP4' by inl; rewrite KS3 by inl; exact X3).
    assert (X4' : getr R5 (reg 4) = getr R0 (reg 4)) by (rewrite KS5 by inl; rewrite RP4' by inl; rewrite KS3 by inl; exact X4).
    assert (STR5 : PGSRDK16.srd_stR (vx V R5) R5 M5v).
    { unfold PGSRDK16.srd_stR, vx. cbn beta iota.
      sweep ltac:(idtac; dsp ltac:(idtac; clear - KB; lia)
                      ltac:(idtac; first [ (rewrite KS5 by inl; rewrite RP4' by inl; rewrite KS3 by inl; sfind)
                                  | (eapply L5.writable_grows; [exact MG5| fin4 DF128 M3v AG43 KB MG3 MV AG3])
                                  | (eapply L5.defined_grows; [exact MG5| fin4 DF128 M3v AG43 KB MG3 MV AG3])
                                  | carry_with M4v AG5 KB ltac:(idtac; fin4 DF128 M3v AG43 KB MG3 MV AG3) ])). }
    assert (STR5' : PGSRDK16.srd_stR (vx V R5) R5 (mrestrict (ahid Ac model5) M5)) by (rewrite HID5, MRT5; exact STR5).
    assert (V76 : vx V R5 76%nat = len1 + len2).
    { unfold vx. cbn beta iota. rewrite D22, V39. apply L5.unsigned_lit.
      match goal with H : 0 <= V 38%nat < _ |- _ => clear - H V38 V39r L2R; lia end. }
    assert (KO4 : forall a, os <= a < os + 296 -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
    { intros a Ha. destruct HP4 as (E & _). apply E. split; [clear - Ha KB V36; lia|]. split.
      - apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. right. apply (PMASR1.in_fframe_of_aobjA FF os 296 a AO). clear - Ha; lia.
      - intros r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. intros Y. apply (NDST a); [right; right; right; left; exact Ha| exact Y]. }
    assert (U264 : L5.u64_at RSEGS M5 (os + 264) qc).
    { apply (L5C.u64_at_agree RSEGS M M5); [| clear - O1; lia| clear - O1; lia| exact F264].
      intros i Hi. rewrite FR5; [| clear - Hi KB V36; lia| cbn beta; clear - Hi V36; lia].
      rewrite KO4 by (clear - Hi; lia). apply FR1; [clear - Hi KB V36; lia|].
      cbn beta. intros [Y|[Y|Y]]; sdx Hi Y V36 V50 KB. }
    assert (U272 : L5.u64_at RSEGS M5 (os + 272) PM.CHUNK).
    { apply (L5C.u64_at_agree RSEGS M M5); [| clear - O1; lia| clear - O1; lia| exact F272].
      intros i Hi. rewrite FR5; [| clear - Hi KB V36; lia| cbn beta; clear - Hi V36; lia].
      rewrite KO4 by (clear - Hi; lia). apply FR1; [clear - Hi KB V36; lia|].
      cbn beta. intros [Y|[Y|Y]]; sdx Hi Y V36 V50 KB. }
    assert (VO5 : forall i, V 36%nat + 280 <= i < V 36%nat + 296 -> M5 (Z_to_bv 64 i) = M5v (Z_to_bv 64 i)).
    { intros i Hi. apply VIS5.
      apply (PGSRDC16.srd_vis L ar C HI LY HIok O R0 M0 model0 K OB LBX FF LK Aw cr sp r (PM.SRC qc de rem) str (PM.STRM g eg sst) Wextra F fl LK2 M2 model2
               M4 model4 LKc Ac i CTX FR BI4).
      right; right; right; left. clear - Hi V36. lia. }
    assert (U280 : L5.u64_at RSEGS M5 (os + 280) (qc + len2)).
    { rewrite <- V34. replace (os + 280) with (V 36%nat + 280) by (clear - V36; lia).
      apply (L5C.u64_at_agree RSEGS M5v M5); [| sd KB| sd KB| exact D280]. intros i Hi. apply VO5. clear - Hi. lia. }
    assert (W288 : L5.u64_at RSEGS M5 (os + 288) (c - len2)).
    { replace (os + 288) with (V 36%nat + 288) by (clear - V36; lia).
      apply (L5C.u64_at_agree RSEGS M5v M5); [| sd KB| sd KB| exact D288]. intros i Hi. apply VO5. clear - Hi. lia. }
    assert (ISS1 : PM.iss_at RSEGS PMA.AD PMSPA.accA M1 ois str (PM.STRM g2 eg st2)) by exact (ISSG M M1 _ EK1 WOS OI_os OS_os _ IA).
    assert (WSP : PMKA.wapp [(p + len1, len2)]).
    { apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI in *; clear - DSH L2R V39r; lia| apply PMKA.wapp_nil]. }
    assert (EK14 : L5SAR.ek L ar LB FF sp (PMSPA.pm_scr 4) [(p + len1, len2)] M1 M4).
    { apply (L5SAR.ek_callee L ar LB [] FF [(F, 1, sp - 160 - 16 + 32)] sp (PMSPA.pm_scr 4) (sp - 160 - 16) 2560 _ [(p + len1, len2)] M1 M4 HP4);
        [clear - SCRv; lia| clear; lia| intros a _ Oq; exact Oq]. }
    assert (ISS4 : PM.iss_at RSEGS PMA.AD PMSPA.accA M4 ois str (PM.STRM g2 eg st2)).
    { apply (ISSG M1 M4 _ EK14 WSP); [| | exact ISS1].
      - intros a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. intros Y. destruct (DX a (NDP a Y)) as (_ & X2 & _). apply X2. exact Ha.
      - intros c1 n1 q1 Es a Ha r0 [<-|[]]. unfold L5.in_rng. cbn [fst snd]. intros Y.
        destruct (DX a (NDP a Y)) as (_ & _ & _ & _ & X5). apply (X5 c1 n1 q1 Es). exact Ha. }
    assert (ISS5 : PM.iss_at RSEGS PMA.AD PMSPA.accA M5 ois str (PM.STRM g2 eg st2)) by exact (ISSG M4 M5 _ EK5 WOS OI_os OS_os _ ISS4).
    assert (DEF5 : L5.defined M5 p (len1 + len2)).
    { apply (L5.defined_grows M4 M5); [exact MGM5|].
      intros i Hi. destruct (Z_lt_le_dec i len1) as [LT|LE].
      - destruct HP4 as (_ & _ & HPD). apply HPD.
        + clear - Hi DP0 DP1 L2R V39r. lia.
        + apply L5SAR.aclient_cons. apply PMASR1.cl_of_bf. apply DCL. clear - Hi LT L2R V39r. lia.
        + exact (L5.defined_grows M M1 p len1 MGM1 DP i ltac:(clear - Hi LT; lia)).
      - replace (p + i) with (p + len1 + (i - len1)) by (clear; lia). exact (DEF4 (i - len1) ltac:(clear - Hi LE L2R; lia)). }
    assert (A1 : qc <= qc + len2) by (clear - L2R; lia).
    assert (A2 : 0 <= c - len2) by (clear - L2R; lia).
    assert (A3 : qc + len2 + (c - len2) <= qc + PM.CHUNK) by (clear - Hc CHv; lia).
    assert (A4 : g <= g2 <= eg) by (clear - Hg2 Hg2e CN; lia).
    assert (A5 : 0 <= len1 + len2 <= k) by (clear - V39r L2R; lia).
    assert (A6 : rem + (eg - g) - (c - len2 + (eg - g2)) = len1 + len2) by (clear - Hl1 Hg2; lia).
    assert (A7 : 1 <= rem -> 1 <= len1 + len2) by (intros _; clear - L2R V39r; lia).
    assert (A8 : len1 + len2 = 0 -> c - len2 = 0 /\ st2 = 2) by (intros E; exfalso; clear - E L2R V39r; lia).
    exact (EXIT fx5 R5 M5 model5 LKc Ac (vx V R5) BI5 V2 V36 V37 V38 V50 V51 SV5 X3' X4' (qc + len2) (c - len2) g2 st2 (len1 + len2)
             STR5' V76 U264 U272 U280 W288 A1 A2 A3 ISS5 A4 Hst2 A5 A6 A7 A8 DEF5).
Qed.

Lemma srd_fill_ret_ok : PGSRDK16.srd_exit_T L ar HI 16 -> PGSRDK16.srd_fill_ret_T L ar HI 16.
Proof using All.
  intros E. exact (PGSRDC16.srd_fill_ret_case_split L ar HI (PGSRDC16.srd_c0 L ar C HI LY HIok IL ICok ILY E) (srd_cnz E)).
Qed.

End WithHeap.
End PGSRDCD16.
