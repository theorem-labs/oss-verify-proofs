(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import base list.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PgV8 PnLayout PnModel PnModelFacts PnStatics PnKeep PnRun. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnRunS_u PnTopS_u PnSHarnessStmts_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNHK.
Import PMS. Import PNH.
(* [comment removed for export] *)
Ltac cred_norm :=
  unfold PMSP.credit_le, PMSP.credit_keep, PNH.P0, PNH.rest1, PNH.rest2, PNH.rest3, PNR.pot_callB, PNR.pot_bparser, PNR.pot_bstack, PGV8.pot_v8, PM.CHUNK, PNM.BSZ,
         PM.credit_add, PM.cost1, PM.pot_text, PNTS.TOPK, PNTS.TOPB, PMSP.cr0, PNR.bparser_init in *;
  cbn [fst snd PNM.b_sk PNM.b_tb PNM.b_tg PNM.b_nb PNM.b_ng PNM.b_bb PNM.b_bg PM.vs_cap PGV8.v8_cap] in *;
  change (2 ^ 12) with 4096 in *; change (2 ^ (0 + 1)) with 2 in *; change (2 ^ 28) with 268435456 in *;
  change (2 ^ 29) with 536870912 in *; change (2 ^ 30) with 1073741824 in *; change (2 ^ 26) with 67108864 in *.
Abbreviation vstr_at := (PM.vstr_at RSEGS PNH.T3).
Abbreviation iss_at := (PM.iss_at RSEGS AD PNH.T3).
Abbreviation bparser_at := (PNM.bparser_at RSEGS AD PNH.T3 PNH.T4 (pa_vp_parser AD)).
Abbreviation v8_at := (PGV8.v8_at RSEGS PNH.T3 PNH.T4).

(* [comment removed for export] *)
Lemma inW_WF_hi a : PMK.inW WF a -> 0x10000 <= a < 0xea5b0.
Proof.
  intros (r & Hin & Hr). unfold WF, PNST.pn_foot, pm_foot in Hin. cbn in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd] in Hr; lia.
Qed.
(* [comment removed for export] *)
Lemma base_not_WF a : (65536 <= a < 0xb83f0 \/ 0xea230 <= a < 0xea238 \/ 0xea253 <= a < 0xea254 \/ 0xea328 <= a < 0xea32c) -> ~ PMK.inW WF a.
Proof.
  intros H (r & Hin & Hr). unfold WF, PNST.pn_foot, pm_foot in Hin. cbn in Hin. unfold L5.in_rng in Hr.
  destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma outside_of_not_inW W a : ~ PMK.inW W a -> L5.outside W a.
Proof. intros N r Hin Hr. apply N. exists r. split; assumption. Qed.

(* [comment removed for export] *)
Lemma lb_remove_mid p c (pre post : list (Z * Z)) :
  NoDup (map fst (pre ++ [(p, c)] ++ post)) -> lb_remove p (pre ++ [(p, c)] ++ post) = pre ++ post.
Proof.
  induction pre as [|a pre IH]; cbn [app map lb_remove fst]; intros ND.
  - rewrite Z.eqb_refl. reflexivity.
  - inversion ND as [|x0 l0 NI0 ND0]. subst.
    destruct (Z.eqb (fst a) p) eqn:EQ.
    + apply Z.eqb_eq in EQ. exfalso. apply NI0. rewrite EQ, map_app. apply elem_of_app. right. cbn [map fst]. constructor.
    + f_equal. apply IH. exact ND0.
Qed.
Lemma lb_remove_mid2 p c (A B post : list (Z * Z)) :
  NoDup (map fst (A ++ B ++ [(p, c)] ++ post)) -> lb_remove p (A ++ B ++ [(p, c)] ++ post) = A ++ B ++ post.
Proof. intros ND. rewrite (app_assoc A B) in ND |- *. rewrite (lb_remove_mid p c (A ++ B) post ND). rewrite <- app_assoc. reflexivity. Qed.
Lemma lb_remove_mid3 p c (A B C post : list (Z * Z)) :
  NoDup (map fst (A ++ B ++ C ++ [(p, c)] ++ post)) -> lb_remove p (A ++ B ++ C ++ [(p, c)] ++ post) = A ++ B ++ C ++ post.
Proof.
  intros ND. rewrite (app_assoc B C) in ND |- *. rewrite (lb_remove_mid2 p c A (B ++ C) post ND). rewrite <- (app_assoc B C). reflexivity.
Qed.

Section Kit.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Variable R0 : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variables (sp ra : Z).
Variable LB0 : list (Z * Z).

Abbreviation hcore := (PNH.hcore L R0 M0 model0 sp ra LB0).
Abbreviation fb := (PNH.fb sp).
Let KL := PMKS.klayout_S L LY.
Let SF := PMKS.sfoot_S L LY.
Lemma SFN : forall iv a, In iv (PNL.pn_d128_foot AN) -> fst iv <= a < snd iv -> PMKP.cstatic L a.
Proof. intros iv a Hin H. apply (PMKS.cstatic_S L LY). cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H; lia. Qed.

(* [comment removed for export] *)
Lemma hcore_facts R M model : hcore R M model ->
  0 <= sp < 2 ^ 64 /\ getr R (reg 2) = Z_to_bv 64 (sp - 784) /\ 140735332483856 <= sp <= 140737488355328 /\ sp mod 16 = 0
  /\ L5.writable RSEGS M (sp - 784) 784 /\ L5C.stk (hl_sptop L) M (sp - 784) (65536 - 784).
Proof.
  unfold PNH.hcore. intros (Hsp & _ & _ & _ & STK & DFR & SPT & _). pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold fb, PNH.fb, FRAME, SCR in *.
  split; [lia|]. split; [exact Hsp|]. split; [lia|]. split. { replace sp with (sp - 784 + 49 * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  split; [|exact STK]. apply (L5C.writable_of_defined RSEGS M (sp - 784) 784 DFR); lia.
Qed.

(* [comment removed for export] *)
Lemma hcore_piece R M model R1 M1 (P : Z -> Prop) :
  hcore R M model -> mem_grows M M1 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) -> (forall a, P a -> fb <= a < fb + 768) ->
  getr R1 (reg 2) = Z_to_bv 64 fb -> (forall k, In k CSK -> getr R1 (reg k) = getr R (reg k)) ->
  hcore R1 M1 model.
Proof.
  unfold PNH.hcore. intros (Hsp & Hcs & Sra & Ss0 & STK & DFR & SPT & EK & LBhi & BASE & MB & MOK) MG FR FP Hsp1 Hcs1.
  pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold fb, PNH.fb, FRAME, SCR in *.
  assert (AG : forall a, sp - 784 + 768 <= a -> a < 2 ^ 64 -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a H1 H2. apply FR; [lia|]. intros Pa. apply FP in Pa. lia. }
  assert (EK1 : PMK.ek L LB0 sp 65536 [] M M1).
  { apply (PMK.ek_piece_in' RSEGS L KL LB0 sp 65536 [] M M1 P FR); [lia| lia| exact LBhi|]. intros a Pa. left. apply FP in Pa. lia. }
  split; [exact Hsp1|]. split; [intros k Hk; rewrite (Hcs1 k Hk); apply Hcs; exact Hk|].
  split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply AG; lia| lia| lia| exact Sra]|].
  split; [apply (L5C.u64_at_agree RSEGS M M1); [intros i Hi; apply AG; lia| lia| lia| exact Ss0]|].
  split; [apply (L5C.stk_grows _ M M1 _ _ MG STK)|].
  split; [intros i Hi; apply MG; apply DFR; exact Hi|]. split; [exact SPT|].
  split; [|split; [exact LBhi|]].
  - intros a Ha. rewrite (EK1 a); [apply EK; exact Ha|]. destruct Ha as (H1 & H2 & H3 & _). split; [exact H1|]. split; [exact H2|]. split; [exact H3| apply L5C.outside_nil].
  - split; [|split; assumption].
    apply (PMKP.base_ok_keep RSEGS AD L KL SF LB0 sp 65536 [] M M1 EK1); first [exact BASE | intros a _; apply L5C.outside_nil].
Qed.

(* [comment removed for export] *)
Lemma hcore_call R M model R' M' model' LBc scr' W' :
  hcore R M model -> regs_preserved R R' -> L5C.hpres L LBc fb scr' W' M M' -> incl LB0 LBc -> 0 <= scr' <= SCR - FRAME ->
  (forall a, PMK.inW W' a -> (fb <= a < fb + 768) \/ PMK.inW WF a) ->
  model_but_vm model model' -> hcore R' M' model'.
Proof.
  unfold PNH.hcore. intros (Hsp & Hcs & Sra & Ss0 & STK & DFR & SPT & EK & LBhi & BASE & MB & MOK) RP HP INC Hscr FP MB'.
  pose proof STK as (A16 & SLO & SHI & STOP & DEF). unfold fb, PNH.fb, FRAME, SCR in *.
  assert (OUT : forall a, sp - 784 + 768 <= a -> L5.outside W' a).
  { intros a Ha. apply outside_of_not_inW. intros I. destruct (FP a I) as [F|F]; [lia| apply inW_WF_hi in F; lia]. }
  assert (EKc : PMK.ek L LBc (sp - 784) scr' W' M M') by (apply (PMK.ek_of_hpres L); exact HP).
  assert (STKc : L5C.stk (hl_sptop L) M (sp - 784) scr') by (apply (PMK.stk_call L M (sp - 784) (65536 - 784) (sp - 784) scr' STK); [lia|lia|lia|exact A16]).
  split; [rewrite (PMK.cs_of_preserved R R' 2 RP ltac:(PMK.inl)); exact Hsp|].
  split. { intros k Hk. rewrite <- (Hcs k Hk). apply (PMK.cs_of_preserved R R' k RP). unfold CSK in Hk. cbn in Hk.
           repeat (destruct Hk as [<-|Hk]; [PMK.inl|]). destruct Hk. }
  split. { apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact Sra].
           apply (PMKP.ek_agree_stack RSEGS L KL LBc (sp - 784) scr' W' M M' _ _ EKc STKc); [lia|lia|lia|].
           intros i Hi. apply OUT. lia. }
  split. { apply (L5C.u64_at_agree RSEGS M M'); [|lia|lia|exact Ss0].
           apply (PMKP.ek_agree_stack RSEGS L KL LBc (sp - 784) scr' W' M M' _ _ EKc STKc); [lia|lia|lia|].
           intros i Hi. apply OUT. lia. }
  split. { apply (PMK.stk_after RSEGS L KL LBc M M' (sp - 784) (65536 - 784) (sp - 784) scr' W' STK HP); lia. }
  split. { intros i Hi. pose proof (PMK.kl_img RSEGS L KL) as KI. pose proof (PMK.kl_errno RSEGS L KL) as KE.
           apply (L5C.hpres_cdef L LBc (sp - 784) scr' W' M M' (sp - 784 + i) HP); [lia| right; left; lia| unfold in_errno; lia| apply DFR; exact Hi]. }
  split; [exact SPT|].
  split; [|split; [exact LBhi|]].
  - apply (PMK.ek_trans L LB0 sp 65536 WF M0 M M' EK).
    apply (PMK.ek_callee_in' RSEGS L KL LB0 LBc sp 65536 (sp - 784) scr' WF W' M M' HP INC); [lia|lia|lia|lia|exact LBhi|].
    intros a I. destruct (FP a I) as [F|F]; [left; lia| right; exact F].
  - split; [|split; [exact (L5C.model_but_vm_trans _ _ _ MB MB')|]].
    + apply (PMKP.base_ok_keep RSEGS AD L KL SF LBc (sp - 784) scr' W' M M' EKc); first [exact BASE |
        intros a Ha; apply outside_of_not_inW; intros I; (destruct (FP a I) as [F|F]; [cbn in Ha; lia| apply (base_not_WF a); [cbn in Ha; lia| exact F]])].
    + destruct MOK as (H1 & H2 & H3). unfold PMSP.model_ok.
      rewrite (L5C.halted_but_vm _ _ MB'), (L5C.lazy_but_vm _ _ MB'), (L5C.materialized_but_vm _ _ MB'). auto.
Qed.

(* [comment removed for export] *)
Definition loc_dom (a : Z) : Prop := 0xc87f2 <= a < 0xc8f30 \/ 0xc9658 <= a < 0xc96b0.
Definition sys_dom (a : Z) : Prop := 0xc87f0 <= a < 0xc87f2.
(* [comment removed for export] *)
Definition err_dom (a : Z) : Prop := 0xc8580 <= a < 0xc85c8 \/ 0xea008 <= a < 0xea228.

Section Along.
Variables (LBc : list (Z * Z)) (sp' scr' : Z) (W : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LBc sp' scr' W M M'.

Lemma loc_keep b : (forall a, PMK.inW W a -> ~ loc_dom a) -> PMST.loc_ok RSEGS AD M b -> PMST.loc_ok RSEGS AD M' b.
Proof.
  intros N. apply (PMKP.loc_ok_keep RSEGS AD L KL SF LBc sp' scr' W M M' E). intros iv a Hin Hr. apply outside_of_not_inW. intros I. apply (N a I).
  unfold loc_dom. cbn in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; lia.
Qed.
Lemma sys_keep b : (forall a, PMK.inW W a -> ~ sys_dom a) -> PMST.sys_ok RSEGS AD M b -> PMST.sys_ok RSEGS AD M' b.
Proof.
  intros N. apply (PMKP.sys_ok_keep RSEGS AD L KL SF LBc sp' scr' W M M' E). intros a Ha. apply outside_of_not_inW. intros I. apply (N a I). unfold sys_dom. cbn in Ha. lia.
Qed.
Lemma err_keep ax : (forall a, PMK.inW W a -> ~ err_dom a) -> PNST.berr_ok RSEGS AD AN M ax -> PNST.berr_ok RSEGS AD AN M' ax.
Proof.
  intros N. apply (PNKP.berr_ok_keep RSEGS AD AN L KL SF PNRS.addrs_wf_B SFN LBc sp' scr' W M M' ax E).
  intros a D. apply outside_of_not_inW. intros I. apply (N a I). unfold err_dom.
  destruct D as [H|[H|(iv & Hin & H)]]; [cbn in H; lia| cbn in H; lia|].
  cbn in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H; lia.
Qed.
(* [comment removed for export] *)
Lemma hstat_keep bl bs be : (forall a, PMK.inW W a -> 0xea5b0 <= a \/ a < 0x10000) -> PNH.hstat M bl bs be -> PNH.hstat M' bl bs be.
Proof.
  intros N (H1 & H2 & H3). split; [|split].
  - apply loc_keep; [|exact H1]. intros a I D. destruct (N a I); unfold loc_dom in D; lia.
  - apply sys_keep; [|exact H2]. intros a I D. destruct (N a I); unfold sys_dom in D; lia.
  - apply err_keep; [|exact H3]. intros a I D. destruct (N a I); unfold err_dom in D; lia.
Qed.
End Along.

(* [comment removed for export] *)
Definition brange (LBc : list (Z * Z)) : Prop :=
  forall B m, In (B, m) LBc -> 4096 <= B /\ (B + m <= 0x10000 \/ 0xeb000 <= B) /\ B + m <= hl_ceil L.
Lemma brange_of_heap (HIok : heap_iface_ok L SCFG HI) LBf LBc cr M VM : hi_heap HI LBf cr M VM -> incl LBc LBf -> brange LBc.
Proof.
  intros HH INC B m Hin. pose proof (proj1 (hio_wf L SCFG HI HIok LBf cr M VM HH) (B, m) (INC _ Hin)) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _).
  cbn [fst snd] in *. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in Q1. split; [exact Q0|]. split; [exact Q1| exact Q4].
Qed.

(* [comment removed for export] *)
Definition hobjs (M : word -> option byte) (s s2 : PM.vstr) (sm : PM.strm) (p : PNM.bpst) : Prop :=
  vstr_at M (fb + 744) s /\ iss_at M (fb + 472) s2 sm /\ bparser_at M (fb + 40) (fb + 472) p /\ L5.u64_at RSEGS M (fb + 464) (pa_vp_visitor AD).

(* [comment removed for export] *)
Section Objs.
Variables (LBc : list (Z * Z)) (scr' : Z) (W' : list L5.range) (M M' : word -> option byte).
Hypothesis E : PMK.ek L LBc fb scr' W' M M'.
Hypothesis STKc : L5C.stk (hl_sptop L) M fb scr'.
Hypothesis SCR0 : 0 <= scr'.
Hypothesis BR : brange LBc.
Hypothesis WSTD : forall a, PMK.inW W' a -> fb <= a \/ 0x10000 <= a < 0xeb000.

Lemma ag_frame a n : fb <= a -> a + n <= fb + 784 -> (forall i, a <= i < a + n -> ~ PMK.inW W' i) -> L5C.agree_on M M' a n.
Proof.
  intros H1 H2 N. pose proof STKc as (_ & _ & SHI & STOP & _). unfold fb, PNH.fb, FRAME in *.
  apply (PMKP.ek_agree_stack RSEGS L KL LBc (sp - 784) scr' W' M M' a n E STKc SCR0); [lia|lia|]. intros i Hi. apply outside_of_not_inW. apply N. exact Hi.
Qed.
Lemma ag_block B m : In (B, m) LBc -> L5C.agree_on M M' B m.
Proof.
  intros Hin. destruct (BR B m Hin) as (Q0 & Q1 & Q4).
  pose proof STKc as (_ & SLO & SHI & STOP & _).
  apply (PMKP.ek_agree L LBc fb scr' W' M M' B m E). intros i Hi.
  apply (PMKP.kept_block RSEGS L KL LBc fb scr' W' B m i Hin Hi); [lia| exact Q4| rewrite (ly_img_lo L LY), (ly_img_hi L LY); exact Q1| lia|].
  apply outside_of_not_inW. intros I. destruct (WSTD i I); unfold fb, PNH.fb, FRAME in *; lia.
Qed.

Lemma u64_keep a v : fb <= a -> a + 8 <= fb + 784 -> (forall i, a <= i < a + 8 -> ~ PMK.inW W' i) -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof.
  intros H1 H2 N. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PNH.fb, FRAME in *.
  apply (L5C.u64_at_agree RSEGS M M'); [apply ag_frame; unfold fb, PNH.fb, FRAME; [lia|lia|exact N]|lia|lia].
Qed.
Lemma u32_keep a v : fb <= a -> a + 4 <= fb + 784 -> (forall i, a <= i < a + 4 -> ~ PMK.inW W' i) -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros H1 H2 N. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PNH.fb, FRAME in *.
  apply (PMF.u32_at_agree RSEGS M M'); [apply ag_frame; unfold fb, PNH.fb, FRAME; [lia|lia|exact N]|lia|lia].
Qed.
Lemma vstr_keep o s : fb <= o -> o + 24 <= fb + 784 -> (forall i, o <= i < o + 24 -> ~ PMK.inW W' i) -> incl (PM.vs_own s) LBc ->
  vstr_at M o s -> vstr_at M' o s.
Proof.
  intros H1 H2 N INC VS. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PNH.fb, FRAME in *.
  apply (PMF.vstr_at_agree RSEGS M M' o s); [lia|lia| apply ag_frame; unfold fb, PNH.fb, FRAME; [lia|lia|exact N]| |exact VS].
  intros c n p ->. apply ag_block. apply INC. cbn. auto.
Qed.
Lemma iss_keep ois str sm : fb <= ois -> ois + 272 <= fb + 784 -> (forall i, ois <= i < ois + 272 -> ~ PMK.inW W' i) -> incl (PM.vs_own str) LBc ->
  iss_at M ois str sm -> iss_at M' ois str sm.
Proof.
  intros H1 H2 N INC VS. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PNH.fb, FRAME in *.
  apply (PMF.iss_at_agree RSEGS AD M M' ois str sm); [lia|lia| apply ag_frame; unfold fb, PNH.fb, FRAME; [lia|lia|exact N]| |exact VS].
  intros c n p ->. apply ag_block. apply INC. cbn. auto.
Qed.
Lemma v8_keep o x : fb <= o -> o + 24 <= fb + 784 -> (forall i, o <= i < o + 24 -> ~ PMK.inW W' i) -> incl (PGV8.v8_own x) LBc ->
  v8_at M o x -> v8_at M' o x.
Proof.
  intros H1 H2 N INC VS. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PNH.fb, FRAME in *.
  apply (PNMF.v8_at_keep RSEGS M M' o x); [lia|lia| apply ag_frame; unfold fb, PNH.fb, FRAME; [lia|lia|exact N]| |exact VS].
  intros b n c ->. apply PNMF.dkr_agree. apply ag_block. apply INC. cbn. auto.
Qed.
Lemma parser_keep op ois s : fb <= op -> op + 416 <= fb + 784 -> (forall i, op <= i < op + 416 -> ~ PMK.inW W' i) -> incl (PNM.bparser_own s) LBc ->
  bparser_at M op ois s -> bparser_at M' op ois s.
Proof.
  intros H1 H2 N INC PA. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PNH.fb, FRAME in *.
  apply (PNMF.bparser_at_agree RSEGS AD (pa_vp_parser AD) M M' op ois s); unfold PNM.PSIZE; [lia|lia| apply ag_frame; unfold fb, PNH.fb, FRAME; [lia|lia|exact N]| |exact PA].
  intros B m Hin. apply INC in Hin. destruct (BR _ _ Hin) as (Q0 & Q1 & Q4). split; [lia|]. split; [lia|]. apply ag_block. exact Hin.
Qed.
Lemma nullis_keep o : fb <= o -> o + 232 <= fb + 784 -> (forall i, o <= i < o + 232 -> ~ PMK.inW W' i) ->
  PM.nullis_at RSEGS AD PNH.T3 M o -> PM.nullis_at RSEGS AD PNH.T3 M' o.
Proof.
  intros H1 H2 N. pose proof STKc as (_ & SLO & SHI & STOP & _). unfold fb, PNH.fb, FRAME in *.
  apply (PMF.nullis_at_agree RSEGS AD M M' o); [lia|lia| apply ag_frame; unfold fb, PNH.fb, FRAME; [lia|lia|exact N]].
Qed.
Lemma src_keep os isp sbp src : fb <= os -> os + 296 <= fb + 784 -> (forall i, os + 240 <= i < os + 296 -> ~ PMK.inW W' i) -> In (PM.sr_qc src, PM.CHUNK) LBc ->
  PM.src_fields_at RSEGS PNH.T3 M os isp sbp src -> PM.src_fields_at RSEGS PNH.T3 M' os isp sbp src.
Proof.
  intros H1 H2 N Bq. pose proof STKc as (_ & SLO & SHI & STOP & _). destruct (BR _ _ Bq) as (Q0 & Q1 & Q4). unfold fb, PNH.fb, FRAME in *.
  apply (PMF.src_fields_at_agree RSEGS M M' os isp sbp src); [lia|lia|lia|lia| apply ag_frame; unfold fb, PNH.fb, FRAME; [lia|lia|intros i Hi; apply N; lia]| apply ag_block; exact Bq].
Qed.
Lemma hobjs_call s s2 sm p : (forall a, PMK.inW W' a -> ~ (fb + 40 <= a < fb + 456) /\ ~ (fb + 464 <= a < fb + 768)) ->
  incl (PNM.bparser_own p ++ PM.vs_own s2 ++ PM.vs_own s) LBc -> hobjs M s s2 sm p -> hobjs M' s s2 sm p.
Proof.
  intros N INC (VS & IA & PA & VV). unfold fb, PNH.fb, FRAME in *.
  split. { apply vstr_keep; unfold fb, PNH.fb, FRAME; [lia|lia| intros i Hi I; destruct (N i I); lia| |exact VS].
           intros x Hx. apply INC. apply in_or_app. right. apply in_or_app. right. exact Hx. }
  split. { apply iss_keep; unfold fb, PNH.fb, FRAME; [lia|lia| intros i Hi I; destruct (N i I); lia| |exact IA].
           intros x Hx. apply INC. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  split. { apply parser_keep; unfold fb, PNH.fb, FRAME; [lia|lia| intros i Hi I; destruct (N i I); lia| |exact PA].
           intros x Hx. apply INC. apply in_or_app. left. exact Hx. }
  apply u64_keep; unfold fb, PNH.fb, FRAME; [lia|lia| intros i Hi I; destruct (N i I); lia| exact VV].
Qed.
End Objs.

(* [comment removed for export] *)
Section Piece.
Variables (LBc : list (Z * Z)) (M M1 : word -> option byte) (P : Z -> Prop) (scrx : Z).
Hypothesis FRZ : forall a, 0 <= a < 2 ^ 64 -> ~ P a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis PF : forall a, P a -> fb <= a < fb + 784.
Hypothesis STKx : L5C.stk (hl_sptop L) M fb scrx.
Hypothesis SCRx : 0 <= scrx.
Hypothesis BR : brange LBc.

Lemma agp a n : 0 <= a -> a + n <= 2 ^ 64 -> (forall i, a <= i < a + n -> ~ P i) -> L5C.agree_on M M1 a n.
Proof. intros H1 H2 N i Hi. apply FRZ; [lia| apply N; exact Hi]. Qed.
Lemma agp_block B m : In (B, m) LBc -> L5C.agree_on M M1 B m.
Proof.
  intros Hin. destruct (BR B m Hin) as (Q0 & Q1 & Q4).
  pose proof STKx as (_ & SLO & SHI & STOP & _). apply agp; [lia|lia|]. intros i Hi Pi. apply PF in Pi. lia.
Qed.
Lemma u64_keep_p a v : 0 <= a -> a + 8 <= 2 ^ 64 -> (forall i, a <= i < a + 8 -> ~ P i) -> L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M1 a v.
Proof. intros H1 H2 N. apply (L5C.u64_at_agree RSEGS M M1); [apply agp; assumption|lia|lia]. Qed.
Lemma u32_keep_p a v : 0 <= a -> a + 4 <= 2 ^ 64 -> (forall i, a <= i < a + 4 -> ~ P i) -> L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M1 a v.
Proof. intros H1 H2 N. apply (PMF.u32_at_agree RSEGS M M1); [apply agp; assumption|lia|lia]. Qed.
Lemma vstr_keep_p o s : 0 <= o -> o + 24 <= 2 ^ 64 -> (forall i, o <= i < o + 24 -> ~ P i) -> incl (PM.vs_own s) LBc -> vstr_at M o s -> vstr_at M1 o s.
Proof.
  intros H1 H2 N INC. apply (PMF.vstr_at_agree RSEGS M M1 o s); [lia|lia|apply agp; assumption|].
  intros c n p ->. apply agp_block. apply INC. cbn. auto.
Qed.
Lemma iss_keep_p ois str sm : 0 <= ois -> ois + 272 <= 2 ^ 64 -> (forall i, ois <= i < ois + 272 -> ~ P i) -> incl (PM.vs_own str) LBc ->
  iss_at M ois str sm -> iss_at M1 ois str sm.
Proof.
  intros H1 H2 N INC. apply (PMF.iss_at_agree RSEGS AD M M1 ois str sm); [lia|lia|apply agp; assumption|].
  intros c n p ->. apply agp_block. apply INC. cbn. auto.
Qed.
Lemma v8_keep_p o x : 0 <= o -> o + 24 <= 2 ^ 64 -> (forall i, o <= i < o + 24 -> ~ P i) -> incl (PGV8.v8_own x) LBc -> v8_at M o x -> v8_at M1 o x.
Proof.
  intros H1 H2 N INC. apply (PNMF.v8_at_keep RSEGS M M1 o x); [lia|lia|apply agp; assumption|].
  intros b n c ->. apply PNMF.dkr_agree. apply agp_block. apply INC. cbn. auto.
Qed.
Lemma parser_keep_p op ois s : 0 <= op -> op + 416 <= 2 ^ 64 -> (forall i, op <= i < op + 416 -> ~ P i) -> incl (PNM.bparser_own s) LBc ->
  bparser_at M op ois s -> bparser_at M1 op ois s.
Proof.
  intros H1 H2 N INC PA. pose proof STKx as (_ & SLO & SHI & STOP & _).
  apply (PNMF.bparser_at_agree RSEGS AD (pa_vp_parser AD) M M1 op ois s); unfold PNM.PSIZE; [lia|lia|apply agp; assumption| |exact PA].
  intros B m Hin. apply INC in Hin. destruct (BR _ _ Hin) as (Q0 & Q1 & Q4). split; [lia|]. split; [lia|]. apply agp_block. exact Hin.
Qed.
Lemma nullis_keep_p o : 0 <= o -> o + 232 <= 2 ^ 64 -> (forall i, o <= i < o + 232 -> ~ P i) ->
  PM.nullis_at RSEGS AD PNH.T3 M o -> PM.nullis_at RSEGS AD PNH.T3 M1 o.
Proof. intros H1 H2 N. apply (PMF.nullis_at_agree RSEGS AD M M1 o); [lia|lia|apply agp; assumption]. Qed.
Lemma src_keep_p os isp sbp src : 0 <= os -> os + 296 <= 2 ^ 64 -> (forall i, os + 240 <= i < os + 296 -> ~ P i) -> In (PM.sr_qc src, PM.CHUNK) LBc ->
  PM.src_fields_at RSEGS PNH.T3 M os isp sbp src -> PM.src_fields_at RSEGS PNH.T3 M1 os isp sbp src.
Proof.
  intros H1 H2 N Bq. destruct (BR _ _ Bq) as (Q0 & Q1 & Q4). pose proof STKx as (_ & SLO & SHI & STOP & _).
  apply (PMF.src_fields_at_agree RSEGS M M1 os isp sbp src); [lia|lia|lia|lia| apply agp; [lia|lia|intros i Hi; apply N; lia]| apply agp_block; exact Bq].
Qed.
Lemma hobjs_piece s s2 sm p : (forall a, P a -> (fb + 16 <= a < fb + 40) \/ (fb + 456 <= a < fb + 464)) ->
  incl (PNM.bparser_own p ++ PM.vs_own s2 ++ PM.vs_own s) LBc -> hobjs M s s2 sm p -> hobjs M1 s s2 sm p.
Proof.
  intros N INC (VS & IA & PA & VV). pose proof STKx as (_ & SLO & SHI & STOP & _). unfold hobjs. unfold fb, PNH.fb, FRAME in *.
  split. { apply vstr_keep_p; [lia|lia| intros i Hi Pi; destruct (N i Pi); lia| |exact VS].
           intros x Hx. apply INC. apply in_or_app. right. apply in_or_app. right. exact Hx. }
  split. { apply iss_keep_p; [lia|lia| intros i Hi Pi; destruct (N i Pi); lia| |exact IA].
           intros x Hx. apply INC. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  split. { apply parser_keep_p; [lia|lia| intros i Hi Pi; destruct (N i Pi); lia| |exact PA].
           intros x Hx. apply INC. apply in_or_app. left. exact Hx. }
  apply u64_keep_p; [lia|lia| intros i Hi Pi; destruct (N i Pi); lia| exact VV].
Qed.
(* [comment removed for export] *)
Lemma hstat_piece bl bs be : L5C.stk (hl_sptop L) M fb (SCR - FRAME) -> (forall b, In b LBc -> fst b + snd b <= hl_ceil L) ->
  PNH.hstat M bl bs be -> PNH.hstat M1 bl bs be.
Proof.
  intros (_ & SLO & SHI & STOP & _) LBhi. unfold fb, PNH.fb, FRAME, SCR in *.
  assert (EK1 : PMK.ek L LBc sp 65536 [] M M1).
  { apply (PMK.ek_piece_in' RSEGS L KL LBc sp 65536 [] M M1 P FRZ); [lia|lia|exact LBhi|]. intros a Pa. left. apply PF in Pa. unfold fb, PNH.fb, FRAME in Pa. lia. }
  apply (hstat_keep LBc sp 65536 [] M M1 EK1). intros a (r & [] & _).
Qed.
End Piece.

End Kit.
End PNHK.
