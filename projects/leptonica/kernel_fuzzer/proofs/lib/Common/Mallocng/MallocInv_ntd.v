(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_dll MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh
  MallocInv_ops MallocInv_live MallocInv_getmeta MallocInv_free MallocInv_tryavail MallocInv_ameta_iface
  MallocInv_ntfree MallocInv_ntpieces MallocInv_ntpost MallocInv_ntq MallocInv_act MallocInv_ntac MallocInv_ntok.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
Record deqrel (A A1 : astate) (ma : Z) (mt : meta_rec) : Prop := {
  dq_live : a_live A1 = a_live A;
  dq_areas : a_areas A1 = a_areas A;
  dq_pages : a_pages A1 = a_pages A;
  dq_mblocks : a_mblocks A1 = a_mblocks A;
  dq_xmaps : a_xmaps A1 = a_xmaps A;
  dq_fl : a_freelist A1 = a_freelist A;
  dq_ctx : forall k, (forall c, k <> KActive c) -> a_ctx A1 k = a_ctx A k;
  dq_act : forall c, ~ (0 <= c < 48) -> a_active A1 c = a_active A c;
  dq_ma : exists mt1, a_meta A1 ma = Some mt1 /\ mt_role mt1 = mt_role mt /\ mt_w32 mt1 = mt_w32 mt /\ mt_mem mt1 = mt_mem mt /\
            mt_avail mt1 = mt_avail mt /\ mt_freed mt1 = mt_freed mt;
  dq_unlinked : forall c, ~ In ma (a_active A1 c);
  dq_grp : forall x mtx aibx slx, a_meta A1 x = Some mtx -> mt_role mtx = RGroup aibx slx ->
     exists mt0, a_meta A x = Some mt0 /\ mt_role mt0 = RGroup aibx slx /\ mt_w32 mt0 = mt_w32 mtx /\ mt_mem mt0 = mt_mem mtx;
  dq_dom : forall x, dom A1 x <-> dom A x
}.

(* [comment removed for export] *)
Lemma deqrel_refl : forall A ma mt, a_meta A ma = Some mt -> (forall c, ~ In ma (a_active A c)) -> deqrel A A ma mt.
Proof.
  intros A ma mt Hma Hn. constructor; try reflexivity; try tauto.
  - exists mt. auto 10.
  - intros x mtx aibx slx Hx Hr. exists mtx. auto.
Qed.

Lemma deqrel_act : forall A A1 A2 ma mt sc, deqrel A A1 ma mt -> actrel A1 A2 sc -> ma <> 0 -> deqrel A A2 ma mt.
Proof.
  intros A A1 A2 ma mt sc [L1 Ar1 P1 B1 X1 F1 C1 Q1 M1 U1 G1 D1] R2 Hma0.
  destruct R2 as [L2 Ar2 P2 B2 X2 F2 Ac2 C2 O2 H2 K2 D2].
  constructor.
  - rewrite L2. exact L1.
  - rewrite Ar2. exact Ar1.
  - rewrite P2. exact P1.
  - rewrite B2. exact B1.
  - rewrite X2. exact X1.
  - rewrite F2. exact F1.
  - intros k Hk. rewrite C2. apply C1. exact Hk.
  - intros c Hc. rewrite Ac2. apply Q1. exact Hc.
  - destruct M1 as (mt1 & Hm1 & R & W & M & Av & Fr).
    assert (Hne : ma <> hd 0 (a_active A1 sc)).
    { intros E. destruct (a_active A1 sc) as [|x r] eqn:El; [cbn in E; exact (Hma0 E)|].
      apply (U1 sc). rewrite El, E. left. reflexivity. }
    exists mt1. rewrite (O2 ma Hne). auto 10.
  - intros c. rewrite Ac2. apply U1.
  - intros x mtx aibx slx Hx Hr. destruct (K2 x mtx Hx) as (mt1 & Hx1 & R1 & W1 & Mm1).
    rewrite Hr in R1. destruct (G1 x mt1 aibx slx Hx1 (eq_sym R1)) as (mt0 & Hx0 & R0 & W0 & M0).
    exists mt0. rewrite W0, M0. auto.
  - intros x. rewrite (D2 x). apply D1.
Qed.

Section Deq.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Variables (l1 l2 : list Z).
  Let sc := mt_sc mt.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active A sc = l1 ++ ma :: l2.

  Let l := l1 ++ ma :: l2.
  Let n := length l.
  Let i0 := length l1.
  Let xn := nth (S i0 mod n) l 0.
  Let xp := nth ((i0 + n - 1) mod n)%nat l 0.
  Let hd0 := hd 0 l.
  Let Ad := deqA A sc ma l1 l2.
  (* [comment removed for export] *)
  Let Wz2 := FCT (ma + 8) 8 0.
  Let Wz1 := FCT ma 8 0.
  Let dws : list fct :=
    if list_eq_dec Z.eq_dec (l1 ++ l2) []
    then [Wz2; Wz1; FCT (caddr (KActive sc)) 8 0]
    else if list_eq_dec Z.eq_dec l1 []
         then [Wz2; Wz1; FCT (caddr (KActive sc)) 8 xn; FCT xn 8 xp; FCT (xp + 8) 8 xn]
         else [Wz2; Wz1; FCT xn 8 xp; FCT (xp + 8) 8 xn].

  Lemma DW : WF A. Proof. exact (is_wf _ _ _ _ _ _ (ii_is HII)). Qed.
  Lemma DR : Rep A (ms_mem s). Proof. exact (is_rep _ _ _ _ _ _ (ii_is HII)). Qed.
  Lemma DWIN : WIN s. Proof. exact (is_win _ _ _ _ _ _ (ii_is HII)). Qed.

  Lemma Dlinks : mt_next mt = xn /\ mt_prev mt = xp.
  Proof.
    destruct (g_links A DW sc ma l1 l2 Hsc Hact) as (mtg & aibg & slg & Hmg & _ & _ & Hn & Hp).
    rewrite Hma in Hmg. injection Hmg as <-. split; [exact Hn | exact Hp].
  Qed.

  Lemma Dhd0 : hd0 = match l1 with [] => ma | a :: _ => a end.
  Proof. unfold hd0, l. destruct l1; reflexivity. Qed.

  Lemma Dma_facts : 0x1000 <= ma /\ ma + 40 <= alloc_ceiling /\ ma mod 8 = 0 /\ ma <> 0.
  Proof. pose proof (meta_facts A ma mt DW Hma) as (M1 & M2 & _ & M4 & _). repeat split; try llia. Qed.

  Lemma Dmulti : l1 ++ l2 <> [] ->
    exists mtn mtp, a_meta A xn = Some mtn /\ a_meta A xp = Some mtp /\ In xn (l1 ++ l2) /\ In xp (l1 ++ l2) /\
      xn <> ma /\ xp <> ma /\ (2 <= n)%nat /\
      (l1 = [] -> hd 0 (l1 ++ l2) = xn /\ mt_avail mtn = 0).
  Proof.
    intros Hne. destruct (multi_links A DW sc ma l1 l2 Hsc Hact Hne) as (Hin_n & Hin_p & Hnm & Hpm & Hn2).
    fold l n i0 xn xp in Hin_n, Hin_p, Hnm, Hpm, Hn2.
    assert (Hin_n' : In xn l) by (unfold l; apply in_app_iff in Hin_n; apply in_app_iff; destruct Hin_n; [left | right; right]; assumption).
    assert (Hin_p' : In xp l) by (unfold l; apply in_app_iff in Hin_p; apply in_app_iff; destruct Hin_p; [left | right; right]; assumption).
    destruct (wf_act_mem A DW sc xn ltac:(rewrite Hact; exact Hin_n')) as (mtn & aibn & sln & Hmn & _).
    destruct (wf_act_mem A DW sc xp ltac:(rewrite Hact; exact Hin_p')) as (mtp & aibp & slp & Hmp & _).
    exists mtn, mtp. split; [exact Hmn|]. split; [exact Hmp|]. split; [exact Hin_n|]. split; [exact Hin_p|].
    split; [exact Hnm|]. split; [exact Hpm|]. split; [exact Hn2|].
    intros El. split.
    { rewrite (hd_sub A sc ma l1 l2 Hsc Hact Hne).
      assert (HM : forall l0 : list Z, l0 = [] -> match l0 with [] => xn | a :: _ => a end = xn) by (intros l0 ->; reflexivity).
      exact (HM l1 El). }
    apply (wf_act_nonhead A DW sc xn mtn); [rewrite Hact; exact Hin_n' | | exact Hmn].
    rewrite Hact, El. cbn. intros E. exact (Hnm E).
  Qed.

  (* [comment removed for export] *)
  Let RL := MallocInv_wf3.relink (deqP ma l1 l2) (deqN ma l1 l2).

  Lemma rl_next_ma : forall mtx, mt_next (RL ma mtx) = 0.
  Proof. intros mtx. unfold RL, mt_next, MallocInv_wf3.relink. rewrite mt_f_MT. unfold deqN. cbv zeta. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma rl_prev_ma : forall mtx, mt_prev (RL ma mtx) = 0.
  Proof. intros mtx. unfold RL, mt_prev, MallocInv_wf3.relink. rewrite mt_f_MT. unfold deqP. cbv zeta. rewrite Z.eqb_refl. reflexivity. Qed.
  Lemma rl_next_other : forall x mtx, x <> ma -> mt_next (RL x mtx) = if x =? xp then xn else mt_next mtx.
  Proof.
    intros x mtx Hx. unfold RL, mt_next, MallocInv_wf3.relink. rewrite mt_f_MT. unfold deqN. cbv zeta. fold l n i0 xn xp.
    rewrite (proj2 (Z.eqb_neq x ma) Hx). destruct (x =? xp); reflexivity.
  Qed.
  Lemma rl_prev_other : forall x mtx, x <> ma -> mt_prev (RL x mtx) = if x =? xn then xp else mt_prev mtx.
  Proof.
    intros x mtx Hx. unfold RL, mt_prev, MallocInv_wf3.relink. rewrite mt_f_MT. unfold deqP. cbv zeta. fold l n i0 xn xp.
    rewrite (proj2 (Z.eqb_neq x ma) Hx). destruct (x =? xn); reflexivity.
  Qed.
  Lemma rl_f_other : forall x mtx fl, fl <> FPrev -> fl <> FNext -> mt_f (RL x mtx) fl = mt_f mtx fl.
  Proof. intros x mtx fl H1 H2. unfold RL, MallocInv_wf3.relink. rewrite mt_f_MT. destruct fl; try reflexivity; contradiction. Qed.
  Lemma rl_id : forall x mtx, x <> ma -> x <> xn -> x <> xp -> RL x mtx = mtx.
  Proof. intros x mtx H1 H2 H3. unfold RL. apply (relink_other ma l1 l2 x mtx H1 H2 H3). Qed.

  Lemma Ad_meta : forall x, a_meta Ad x = option_map (RL x) (a_meta A x).
  Proof. intros x. apply deqA_meta. Qed.
  Lemma Ad_meta_inv : forall x mt', a_meta Ad x = Some mt' -> exists mtx, a_meta A x = Some mtx /\ mt' = RL x mtx.
  Proof. intros x mt' Hx. rewrite Ad_meta in Hx. destruct (a_meta A x) as [mtx|]; [| discriminate Hx]. cbn in Hx. injection Hx as <-. exists mtx. auto. Qed.
  Lemma Ad_ma : a_meta Ad ma = Some (RL ma mt).
  Proof. rewrite Ad_meta, Hma. reflexivity. Qed.
  Lemma HWd : WF Ad.
  Proof. exact (WF_deqA A DW sc ma l1 l2 Hsc Hact). Qed.
  Lemma Ad_ctx_valid : forall k, cvalid k -> a_ctx Ad k = if cslot_eq_dec k (KActive sc) then hd 0 (l1 ++ l2) else a_ctx A k.
  Proof. exact (deqA_ctx_valid A DW sc ma l1 l2 Hsc). Qed.
  Lemma Ad_active_sc : a_active Ad sc = l1 ++ l2.
  Proof. unfold Ad. apply (deqA_active_sc A sc ma l1 l2). Qed.

  Lemma meta_usage_Ad : forall c x, meta_usage Ad c x = meta_usage A c x.
  Proof.
    intros c x. unfold meta_usage. rewrite Ad_meta. destruct (a_meta A x) as [mtx|]; [cbn [option_map] | reflexivity].
    change (mt_role (RL x mtx)) with (mt_role mtx). unfold RL. rewrite MallocInv_wf3.rl_sc, MallocInv_wf3.rl_cnt. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma has_Ad : forall f, has Ad f ->
    has A f \/ f = FCT (caddr (KActive sc)) 8 (hd 0 (l1 ++ l2)) \/
    exists x mtx fl, a_meta A x = Some mtx /\ (fl = FNext \/ fl = FPrev) /\ (x = ma \/ x = xn \/ x = xp) /\
      f = FCT (x + moff fl) (mlen fl) (mt_f (RL x mtx) fl).
  Proof.
    intros f Hf. pose proof DW as HW.
    destruct (MallocInv_wf3.relists_has_inv A (deqP ma l1 l2) (deqN ma l1 l2) (deq_act A sc l1 l2) (a_freelist A) None I f Hf) as [(k & Hk & ->) | Hrest].
    - change (MallocInv_wf3.c' A (deq_act A sc l1 l2) (a_freelist A) k) with (a_ctx Ad k). rewrite (Ad_ctx_valid k Hk).
      destruct (cslot_eq_dec k (KActive sc)) as [-> | Hne]; [right; left; reflexivity | left; left; exists k; auto].
    - destruct Hrest as [Har | [(x & mt' & fl & Hx & ->) | Hgr]].
      + left. right; left. exact Har.
      + change (MallocInv_wf3.g' A (deqP ma l1 l2) (deqN ma l1 l2) None x) with (a_meta Ad x) in Hx. destruct (Ad_meta_inv x mt' Hx) as (mtx & Hx0 & ->).
        assert (CASE : (x = ma \/ x = xn \/ x = xp) \/ (x <> ma /\ x <> xn /\ x <> xp)).
        { destruct (Z.eq_dec x ma); [left; auto|]. destruct (Z.eq_dec x xn); [left; auto|]. destruct (Z.eq_dec x xp); [left; auto | right; auto]. }
        destruct CASE as [Hxin | (H1 & H2 & H3)].
        * destruct fl.
          1: right; right; exists x, mtx, FPrev; auto 10.
          1: right; right; exists x, mtx, FNext; auto 10.
          all: left; right; right; left; exists x, mtx; eexists; split; [exact Hx0 | rewrite rl_f_other by discriminate; reflexivity].
        * left. right; right; left. exists x, mtx, fl. rewrite (rl_id x mtx H1 H2 H3). auto.
      + left. right; right; right. exact Hgr.
  Qed.

  Lemma deqrel_Ad : deqrel A Ad ma mt.
  Proof.
    pose proof DW as HW.
    constructor; try reflexivity.
    - intros k Hk. unfold Ad, deqA, MallocInv_wf3.A', MallocInv_wf3.c'. cbn [a_ctx]. destruct k; try reflexivity.
      + symmetry. apply (wf_fl_head A HW).
      + exfalso. exact (Hk i eq_refl).
    - intros c Hc. unfold Ad. apply (deqA_active_other A sc ma l1 l2 c). intros ->. exact (Hc Hsc).
    - exists (RL ma mt). rewrite Ad_ma. split; [reflexivity|]. split; [reflexivity|].
      unfold RL. rewrite MallocInv_wf3.rl_w32, MallocInv_wf3.rl_mem, MallocInv_wf3.rl_avail, MallocInv_wf3.rl_freed. auto.
    - intros c. destruct (Z.eq_dec c sc) as [-> | Hne].
      + rewrite Ad_active_sc. exact (dq_g_notin A HW sc ma l1 l2 Hact).
      + unfold Ad. rewrite (deqA_active_other A sc ma l1 l2 c Hne). intros Hin.
        destruct (wf_act_mem A HW c ma Hin) as (mt' & aib' & sl' & Hm' & _ & Hs'). rewrite Hma in Hm'. injection Hm' as <-. apply Hne. rewrite <- Hs'. reflexivity.
    - intros x mtx aibx slx Hx Hrx. destruct (Ad_meta_inv x mtx Hx) as (mt0 & Hx0 & ->). exists mt0.
      change (mt_role (RL x mt0)) with (mt_role mt0) in Hrx. unfold RL. rewrite MallocInv_wf3.rl_w32, MallocInv_wf3.rl_mem. auto.
    - intros x. unfold Ad. apply (dom_deqA A sc ma l1 l2).
  Qed.

  Lemma AUD_Ad : AvOK Ad /\ UsOK Ad /\ deads Ad D.
  Proof.
    assert (BK : forall x mt', a_meta Ad x = Some mt' -> exists mtx, a_meta A x = Some mtx /\ mt_role mt' = mt_role mtx).
    { intros x mt' Hx. destruct (Ad_meta_inv x mt' Hx) as (mtx & Hx0 & ->). exists mtx. auto. }
    split; [| split].
    - apply (AvOK_transfer A Ad (ii_av HII)); [reflexivity | apply (Ad_ctx_valid KAmc I) |].
      intros x mt' Hx Hrl. destruct (BK x mt' Hx) as (mtx & H1 & R1). exists mtx. rewrite <- R1. auto.
    - apply (UsOK_transfer A Ad (ii_us HII)); [reflexivity | | exact meta_usage_Ad].
      intros c Hc. rewrite (Ad_ctx_valid (KUsage c) Hc). destruct (cslot_eq_dec (KUsage c) (KActive sc)) as [E | _]; [discriminate E | reflexivity].
    - apply (deads_transfer A Ad D (ii_dd HII)). intros x. split.
      + intros (mt' & Hx & Hrl). destruct (BK x mt' Hx) as (mtx & H1 & R1). exists mtx. rewrite <- R1. auto.
      + intros (mtx & Hx & Hrl). exists (RL x mtx). rewrite Ad_meta, Hx. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma dws_range : forall w, In w dws ->
    (w = FCT (caddr (KActive sc)) 8 (hd 0 (l1 ++ l2)) /\ (l1 ++ l2 = [] \/ l1 = [])) \/
    (exists x d v, (x = ma \/ (l1 ++ l2 <> [] /\ (x = xn \/ x = xp))) /\ (d = 0 \/ d = 8) /\ w = FCT (x + d) 8 v).
  Proof.
    intros w Hw. unfold dws in Hw.
    destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []) as [E12 | E12].
    - destruct Hw as [<- | [<- | [<- | []]]].
      + right. exists ma, 8, 0. auto 10.
      + right. exists ma, 0, 0. unfold Wz1. rewrite Z.add_0_r. auto 10.
      + left. rewrite E12. cbn [hd]. auto.
    - destruct (list_eq_dec Z.eq_dec l1 []) as [E1 | E1].
      + destruct Hw as [<- | [<- | [<- | [<- | [<- | []]]]]].
        * right. exists ma, 8, 0. auto 10.
        * right. exists ma, 0, 0. unfold Wz1. rewrite Z.add_0_r. auto 10.
        * left. destruct (Dmulti E12) as (mtn & mtp & _ & _ & _ & _ & _ & _ & _ & Hh). rewrite (proj1 (Hh E1)). auto.
        * right. exists xn, 0, xp. rewrite Z.add_0_r. auto 10.
        * right. exists xp, 8, xn. auto 10.
      + destruct Hw as [<- | [<- | [<- | [<- | []]]]].
        * right. exists ma, 8, 0. auto 10.
        * right. exists ma, 0, 0. unfold Wz1. rewrite Z.add_0_r. auto 10.
        * right. exists xn, 0, xp. rewrite Z.add_0_r. auto 10.
        * right. exists xp, 8, xn. auto 10.
  Qed.

  Lemma WOd : writes_ok A dws.
  Proof.
    pose proof DW as HW. intros w x Hw Hx.
    destruct (dws_range w Hw) as [(-> & _) | (y & d & v & Hy & Hd & ->)].
    - apply (writes_ok_ctx A [] (KActive sc) (hd 0 (l1 ++ l2)) HW (writes_ok_nil A) Hsc _ x (or_introl eq_refl) Hx).
    - cbn [f_a f_n] in Hx.
      assert (Hym : exists mty, a_meta A y = Some mty).
      { destruct Hy as [-> | (E12 & Hy)]; [exists mt; exact Hma|].
        destruct (Dmulti E12) as (mtn & mtp & Hmn & Hmp & _). destruct Hy as [-> | ->]; [exists mtn; exact Hmn | exists mtp; exact Hmp]. }
      destruct Hym as (mty & Hmy). destruct (meta_dom_nolive A y mty x HW Hmy ltac:(lia)) as [H1 H2]. split; [left; exact H1 | exact H2].
  Qed.

  Lemma has_Ad_written : forall f, has Ad f -> has A f \/ (forall x, f_a f <= x < f_a f + f_n f -> wlook dws x <> None).
  Proof.
    intros f Hf. pose proof DW as HW. pose proof Dlinks as [Hnx Hpx].
    assert (CV : forall a v x, In (FCT a 8 v) dws -> a <= x < a + 8 -> wlook dws x <> None).
    { intros a v x Hin Hx. apply (wlook_cov_some dws (FCT a 8 v) x Hin). cbn [f_a f_n]. exact Hx. }
    destruct (has_Ad f Hf) as [H | [-> | (x & mtx & fl & Hx & Hfl & Hxin & ->)]]; [left; exact H | |].
    - (* [comment removed for export] *)
      unfold dws in CV |- *. destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []) as [E12 | E12].
      + right. cbn [f_a f_n]. intros x Hx. apply (CV (caddr (KActive sc)) 0); [cbn; auto | exact Hx].
      + destruct (list_eq_dec Z.eq_dec l1 []) as [E1 | E1].
        * right. cbn [f_a f_n]. intros x Hx. apply (CV (caddr (KActive sc)) xn); [cbn; auto | exact Hx].
        * left. replace (hd 0 (l1 ++ l2)) with (a_ctx A (KActive sc)); [left; exists (KActive sc); auto|].
          rewrite (wf_act_head A HW sc Hsc), Hact. destruct l1; [contradiction | reflexivity].
    - (* [comment removed for export] *)
      destruct (Z.eq_dec x ma) as [-> | Hxm].
      + right. destruct Hfl as [-> | ->]; cbn [moff mlen f_a f_n]; intros y Hy.
        * apply (CV (ma + 8) 0 y); [| exact Hy]. unfold dws. destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []); [| destruct (list_eq_dec Z.eq_dec l1 [])]; left; reflexivity.
        * apply (CV ma 0 y); [| lia]. unfold dws, Wz1. destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []); [| destruct (list_eq_dec Z.eq_dec l1 [])]; right; left; reflexivity.
      + assert (E12 : l1 ++ l2 <> []).
        { intros E12. destruct (single_links A sc ma l1 l2 Hact E12) as [En Ep]. fold l n i0 xn xp in En, Ep.
          destruct Hxin as [E | [E | E]]; congruence. }
        destruct (Dmulti E12) as (mtn & mtp & Hmn & Hmp & _ & _ & Hnm & Hpm & _).
        assert (INn : In (FCT xn 8 xp) dws).
        { unfold dws. destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []); [contradiction|]. destruct (list_eq_dec Z.eq_dec l1 []); cbn; auto 10. }
        assert (INp : In (FCT (xp + 8) 8 xn) dws).
        { unfold dws. destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []); [contradiction|]. destruct (list_eq_dec Z.eq_dec l1 []); cbn; auto 10. }
        destruct Hfl as [-> | ->].
        * (* [comment removed for export] *)
          change (mt_f (RL x mtx) FNext) with (mt_next (RL x mtx)). rewrite (rl_next_other x mtx Hxm).
          destruct (Z.eqb_spec x xp) as [-> | Hxp].
          -- right. cbn [moff mlen f_a f_n]. intros y Hy. exact (CV (xp + 8) xn y INp Hy).
          -- left. right; right; left. exists x, mtx, FNext. auto.
        * change (mt_f (RL x mtx) FPrev) with (mt_prev (RL x mtx)). rewrite (rl_prev_other x mtx Hxm).
          destruct (Z.eqb_spec x xn) as [-> | Hxn].
          -- right. cbn [moff mlen f_a f_n]. intros y Hy. apply (CV xn xp y INn). lia.
          -- left. right; right; left. exists x, mtx, FPrev. auto.
  Qed.

  Lemma dws_lookup : forall x b, wlook dws x = Some b ->
    (exists y mty fl, a_meta Ad y = Some mty /\ y + moff fl <= x < y + moff fl + mlen fl /\ b = byte_of (mt_f mty fl) (x - (y + moff fl))) \/
    (exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (a_ctx Ad k) (x - caddr k)) \/
    (forall f, has Ad f -> ~ (f_a f <= x < f_a f + f_n f)).
  Proof.
    intros x b Hw. pose proof DW as HW. pose proof Dma_facts as (M1 & M2 & M4 & M0).
    pose proof (meta_facts A ma mt HW Hma) as (_ & _ & M3 & _ & _).
    pose proof (ctx_slot_range (KActive sc) Hsc) as (C1 & C2 & C3). cbn [clen] in C2, C3.
    pose proof Ad_ma as Hma2.
    assert (N2 : mt_f (RL ma mt) FNext = 0) by (change (mt_f (RL ma mt) FNext) with (mt_next (RL ma mt)); apply rl_next_ma).
    assert (P2 : mt_f (RL ma mt) FPrev = 0) by (change (mt_f (RL ma mt) FPrev) with (mt_prev (RL ma mt)); apply rl_prev_ma).
    assert (HD : a_ctx Ad (KActive sc) = hd 0 (l1 ++ l2)).
    { rewrite (Ad_ctx_valid (KActive sc) Hsc). destruct (cslot_eq_dec (KActive sc) (KActive sc)); [reflexivity | contradiction]. }
    (* [comment removed for export] *)
    unfold dws in Hw.
    assert (ZM : forall ws', wlook (Wz2 :: Wz1 :: ws') x = Some b ->
      (ma + 8 <= x < ma + 16 /\ b = byte_of 0 (x - (ma + 8))) \/ (ma <= x < ma + 8 /\ b = byte_of 0 (x - ma)) \/
      ((x < ma \/ ma + 16 <= x) /\ wlook ws' x = Some b)).
    { intros ws' H. unfold Wz2, Wz1 in H.
      destruct (Z.lt_ge_cases x ma) as [Hl | Hl].
      { right; right. rewrite 2 wlook_skip in H by (cbn [f_a f_n f_v]; lia). split; [left; exact Hl | exact H]. }
      destruct (Z.lt_ge_cases x (ma + 8)) as [H8 | H8].
      { right; left. rewrite wlook_skip in H by (cbn [f_a f_n f_v]; lia). rewrite wlook_hit in H by (cbn [f_a f_n f_v]; lia). injection H as <-. cbn [f_v f_a]. auto. }
      destruct (Z.lt_ge_cases x (ma + 16)) as [H16 | H16].
      { left. rewrite wlook_hit in H by (cbn [f_a f_n f_v]; lia). injection H as <-. cbn [f_v f_a]. auto. }
      right; right. rewrite 2 wlook_skip in H by (cbn [f_a f_n f_v]; lia). split; [right; exact H16 | exact H]. }
    assert (MAcase : forall ws', wlook (Wz2 :: Wz1 :: ws') x = Some b ->
      (exists y mty fl, a_meta Ad y = Some mty /\ y + moff fl <= x < y + moff fl + mlen fl /\ b = byte_of (mt_f mty fl) (x - (y + moff fl))) \/
      ((x < ma \/ ma + 16 <= x) /\ wlook ws' x = Some b)).
    { intros ws' H. destruct (ZM ws' H) as [(Hx & ->) | [(Hx & ->) | Hrest]]; [left | left | right; exact Hrest].
      - exists ma, (RL ma mt), FNext. split; [exact Hma2|]. cbn [moff mlen]. split; [lia|]. rewrite N2. reflexivity.
      - exists ma, (RL ma mt), FPrev. split; [exact Hma2|]. cbn [moff mlen]. split; [lia|]. rewrite P2, Z.add_0_r. reflexivity. }
    destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []) as [E12 | E12].
    - destruct (MAcase _ Hw) as [H | (Hfar & H)]; [left; exact H|].
      destruct (wlook_some_cov _ _ _ H) as (w & [<- | []] & Hxw). cbn [f_a f_n] in Hxw.
      rewrite wlook_hit in H by (cbn [f_a f_n f_v]; lia). injection H as <-. cbn [f_v f_a].
      right; left. exists (KActive sc). cbn [clen]. split; [exact Hsc|]. split; [lia|]. rewrite HD, E12. reflexivity.
    - destruct (Dmulti E12) as (mtn & mtp & Hmn & Hmp & _ & _ & Hnm & Hpm & _ & Hh).
      pose proof (meta_facts A xn mtn HW Hmn) as (N1 & N2' & N3 & N4 & _). pose proof (meta_facts A xp mtp HW Hmp) as (Q1 & Q2 & Q3 & Q4 & _).
      pose proof (metas_apart A xn mtn ma mt HW Hmn Hma Hnm) as Dnm. pose proof (metas_apart A xp mtp ma mt HW Hmp Hma Hpm) as Dpm.
      assert (Dnp : xn = xp \/ xn + 40 <= xp \/ xp + 40 <= xn).
      { destruct (Z.eq_dec xn xp) as [E | NE]; [left; exact E | right; exact (metas_apart A xn mtn xp mtp HW Hmn Hmp NE)]. }
      assert (Hn2 : a_meta Ad xn = Some (RL xn mtn)) by (rewrite Ad_meta, Hmn; reflexivity).
      assert (Hp2 : a_meta Ad xp = Some (RL xp mtp)) by (rewrite Ad_meta, Hmp; reflexivity).
      assert (XN : forall H : xn <= x < xn + 8, b = byte_of xp (x - xn) ->
        exists y mty fl, a_meta Ad y = Some mty /\ y + moff fl <= x < y + moff fl + mlen fl /\ b = byte_of (mt_f mty fl) (x - (y + moff fl))).
      { intros Hx ->. exists xn, (RL xn mtn), FPrev. split; [exact Hn2|]. cbn [moff mlen]. split; [lia|].
        change (mt_f (RL xn mtn) FPrev) with (mt_prev (RL xn mtn)). rewrite (rl_prev_other xn mtn Hnm), Z.eqb_refl, Z.add_0_r. reflexivity. }
      assert (XP : forall H : xp + 8 <= x < xp + 16, b = byte_of xn (x - (xp + 8)) ->
        exists y mty fl, a_meta Ad y = Some mty /\ y + moff fl <= x < y + moff fl + mlen fl /\ b = byte_of (mt_f mty fl) (x - (y + moff fl))).
      { intros Hx ->. exists xp, (RL xp mtp), FNext. split; [exact Hp2|]. cbn [moff mlen]. split; [lia|].
        change (mt_f (RL xp mtp) FNext) with (mt_next (RL xp mtp)). rewrite (rl_next_other xp mtp Hpm), Z.eqb_refl. reflexivity. }
      destruct (list_eq_dec Z.eq_dec l1 []) as [E1 | E1].
      + destruct (MAcase _ Hw) as [H | (Hfar & H)]; [left; exact H|].
        destruct (wlook_some_cov _ _ _ H) as (w & Hin & Hxw). destruct Hin as [<- | [<- | [<- | []]]]; cbn [f_a f_n] in Hxw.
        * rewrite wlook_hit in H by (cbn [f_a f_n f_v]; lia). injection H as <-. cbn [f_v f_a].
          right; left. exists (KActive sc). cbn [clen]. split; [exact Hsc|]. split; [lia|]. rewrite HD, (proj1 (Hh E1)). reflexivity.
        * rewrite wlook_skip in H by (cbn [f_a f_n f_v]; llia). rewrite wlook_hit in H by (cbn [f_a f_n f_v]; lia). injection H as <-. cbn [f_v f_a].
          left. apply XN; [lia | reflexivity].
        * rewrite wlook_skip in H by (cbn [f_a f_n f_v]; llia). rewrite wlook_skip in H by (cbn [f_a f_n f_v]; lia). rewrite wlook_hit in H by (cbn [f_a f_n f_v]; lia).
          injection H as <-. cbn [f_v f_a]. left. apply XP; [lia | reflexivity].
      + destruct (MAcase _ Hw) as [H | (Hfar & H)]; [left; exact H|].
        destruct (wlook_some_cov _ _ _ H) as (w & Hin & Hxw). destruct Hin as [<- | [<- | []]]; cbn [f_a f_n] in Hxw.
        * rewrite wlook_hit in H by (cbn [f_a f_n f_v]; lia). injection H as <-. cbn [f_v f_a]. left. apply XN; [lia | reflexivity].
        * rewrite wlook_skip in H by (cbn [f_a f_n f_v]; lia). rewrite wlook_hit in H by (cbn [f_a f_n f_v]; lia). injection H as <-. cbn [f_v f_a].
          left. apply XP; [lia | reflexivity].
  Qed.

  Lemma commit_d : forall m', RepW A (ms_mem s) dws m' ->
    II sp0 argv envp cb D Ad (upd s m' (ms_vm s)) /\ ntframe A s (upd s m' (ms_vm s)).
  Proof.
    intros m' RW. pose proof DW as HW. pose proof WOd as WO. pose proof HWd as HW'.
    split; [| exact (ntframe_commit A s dws m' HW RW WO)].
    pose proof AUD_Ad as (Hav & Hus & Hdd).
    apply II_intro; [| cbn [ms_vm upd]; unfold Ad; apply (VMok_deqA A sc ma l1 l2); exact (ii_vm HII) | exact Hav | exact Hus | exact Hdd].
    apply (IS_commit sp0 argv envp cb A Ad s dws m' (ii_is HII) RW WO HW').
    apply (repw_commit2 A Ad (ms_mem s) dws m' HW' RW has_Ad_written dws_lookup).
    intros x Hx. apply (proj1 (dom_deqA A sc ma l1 l2 x)). exact Hx.
  Qed.

  Theorem ts_nt_deqact : forall (K : unit -> M R) P,
    (forall s' A', II sp0 argv envp cb D A' s' -> ntframe A s s' -> deqrel A A' ma mt -> tsafe (K tt s') P) ->
    tsafe ((x <- nt_deqact (Z_to_bv 64 ma) (Z_to_bv 64 (mt_next mt)) (Z_to_bv 64 sc) ;; K x) s) P.
  Proof.
    intros K P HK. pose proof DW as HW. pose proof DR as HR. pose proof DWIN as HWIN. ceil.
    pose proof Dma_facts as (M1 & M2 & M4 & M0). pose proof (meta_facts A ma mt HW Hma) as (_ & _ & M3 & _ & Mdom).
    pose proof Dlinks as [Hnx Hpx].
    pose proof (repw_init A (ms_mem s) HW HR) as RW0.
    pose proof (ctx_slot_range (KActive sc) Hsc) as (C1 & C2 & C3). cbn [clen] in C2, C3.
    assert (Hhd0 : 0 <= hd0 < 2^64 /\ (hd0 = ma <-> l1 = [])).
    { rewrite Dhd0. destruct l1 as [|a l1'] eqn:El; [split; [llia | tauto]|].
      destruct (wf_act_mem A HW sc a ltac:(rewrite Hact; left; reflexivity)) as (mta & _ & _ & Hmta & _).
      pose proof (meta_facts A a mta HW Hmta) as (X1 & X2 & _). split; [llia|]. split; [| discriminate].
      intros ->. exfalso. apply (dq_g_notin A HW sc ma (ma :: l1') l2); [exact Hact | left; reflexivity]. }
    destruct Hhd0 as [Hhd64 Hhdma].
    unfold nt_deqact. try reassoc. apply ts_assert. { unfold wlit. rewrite c_ltu_Z by llia. apply Z.ltb_lt. llia. }
    cbv zeta. rewrite (addr_active sc) by llia. try reassoc.
    eapply (ts_ld_ctxfW A HW s (ms_mem s) [] (KActive sc)); [exact RW0 | exact HWIN | exact Hsc | reflexivity | apply wfree_range_nil |].
    rewrite (wf_act_head A HW sc Hsc), Hact. change (hd 0 (l1 ++ ma :: l2)) with hd0.
    (* [comment removed for export] *)
    try reassoc. unfold nt_deq. rewrite Hnx. rewrite ?(addr_active sc) by llia.
    assert (Hxn64 : 0 <= xn < 2^64 /\ 0 <= xp < 2^64).
    { destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []) as [E12 | E12].
      - destruct (single_links A sc ma l1 l2 Hact E12) as [En Ep]. fold l n i0 xn xp in En, Ep. rewrite En, Ep. llia.
      - destruct (Dmulti E12) as (mtn & mtp & Hmn & Hmp & _). pose proof (meta_u64 A xn mtn HW Hmn). pose proof (meta_u64 A xp mtp HW Hmp). llia. }
    destruct Hxn64 as [Hxn64 Hxp64].
    rewrite c_eq_Z by llia.
    (* [comment removed for export] *)
    assert (TAIL : forall s1 ws (cnd : bool),
      RepW A (ms_mem s) ws (ms_mem s1) -> WIN s1 -> ms_vm s1 = ms_vm s -> ms_lo s1 = ms_lo s -> ms_hi s1 = ms_hi s ->
      Wz2 :: Wz1 :: ws = dws -> (cnd = true <-> hd0 <> ma) ->
      tsafe ((x <- (m_sd (Z_to_bv 64 ma) w0 ;; m_sd (Z_to_bv 64 (ma + 8)) w0 ;;
                    (if cnd then mret tt
                     else nt_activate (v_add A_CTX (v_slli (Z_to_bv 64 sc) 3)))) ;; K x) s1) P).
    { intros s1 ws cnd RW HWIN1 Hvm Hlo Hhi Hws Hcnd.
      try reassoc. replace (Z_to_bv 64 ma) with (Z_to_bv 64 (ma + 0)) at 1 by (f_equal; lia).
      eapply (ts_sd_metaW A HW); [exact RW | exact HWIN1 | exact Hma | lia | lia |]. intros m1 RW1. change (bv_unsigned w0) with 0 in RW1. rewrite Z.add_0_r in RW1.
      try reassoc.
      eapply (ts_sd_metaW A HW); [exact RW1 | exact HWIN1 | exact Hma | lia | lia |]. intros m2 RW2. change (bv_unsigned w0) with 0 in RW2.
      fold Wz1 Wz2 in RW2. rewrite Hws in RW2.
      destruct (commit_d m2 RW2) as [HII2 HF2].
      lazymatch goal with |- tsafe (mbind ?a ?k ?st) ?Q =>
        replace st with (upd s m2 (ms_vm s)) by (unfold upd; cbn; rewrite ?Hvm, ?Hlo, ?Hhi; reflexivity) end.
      destruct cnd.
      2: assert (Ehd : hd0 = ma) by (destruct (Z.eq_dec hd0 ma) as [E | NE]; [exact E | exfalso; pose proof (proj2 Hcnd NE); discriminate]).
      1: assert (Nhd : hd0 <> ma) by (apply (proj1 Hcnd); reflexivity).
      all: swap 1 2.
      - (* [comment removed for export] *)
        apply (ts_nt_activate sp0 argv envp cb D Ad (upd s m2 (ms_vm s)) HII2 sc Hsc).
        + intros m3 rest mt3 Hl3 Hm3. pose proof Hl3 as Hl3'. unfold Ad in Hl3. rewrite (deqA_active_sc A sc ma l1 l2) in Hl3.
          assert (E12 : l1 ++ l2 <> []) by (rewrite Hl3; discriminate).
          destruct (Dmulti E12) as (mtn & mtp & Hmn & Hmp & _ & _ & Hnm & Hpm & _ & Hh).
          destruct (Hh (proj1 Hhdma Ehd)) as [Ehd3 Hav]. rewrite Hl3 in Ehd3. cbn [hd] in Ehd3. subst m3.
          rewrite Ad_meta, Hmn in Hm3. cbn in Hm3. injection Hm3 as <-. unfold RL. rewrite MallocInv_wf3.rl_avail. exact Hav.
        + intros s' B' HII' HF' HR'. apply (HK s' B' HII').
          * apply (ntframe_trans A Ad s (upd s m2 (ms_vm s)) s' HF2 HF'); [| reflexivity].
            intros x Hx. destruct Hx as [Hx | Hx]; [left; exact Hx | right]. apply (proj1 (dom_deqA A sc ma l1 l2 x)). exact Hx.
          * apply (deqrel_act A Ad B' ma mt sc deqrel_Ad HR' M0).
      - apply ts_bind_ret. apply (HK _ Ad HII2 HF2 deqrel_Ad). }
    destruct (Z.eqb_spec xn ma) as [Exn | Nxn].
    - (* [comment removed for export] *)
      assert (E12 : l1 ++ l2 = []).
      { destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []) as [E | E]; [exact E|]. exfalso. destruct (Dmulti E) as (mtn & mtp & _ & _ & _ & _ & Hnm & _). exact (Hnm Exn). }
      try reassoc. eapply (ts_sd_ctxW A s (ms_mem s) [] (KActive sc)); [exact RW0 | exact HWIN | exact Hsc | reflexivity |].
      intros m1 RW1. change (bv_unsigned w0) with 0 in RW1. rewrite ?at_Z.
      apply (TAIL (upd s m1 (ms_vm s)) _ _ RW1 HWIN eq_refl eq_refl eq_refl).
      + unfold dws. rewrite E12. cbn [list_eq_dec app]. reflexivity.
      + rewrite c_eq_Z by llia. rewrite Bool.negb_true_iff, Z.eqb_neq. tauto.
    - (* [comment removed for export] *)
      assert (E12 : l1 ++ l2 <> []).
      { intros E. destruct (single_links A sc ma l1 l2 Hact E) as [En _]. fold l n i0 xn xp in En. exact (Nxn En). }
      destruct (Dmulti E12) as (mtn & mtp & Hmn & Hmp & Hin_n & Hin_p & Hnm & Hpm & Hn2 & Hh).
      pose proof (meta_facts A xn mtn HW Hmn) as (N1 & N2 & N3 & N4 & Ndom). pose proof (meta_facts A xp mtp HW Hmp) as (Q1 & Q2 & Q3 & Q4 & Qdom).
      pose proof (metas_apart A xn mtn ma mt HW Hmn Hma Hnm) as Dnm. pose proof (metas_apart A xp mtp ma mt HW Hmp Hma Hpm) as Dpm.
      assert (Dnp : xn = xp \/ xn + 40 <= xp \/ xp + 40 <= xn).
      { destruct (Z.eq_dec xn xp) as [E | NE]; [left; exact E | right; exact (metas_apart A xn mtn xp mtp HW Hmn Hmp NE)]. }
      (* [comment removed for export] *)
      try reassoc. replace (Z_to_bv 64 ma) with (Z_to_bv 64 (ma + moff FPrev)) at 1 by (f_equal; cbn; lia).
      eapply (ts_ld_metaW A HW s (ms_mem s) [] ma mt FPrev); [exact RW0 | exact HWIN | exact Hma | reflexivity | apply wfree_range_nil | change (mt_f mt FPrev) with (mt_prev mt); llia |].
      change (mt_f mt FPrev) with (mt_prev mt). rewrite Hpx.
      (* [comment removed for export] *)
      try reassoc. rewrite ?at_Z.
      eapply (ts_sd_metaW A HW); [exact RW0 | exact HWIN | exact Hmp | lia | lia |]. intros m1 RW1. rewrite uZ in RW1 by llia.
      (* [comment removed for export] *)
      try reassoc. replace (Z_to_bv 64 ma) with (Z_to_bv 64 (ma + moff FPrev)) at 1 by (f_equal; cbn; lia).
      eapply (ts_ld_metaW A HW _ (ms_mem s) _ ma mt FPrev); [exact RW1 | exact HWIN | exact Hma | reflexivity | | change (mt_f mt FPrev) with (mt_prev mt); llia |].
      { cbn [moff]. apply wfree_range_cons; [cbn [f_a f_n]; lia | apply wfree_range_nil]. }
      change (mt_f mt FPrev) with (mt_prev mt). rewrite Hpx.
      try reassoc. rewrite ?at_Z. change (ma + 8) with (ma + moff FNext).
      eapply (ts_ld_metaW A HW _ (ms_mem s) _ ma mt FNext); [exact RW1 | exact HWIN | exact Hma | reflexivity | | change (mt_f mt FNext) with (mt_next mt); llia |].
      { cbn [moff]. apply wfree_range_cons; [cbn [f_a f_n]; lia | apply wfree_range_nil]. }
      change (mt_f mt FNext) with (mt_next mt). rewrite Hnx.
      (* [comment removed for export] *)
      try reassoc. replace (Z_to_bv 64 xn) with (Z_to_bv 64 (xn + 0)) at 1 by (f_equal; lia).
      eapply (ts_sd_metaW A HW); [exact RW1 | exact HWIN | exact Hmn | lia | lia |]. intros m2 RW2. rewrite uZ, Z.add_0_r in RW2 by llia.
      (* [comment removed for export] *)
      try reassoc.
      eapply (ts_ld_ctxfW A HW _ (ms_mem s) _ (KActive sc)); [exact RW2 | exact HWIN | exact Hsc | reflexivity | |].
      { repeat apply wfree_range_cons; try apply wfree_range_nil; cbn [f_a f_n]; llia. }
      rewrite (wf_act_head A HW sc Hsc), Hact. change (hd 0 (l1 ++ ma :: l2)) with hd0.
      rewrite c_eq_Z by llia. destruct (Z.eqb_spec hd0 ma) as [Ehd | Nhd].
      + (* [comment removed for export] *)
        try reassoc. rewrite ?at_Z. change (ma + 8) with (ma + moff FNext).
        eapply (ts_ld_metaW A HW _ (ms_mem s) _ ma mt FNext); [exact RW2 | exact HWIN | exact Hma | reflexivity | | change (mt_f mt FNext) with (mt_next mt); llia |].
        { cbn [moff]. repeat apply wfree_range_cons; try apply wfree_range_nil; cbn [f_a f_n]; lia. }
        change (mt_f mt FNext) with (mt_next mt). rewrite Hnx.
        eapply (ts_sd_ctxW A _ (ms_mem s) _ (KActive sc)); [exact RW2 | exact HWIN | exact Hsc | reflexivity |].
        intros m3 RW3. rewrite uZ in RW3 by llia. change (ma + moff FNext) with (ma + 8).
        apply (TAIL (upd s m3 (ms_vm s)) _ _ RW3 HWIN eq_refl eq_refl eq_refl).
        * unfold dws. destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []); [contradiction|].
          destruct (list_eq_dec Z.eq_dec l1 []) as [_ | NE]; [reflexivity | exfalso; exact (NE (proj1 Hhdma Ehd))].
        * cbn [negb]. split; [discriminate | intros NE; exfalso; exact (NE Ehd)].
      + apply ts_bind_ret. change (ma + moff FNext) with (ma + 8).
        apply (TAIL (upd s m2 (ms_vm s)) _ _ RW2 HWIN eq_refl eq_refl eq_refl).
        * unfold dws. destruct (list_eq_dec Z.eq_dec (l1 ++ l2) []); [contradiction|].
          destruct (list_eq_dec Z.eq_dec l1 []) as [E1 | _]; [exfalso; exact (Nhd (proj2 Hhdma E1)) | reflexivity].
        * cbn [negb]. tauto.
  Qed.
End Deq.
End WithLayout.
