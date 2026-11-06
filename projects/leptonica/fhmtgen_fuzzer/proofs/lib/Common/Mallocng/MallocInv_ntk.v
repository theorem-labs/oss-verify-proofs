(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_dll MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh
  MallocInv_ops MallocInv_live MallocInv_getmeta MallocInv_free MallocInv_tryavail MallocInv_ameta_iface
  MallocInv_ntfree MallocInv_ntpieces MallocInv_ntpost MallocInv_ntq MallocInv_nt1.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Section Keep.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Variables (ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i : Z).
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi : nth_error slots (Z.to_nat i) = Some STaken.
  Hypothesis Hi0 : 0 <= i.
  (* [comment removed for export] *)
  Hypothesis Hkeep : Z.lor (mt_avail mt) (mt_freed mt) = 0 -> mt_sc mt < 48 /\ 16 * size_class (mt_sc mt) <= mt_stride mt.

  Let mask := Z.lor (mt_avail mt) (mt_freed mt).
  Let sc := mt_sc mt.
  Let l := a_active A sc.
  Let hd0 := hd 0 l.
  Let h := hd ma l.
  Let t := last l ma.
  Let fr' := fb_fr mt i.
  Let A1 := fbA A ma mt aib slots i.
  Let A2 := queA A1 sc ma l h t.
  Let Wfr := FCT (ma + 28) 4 (sx32 fr').
  (* [comment removed for export] *)
  Let qws : list fct :=
    if list_eq_dec Z.eq_dec l []
    then [FCT (caddr (KActive sc)) 8 ma; FCT (ma + 8) 8 ma; FCT ma 8 ma]
    else [FCT hd0 8 ma; FCT (t + 8) 8 ma; FCT ma 8 t; FCT (ma + 8) 8 hd0].

  Lemma KW : WF A. Proof. exact (is_wf _ _ _ _ _ _ (ii_is HII)). Qed.
  Lemma KR : Rep A (ms_mem s). Proof. exact (is_rep _ _ _ _ _ _ (ii_is HII)). Qed.
  Lemma KWIN : WIN s. Proof. exact (is_win _ _ _ _ _ _ (ii_is HII)). Qed.

  Lemma Kgrp : 0 <= mt_w32 mt < 2^64 /\ (mt_sc mt < 48 \/ (mt_sc mt = 63 /\ mt_last mt = 0 /\ 0 < mt_maplen mt)) /\
    Z.of_nat (length slots) = mt_cnt mt /\
    0 <= mt_avail mt < 2 ^ (mt_cnt mt) /\ 0 <= mt_freed mt < 2 ^ (mt_cnt mt) /\
    0 <= aib < 256 /\ aib mod 32 <= mt_last mt /\
    (forall j st, nth_error slots (Z.to_nat j) = Some st -> 0 <= j -> (Z.testbit mask j = true <-> st = SIdle)).
  Proof.
    destruct (wf_grp A KW ma mt aib slots Hma Hr) as (H1 & _ & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & _).
    repeat split; try llia; try exact H3; apply H11; assumption.
  Qed.

  Lemma Kic : i < mt_cnt mt /\ i < 32 /\ mt_cnt mt <= 32.
  Proof.
    pose proof Kgrp as (_ & _ & Hlen & _). pose proof (w_last_range (mt_w32 mt)) as Hl.
    assert (Hilt : (Z.to_nat i < length slots)%nat) by (apply (proj1 (nth_error_Some slots (Z.to_nat i))); rewrite Hi; discriminate).
    unfold mt_cnt, mt_last in *. llia.
  Qed.

  Lemma Kmask32 : 0 <= mask < 2^32 /\ 0 <= mt_avail mt < 2^32 /\ 0 <= mt_freed mt < 2^32.
  Proof.
    pose proof Kgrp as (_ & _ & _ & Hav & Hfr & _). pose proof Kic as (_ & _ & Hc).
    assert (2 ^ mt_cnt mt <= 2 ^ 32) by (apply Z.pow_le_mono_r; llia).
    pose proof (lor_range32 (mt_avail mt) (mt_freed mt) ltac:(llia) ltac:(llia)). subst mask. llia.
  Qed.

  Lemma Hreuse : mt_sc mt < 48 -> Z.lor (mt_avail mt) (mt_freed mt) <> 0 \/ 16 * size_class (mt_sc mt) <= mt_stride mt.
  Proof. intros Hsc. destruct (Z.eq_dec mask 0) as [E | NE]; [right; exact (proj2 (Hkeep E)) | left; exact NE]. Qed.

  Lemma HW1 : WF A1.
  Proof. exact (WF_fbA A KW ma mt aib slots i Hma Hr Hi0 Hi Hreuse). Qed.

  Lemma A1_ma : a_meta A1 ma = Some (fb_mt mt aib slots i).
  Proof. apply fbA_meta_same. Qed.
  Lemma A1_other : forall x, x <> ma -> a_meta A1 x = a_meta A x.
  Proof. intros x Hx. apply fbA_meta_other. exact Hx. Qed.
  Lemma A1_meta_inv : forall x mtx, a_meta A1 x = Some mtx -> (x = ma /\ mtx = fb_mt mt aib slots i) \/ (x <> ma /\ a_meta A x = Some mtx).
  Proof.
    intros x mtx Hx. destruct (Z.eq_dec x ma) as [-> | Hne].
    - left. rewrite A1_ma in Hx. injection Hx as <-. auto.
    - right. rewrite (A1_other x Hne) in Hx. auto.
  Qed.
  Lemma fbmt_role : mt_role (fb_mt mt aib slots i) = RGroup aib (fb_slots slots i). Proof. reflexivity. Qed.
  Lemma fbmt_f : forall fl, fl <> FFreed -> mt_f (fb_mt mt aib slots i) fl = mt_f mt fl.
  Proof. intros fl Hfl. rewrite fb_mt_f. destruct (mfield_eq_dec fl FFreed); [contradiction | reflexivity]. Qed.
  Lemma fbmt_freed : mt_f (fb_mt mt aib slots i) FFreed = fr'.
  Proof. rewrite fb_mt_f. destruct (mfield_eq_dec FFreed FFreed); [reflexivity | contradiction]. Qed.
  Lemma fbmt_sc : mt_sc (fb_mt mt aib slots i) = mt_sc mt. Proof. unfold mt_sc, mt_w32. rewrite fbmt_f by discriminate. reflexivity. Qed.
  Lemma fbmt_cnt : mt_cnt (fb_mt mt aib slots i) = mt_cnt mt. Proof. unfold mt_cnt, mt_last, mt_w32. rewrite fbmt_f by discriminate. reflexivity. Qed.
  Lemma fbmt_last : mt_last (fb_mt mt aib slots i) = mt_last mt. Proof. unfold mt_last, mt_w32. rewrite fbmt_f by discriminate. reflexivity. Qed.
  Lemma fbmt_avail : mt_avail (fb_mt mt aib slots i) = mt_avail mt. Proof. unfold mt_avail. apply fbmt_f. discriminate. Qed.
  Lemma fbmt_freed' : mt_freed (fb_mt mt aib slots i) = fr'. Proof. unfold mt_freed. apply fbmt_freed. Qed.
  Lemma fbmt_w32 : mt_w32 (fb_mt mt aib slots i) = mt_w32 mt. Proof. unfold mt_w32. apply fbmt_f. discriminate. Qed.
  Lemma fbmt_mem : mt_mem (fb_mt mt aib slots i) = mt_mem mt. Proof. unfold mt_mem. apply fbmt_f. discriminate. Qed.
  Lemma fbmt_prev : mt_prev (fb_mt mt aib slots i) = mt_prev mt. Proof. unfold mt_prev. apply fbmt_f. discriminate. Qed.
  Lemma fbmt_next : mt_next (fb_mt mt aib slots i) = mt_next mt. Proof. unfold mt_next. apply fbmt_f. discriminate. Qed.

  Lemma meta_usage_A1 : forall c x, meta_usage A1 c x = meta_usage A c x.
  Proof.
    intros c x. unfold meta_usage. destruct (Z.eq_dec x ma) as [-> | Hne].
    - rewrite A1_ma, Hma, Hr. cbn [mt_role fb_mt MT]. rewrite fbmt_sc, fbmt_cnt. reflexivity.
    - rewrite (A1_other x Hne). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma has_A1 : forall f, has A1 f -> has A f \/ f = FCT (ma + 28) 4 fr'.
  Proof.
    intros f Hf.
    destruct (has_grp_upd A ma mt (mt_avail mt) (fb_fr mt i) aib (fb_slots slots i) (a_live A) f Hf)
      as [[HfA _] | [[fl ->] | [Hhdr | (j & st & Hj & Hin)]]].
    - left. exact HfA.
    - destruct (mfield_eq_dec fl FFreed) as [-> | Hne]; [right; reflexivity | left].
      right; right; left. exists ma, mt, fl. split; [exact Hma|]. destruct fl; try reflexivity; contradiction.
    - left. right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. left. exact Hhdr.
    - left. right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. right.
      unfold fb_slots in Hj. destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(-> & -> & _) | (Hne & Hj')].
      + exists (Z.to_nat i), STaken. split; [exact Hi | exact Hin].
      + exists j, st. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma ntrel_A1 : ntrel A A1 ma slots i.
  Proof.
    constructor; try reflexivity.
    - intros x mtx aibx slx Hx Hrx. destruct (A1_meta_inv x mtx Hx) as [(Ex & Em) | (Hne & Hx')].
      + subst x mtx. cbn [mt_role fb_mt MT] in Hrx. injection Hrx as <- <-. exists mt, slots. rewrite fbmt_w32, fbmt_mem.
        split; [exact Hma|]. split; [exact Hr|]. split; [reflexivity|]. split; [reflexivity|]. left. split; reflexivity.
      + exists mtx, slx. split; [exact Hx'|]. split; [exact Hrx|]. split; [reflexivity|]. split; [reflexivity|]. right. split; [exact Hne | left; reflexivity].
    - intros x Hx. apply (proj1 (dom_fbA A ma mt aib slots i Hma Hr x)). exact Hx.
    - exists []. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma AUD_A1 : AvOK A1 /\ UsOK A1 /\ deads A1 D.
  Proof.
    split; [| split].
    - apply (AvOK_transfer A A1 (ii_av HII)); try reflexivity. intros x mt' Hx Hrl.
      destruct (A1_meta_inv x mt' Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrl; discriminate | exists mt'; auto].
    - apply (UsOK_transfer A A1 (ii_us HII)); [reflexivity | intros; reflexivity | exact meta_usage_A1].
    - apply (deads_transfer A A1 D (ii_dd HII)). intros x. split.
      + intros (mt' & Hx & Hrl). destruct (A1_meta_inv x mt' Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrl; discriminate | exists mt'; auto].
      + intros (mt0 & Hx & Hrl). exists mt0. destruct (Z.eq_dec x ma) as [-> | Hne].
        * rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrl. discriminate.
        * rewrite (A1_other x Hne). auto.
  Qed.

  Lemma commit_a : forall m', RepW A (ms_mem s) [Wfr] m' ->
    II sp0 argv envp cb D A1 (upd s m' (ms_vm s)) /\ ntframe A s (upd s m' (ms_vm s)).
  Proof.
    intros m' RW. pose proof KW as HW.
    assert (WO : writes_ok A [Wfr]).
    { unfold Wfr. apply (writes_ok_meta A [] ma mt 28 4 _ HW (writes_ok_nil A) Hma); lia. }
    split; [| exact (ntframe_commit A s [Wfr] m' HW RW WO)].
    pose proof AUD_A1 as (Hav & Hus & Hdd).
    apply II_intro; [| cbn [ms_vm upd]; apply (VMok_fbA A ma mt aib slots i Hma Hr); exact (ii_vm HII) | exact Hav | exact Hus | exact Hdd].
    apply (IS_commit sp0 argv envp cb A A1 s [Wfr] m' (ii_is HII) RW WO HW1).
    apply (repw_commit2 A A1 (ms_mem s) [Wfr] m' HW1 RW).
    - intros f Hf. destruct (has_A1 f Hf) as [H | ->]; [left; exact H | right]. cbn [f_a f_n]. intros x Hx.
      unfold Wfr. rewrite wlook_hit by (cbn [f_a f_n f_v]; lia). discriminate.
    - intros x b Hw. left. unfold Wfr in Hw. destruct (wlook_some_cov _ _ _ Hw) as (w & [<- | []] & Hx). cbn [f_a f_n] in Hx.
      rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. cbn [f_v f_a].
      exists ma, (fb_mt mt aib slots i), FFreed. split; [exact A1_ma|]. cbn [moff mlen]. split; [lia|].
      rewrite fbmt_freed. apply byte_of_sx32. lia.
    - intros x Hx. apply (proj1 (dom_fbA A ma mt aib slots i Hma Hr x)). exact Hx.
  Qed.

  (* [comment removed for export] *)
  Section Requeue.
    Hypothesis Hm0 : mask = 0.
    Hypothesis Hhd : hd0 <> ma.

    Lemma Ksc : 0 <= sc < 48.
    Proof. pose proof (w_sc_range (mt_w32 mt)). subst sc. unfold mt_sc. pose proof (proj1 (Hkeep Hm0)). unfold mt_sc in *. llia. Qed.
    Lemma Kav0 : mt_avail mt = 0 /\ mt_freed mt = 0.
    Proof.
      pose proof Kgrp as (_ & _ & _ & Hav & Hfr & _). subst mask.
      split; apply Z.bits_inj'; intros j Hj; rewrite Z.bits_0;
        pose proof (Z.lor_spec (mt_avail mt) (mt_freed mt) j) as E; rewrite Hm0, Z.bits_0 in E;
        symmetry in E; apply Bool.orb_false_iff in E; tauto.
    Qed.
    Lemma Knin : ~ In ma l.
    Proof.
      intros Hin. destruct (wf_act_nonhead A KW sc ma mt Hin ltac:(intros E; apply Hhd; symmetry; exact E) Hma) as [_ Hfr]. exact (Hfr (proj2 Kav0)).
    Qed.
    Lemma Klinks : mt_prev mt = 0 /\ mt_next mt = 0.
    Proof. apply (wf_unlinked A KW ma mt aib slots Hma Hr). exact Knin. Qed.
    Lemma Kfull : ~ (aib mod 32 < mt_last mt).
    Proof.
      intros Hlt. pose proof (wf_inactive A KW ma mt aib slots (mt_last mt) Hma Hr ltac:(llia)) as Hb.
      rewrite (proj2 Kav0), Z.bits_0 in Hb. discriminate Hb.
    Qed.

    Lemma HW2 : WF A2.
    Proof.
      apply (WF_queA A1 HW1 sc ma (fb_mt mt aib slots i) aib (fb_slots slots i) l h t Ksc A1_ma fbmt_role fbmt_sc eq_refl eq_refl eq_refl Knin).
      - intros _. rewrite fbmt_avail. exact (proj1 Kav0).
      - intros _. rewrite fbmt_freed'. subst fr'. exact (fb_fr_nz A KW ma mt aib slots i Hma Hr Hi0).
      - intros _. rewrite fbmt_last. exact Kfull.
    Qed.

    Lemma l_metas : forall x, In x l -> exists mtx aibx slx, a_meta A x = Some mtx /\ mt_role mtx = RGroup aibx slx /\ mt_sc mtx = sc /\ x <> ma.
    Proof.
      intros x Hx. destruct (wf_act_mem A KW sc x Hx) as (mtx & aibx & slx & H1 & H2 & H3). exists mtx, aibx, slx.
      repeat split; auto. intros ->. exact (Knin Hx).
    Qed.

    Lemma l_ne_facts : l <> [] -> h = hd0 /\ In hd0 l /\ In t l /\ hd0 <> ma /\ t <> ma /\ hd0 <> 0 /\
      exists mth mtt, a_meta A hd0 = Some mth /\ a_meta A t = Some mtt /\ mt_prev mth = last l 0 /\ last l 0 = t.
    Proof.
      intros Hne. assert (Eh : h = hd0) by (subst h hd0; apply hd_default_ne; exact Hne).
      assert (Hin_h : In hd0 l) by (subst hd0; destruct l; [contradiction | left; reflexivity]).
      assert (Hin_t : In t l) by (subst t; apply last_In_ne; exact Hne).
      destruct (l_metas hd0 Hin_h) as (mth & aibh & slh & Hh1 & _ & _ & Hhma).
      destruct (l_metas t Hin_t) as (mtt & aibt & slt & Ht1 & _ & _ & Htma).
      pose proof (meta_facts A hd0 mth KW Hh1) as (L1 & _).
      split; [exact Eh|]. split; [exact Hin_h|]. split; [exact Hin_t|]. split; [exact Hhma|]. split; [exact Htma|]. split; [llia|].
      exists mth, mtt. split; [exact Hh1|]. split; [exact Ht1|].
      pose proof (wf_act_dll A KW sc Ksc) as Hd. fold l in Hd.
      assert (H0 : nth_error l 0 = Some hd0) by (subst hd0; destruct l; [contradiction | reflexivity]).
      destruct (Hd 0%nat hd0 H0) as (mt' & Hm' & _ & Hp). rewrite Hh1 in Hm'. injection Hm' as <-.
      rewrite Hp. replace ((0 + length l - 1) mod length l)%nat with (length l - 1)%nat.
      2:{ rewrite Nat.add_0_l. symmetry. apply Nat.mod_small. destruct l; [contradiction | cbn; lia]. }
      rewrite <- (last_nth l 0 Hne). split; [reflexivity|]. subst t. apply last_default_ne. exact Hne.
    Qed.

    Lemma A2_meta : forall x, a_meta A2 x = option_map (MallocInv_wf3.relink (qP ma h t) (qN ma h t) x) (a_meta A1 x).
    Proof. intros x. apply queA_meta. Qed.

    Lemma meta_usage_A2 : forall c x, meta_usage A2 c x = meta_usage A c x.
    Proof.
      intros c x. rewrite <- meta_usage_A1. unfold meta_usage. rewrite A2_meta.
      destruct (a_meta A1 x) as [mtx|]; [cbn [option_map] | reflexivity].
      change (mt_role (MallocInv_wf3.relink (qP ma h t) (qN ma h t) x mtx)) with (mt_role mtx).
      rewrite MallocInv_wf3.rl_sc, MallocInv_wf3.rl_cnt. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma has_A2 : forall f, has A2 f ->
      has A f \/ f = FCT (ma + 28) 4 fr' \/
      (l = [] /\ (f = FCT (caddr (KActive sc)) 8 ma \/ f = FCT (ma + 8) 8 ma \/ f = FCT ma 8 ma)) \/
      (l <> [] /\ (f = FCT hd0 8 ma \/ f = FCT (t + 8) 8 ma \/ f = FCT ma 8 t \/ f = FCT (ma + 8) 8 hd0)).
    Proof.
      intros f Hf.
      destruct (has_queA_inv A1 HW1 sc ma l h t Ksc eq_refl f Hf) as [H1 | [-> | (x & mtx & fl & Hx & Hfl & Hxin & ->)]].
      - destruct (has_A1 f H1) as [H | H]; [left; exact H | right; left; exact H].
      - destruct (list_eq_dec Z.eq_dec l []) as [El | El].
        + right; right; left. split; [exact El|]. left. subst h. rewrite El. reflexivity.
        + left. destruct (l_ne_facts El) as (Eh & _). rewrite Eh. unfold hd0, l. rewrite <- (wf_act_head A KW sc Ksc).
          left. exists (KActive sc). split; [exact Ksc | reflexivity].
      - destruct (list_eq_dec Z.eq_dec l []) as [El | El].
        + (* [comment removed for export] *)
          assert (Eh : h = ma) by (subst h; rewrite El; reflexivity). assert (Et : t = ma) by (subst t; rewrite El; reflexivity).
          assert (Ex : x = ma) by (destruct Hxin as [E | [E | E]]; congruence).
          right; right; left. split; [exact El|]. right. subst x.
          destruct Hfl as [-> | ->].
          * left. cbn [moff mlen]. f_equal.
            change (mt_f (MallocInv_wf3.relink (qP ma h t) (qN ma h t) ma mtx) FNext) with (mt_next (MallocInv_wf3.relink (qP ma h t) (qN ma h t) ma mtx)).
            rewrite relink_next, Et, Z.eqb_refl. reflexivity.
          * right. cbn [moff mlen]. rewrite Z.add_0_r. f_equal.
            change (mt_f (MallocInv_wf3.relink (qP ma h t) (qN ma h t) ma mtx) FPrev) with (mt_prev (MallocInv_wf3.relink (qP ma h t) (qN ma h t) ma mtx)).
            rewrite relink_prev, Eh, Z.eqb_refl. reflexivity.
        + destruct (l_ne_facts El) as (Eh & Hin_h & Hin_t & Hhma & Htma & Hh0 & mth & mtt & Hmh & Hmt & Hph & Hlt).
          rewrite Eh in *.
          destruct Hfl as [-> | ->].
          * (* [comment removed for export] *)
            change (mt_f (MallocInv_wf3.relink (qP ma hd0 t) (qN ma hd0 t) x mtx) FNext) with (mt_next (MallocInv_wf3.relink (qP ma hd0 t) (qN ma hd0 t) x mtx)).
            rewrite relink_next. cbn [moff mlen].
            destruct (Z.eqb_spec x t) as [-> | Hxt].
            -- right; right; right. split; [exact El|]. right; left. reflexivity.
            -- destruct (Z.eqb_spec x ma) as [-> | Hxm].
               ++ right; right; right. split; [exact El|]. right; right; right. reflexivity.
               ++ (* [comment removed for export] *)
                  assert (x = hd0) by (destruct Hxin as [E | [E | E]]; congruence). subst x.
                  left. rewrite (A1_other hd0 Hhma) in Hx. right; right; left. exists hd0, mtx, FNext. auto.
          * change (mt_f (MallocInv_wf3.relink (qP ma hd0 t) (qN ma hd0 t) x mtx) FPrev) with (mt_prev (MallocInv_wf3.relink (qP ma hd0 t) (qN ma hd0 t) x mtx)).
            rewrite relink_prev. cbn [moff mlen]. rewrite Z.add_0_r.
            destruct (Z.eqb_spec x hd0) as [-> | Hxh].
            -- right; right; right. split; [exact El|]. left. reflexivity.
            -- destruct (Z.eqb_spec x ma) as [-> | Hxm].
               ++ right; right; right. split; [exact El|]. right; right; left. reflexivity.
               ++ assert (x = t) by (destruct Hxin as [E | [E | E]]; congruence). subst x.
                  left. rewrite (A1_other t Htma) in Hx. right; right; left. exists t, mtx, FPrev. rewrite Z.add_0_r. auto.
    Qed.
    Let ws2 := Wfr :: qws.

    Lemma relink_f_other : forall P N x mtx fl, fl <> FPrev -> fl <> FNext -> mt_f (MallocInv_wf3.relink P N x mtx) fl = mt_f mtx fl.
    Proof. intros P N x mtx fl H1 H2. unfold MallocInv_wf3.relink. rewrite mt_f_MT. destruct fl; try reflexivity; contradiction. Qed.

    Lemma A2_ma : a_meta A2 ma = Some (MallocInv_wf3.relink (qP ma h t) (qN ma h t) ma (fb_mt mt aib slots i)).
    Proof. rewrite A2_meta, A1_ma. reflexivity. Qed.

    Lemma ntrel_A2 : ntrel A A2 ma slots i.
    Proof.
      pose proof ntrel_A1 as [L1 Ar1 P1 B1 C1 Q1 G1 D1 F1].
      constructor; try reflexivity.
      - intros k Hk. unfold A2, queA, MallocInv_wf3.A', MallocInv_wf3.c'. cbn [a_ctx]. destruct k; try reflexivity; destruct Hk.
      - intros c Hc. unfold A2. rewrite (queA_active_other A1 sc ma l h t c) by (intros ->; exact (Hc Ksc)). reflexivity.
      - intros x mtx aibx slx Hx Hrx. rewrite A2_meta in Hx. destruct (a_meta A1 x) as [mt1|] eqn:E1; [| discriminate Hx].
        cbn [option_map] in Hx. injection Hx as <-. change (mt_role (MallocInv_wf3.relink (qP ma h t) (qN ma h t) x mt1)) with (mt_role mt1) in Hrx.
        destruct (G1 x mt1 aibx slx E1 Hrx) as (mt0 & sl0 & H0 & R0 & W0 & M0 & K0). exists mt0, sl0.
        rewrite MallocInv_wf3.rl_w32, MallocInv_wf3.rl_mem. auto 10.
      - intros x Hx. apply D1. apply (proj1 (dom_queA A1 sc ma l h t x)). exact Hx.
      - exact F1.
    Qed.

    Lemma AUD_A2 : AvOK A2 /\ UsOK A2 /\ deads A2 D.
    Proof.
      pose proof AUD_A1 as (Hav & Hus & Hdd).
      assert (BK : forall x mt', a_meta A2 x = Some mt' -> exists mt1, a_meta A1 x = Some mt1 /\ mt_role mt' = mt_role mt1).
      { intros x mt' Hx. rewrite A2_meta in Hx. destruct (a_meta A1 x) as [mt1|]; [| discriminate Hx]. cbn in Hx. injection Hx as <-. exists mt1. auto. }
      split; [| split].
      - apply (AvOK_transfer A1 A2 Hav); [reflexivity | apply (queA_ctx_valid A1 HW1 sc ma l h t Ksc eq_refl KAmc I) |].
        intros x mt' Hx Hrl. destruct (BK x mt' Hx) as (mt1 & H1 & R1). exists mt1. rewrite <- R1. auto.
      - apply (UsOK_transfer A1 A2 Hus); [reflexivity | | intros c x; rewrite meta_usage_A2, meta_usage_A1; reflexivity].
        intros c Hc. unfold A2. rewrite (queA_ctx_valid A1 HW1 sc ma l h t Ksc eq_refl (KUsage c) Hc).
        destruct (cslot_eq_dec (KUsage c) (KActive sc)) as [E | _]; [discriminate E | reflexivity].
      - apply (deads_transfer A1 A2 D Hdd). intros x. split.
        + intros (mt' & Hx & Hrl). destruct (BK x mt' Hx) as (mt1 & H1 & R1). exists mt1. rewrite <- R1. auto.
        + intros (mt1 & Hx & Hrl). exists (MallocInv_wf3.relink (qP ma h t) (qN ma h t) x mt1). rewrite A2_meta, Hx. auto.
    Qed.

    Lemma qws_range : forall w, In w qws ->
      (w = FCT (caddr (KActive sc)) 8 ma /\ l = []) \/
      (exists x d, (x = ma \/ (l <> [] /\ (x = hd0 \/ x = t))) /\ (d = 0 \/ d = 8) /\ f_a w = x + d /\ f_n w = 8).
    Proof.
      intros w Hw. unfold qws in Hw. destruct (list_eq_dec Z.eq_dec l []) as [El | El].
      - destruct Hw as [<- | [<- | [<- | []]]]; [left; auto | right | right].
        + exists ma, 8. cbn. auto 10.
        + exists ma, 0. cbn. repeat split; auto. lia.
      - right. destruct Hw as [<- | [<- | [<- | [<- | []]]]]; cbn [f_a f_n].
        + exists hd0, 0. repeat split; auto 10. lia.
        + exists t, 8. auto 10.
        + exists ma, 0. repeat split; auto. lia.
        + exists ma, 8. auto 10.
    Qed.

    Lemma WO2 : writes_ok A ws2.
    Proof.
      pose proof KW as HW. unfold ws2. unfold Wfr. apply (writes_ok_meta A qws ma mt 28 4 _ HW); [| exact Hma | lia | lia].
      intros w x Hw Hx. destruct (qws_range w Hw) as [(-> & El) | (y & d & Hy & Hd & Ea & En)].
      - apply (writes_ok_ctx A [] (KActive sc) ma HW (writes_ok_nil A) Ksc _ x (or_introl eq_refl) Hx).
      - rewrite Ea, En in Hx.
        assert (Hym : exists mty, a_meta A y = Some mty).
        { destruct Hy as [-> | (El & [-> | ->])]; [exists mt; exact Hma | |];
            destruct (l_ne_facts El) as (_ & _ & _ & _ & _ & _ & mth & mtt & Hmh & Hmt & _); [exists mth; exact Hmh | exists mtt; exact Hmt]. }
        destruct Hym as (mty & Hmy). destruct (meta_dom_nolive A y mty x HW Hmy ltac:(lia)) as [H1 H2]. split; [left; exact H1 | exact H2].
    Qed.

    (* [comment removed for export] *)
    Lemma ws2_lookup : forall x b, wlook ws2 x = Some b ->
      (exists y mty fl, a_meta A2 y = Some mty /\ y + moff fl <= x < y + moff fl + mlen fl /\ b = byte_of (mt_f mty fl) (x - (y + moff fl))) \/
      (exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (a_ctx A2 k) (x - caddr k)) \/
      (forall f, has A2 f -> ~ (f_a f <= x < f_a f + f_n f)).
    Proof.
      intros x b Hw. pose proof KW as HW. pose proof (meta_facts A ma mt HW Hma) as (M1 & M2 & M3 & M4 & _).
      pose proof (ctx_slot_range (KActive sc) Ksc) as (C1 & C2 & C3). cbn [clen] in C2, C3.
      pose proof A2_ma as Hma2.
      set (mt2 := MallocInv_wf3.relink (qP ma h t) (qN ma h t) ma (fb_mt mt aib slots i)) in Hma2.
      assert (N2 : mt_f mt2 FNext = if ma =? t then ma else h).
      { change (mt_f mt2 FNext) with (mt_next mt2). subst mt2. rewrite relink_next, Z.eqb_refl. reflexivity. }
      assert (P2 : mt_f mt2 FPrev = if ma =? h then ma else t).
      { change (mt_f mt2 FPrev) with (mt_prev mt2). subst mt2. rewrite relink_prev, Z.eqb_refl. reflexivity. }
      assert (F2 : mt_f mt2 FFreed = fr').
      { subst mt2. rewrite relink_f_other by discriminate. exact fbmt_freed. }
      (* [comment removed for export] *)
      assert (QW : wlook qws x = Some b ->
        (exists y mty fl, a_meta A2 y = Some mty /\ y + moff fl <= x < y + moff fl + mlen fl /\ b = byte_of (mt_f mty fl) (x - (y + moff fl))) \/
        (exists k, cvalid k /\ caddr k <= x < caddr k + clen k /\ b = byte_of (a_ctx A2 k) (x - caddr k))).
      { clear Hw. intros Hw. unfold qws in Hw. destruct (list_eq_dec Z.eq_dec l []) as [El | El].
        - assert (Eh : h = ma) by (subst h; rewrite El; reflexivity). assert (Et : t = ma) by (subst t; rewrite El; reflexivity).
          rewrite <- Eh in P2. rewrite <- Et in N2. rewrite Z.eqb_refl in N2, P2.
          destruct (wlook_some_cov _ _ _ Hw) as (w & Hin & Hxw).
          destruct Hin as [<- | [<- | [<- | []]]]; cbn [f_a f_n] in Hxw.
          + rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. right. exists (KActive sc). cbn [f_v f_a clen].
            split; [exact Ksc|]. split; [lia|]. unfold A2. rewrite (queA_ctx_valid A1 HW1 sc ma l h t Ksc eq_refl (KActive sc) Ksc).
            destruct (cslot_eq_dec (KActive sc) (KActive sc)); [| contradiction]. rewrite Eh. reflexivity.
          + rewrite wlook_skip in Hw by (cbn [f_a f_n f_v]; llia). rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. left.
            exists ma, mt2, FNext. split; [exact Hma2|]. cbn [moff mlen f_v f_a]. split; [lia|]. rewrite N2, Et. reflexivity.
          + rewrite wlook_skip in Hw by (cbn [f_a f_n f_v]; llia). rewrite wlook_skip in Hw by (cbn [f_a f_n f_v]; lia). rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. left.
            exists ma, mt2, FPrev. split; [exact Hma2|]. cbn [moff mlen f_v f_a]. split; [lia|]. rewrite P2, Eh, Z.add_0_r. reflexivity.
        - destruct (l_ne_facts El) as (Eh & Hin_h & Hin_t & Hhma & Htma & Hh0 & mth & mtt & Hmh & Hmt & Hph & Hlt).
          pose proof (meta_facts A hd0 mth HW Hmh) as (Q1 & Q2 & Q3 & Q4 & _). pose proof (meta_facts A t mtt HW Hmt) as (T1 & T2 & T3 & T4 & _).
          pose proof (metas_apart A hd0 mth ma mt HW Hmh Hma Hhma) as Dhm. pose proof (metas_apart A t mtt ma mt HW Hmt Hma Htma) as Dtm.
          assert (Dht : hd0 = t \/ hd0 + 40 <= t \/ t + 40 <= hd0).
          { destruct (Z.eq_dec hd0 t) as [E | NE]; [left; exact E | right; exact (metas_apart A hd0 mth t mtt HW Hmh Hmt NE)]. }
          assert (Hh2 : a_meta A2 hd0 = Some (MallocInv_wf3.relink (qP ma h t) (qN ma h t) hd0 mth)).
          { rewrite A2_meta, (A1_other hd0 Hhma), Hmh. reflexivity. }
          assert (Ht2 : a_meta A2 t = Some (MallocInv_wf3.relink (qP ma h t) (qN ma h t) t mtt)).
          { rewrite A2_meta, (A1_other t Htma), Hmt. reflexivity. }
          rewrite Eh in N2, P2. rewrite (proj2 (Z.eqb_neq ma t) ltac:(intros E; apply Htma; symmetry; exact E)) in N2.
          rewrite (proj2 (Z.eqb_neq ma hd0) ltac:(intros E; apply Hhma; symmetry; exact E)) in P2.
          destruct (wlook_some_cov _ _ _ Hw) as (w & Hin & Hxw).
          destruct Hin as [<- | [<- | [<- | [<- | []]]]]; cbn [f_a f_n] in Hxw.
          + (* [comment removed for export] *)
            rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. left.
            exists hd0, (MallocInv_wf3.relink (qP ma h t) (qN ma h t) hd0 mth), FPrev. split; [exact Hh2|]. cbn [moff mlen f_v f_a]. split; [lia|].
            change (mt_f (MallocInv_wf3.relink (qP ma h t) (qN ma h t) hd0 mth) FPrev) with (mt_prev (MallocInv_wf3.relink (qP ma h t) (qN ma h t) hd0 mth)).
            rewrite relink_prev, Eh, Z.eqb_refl. rewrite Z.add_0_r. reflexivity.
          + (* [comment removed for export] *)
            rewrite wlook_skip in Hw by (cbn [f_a f_n f_v]; lia). rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. left.
            exists t, (MallocInv_wf3.relink (qP ma h t) (qN ma h t) t mtt), FNext. split; [exact Ht2|]. cbn [moff mlen f_v f_a]. split; [lia|].
            change (mt_f (MallocInv_wf3.relink (qP ma h t) (qN ma h t) t mtt) FNext) with (mt_next (MallocInv_wf3.relink (qP ma h t) (qN ma h t) t mtt)).
            rewrite relink_next, Z.eqb_refl. reflexivity.
          + (* [comment removed for export] *)
            rewrite 2 wlook_skip in Hw by (cbn [f_a f_n f_v]; lia). rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. left.
            exists ma, mt2, FPrev. split; [exact Hma2|]. cbn [moff mlen f_v f_a]. split; [lia|]. rewrite P2, Z.add_0_r. reflexivity.
          + (* [comment removed for export] *)
            rewrite 3 wlook_skip in Hw by (cbn [f_a f_n f_v]; lia). rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. left.
            exists ma, mt2, FNext. split; [exact Hma2|]. cbn [moff mlen f_v f_a]. split; [lia|]. rewrite N2. reflexivity. }
      unfold ws2 in Hw. cbn [wlook] in Hw. fold (wlook qws x) in Hw.
      destruct (wcov Wfr x) eqn:Ec.
      - (* [comment removed for export] *)
        apply wcov_spec in Ec. unfold Wfr in Ec. cbn [f_a f_n] in Ec. injection Hw as <-. left.
        exists ma, mt2, FFreed. split; [exact Hma2|]. unfold Wfr. cbn [moff mlen f_v f_a]. split; [lia|]. rewrite F2. apply byte_of_sx32. lia.
      - destruct (QW Hw) as [H | H]; [left; exact H | right; left; exact H].
    Qed.

    Lemma has_A2_written : forall f, has A2 f -> has A f \/ (forall x, f_a f <= x < f_a f + f_n f -> wlook ws2 x <> None).
    Proof.
      intros f Hf.
      assert (INQ : forall w, In w qws -> In w ws2) by (intros w Hw; right; exact Hw).
      destruct (has_A2 f Hf) as [H | [-> | [(El & Hc) | (El & Hc)]]]; [left; exact H | right | right | right].
      - cbn [f_a f_n]. intros x Hx. apply (wlook_cov_some ws2 Wfr x); [left; reflexivity | unfold Wfr; cbn [f_a f_n]; lia].
      - assert (Q : qws = [FCT (caddr (KActive sc)) 8 ma; FCT (ma + 8) 8 ma; FCT ma 8 ma]).
        { unfold qws. destruct (list_eq_dec Z.eq_dec l []); [reflexivity | contradiction]. }
        rewrite Q in INQ.
        destruct Hc as [-> | [-> | ->]]; cbn [f_a f_n]; intros x Hx.
        + apply (wlook_cov_some ws2 (FCT (caddr (KActive sc)) 8 ma) x); [apply INQ; cbn; auto | cbn [f_a f_n]; lia].
        + apply (wlook_cov_some ws2 (FCT (ma + 8) 8 ma) x); [apply INQ; cbn; auto | cbn [f_a f_n]; lia].
        + apply (wlook_cov_some ws2 (FCT ma 8 ma) x); [apply INQ; cbn; auto | cbn [f_a f_n]; lia].
      - assert (Q : qws = [FCT hd0 8 ma; FCT (t + 8) 8 ma; FCT ma 8 t; FCT (ma + 8) 8 hd0]).
        { unfold qws. destruct (list_eq_dec Z.eq_dec l []); [contradiction | reflexivity]. }
        rewrite Q in INQ.
        destruct Hc as [-> | [-> | [-> | ->]]]; cbn [f_a f_n]; intros x Hx.
        + apply (wlook_cov_some ws2 (FCT hd0 8 ma) x); [apply INQ; cbn; auto | cbn [f_a f_n]; lia].
        + apply (wlook_cov_some ws2 (FCT (t + 8) 8 ma) x); [apply INQ; cbn; auto 10 | cbn [f_a f_n]; lia].
        + apply (wlook_cov_some ws2 (FCT ma 8 t) x); [apply INQ; cbn; auto 10 | cbn [f_a f_n]; lia].
        + apply (wlook_cov_some ws2 (FCT (ma + 8) 8 hd0) x); [apply INQ; cbn; auto 10 | cbn [f_a f_n]; lia].
    Qed.

    Lemma commit_b : forall m', RepW A (ms_mem s) ws2 m' ->
      II sp0 argv envp cb D A2 (upd s m' (ms_vm s)) /\ ntframe A s (upd s m' (ms_vm s)).
    Proof.
      intros m' RW. pose proof KW as HW. pose proof WO2 as WO. pose proof HW2 as HWb.
      split; [| exact (ntframe_commit A s ws2 m' HW RW WO)].
      pose proof AUD_A2 as (Hav & Hus & Hdd).
      apply II_intro; [| cbn [ms_vm upd]; apply (VMok_queA A1 sc ma l h t); apply (VMok_fbA A ma mt aib slots i Hma Hr); exact (ii_vm HII) | exact Hav | exact Hus | exact Hdd].
      apply (IS_commit sp0 argv envp cb A A2 s ws2 m' (ii_is HII) RW WO HWb).
      apply (repw_commit2 A A2 (ms_mem s) ws2 m' HWb RW has_A2_written ws2_lookup).
      intros x Hx. apply (proj1 (dom_fbA A ma mt aib slots i Hma Hr x)). apply (proj1 (dom_queA A1 sc ma l h t x)). exact Hx.
    Qed.
  End Requeue.

  (* [comment removed for export] *)
  Lemma if_true : forall (T : Type) (a b : T), (if true then a else b) = a. Proof. reflexivity. Qed.
  Lemma if_false : forall (T : Type) (a b : T), (if false then a else b) = b. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma keep_tail : forall s1 ws (K : word * word -> M R) P,
    RepW A (ms_mem s) ws (ms_mem s1) -> WIN s1 -> wfree_range ws (ma + 28) 4 ->
    (forall m', RepW A (ms_mem s) (Wfr :: ws) m' -> tsafe (K (w0, w0) (upd s1 m' (ms_vm s1))) P) ->
    tsafe ((x <- (massert (is0 (v_andi (at_ (Z_to_bv 64 ma) 28) 3)) ;;
                  fr3 <- m_lw (at_ (Z_to_bv 64 ma) 28) ;;
                  m_sw (at_ (Z_to_bv 64 ma) 28) (v_or fr3 (w32 (2 ^ i))) ;;
                  mret (w0, w0)) ;; K x) s1) P.
  Proof.
    intros s1 ws K P RW HWIN1 Hfree HK. pose proof KW as HW.
    pose proof (meta_facts A ma mt HW Hma) as (M1 & M2 & M3 & M4 & Mdom). ceil.
    pose proof Kmask32 as (Hm32 & Hav32 & Hfr32). pose proof Kic as (Hic & Hi32 & Hc32).
    rewrite at_Z. reassoc. apply ts_assert.
    { rewrite v_andi_Z by llia. rewrite is0_Z by (pose proof (Z.land_nonneg (ma + 28) 3); pose proof (land_le_left (ma + 28) 3); llia).
      change 3 with (2^2 - 1). rewrite land_ones_low by llia. apply Z.eqb_eq. change (2^2) with 4.
      replace (ma + 28) with ((ma / 8 * 2 + 7) * 4) by (pose proof (Z.div_mod ma 8 ltac:(lia)); lia). apply Z_mod_mult. }
    reassoc. change (ma + 28) with (ma + moff FFreed).
    eapply (ts_lw_metaW A HW s1 (ms_mem s) ws ma mt FFreed); [exact RW | exact HWIN1 | exact Hma | reflexivity | exact Hfree | change (mt_f mt FFreed) with (mt_freed mt); llia |].
    change (mt_f mt FFreed) with (mt_freed mt). cbn [moff].
    reassoc. rewrite v_or_w32 by (split; [llia | apply Z.pow_lt_mono_r; llia] || llia).
    unfold m_sw.
    eapply (ts_st_domW A HW s1 (ms_mem s) ws 4 (ma + 28)); [exact RW | exact HWIN1 | lia | intros j Hj; rewrite <- Z.add_assoc; apply Mdom; lia |].
    intros m' RW'. apply ts_bind_ret. apply HK.
    rewrite u_w32 in RW'. change (Z.of_nat 4) with 4 in RW'.
    destruct (add_clear_bit (mt_freed mt) i (mt_cnt mt) ltac:(exact (proj1 (proj2 (proj2 (proj2 (proj2 Kgrp)))))) ltac:(llia)
                (fb_bit_fr A HW ma mt aib slots i Hma Hr Hi0 Hi)) as [E _].
    unfold Wfr, fr', fb_fr. rewrite E. exact RW'.
  Qed.

  Theorem ts_nt_keep : forall (K : word * word -> M R) P,
    (forall s' A', II sp0 argv envp cb D A' s' -> ntframe A s s' -> ntrel A A' ma slots i ->
       a_xmaps A' = a_xmaps A -> (forall x, dom A x -> dom A' x) -> tsafe (K (w0, w0) s') P) ->
    tsafe ((r <- nt_keep (Z_to_bv 64 ma) (w32 mask) (w32 (2 ^ i)) (Z_to_bv 64 sc) ;; K r) s) P.
  Proof.
    intros K P HK. pose proof KW as HW. pose proof KR as HR. pose proof KWIN as HWIN.
    pose proof Kmask32 as (Hm32 & Hav32 & Hfr32). pose proof Kic as (Hic & Hi32 & Hc32).
    pose proof (meta_facts A ma mt HW Hma) as (M1 & M2 & M3 & M4 & Mdom). ceil.
    pose proof (w_sc_range (mt_w32 mt)) as Hscr. change (w_sc (mt_w32 mt)) with sc in Hscr.
    pose proof (repw_init A (ms_mem s) HW HR) as RW0.
    assert (DOMA1 : forall x, dom A x -> dom A1 x) by (intros x Hx; apply (proj2 (dom_fbA A ma mt aib slots i Hma Hr x)); exact Hx).
    unfold nt_keep. reassoc.
    rewrite is0_w32, (Z.mod_small mask (2^32)) by llia.
    destruct (Z.eqb_spec mask 0) as [Hm0 | Hmnz].
    - (* [comment removed for export] *)
      cbn [negb]. unfold nt_requeue. reassoc.
      pose proof (Hkeep Hm0) as [Hsc48 Hstr].
      apply ts_assert. { unfold wlit. rewrite c_ltu_Z by llia. apply Z.ltb_lt. exact Hsc48. }
      cbv zeta. rewrite (addr_active sc) by llia. reassoc.
      eapply (ts_ld_ctxfW A HW s (ms_mem s) [] (KActive sc)); [exact RW0 | exact HWIN | cbn; llia | reflexivity | apply wfree_range_nil |].
      rewrite (wf_act_head A HW sc ltac:(llia)). change (hd 0 (a_active A sc)) with hd0.
      assert (Hhd64 : 0 <= hd0 < 2^64 /\ (hd0 <> 0 -> l <> [])).
      { unfold hd0. destruct l as [|x r] eqn:El; cbn [hd]; [llia|].
        destruct (wf_act_mem A HW sc x ltac:(fold l; rewrite El; left; reflexivity)) as (mtx & _ & _ & Hx & _).
        pose proof (meta_facts A x mtx HW Hx) as (X1 & X2 & _). split; [llia | intros _; discriminate]. }
      destruct Hhd64 as [Hhd64 Hlne].
      rewrite c_eq_Z by llia.
      destruct (Z.eqb_spec hd0 ma) as [Ehd | Hhd].
      + (* [comment removed for export] *)
        apply ts_bind_ret.
        apply (keep_tail s [] K P RW0 HWIN (wfree_range_nil _ _)).
        intros m' RW'. destruct (commit_a m' RW') as [HII' HF']. apply (HK _ A1 HII' HF' ntrel_A1 eq_refl DOMA1).
      + reassoc.
        destruct (Klinks Hm0 Hhd) as [Hpv Hnx].
        rewrite at_Z. change (ma + 8) with (ma + moff FNext).
        eapply (ts_ld_metaW A HW s (ms_mem s) [] ma mt FNext); [exact RW0 | exact HWIN | exact Hma | reflexivity | apply wfree_range_nil | unfold mt_next in Hnx; llia |].
        change (mt_f mt FNext) with (mt_next mt). rewrite Hnx. reassoc. apply ts_assert; [reflexivity|].
        reassoc. replace (Z_to_bv 64 ma) with (Z_to_bv 64 (ma + moff FPrev)) at 1 by (f_equal; cbn; lia).
        eapply (ts_ld_metaW A HW s (ms_mem s) [] ma mt FPrev); [exact RW0 | exact HWIN | exact Hma | reflexivity | apply wfree_range_nil | unfold mt_prev in Hpv; llia |].
        change (mt_f mt FPrev) with (mt_prev mt). rewrite Hpv. reassoc. apply ts_assert; [reflexivity|].
        apply (ts_nt_queue A HW s (ms_mem s) [] (KActive sc) ma hd0 t mt _ P RW0 HWIN ltac:(cbn; llia) eq_refl Hma ltac:(llia)).
        * intros Hh0. destruct (l_ne_facts Hm0 Hhd (Hlne Hh0)) as (Eh & Hin_h & Hin_t & Hhma & Htma & _ & mth & mtt & Hmh & Hmt & Hph & Hlt).
          exists mth, mtt. rewrite Hph, Hlt. repeat split; auto using wfree_range_nil.
        * intros Hh0 m1 RW1.
          assert (El : l = []).
          { destruct (list_eq_dec Z.eq_dec l []) as [El | El]; [exact El|]. exfalso.
            destruct (l_ne_facts Hm0 Hhd El) as (_ & _ & _ & _ & _ & Hne0 & _). exact (Hne0 Hh0). }
          apply (keep_tail (upd s m1 (ms_vm s)) _ K P RW1 HWIN).
          { repeat apply wfree_range_cons; try apply wfree_range_nil; cbn [f_a f_n];
              pose proof (ctx_slot_range (KActive sc) ltac:(cbn; llia)) as (C1 & C2 & C3); llia. }
          intros m' RW'. cbn [upd ms_vm ms_lo ms_hi].
          assert (RW2 : RepW A (ms_mem s) (Wfr :: qws) m').
          { unfold qws. destruct (list_eq_dec Z.eq_dec l []); [| contradiction]. cbn [clen] in RW'. exact RW'. }
          destruct (commit_b Hm0 Hhd m' RW2) as [HII' HF'].
          apply (HK _ A2 HII' HF' (ntrel_A2 Hm0) eq_refl). intros x Hx. apply (proj2 (dom_queA A1 sc ma l h t x)). apply DOMA1. exact Hx.
        * intros Hh0 m1 RW1. pose proof (Hlne Hh0) as El.
          destruct (l_ne_facts Hm0 Hhd El) as (Eh & Hin_h & Hin_t & Hhma & Htma & _ & mth & mtt & Hmh & Hmt & Hph & Hlt).
          pose proof (metas_apart A hd0 mth ma mt HW Hmh Hma Hhma) as Dhm. pose proof (metas_apart A t mtt ma mt HW Hmt Hma Htma) as Dtm.
          apply (keep_tail (upd s m1 (ms_vm s)) _ K P RW1 HWIN).
          { repeat apply wfree_range_cons; try apply wfree_range_nil; cbn [f_a f_n]; llia. }
          intros m' RW'. cbn [upd ms_vm ms_lo ms_hi].
          assert (RW2 : RepW A (ms_mem s) (Wfr :: qws) m').
          { unfold qws. destruct (list_eq_dec Z.eq_dec l []); [contradiction |]. exact RW'. }
          destruct (commit_b Hm0 Hhd m' RW2) as [HII' HF'].
          apply (HK _ A2 HII' HF' (ntrel_A2 Hm0) eq_refl). intros x Hx. apply (proj2 (dom_queA A1 sc ma l h t x)). apply DOMA1. exact Hx.
    - (* [comment removed for export] *)
      cbn [negb]. apply ts_bind_ret.
      apply (keep_tail s [] K P RW0 HWIN (wfree_range_nil _ _)).
      intros m' RW'. destruct (commit_a m' RW') as [HII' HF']. apply (HK _ A1 HII' HF' ntrel_A1 eq_refl DOMA1).
  Qed.
End Keep.
End WithLayout.
