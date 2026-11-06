(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_ameta_iface MallocInv_tryavail MallocInv_ntfree MallocInv_ntpost.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac pu_keep K := repeat match goal with H : ?T |- _ => lazymatch type of T with Prop => idtac | _ => fail end; lazymatch K with context [H] => fail | _ => idtac end;
                                                          tryif (match goal with X := _ |- _ => constr_eq X H end) then fail else clear H end.   (* [comment removed for export] *)
Local Ltac llia ::= first [ solve [LiaFast.flia2] | pose proof layout_small; lia | pose proof layout_nums; lia | lia ].   (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Section TavDeq.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Variables (sc h : Z) (rest : list Z).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active A sc = h :: rest.
  Implicit Types (P : R -> mstate -> Prop).

  Let l := h :: rest.
  Let n := length l.
  Let xn := nth (1 mod n) l 0.
  Let xp := nth ((0 + n - 1) mod n)%nat l 0.
  Let A1 := deqA A sc h [] rest.
  Let PM := caddr (KActive sc).

  Lemma HWd : WF A. Proof using HII. pu_keep (HII). exact (is_wf _ _ _ _ _ _ (ii_is HII)). Qed.
  Lemma Hact' : a_active A sc = [] ++ h :: rest. Proof using Hact. pu_keep (Hact). exact Hact. Qed.

  (* [comment removed for export] *)
  Lemma dqm : forall x, In x l -> exists mt aib sl, a_meta A x = Some mt /\ mt_role mt = RGroup aib sl /\ mt_sc mt = sc /\
    0x1000 <= x /\ x + 40 <= alloc_ceiling /\ (forall j, 0 <= j < 40 -> dom A (x + j)) /\
    exists pg k, In pg (a_areas A) /\ 0 <= k < 101 /\ x = meta_addr pg k.
  Proof using HII Hact. pu_keep (HII, Hact). intros x Hx. exact (dq_mem A HWd sc h [] rest Hact' x Hx). Qed.

  Lemma dqm_img : forall x, In x l -> x + 40 <= IMG_LO \/ IMG_HI <= x.
  Proof using HII Hact Hsc PM xn xp. pu_keep (HII, Hact, Hsc, PM, xn, xp).
    intros x Hx. destruct (dqm x Hx) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & pg & k & Hpg & Hk & ->).
    destruct (wf_areas_al A HWd pg Hpg) as [_ Hph]. unfold heap_range in Hph. pose proof (meta_addr_range pg k Hk). llia.
  Qed.

  Lemma dqm_apart : forall x y, In x l -> In y l -> x <> y -> x + 40 <= y \/ y + 40 <= x.
  Proof using HII Hact. pu_keep (HII, Hact).
    intros x y Hx Hy Hne. destruct (dqm x Hx) as (mtx & _ & _ & Hmx & _). destruct (dqm y Hy) as (mty & _ & _ & Hmy & _).
    exact (metas_apart A x mtx y mty HWd Hmx Hmy Hne).
  Qed.

  Lemma h_in : In h l. Proof using rest. pu_keep (rest). left. reflexivity. Qed.

  Lemma h_links : exists mth aib sl, a_meta A h = Some mth /\ mt_role mth = RGroup aib sl /\ mt_sc mth = sc /\
    mt_next mth = xn /\ mt_prev mth = xp.
  Proof using HII Hact Hsc n. pu_keep (HII, Hact, Hsc, n). exact (g_links A HWd sc h [] rest Hsc Hact'). Qed.

  Lemma single_links' : rest = [] -> xn = h /\ xp = h.
  Proof using Hact. pu_keep (Hact). intros Er. exact (single_links A sc h [] rest Hact' Er). Qed.

  Lemma multi_links' : rest <> [] -> In xn rest /\ In xp rest /\ xn <> h /\ xp <> h /\ (2 <= n)%nat.
  Proof using HII Hact Hsc. pu_keep (HII, Hact, Hsc). intros Er. exact (multi_links A HWd sc h [] rest Hsc Hact' Er). Qed.

  Lemma hd_rest : rest <> [] -> hd 0 rest = xn.
  Proof using Hact Hsc n. pu_keep (Hact, Hsc, n). intros Er. exact (hd_sub A sc h [] rest Hsc Hact' Er). Qed.

  Lemma xn_in' : In xn l. Proof using Hsc n. pu_keep (Hsc, n). exact (xn_in sc h [] rest Hsc). Qed.
  Lemma xp_in' : In xp l. Proof using Hsc n. pu_keep (Hsc, n). exact (xp_in sc h [] rest Hsc). Qed.

  Ltac fold_xnp H :=
    change (nth (S (length (@nil Z)) mod length ((@nil Z) ++ h :: rest)) ((@nil Z) ++ h :: rest) 0) with xn in H;
    change (nth ((length (@nil Z) + length ((@nil Z) ++ h :: rest) - 1) mod length ((@nil Z) ++ h :: rest)) ((@nil Z) ++ h :: rest) 0) with xp in H.

  Lemma A1_meta : forall x, a_meta A1 x = option_map (MallocInv_wf3.relink (deqP h [] rest) (deqN h [] rest) x) (a_meta A x).
  Proof using sc. pu_keep (sc). intros x. reflexivity. Qed.

  Lemma A1_ctx : forall k, cvalid k -> a_ctx A1 k = if cslot_eq_dec k (KActive sc) then hd 0 rest else a_ctx A k.
  Proof using HII Hsc h. pu_keep (HII, Hsc, h). intros k Hk. exact (deqA_ctx_valid A HWd sc h [] rest Hsc k Hk). Qed.

  (* [comment removed for export] *)
  Definition dqCH (x : Z) : Prop :=
    h <= x < h + 16 \/ PM <= x < PM + 8 \/ (rest <> [] /\ (xn <= x < xn + 8 \/ xp + 8 <= x < xp + 16)).

  Lemma deq_commit : forall ws m4, RepW A (ms_mem s) ws m4 ->
    (forall x, wlook ws x <> None -> dqCH x) ->
    (forall x, h <= x < h + 16 -> wlook ws x = Some 0) ->
    (forall x, PM <= x < PM + 8 -> wlook ws x = Some (byte_of (hd 0 rest) (x - PM))) ->
    (rest <> [] -> forall x, xn <= x < xn + 8 -> wlook ws x = Some (byte_of xp (x - xn))) ->
    (rest <> [] -> forall x, xp + 8 <= x < xp + 16 -> wlook ws x = Some (byte_of xn (x - (xp + 8)))) ->
    Rep A1 m4.
  Proof using HII Hact Hsc MLok. pu_keep (HII, Hact, Hsc, MLok).
    intros ws m4 HRW HCH H0 H1 H2 H3.
    pose proof HWd as HW. pose proof (WF_deqA A HW sc h [] rest Hsc Hact') as HW2. fold A1 in HW2.
    destruct h_links as (mth & aibh & slh & Hm & Hrm & Hsm & Hnx & Hpv).
    apply (repw_commit A A1 (ms_mem s) ws m4 HRW).
    - intros x b (f & Hf & Hfb).
      destruct (MallocInv_wf3.relists_has_inv A (deqP h [] rest) (deqN h [] rest) (deq_act A sc [] rest) (a_freelist A) None I f Hf)
        as [(k & Hk & ->) | [Har | [(x0 & mt' & fl & Hx0 & ->) | Hg]]].
      + destruct (cslot_eq_dec k (KActive sc)) as [-> | Hne].
        * right. destruct Hfb as [Hx _]. cbn [f_a f_n clen] in Hx. rewrite (H1 x) by (unfold PM; llia). discriminate.
        * left. exists (FCT (caddr k) (clen k) (a_ctx A k)). split; [left; exists k; auto|].
          replace (a_ctx A k) with (MallocInv_wf3.c' A (deq_act A sc [] rest) (a_freelist A) k); [exact Hfb|].
          change (MallocInv_wf3.c' A (deq_act A sc [] rest) (a_freelist A) k) with (a_ctx A1 k). rewrite (A1_ctx k Hk).
          destruct (cslot_eq_dec k (KActive sc)); [contradiction | reflexivity].
      + left. exists f. split; [right; left; exact Har | exact Hfb].
      + change (MallocInv_wf3.g' A (deqP h [] rest) (deqN h [] rest) None x0) with (a_meta A1 x0) in Hx0.
        destruct (deqA_meta_inv A sc h [] rest x0 mt' Hx0) as (mt0 & Hx0' & ->).
        assert (SAME : forall fl', fbyte (FCT (x0 + moff fl') (mlen fl') (mt_f mt0 fl')) x b -> facts A x b \/ wlook ws x <> None).
        { intros fl' Hfb'. left. exists (FCT (x0 + moff fl') (mlen fl') (mt_f mt0 fl')). split; [right; right; left; exists x0, mt0, fl'; auto | exact Hfb']. }
        destruct fl; [ | | apply (SAME FMem); exact Hfb | apply (SAME FAvail); exact Hfb | apply (SAME FFreed); exact Hfb | apply (SAME FW32); exact Hfb].
        * unfold MallocInv_wf3.relink in Hfb. rewrite mt_f_MT in Hfb. cbn beta iota in Hfb. unfold deqP in Hfb. fold_xnp Hfb.
          destruct (Z.eqb_spec x0 h) as [-> | Hnh].
          -- right. destruct Hfb as [Hx _]. cbn [moff mlen f_a f_n] in Hx. rewrite (H0 x) by llia. discriminate.
          -- destruct (Z.eqb_spec x0 xn) as [-> | Hnx'].
             ++ assert (Er : rest <> []) by (intros Er; destruct (single_links' Er) as [E _]; exact (Hnh E)).
                right. destruct Hfb as [Hx _]. cbn [moff mlen f_a f_n dflt] in Hx. rewrite (H2 Er x) by llia. discriminate.
             ++ apply (SAME FPrev). exact Hfb.
        * unfold MallocInv_wf3.relink in Hfb. rewrite mt_f_MT in Hfb. cbn beta iota in Hfb. unfold deqN in Hfb. fold_xnp Hfb.
          destruct (Z.eqb_spec x0 h) as [-> | Hnh].
          -- right. destruct Hfb as [Hx _]. cbn [moff mlen f_a f_n] in Hx. rewrite (H0 x) by llia. discriminate.
          -- destruct (Z.eqb_spec x0 xp) as [-> | Hnp'].
             ++ assert (Er : rest <> []) by (intros Er; destruct (single_links' Er) as [_ E]; exact (Hnh E)).
                right. destruct Hfb as [Hx _]. cbn [moff mlen f_a f_n dflt] in Hx. rewrite (H3 Er x) by llia. discriminate.
             ++ apply (SAME FNext). exact Hfb.
      + left. exists f. split; [right; right; right; exact Hg | exact Hfb].
    - intros x b (f & Hf & [Hx ->]) Hw. pose proof (HCH x Hw) as C.
      assert (Hm1 : a_meta A1 h = Some (MallocInv_wf3.relink (deqP h [] rest) (deqN h [] rest) h mth)).
      { rewrite A1_meta, Hm. reflexivity. }
      destruct C as [Cm | [Cf | (Er & [Cn | Cp])]].
      + rewrite (H0 x Cm). f_equal.
        destruct (Z.lt_ge_cases x (h + 8)) as [C0 | C8].
        * pose proof (fact_at_meta A1 HW2 f h _ FPrev x Hf Hm1 Hx ltac:(cbn; llia)) as ->.
          cbn [f_a f_v]. unfold MallocInv_wf3.relink. rewrite mt_f_MT. unfold deqP. rewrite Z.eqb_refl. cbn [dflt]. rewrite byte_of_zero. reflexivity.
        * pose proof (fact_at_meta A1 HW2 f h _ FNext x Hf Hm1 Hx ltac:(cbn; llia)) as ->.
          cbn [f_a f_v]. unfold MallocInv_wf3.relink. rewrite mt_f_MT. unfold deqN. rewrite Z.eqb_refl. cbn [dflt]. rewrite byte_of_zero. reflexivity.
      + rewrite (H1 x Cf). f_equal.
        pose proof (fact_at_ctx A1 HW2 f (KActive sc) x Hf Hsc Hx ltac:(cbn [clen]; unfold PM in Cf; llia)) as ->.
        cbn [f_a f_v]. rewrite (A1_ctx (KActive sc) Hsc). destruct (cslot_eq_dec (KActive sc) (KActive sc)); [| contradiction]. reflexivity.
      + rewrite (H2 Er x Cn). f_equal.
        destruct (multi_links' Er) as (Hxn_in & Hxp_in & Hxnm & Hxpm & Hn2).
        destruct (dqm xn xn_in') as (mtn & aibn & sln & Hmn & _).
        assert (Hmn' : a_meta A1 xn = Some (MallocInv_wf3.relink (deqP h [] rest) (deqN h [] rest) xn mtn)).
        { rewrite A1_meta, Hmn. reflexivity. }
        pose proof (fact_at_meta A1 HW2 f xn _ FPrev x Hf Hmn' Hx ltac:(cbn [moff mlen]; llia)) as ->.
        cbn [f_a f_v]. unfold MallocInv_wf3.relink. rewrite mt_f_MT. unfold deqP.
        rewrite (proj2 (Z.eqb_neq xn h) Hxnm). rewrite Z.eqb_refl. cbn [dflt moff]. f_equal. llia.
      + rewrite (H3 Er x Cp). f_equal.
        destruct (multi_links' Er) as (Hxn_in & Hxp_in & Hxnm & Hxpm & Hn2).
        destruct (dqm xp xp_in') as (mtp & aibp & slp & Hmp & _).
        assert (Hmp' : a_meta A1 xp = Some (MallocInv_wf3.relink (deqP h [] rest) (deqN h [] rest) xp mtp)).
        { rewrite A1_meta, Hmp. reflexivity. }
        pose proof (fact_at_meta A1 HW2 f xp _ FNext x Hf Hmp' Hx ltac:(cbn [moff mlen]; llia)) as ->.
        cbn [f_a f_v]. unfold MallocInv_wf3.relink. rewrite mt_f_MT. unfold deqN.
        rewrite (proj2 (Z.eqb_neq xp h) Hxpm).
        destruct (Z.eqb_spec xp xn) as [E | _]; rewrite ?Z.eqb_refl; cbn [dflt]; reflexivity.
    - intros x Hx. apply (proj1 (MallocInv_wf3.dom_relists A (deqP h [] rest) (deqN h [] rest) (deq_act A sc [] rest) (a_freelist A) None I x)). exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma dqCH_where : forall x, dqCH x ->
    (PM <= x < PM + 8) \/ (dom A x /\ exists pg, In pg (a_areas A) /\ pg <= x < pg + 4096).
  Proof using HII Hact Hsc. pu_keep (HII, Hact, Hsc).
    assert (MLm : forall y x, In y l -> y <= x < y + 40 -> dom A x /\ exists pg, In pg (a_areas A) /\ pg <= x < pg + 4096).
    { intros y x Hy Hx. destruct (dqm y Hy) as (_ & _ & _ & _ & _ & _ & _ & _ & Hd & pg & k & Hpg & Hk & ->).
      pose proof (meta_addr_range pg k Hk). split; [replace x with (meta_addr pg k + (x - meta_addr pg k)) by llia; apply Hd; llia|].
      exists pg. split; [exact Hpg | llia]. }
    intros x [Cm | [Cf | (Er & C2)]]; [right; apply (MLm h); [exact h_in | llia] | left; exact Cf |].
    destruct (multi_links' Er) as (Hxn_in & Hxp_in & _). right.
    destruct C2 as [Cn | Cp]; [apply (MLm xn); [right; exact Hxn_in | llia] | apply (MLm xp); [right; exact Hxp_in | llia]].
  Qed.

  Lemma dq_finish : forall (K : unit -> M R) P m4,
    (forall s', II sp0 argv envp cb D A1 s' -> ntframe A s s' -> tsafe (K tt s') P) ->
    Rep A1 m4 ->
    (forall a : word, m4 a = ms_mem s a \/ dqCH (bv_unsigned a)) ->
    (forall a : word, ms_mem s a <> None -> m4 a <> None) ->
    tsafe (K tt (upd s m4 (ms_vm s))) P.
  Proof using HII Hact Hsc MLok. pu_keep (HII, Hact, Hsc, MLok).
    intros K P m4 HK HR4 FRM KEEP. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (WF_deqA A HW sc h [] rest Hsc Hact') as HW2. fold A1 in HW2.
    pose proof (tkeep_deqA A HW sc h [] rest Hsc Hact') as TK. fold A1 in TK.
    pose proof (ctx_slot_range (KActive sc) Hsc) as (C1 & C2 & C3). cbn [clen] in C2. ceil.
    apply HK.
    - constructor.
      + apply (IS_mem sp0 argv envp cb A A1 s m4 HI HW2 HR4).
        * intros a. destruct (FRM a) as [E | X]; [left; exact E | right]. destruct (dqCH_where _ X) as [Hc | (Hd & _)].
          -- unfold mzone. do 3 right. unfold PM in Hc. llia.
          -- destruct (dom_heap A (bv_unsigned a) HW Hd) as (lo & hi & Hh & Hx). unfold heap_range in Hh. unfold mzone. llia.
        * intros a Ha. destruct (FRM a) as [E | X]; [left; rewrite <- E; exact Ha|]. destruct (dqCH_where _ X) as [Hc | (Hd & _)].
          -- right; left. unfold PM in Hc. llia.
          -- left. rewrite <- (Z_to_bv_bv_unsigned 64 a). apply (rep_dom A _ HR). exact Hd.
      + cbn [ms_vm upd]. apply (VMok_deqA A sc h [] rest). exact (ii_vm HII).
      + apply (tk_AvOK A A1 sc TK (ii_av HII)). apply (tk_ctx _ _ _ TK); [exact I | discriminate | discriminate].
      + apply (tk_UsOK A A1 sc TK (ii_us HII)). intros c Hc. apply (tk_ctx _ _ _ TK); [exact Hc | discriminate | discriminate].
      + apply (tk_deads A A1 sc TK). exact (ii_dd HII).
    - constructor; cbn [ms_lo ms_hi ms_vm ms_mem upd]; try reflexivity.
      + intros a Ho. destruct (FRM a) as [E | X]; [exact E | exfalso]. apply Ho. destruct (dqCH_where _ X) as [Hc | (Hd & _)].
        * left. unfold PM in Hc. llia.
        * right. exact Hd.
      + intros q k a Hq Ha. destruct (FRM a) as [E | X]; [exact E | exfalso]. destruct (dqCH_where _ X) as [Hc | (Hd & pg & Hpg & Hx)].
        * destruct (live_heap A q k HW Hq) as (N0 & P1 & P2 & P3 & _). pose proof (MallocInv_live.round16_ge k). unfold PM in Hc. llia.
        * exact (area_not_live A pg (bv_unsigned a) q k HW Hpg Hx Hq Ha).
      + exact KEEP.
  Qed.
  Variable mth : meta_rec.
  Hypothesis Hh : a_meta A h = Some mth.

  Theorem ts_tav_dequeue : forall (K : unit -> M R) P,
    (forall s', II sp0 argv envp cb D A1 s' -> ntframe A s s' -> tsafe (K tt s') P) ->
    tsafe ((x <- (if c_eq (Z_to_bv 64 (mt_next mth)) (Z_to_bv 64 h) then m_sd (Z_to_bv 64 PM) w0
                  else pv <- m_ld (Z_to_bv 64 h) ;;
                       m_sd (at_ pv 8) (Z_to_bv 64 (mt_next mth)) ;;
                       pv2 <- m_ld (Z_to_bv 64 h) ;;
                       nx2 <- m_ld (at_ (Z_to_bv 64 h) 8) ;;
                       m_sd nx2 pv2 ;;
                       hh <- m_ld (Z_to_bv 64 PM) ;;
                       (if c_eq hh (Z_to_bv 64 h) then n3 <- m_ld (at_ (Z_to_bv 64 h) 8) ;; m_sd (Z_to_bv 64 PM) n3
                        else mret tt)) ;;
            y <- m_sd (Z_to_bv 64 h) w0 ;;
            z <- m_sd (at_ (Z_to_bv 64 h) 8) w0 ;;
            K z) s) P.
  Proof using HII Hact Hh Hsc MLok xn xp. pu_keep (HII, Hact, Hh, Hsc, MLok, xn, xp).
    intros K P HK. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG]. ceil.
    destruct h_links as (mth' & aibh & slh & Hm & Hrm & Hsm & Hnx & Hpv). rewrite Hh in Hm. injection Hm as <-.
    destruct (dqm h h_in) as (_ & _ & _ & _ & _ & _ & Hmlo & Hmhi & Hdom_m & _).
    pose proof (dqm_img h h_in) as Hmimg.
    assert (Hxn0 : 0 <= xn < 2^64) by (destruct (dqm xn xn_in') as (mt1 & ab1 & sl1 & H1 & H2 & H3 & H4 & H5 & _); llia).
    assert (Hxp0 : 0 <= xp < 2^64) by (destruct (dqm xp xp_in') as (mt1 & ab1 & sl1 & H1 & H2 & H3 & H4 & H5 & _); llia).
    assert (Hfn : has A (FCT (h + 8) 8 xn)).
    { right; right; left. exists h, mth, FNext. split; [exact Hh|]. unfold mt_next in Hnx. rewrite <- Hnx. reflexivity. }
    assert (Hfp : has A (FCT h 8 xp)).
    { right; right; left. exists h, mth, FPrev. split; [exact Hh|]. unfold mt_prev in Hpv. rewrite <- Hpv. cbn [moff mlen]. rewrite Z.add_0_r. reflexivity. }
    assert (Hfh : has A (FCT PM 8 h)).
    { left. exists (KActive sc). split; [exact Hsc|]. rewrite (wf_act_head A HW sc Hsc), Hact. reflexivity. }
    pose proof (ctx_slot_range (KActive sc) Hsc) as (C1 & C2 & C3). cbn [clen] in C2. fold PM in C1, C2.
    pose proof (repw_init A _ HW HR) as RW0.
    rewrite Hnx.
    destruct (list_eq_dec Z.eq_dec rest []) as [Er | Er].
    - (* [comment removed for export] *)
      destruct (single_links' Er) as [Exn Exp].
      replace (c_eq (Z_to_bv 64 xn) (Z_to_bv 64 h)) with true by (rewrite Exn, c_eq_Z by llia; rewrite Z.eqb_refl; reflexivity).
      cbv iota.
      unfold m_sd at 1. change 8%nat with (Z.to_nat (clen (KActive sc))) at 1.
      eapply (ts_st_ctxw A s (ms_mem s) []); [exact RW0 | exact HWIN | exact Hsc |].
      pose proof (repw_st_ctx A s (ms_mem s) [] (KActive sc) w0 RW0 Hsc) as RW1.
      set (m1 := wbytes (ms_mem s) (Z_to_bv 64 (caddr (KActive sc))) (word_to_le_bytes (Z.to_nat (clen (KActive sc))) w0)) in RW1 |- *.
      unfold m_sd at 1.
      eapply (ts_st_domw A HW (upd s m1 (ms_vm s)) (ms_mem s)); [exact RW1 | exact HWIN | cbv; llia | intros j Hj; cbn in Hj; apply Hdom_m; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m1 (ms_vm s)) (ms_mem s) _ 8 h w0 RW1 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; apply Hdom_m; llia)) as RW2.
      cbn [ms_mem upd] in RW2.
      set (m2 := wbytes m1 (Z_to_bv 64 h) (word_to_le_bytes 8 w0)) in RW2 |- *.
      unfold m_sd at 1. rewrite ?at_Z.
      eapply (ts_st_domw A HW (upd s m2 (ms_vm s)) (ms_mem s)); [exact RW2 | exact HWIN | cbv; llia | intros j Hj; cbn in Hj; replace (h + 8 + j) with (h + (8 + j)) by llia; apply Hdom_m; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m2 (ms_vm s)) (ms_mem s) _ 8 (h + 8) w0 RW2 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; replace (h + 8 + j) with (h + (8 + j)) by llia; apply Hdom_m; llia)) as RW3.
      cbn [ms_mem upd] in RW3.
      set (m3 := wbytes m2 (Z_to_bv 64 (h + 8)) (word_to_le_bytes 8 w0)) in RW3 |- *.
      apply (dq_finish K P m3 HK).
      + apply (deq_commit _ m3 RW3).
        * intros x Hw. unfold dqCH.
          assert (DQrng : h <= x < (h + 16) \/ PM <= x < (PM + 8) \/
                         (~ (h <= x < (h + 16)) /\ ~ (PM <= x < (PM + 8)))) by lia.
          destruct DQrng as [DQrng | [DQrng | DQrng]];
            [ left; llia
            | right; left; llia |].
           
            exfalso; apply Hw; cbn [f_a f_n f_v caddr clen Z.of_nat Z.to_nat Pos.to_nat] in *; unfold PM, C_ACTIVE in *; rewrite !wlook_skip by (cbn [f_a f_n]; llia); reflexivity.
        * intros x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat] in *. unfold PM, C_ACTIVE in *.
          destruct (Z.lt_ge_cases x (h + 8)).
          -- rewrite wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v].
             replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
          -- rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
        * intros x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat] in *. unfold PM, C_ACTIVE in *.
          rewrite !wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v].
          replace (bv_unsigned w0) with 0 by reflexivity. rewrite Er. cbn [hd]. reflexivity.
        * intros Er'. exfalso. exact (Er' Er).
        * intros Er'. exfalso. exact (Er' Er).
      + intros a. pose proof (u64_range a). unfold dqCH.
        assert (DQrng : h <= (bv_unsigned a) < (h + 16) \/ PM <= (bv_unsigned a) < (PM + 8) \/
                       (~ (h <= (bv_unsigned a) < (h + 16)) /\ ~ (PM <= (bv_unsigned a) < (PM + 8)))) by lia.
        destruct DQrng as [DQrng | [DQrng | DQrng]];
          [ right; left; llia
          | right; right; left; llia |].
         
          left; unfold m3, m2, m1; cbn [caddr clen Z.to_nat Pos.to_nat] in *; unfold PM, C_ACTIVE in *;
          rewrite !wbytes_other_Z by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Z.to_nat Pos.to_nat Pos.of_succ_nat Pos.succ Nat.iter]; llia); reflexivity.
      + intros a Ha. unfold m3, m2, m1. cbn [caddr clen Z.to_nat Pos.to_nat] in *. unfold PM, C_ACTIVE in *.
        repeat (apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by (cbn [length Z.of_nat Z.to_nat Pos.to_nat Pos.of_succ_nat Pos.succ Nat.iter]; llia); cbn [length Z.of_nat Z.to_nat Pos.to_nat Pos.of_succ_nat Pos.succ Nat.iter]; llia|]). exact Ha.
    - (* [comment removed for export] *)
      destruct (multi_links' Er) as (Hxn_in & Hxp_in & Hxnm & Hxpm & Hn2).
      destruct (dqm xn xn_in') as (mtn & abn & sln & Hmn & Hrn & _ & Hxnlo & Hxnhi & Hdom_xn & _).
      destruct (dqm xp xp_in') as (mtp & abp & slp & Hmp & Hrp & _ & Hxplo & Hxphi & Hdom_xp & _).
      pose proof (dqm_img xn xn_in') as Hxnimg. pose proof (dqm_img xp xp_in') as Hxpimg.
      pose proof (dqm_apart h xn h_in xn_in' ltac:(intros E; exact (Hxnm (eq_sym E)))) as Dmn.
      pose proof (dqm_apart h xp h_in xp_in' ltac:(intros E; exact (Hxpm (eq_sym E)))) as Dmp.
      assert (Dnp : xn = xp \/ xn + 40 <= xp \/ xp + 40 <= xn).
      { destruct (Z.eq_dec xn xp) as [E | Hne]; [left; exact E | right]. exact (dqm_apart xn xp xn_in' xp_in' Hne). }
      replace (c_eq (Z_to_bv 64 xn) (Z_to_bv 64 h)) with false by (rewrite c_eq_Z by llia; symmetry; apply Z.eqb_neq; exact Hxnm).
      cbv iota. apply ts_assoc.
      (* [comment removed for export] *)
      eapply (ts_ld_factw A HW s (ms_mem s) [] h xp); [exact RW0 | exact HWIN | exact Hfp | apply wfree_range_nil | llia |].
      cbv beta. apply ts_assoc. unfold m_sd at 1. rewrite ?at_Z.
      (* [comment removed for export] *)
      eapply (ts_st_domw A HW s (ms_mem s) []); [exact RW0 | exact HWIN | cbv; llia | intros j Hj; cbn in Hj; replace (xp + 8 + j) with (xp + (8 + j)) by llia; apply Hdom_xp; llia |].
      pose proof (repw_st_dom A HW s (ms_mem s) [] 8 (xp + 8) (Z_to_bv 64 xn) RW0 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; replace (xp + 8 + j) with (xp + (8 + j)) by llia; apply Hdom_xp; llia)) as RW1.
      rewrite uZ in RW1 by llia.
      set (m1 := wbytes (ms_mem s) (Z_to_bv 64 (xp + 8)) (word_to_le_bytes 8 (Z_to_bv 64 xn))) in RW1 |- *.
      cbn [ms_mem ms_vm upd]. apply ts_assoc.
      (* [comment removed for export] *)
      eapply (ts_ld_factw A HW (upd s m1 (ms_vm s)) (ms_mem s) _ h xp); [exact RW1 | apply WIN_upd; exact HWIN | exact Hfp | apply wfree_range_cons; [cbn [f_a f_n]; llia | apply wfree_range_nil] | llia |].
      cbv beta. apply ts_assoc.
      (* [comment removed for export] *)
      rewrite ?at_Z.
      eapply (ts_ld_factw A HW (upd s m1 (ms_vm s)) (ms_mem s) _ (h + 8) xn); [exact RW1 | apply WIN_upd; exact HWIN | exact Hfn | apply wfree_range_cons; [cbn [f_a f_n]; llia | apply wfree_range_nil] | llia |].
      cbv beta. apply ts_assoc. unfold m_sd at 1.
      (* [comment removed for export] *)
      eapply (ts_st_domw A HW (upd s m1 (ms_vm s)) (ms_mem s)); [exact RW1 | apply WIN_upd; exact HWIN | cbv; llia | intros j Hj; cbn in Hj; apply Hdom_xn; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m1 (ms_vm s)) (ms_mem s) _ 8 xn (Z_to_bv 64 xp) RW1 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; apply Hdom_xn; llia)) as RW2.
      cbn [ms_mem upd] in RW2. rewrite uZ in RW2 by llia.
      set (m2 := wbytes m1 (Z_to_bv 64 xn) (word_to_le_bytes 8 (Z_to_bv 64 xp))) in RW2 |- *.
      apply ts_assoc.
      (* [comment removed for export] *)
      eapply (ts_ld_factw A HW (upd s m2 (ms_vm s)) (ms_mem s) _ PM h); [exact RW2 | apply WIN_upd; exact HWIN | exact Hfh | | llia |].
      { apply wfree_range_cons; [cbn [f_a f_n]; llia|]. apply wfree_range_cons; [cbn [f_a f_n]; llia|]. apply wfree_range_nil. }
      cbv beta. rewrite c_eq_Z by llia. rewrite Z.eqb_refl. cbv iota. apply ts_assoc.
      (* [comment removed for export] *)
      rewrite ?at_Z.
      eapply (ts_ld_factw A HW (upd s m2 (ms_vm s)) (ms_mem s) _ (h + 8) xn); [exact RW2 | apply WIN_upd; exact HWIN | exact Hfn | | llia |].
      { apply wfree_range_cons; [cbn [f_a f_n]; llia|]. apply wfree_range_cons; [cbn [f_a f_n]; llia|]. apply wfree_range_nil. }
      cbv beta. unfold m_sd at 1. change 8%nat with (Z.to_nat (clen (KActive sc))) at 1. unfold PM at 1.
      (* [comment removed for export] *)
      eapply (ts_st_ctxw A (upd s m2 (ms_vm s)) (ms_mem s)); [exact RW2 | apply WIN_upd; exact HWIN | exact Hsc |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_ctx A (upd s m2 (ms_vm s)) (ms_mem s) _ (KActive sc) (Z_to_bv 64 xn) RW2 Hsc) as RW3.
      cbn [ms_mem upd] in RW3. rewrite uZ in RW3 by llia.
      set (m3 := wbytes m2 (Z_to_bv 64 (caddr (KActive sc))) (word_to_le_bytes (Z.to_nat (clen (KActive sc))) (Z_to_bv 64 xn))) in RW3 |- *.
      unfold m_sd at 1.
      (* [comment removed for export] *)
      eapply (ts_st_domw A HW (upd s m3 (ms_vm s)) (ms_mem s)); [exact RW3 | apply WIN_upd; exact HWIN | cbv; llia | intros j Hj; cbn in Hj; apply Hdom_m; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m3 (ms_vm s)) (ms_mem s) _ 8 h w0 RW3 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; apply Hdom_m; llia)) as RW4.
      cbn [ms_mem upd] in RW4.
      set (m4 := wbytes m3 (Z_to_bv 64 h) (word_to_le_bytes 8 w0)) in RW4 |- *.
      unfold m_sd at 1. rewrite ?at_Z.
      (* [comment removed for export] *)
      eapply (ts_st_domw A HW (upd s m4 (ms_vm s)) (ms_mem s)); [exact RW4 | apply WIN_upd; exact HWIN | cbv; llia | intros j Hj; cbn in Hj; replace (h + 8 + j) with (h + (8 + j)) by llia; apply Hdom_m; llia |].
      cbn [ms_mem ms_vm upd].
      pose proof (repw_st_dom A HW (upd s m4 (ms_vm s)) (ms_mem s) _ 8 (h + 8) w0 RW4 ltac:(cbv; llia) ltac:(intros j Hj; cbn in Hj; replace (h + 8 + j) with (h + (8 + j)) by llia; apply Hdom_m; llia)) as RW5.
      cbn [ms_mem upd] in RW5.
      set (m5 := wbytes m4 (Z_to_bv 64 (h + 8)) (word_to_le_bytes 8 w0)) in RW5 |- *.
      apply (dq_finish K P m5 HK).
      + apply (deq_commit _ m5 RW5).
        * intros x Hw. unfold dqCH.
          assert (DQrng : h <= x < (h + 16) \/ PM <= x < (PM + 8) \/ xn <= x < (xn + 8) \/ (xp + 8) <= x < (xp + 16) \/
                         (~ (h <= x < (h + 16)) /\ ~ (PM <= x < (PM + 8)) /\ ~ (xn <= x < (xn + 8)) /\ ~ ((xp + 8) <= x < (xp + 16)))) by lia.
          destruct DQrng as [DQrng | [DQrng | [DQrng | [DQrng | DQrng]]]];
            [ left; llia
            | right; left; llia
            | right; right; split; [exact Er | left; llia]
            | right; right; split; [exact Er | right; llia] |].
           
            exfalso; apply Hw; cbn [f_a f_n f_v caddr clen Z.of_nat Z.to_nat Pos.to_nat] in *; unfold PM, C_ACTIVE in *; rewrite !wlook_skip by (cbn [f_a f_n]; llia); reflexivity.
        * intros x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat] in *. unfold PM, C_ACTIVE in *.
          destruct (Z.lt_ge_cases x (h + 8)).
          -- rewrite wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v].
             replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
          -- rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. replace (bv_unsigned w0) with 0 by reflexivity. rewrite byte_of_zero. reflexivity.
        * intros x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat] in *. unfold PM, C_ACTIVE in *.
          rewrite 2!wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v].
          rewrite (hd_rest Er). reflexivity.
        * intros _ x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat] in *. unfold PM, C_ACTIVE in *.
          rewrite 3!wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. reflexivity.
        * intros _ x Hx. cbn [caddr clen Z.to_nat Z.of_nat Pos.to_nat] in *. unfold PM, C_ACTIVE in *.
          destruct Dnp as [Enp | Dnp'].
          -- (* [comment removed for export] *)
             rewrite 3!wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_skip by (cbn [f_a f_n]; llia).
             rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. reflexivity.
          -- rewrite 4!wlook_skip by (cbn [f_a f_n]; llia). rewrite wlook_hit by (cbn [f_a f_n]; llia). cbn [f_a f_v]. reflexivity.
      + intros a. pose proof (u64_range a). unfold dqCH.
        assert (DQrng : h <= (bv_unsigned a) < (h + 16) \/ PM <= (bv_unsigned a) < (PM + 8) \/ xn <= (bv_unsigned a) < (xn + 8) \/ (xp + 8) <= (bv_unsigned a) < (xp + 16) \/
                       (~ (h <= (bv_unsigned a) < (h + 16)) /\ ~ (PM <= (bv_unsigned a) < (PM + 8)) /\ ~ (xn <= (bv_unsigned a) < (xn + 8)) /\ ~ ((xp + 8) <= (bv_unsigned a) < (xp + 16)))) by lia.
        destruct DQrng as [DQrng | [DQrng | [DQrng | [DQrng | DQrng]]]];
          [ right; left; llia
          | right; right; left; llia
          | right; right; right; split; [exact Er | left; llia]
          | right; right; right; split; [exact Er | right; llia] |].
         
          left; unfold m5, m4, m3, m2, m1; cbn [caddr clen Z.to_nat Pos.to_nat] in *; unfold PM, C_ACTIVE in *;
          rewrite !wbytes_other_Z by (rewrite ?length_N_to_le_bytes; cbn [length Z.of_nat Z.to_nat Pos.to_nat Pos.of_succ_nat Pos.succ Nat.iter]; llia); reflexivity.
      + intros a Ha. unfold m5, m4, m3, m2, m1. cbn [caddr clen Z.to_nat Pos.to_nat] in *. unfold PM, C_ACTIVE in *.
        repeat (apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by (cbn [length Z.of_nat Z.to_nat Pos.to_nat Pos.of_succ_nat Pos.succ Nat.iter]; llia); cbn [length Z.of_nat Z.to_nat Pos.to_nat Pos.of_succ_nat Pos.succ Nat.iter]; llia|]). exact Ha.
  Qed.
End TavDeq.
End WithLayout.
