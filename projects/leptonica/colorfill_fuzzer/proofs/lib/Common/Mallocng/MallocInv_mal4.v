(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_vmops MallocInv_coh MallocInv_usage MallocInv_ops MallocInv_hints MallocInv_sc MallocInv_sc3
  MallocInv_enframe MallocInv_ameta_iface MallocInv_ameta5 MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_freetop MallocInv_take
  MallocInv_actw MallocInv_aslot_iface MallocInv_ametax_iface MallocInv_malloc_iface MallocInv_agm2 MallocInv_agm3 MallocInv_mal1 MallocInv_efII MallocInv_mal3 MallocSureCap MallocSureCredit MallocSurePot.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Unset Lia Cache.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

(* [comment removed for export] *)
Lemma tw_pureQ : forall {B R : Type} W (op : M B) s (Q : B -> Prop) (K : B -> M R) P,
  (forall (K' : B -> M B) (P' : B -> mstate -> Prop), (forall x, Q x -> tsafe (K' x s) P') -> tsafe ((x <- op ;; K' x) s) P') ->
  (forall x, Q x -> tsall W (K x s) P) -> tsall W ((x <- op ;; K x) s) P.
Proof.
  intros B R W op s Q K P Hop HK. eapply (tw_lift W op s (fun x s' => s' = s /\ Q x)).
  - intros K' P' HK'. apply Hop. intros x Hx. apply HK'. auto.
  - intros x s' [-> Hx]. exact (HK x Hx).
Qed.

Lemma first_zero : negb (is0 (v_and (w32 0) (v_subw w0 (w32 0)))) = false.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TakeRel.
  Variables (A : astate) (sc g : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i n : Z) (m0 : word -> option byte) (s2 : mstate).
  Hypothesis HW : WF A.
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hne : a_active A sc <> [].
  Hypothesis Hhd : g = hd 0 (a_active A sc).
  Hypothesis Hg : a_meta A g = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hav : mt_avail mt <> 0.
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hbit : Z.testbit (mt_avail mt) i = true.

  Let A' := tkA A g mt aib slots i.

  Lemma take_gsc : mt_sc mt = sc.
  Proof.
    destruct (wf_act_mem A HW sc g ltac:(rewrite Hhd; destruct (a_active A sc); [exfalso; exact (Hne eq_refl) | left; reflexivity])) as (mt' & aib' & sl' & Hm' & _ & Hs).
    rewrite Hg in Hm'. injection Hm' as <-. exact Hs.
  Qed.

  Lemma take_stride : 16 * size_class sc <= mt_stride mt.
  Proof.
    rewrite <- take_gsc. apply (wf_reusable A HW g mt aib slots Hg Hr); [rewrite take_gsc; clear - Hsc; lia|].
    intros Hz. apply Hav. apply Z.bits_inj'. intros j Hj. rewrite Z.bits_0.
    destruct (wf_grp A HW g mt aib slots Hg Hr) as (_ & _ & _ & _ & Hav' & Hfr' & _).
    pose proof (f_equal (fun z => Z.testbit z j) Hz) as E. cbn beta in E. rewrite Z.lor_spec, Z.bits_0 in E.
    apply Bool.orb_false_iff in E. exact (proj1 E).
  Qed.

  Lemma take_aslot_ok : aslot_ok A A' sc n g i m0 s2.
  Proof.
    pose proof (tk_slot_idle A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr Hi0 Hbit) as Hidle.
    assert (KEEP : aslot_keep A A' sc m0).
    { constructor; try reflexivity.
      - intros x mtx Hx Hrx. unfold A'. rewrite (tkA_meta_other A g mt aib slots i x); [exact Hx|]. intros ->. rewrite Hg in Hx. injection Hx as ->. rewrite Hr in Hrx. discriminate.
      - intros x Hd. apply (proj2 (dom_tkA A g mt aib slots i Hg Hr x)). exact Hd.
      - intros x Hd. left. apply (proj1 (dom_tkA A g mt aib slots i Hg Hr x)). exact Hd.
      - intros x mtx aibx slx Hx Hrx. destruct (Z.eq_dec x g) as [-> | Hxg].
        + rewrite Hg in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
          eexists _, aib, _. split; [apply tkA_meta_same|]. split; [apply tk_mt_role|]. split; [reflexivity|]. split; [reflexivity|].
          split; [unfold tk_slots; apply list_set_length|].
          intros j st Hj Hst. unfold tk_slots. destruct (Nat.eq_dec (Z.to_nat i) j) as [<- | Hnj]; [rewrite Hidle in Hj; injection Hj as <-; exfalso; exact (Hst eq_refl)|].
          rewrite list_set_nth_other by exact Hnj. exact Hj.
        + exists mtx, aibx, slx. unfold A'. rewrite (tkA_meta_other A g mt aib slots i x Hxg). repeat split; auto.
      - intros _. left. split; [reflexivity|]. pose proof (nest_rank_range sc) as Hnr. unfold A', spare. cbn [a_ctx a_freelist tkA set_live ameta_upd set_meta]. clear - Hnr. lia. }
    constructor.
    - exact KEEP.
    - intros x mtx aibx slx Hx Hrx. left. destruct (tkA_meta_inv A g mt aib slots i x mtx Hx) as [(-> & ->) | (Hxg & Hx')]; [exists mt, aib, slots; auto | exists mtx, aibx, slx; auto].
    - intros mt0 aib0 sl0 Hx0 Hr0. rewrite Hg in Hx0. injection Hx0 as <-. rewrite Hr in Hr0. injection Hr0 as <- <-. exact Hidle.
    - intros mtx aibx slx _ _ Hnew. exfalso. exact (Hnew mt aib slots Hg Hr).
    - intros _ x mtx aibx slx Hx Hrx Hxg. unfold A' in Hx. rewrite (tkA_meta_other A g mt aib slots i x Hxg) in Hx. exists mtx, aibx, slx. auto.
    - intros mtx aibx slx _ _ Hnew. exfalso. exact (Hnew mt aib slots Hg Hr).
    - intros mtx aibx slx Hx Hrx Hshort. exfalso. unfold A' in Hx. rewrite (tkA_meta_same A g mt aib slots i) in Hx. injection Hx as <-.
      rewrite tk_mt_stride in Hshort. pose proof take_stride. lia.
    - intros _. left. split; [reflexivity|]. unfold A', spare. cbn [a_ctx a_freelist tkA set_live ameta_upd set_meta]. lia.
  Qed.
End TakeRel.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Small.
  Context {R : Type}.
  Variable W : wmode.
  Hypothesis AS : alloc_slot_specW.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) (sp : word) (n : Z).
  Variables (K : word -> M R) (P : R -> mstate -> Prop).
  Hypothesis HII : II sp0 argv envp cb [] A s.
  Hypothesis Hxm : a_xmaps A = [].
  Hypothesis Hact : ACT48 A.
  Hypothesis Hn : 0 <= n < MMAP_THRESHOLD.
  Hypothesis HL : MLeaf W sp0 argv envp cb A s n K P.

  Theorem mal_small_ok :
    tsall W ((r <- (sc0 <- mal_sc (Z_to_bv 64 n) ;;
                    mt <- m_lbu A_NEED_LOCKS ;; massert (is0 mt) ;;
                    g0 <- m_ld (at_ (v_add A_LOCK (v_slli (v_addiw sc0 0) 3)) 88) ;;
                    r <- mal_coarse sc0 g0 ;;
                    let '(sc, go) := r in
                    mk <- mal_mk go ;;
                    gi <- mal_gi sp (Z_to_bv 64 n) sc go mk ;;
                    mal_fin (Z_to_bv 64 n) gi) ;; K r) s) P.
  Proof.
    pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (envok_rodata _ _ _ _ HE) as HRO. pose proof (envok_statics _ _ _ _ HE) as HST.
    pose proof (repw_init A (ms_mem s) HW HR) as RW0.
    assert (USAGE : forall c, 0 <= c < 48 -> 0 <= a_ctx A (KUsage c) < 2^47).
    { intros c Hc. rewrite (ii_us HII c Hc). exact (usage_of_range A c HW). }
    (* [comment removed for export] *)
    apply tsall_assoc.
    eapply (tw_pureQ W (mal_sc (Z_to_bv 64 n)) s (fun x => exists sc0, x = Z_to_bv 64 sc0 /\ 0 <= sc0 < 48 /\ n + 4 <= 16 * size_class sc0 /\ sc0 = size_to_class_z n)).
    { intros K' P' HK'. apply (mal_sc_ok s n K' P' HRO HWIN Hn). intros sc0 H1 H2 H3. apply HK'. exists sc0. auto. }
    intros x (sc0 & -> & Hsc0 & Hfit0 & Hsc0z).
    (* [comment removed for export] *)
    apply tsall_assoc. eapply (tw_det W _ s _ P (Z_to_bv 64 0) s); [intros K' P' HK'; apply ts_needlocks; [exact HST | exact HWIN | exact HK'] |].
    apply tsall_assoc. apply tw_assert; [reflexivity|].
    (* [comment removed for export] *)
    apply tsall_assoc. rewrite sextw_small by (clear - Hsc0; lia). rewrite (addr_active_lock sc0) by (clear - Hsc0; lia).
    eapply (tw_det W _ s _ P (Z_to_bv 64 (a_ctx A (KActive sc0))) s).
    { intros K' P' HK'. eapply (ts_ld_ctxfW A HW s (ms_mem s) [] (KActive sc0)); [exact RW0 | exact HWIN | cbn; clear - Hsc0; lia | reflexivity | apply wfree_range_nil | exact HK']. }
    (* [comment removed for export] *)
    apply tsall_assoc.
    eapply (tw_pureQ W (mal_coarse (Z_to_bv 64 sc0) (Z_to_bv 64 (a_ctx A (KActive sc0)))) s (coarse_post A n sc0)).
    { intros K' P' HK'. exact (mal_coarse_ok A s n sc0 K' P' HW HR HWIN Hsc0 Hfit0 USAGE HK'). }
    intros r (sc & Hsc & Hfit & Hcls & Hr).
    (* [comment removed for export] *)
    assert (Hcls2 : sc = size_to_class_z n \/ sc = size_to_class_z n + 1).
    { rewrite <- Hsc0z. clear - Hcls. destruct Hcls as [-> | [-> _]]; [left | right]; reflexivity. }
    assert (Hstc : 32 <= size_to_class_z n -> sc = size_to_class_z n).
    { intros H32. destruct Hcls as [-> | [-> Hlt]]; [exact Hsc0z | exfalso; rewrite <- Hsc0z in H32; clear - H32 Hlt; lia]. }
    (* [comment removed for export] *)
    assert (SLOT : forall go, tsall W ((gi <- mal_gi sp (Z_to_bv 64 n) (Z_to_bv 64 sc) go (w32 0) ;; r' <- mal_fin (Z_to_bv 64 n) gi ;; K r') s) P).
    { intros go. unfold mal_gi. cbv zeta. rewrite first_zero. rewrite sextw_small by (clear - Hsc; lia).
      apply tsall_assoc. pose proof (nest_rank_range sc) as Hnr.
      apply (AS ALLOC_FUEL W R sp0 argv envp cb [] A s (at_ sp (-144)) sc n _ P HII Hsc ltac:(clear - Hn; lia) Hfit ltac:(unfold ALLOC_FUEL; clear - Hnr; lia)).
      - (* [comment removed for export] *)
        intros s2 A2 HII2 FR2 AF AV NR GS NRS. rewrite c_lts_wm1_w0.
        exact (fail_leaf W sp0 argv envp cb A s n K P HII Hxm Hact Hn HL sc A2 s2 Hsc HII2 FR2 AF AV NR GS NRS Hcls2).
      - (* [comment removed for export] *)
        intros s2 A2 g idx mt aib slots HII2 FR2 AO AV Hctx Hhd Hne Hmt Hrr Hgsc Hidx Hslot Hreq4 Hstr Hhook GS.
        pose proof (ii_is HII2) as HI2. pose proof HI2 as [HW2 HR2 _ HWIN2 _ _].
        pose proof (w_last_range (mt_w32 mt)) as Hlr. change (w_last (mt_w32 mt)) with (mt_last mt) in Hlr.
        replace (c_lts (Z_to_bv 64 idx) w0) with false
          by (rewrite w0_eq, c_lts_Z by (clear - Hidx Hlr; lia); symmetry; apply Z.ltb_ge; clear - Hidx; lia).
        apply tsall_assoc. rewrite (addr_active_lock sc) by (clear - Hsc; lia).
        eapply (tw_det W _ s2 _ P (Z_to_bv 64 (a_ctx A2 (KActive sc))) s2).
        { intros K' P' HK'. eapply (ts_ld_ctxfW A2 HW2 s2 (ms_mem s2) [] (KActive sc)); [apply repw_init; [exact HW2 | exact HR2] | exact HWIN2 | cbn; clear - Hsc; lia | reflexivity | apply wfree_range_nil | exact HK']. }
        rewrite Hctx. apply tw_bind_ret.
        apply (ok_leaf W sp0 argv envp cb A s n K P HII Hxm Hact Hn HL sc A2 s2 g idx mt aib slots Hsc HII2 FR2 AO AV GS Hmt Hrr Hgsc Hidx Hslot Hreq4 Hstr); [| exact Hhook | exact Hstc | exact Hcls2].
        intros mt0 aib0 sl0 Hx0 Hr0. exact (ao_idle _ _ _ _ _ _ _ _ AO mt0 aib0 sl0 Hx0 Hr0). }
    destruct Hr as [-> | [-> Hz]]; cbv beta iota.
    - (* [comment removed for export] *)
      apply tsall_assoc.
      eapply (tw_lift W (mal_mk (Some (Z_to_bv 64 (a_ctx A (KActive sc))))) s
                (fun x s' => s' = s /\ (x = w32 0 \/ exists g mt aib sl, a_active A sc <> [] /\ g = hd 0 (a_active A sc) /\ a_meta A g = Some mt /\
                                                       mt_role mt = RGroup aib sl /\ 0 < mt_avail mt < 2^32 /\ x = w32 (mt_avail mt)))).
      { intros K' P' HK'. apply (mal_mk_ok A s n sc _ K' P' HW HR HWIN Hsc (or_introl eq_refl)).
        - intros _. apply HK'. auto.
        - intros g mt aib sl Hne Hhd Hg Hrg Hav. apply HK'. split; [reflexivity|].
          destruct (Z.eq_dec (mt_avail mt) 0) as [E | NE]; [left; rewrite E; reflexivity | right]. exists g, mt, aib, sl. repeat split; auto; clear - Hav NE; lia. }
      intros mk s' [-> [-> | (g & mt & aib & sl & Hne & Hhd & Hg & Hrg & Hav & ->)]]; [apply tsall_assoc; exact (SLOT _)|].
      (* [comment removed for export] *)
      apply tsall_assoc. unfold mal_gi. cbv zeta.
      replace (negb (is0 (v_and (w32 (mt_avail mt)) (v_subw w0 (w32 (mt_avail mt)))))) with true
        by (rewrite lowbit_w32 by exact Hav; rewrite is0_w32_false by (apply pow2_ctz_range; exact Hav); reflexivity).
      cbv iota. rewrite (wf_act_head A HW sc Hsc), <- Hhd.
      pose proof (take_facts sp0 argv envp cb [] A s HII sc g mt aib sl Hsc Hg Hrg ltac:(clear - Hav; lia)) as (_ & Hi & Hbit).
      set (i := ctz32 (mt_avail mt)) in *.
      eapply (tw_lift W _ s (fun r s1 => r = Some (Z_to_bv 64 g, Z_to_bv 64 i) /\ II sp0 argv envp cb [] (tkA A g mt aib sl i) s1 /\ ntframe A s s1 /\
                                        0 <= i <= aib mod 32 /\ i <= mt_last mt /\ nth_error sl (Z.to_nat i) = Some SIdle)).
      { intros K' P' HK'. apply (mal_take_ok sp0 argv envp cb [] A s HII sc g mt aib sl Hsc Hne Hhd Hg Hrg ltac:(clear - Hav; lia) K' P').
        intros s1 HII1 NF1 H1 H2 H3. apply HK'. auto 10. }
      intros rr s1 (-> & HII1 & NF1 & Hiaib & Hilast & Hidle).
      set (A1 := tkA A g mt aib sl i) in *.
      pose proof (take_gsc A sc g mt HW Hne Hhd Hg) as Hgsc.
      pose proof (take_stride A sc g mt aib sl HW Hsc Hne Hhd Hg Hrg ltac:(clear - Hav; lia)) as Hstride.
      apply (ok_leaf W sp0 argv envp cb A s n K P HII Hxm Hact Hn HL sc A1 s1 g i (tk_mt mt aib sl i) aib (tk_slots sl i) Hsc HII1).
      + apply (FR_of_ntframe' A A1 s s1 NF1); [| intros; assumption].
        intros x [Hc | Hd]; [left; exact Hc | right]. apply (proj2 (dom_tkA A g mt aib sl i Hg Hrg x)). exact Hd.
      + exact (take_aslot_ok A sc g mt aib sl i n (ms_mem s) s1 HW Hsc Hne Hhd Hg Hrg ltac:(clear - Hav; lia) ltac:(clear - Hi; lia) Hbit).
      + constructor; rewrite (nf_vm _ _ _ NF1); [auto | auto | intros _; pose proof (nest_rank_range sc); clear - H; nia].
      + (* [comment removed for export] *)
        unfold aslot_growS. pose proof (nest_rank_range sc) as Hnr'. pose proof (grp_cap_ge sc) as Hgc'.
        split; [apply (sgrow_weaken 0 0 0); [apply sgrow_same; [exact (nf_vm _ _ _ NF1) | reflexivity | apply Z.le_refl] | clear - Hnr'; lia | clear - Hnr' Hgc'; lia | clear - Hnr'; lia| clear - Hnr'; lia]|].
        (* [comment removed for export] *)
        assert (PT : pot A <= pot A1 + 16 * size_class sc).
        { apply (pot_take A A1 sc g mt aib sl (Z.to_nat i) STaken HW Hsc (fun c => eq_refl) Hne Hhd Hg Hrg Hidle ltac:(discriminate)).
          - exact (slots_of_grp _ g _ aib _ (tkA_meta_same A g mt aib sl i) (tk_mt_role mt aib sl i)).
          - intros x Hx. exact (tkA_meta_other A g mt aib sl i x Hx). }
        pose proof (proj1 (acostS_ge sc Hsc)) as HcT.
        exact (pgrow_weaken _ _ _ _ _ _ (pgrow_take _ A A1 _ _ (nf_vm _ _ _ NF1) PT (Z.le_refl _)) HcT).
      + apply tkA_meta_same.
      + apply tk_mt_role.
      + rewrite tk_mt_sc. exact Hgsc.
      + rewrite tk_mt_last. clear - Hi Hilast. lia.
      + exact (tk_slots_i A HW sc g mt aib sl i Hsc Hhd Hne Hg Hrg ltac:(clear - Hi; lia) Hbit).
      + rewrite tk_mt_stride. clear - Hfit Hstride. lia.
      + left. rewrite tk_mt_stride. exact Hstride.
      + intros mt0 aib0 sl0 Hx0 Hr0. rewrite Hg in Hx0. injection Hx0 as <-. rewrite Hrg in Hr0. injection Hr0 as <- <-. exact Hidle.
      + intros _. exists g, mt, aib, sl, (Z.to_nat i). split; [exact Hg|]. split; [exact Hrg|]. split; [rewrite Hgsc; clear - Hsc; lia | exact Hidle].
      + exact Hstc.
      + exact Hcls2.
    - (* [comment removed for export] *)
      apply tsall_assoc. unfold mal_mk. apply tw_bind_ret. rewrite w0_w32. apply tsall_assoc. exact (SLOT None).
  Qed.
End Small.

End WithLayout.
