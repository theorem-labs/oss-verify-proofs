(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_wf2
  MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_sc MallocInv_free
  MallocInv_ameta_iface MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_aspieces.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Take.
  Variable A : astate.
  Hypothesis HW : WF A.
  Variables (sc ma : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st) (i : Z).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hhd : ma = hd 0 (a_active A sc).
  Hypothesis Hne : a_active A sc <> [].
  Hypothesis Hma : a_meta A ma = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hi0 : 0 <= i.
  Hypothesis Hbit : Z.testbit (mt_avail mt) i = true.

  Definition tk_av : Z := mt_avail mt - 2 ^ i.
  Definition tk_slots : list slot_st := list_set slots (Z.to_nat i) STaken.
  Definition tk_mt : meta_rec := MT (gu_f mt tk_av (mt_freed mt)) (RGroup aib tk_slots).
  Definition tkA : astate := set_live (ameta_upd A ma tk_mt) (a_live A).

  Lemma tk_grp : 0 <= mt_w32 mt < 2^64 /\ Z.of_nat (length slots) = mt_cnt mt /\
    0 <= mt_avail mt < 2 ^ (mt_cnt mt) /\ 0 <= mt_freed mt < 2 ^ (mt_cnt mt) /\
    Z.land (mt_avail mt) (mt_freed mt) = 0 /\ 0 <= aib < 256 /\ mt_avail mt < 2 ^ (aib mod 32 + 1) /\ aib mod 32 <= mt_last mt /\
    (forall j st, nth_error slots (Z.to_nat j) = Some st -> 0 <= j -> (Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) j = true <-> st = SIdle)) /\
    mt_sc mt = sc.
  Proof.
    destruct (wf_grp A HW ma mt aib slots Hma Hr) as (H1 & _ & _ & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & _).
    repeat (split; [assumption|]).
    destruct (wf_act_mem A HW sc ma ltac:(rewrite Hhd; destruct (a_active A sc); [contradiction | left; reflexivity])) as (mt1 & aib1 & sl1 & Hm1 & _ & Hsc1).
    rewrite Hma in Hm1. injection Hm1 as <-. exact Hsc1.
  Qed.

  Lemma tk_i_aib : i <= aib mod 32.
  Proof.
    pose proof tk_grp as (_ & _ & Hav & _ & _ & Haib & Havact & _).
    destruct (Z.lt_ge_cases (aib mod 32) i) as [Hlt | Hge]; [| exact Hge]. exfalso.
    rewrite Z.testbit_true in Hbit by lia.
    assert (2 ^ (aib mod 32 + 1) <= 2 ^ i) by (apply Z.pow_le_mono_r; lia).
    rewrite Z.div_small in Hbit by lia. cbn in Hbit. lia.
  Qed.
  Lemma tk_i_last : i <= mt_last mt.
  Proof. pose proof tk_grp as (_ & _ & _ & _ & _ & _ & _ & Haibl & _). pose proof tk_i_aib. lia. Qed.
  Lemma tk_i_cnt : i < mt_cnt mt.
  Proof. pose proof tk_i_last. unfold mt_cnt. lia. Qed.
  Lemma tk_ilt : (Z.to_nat i < length slots)%nat.
  Proof. pose proof tk_grp as (_ & Hlen & _). pose proof tk_i_cnt. lia. Qed.
  Lemma tk_slot_idle : nth_error slots (Z.to_nat i) = Some SIdle.
  Proof.
    pose proof tk_grp as (_ & _ & _ & _ & _ & _ & _ & _ & Hidle & _).
    destruct (nth_error slots (Z.to_nat i)) as [st|] eqn:E; [| exfalso; apply nth_error_None in E; pose proof tk_ilt; lia].
    f_equal. apply (proj1 (Hidle i st E Hi0)). rewrite Z.lor_spec, Hbit. reflexivity.
  Qed.
  Lemma tk_av_testbit : forall j, 0 <= j -> Z.testbit tk_av j = if j =? i then false else Z.testbit (mt_avail mt) j.
  Proof. intros j Hj. unfold tk_av. pose proof tk_grp as (_ & _ & Hav & _). apply sub_lowbit_testbit; [lia | lia | lia | exact Hbit]. Qed.
  Lemma tk_av_range : 0 <= tk_av < 2 ^ (mt_cnt mt) /\ tk_av <= mt_avail mt /\ tk_av < 2 ^ (aib mod 32 + 1).
  Proof.
    pose proof tk_grp as (_ & _ & Hav & _ & _ & _ & Havact & _). unfold tk_av. pose proof (Z.pow_nonneg 2 i ltac:(lia)).
    assert (2 ^ i <= mt_avail mt).
    { destruct (Z.lt_ge_cases (mt_avail mt) (2 ^ i)) as [Hlt | Hge]; [| exact Hge]. exfalso.
      rewrite Z.testbit_true in Hbit by lia. rewrite Z.div_small in Hbit by lia. cbn in Hbit. lia. }
    lia.
  Qed.

  Theorem WF_tkA : WF tkA.
  Proof.
    pose proof tk_grp as (Hw & Hlen & Hav & Hfr & Hdis & Haib & Havact & Haibl & Hidle & Hscm). pose proof tk_av_range as (R1 & R2 & R3).
    apply (WF_grp_upd A HW ma mt aib slots Hma Hr tk_av (mt_freed mt) aib tk_slots (a_live A)).
    - unfold tk_slots. apply list_set_length.
    - intros j st st' Hj Hj'. unfold tk_slots in Hj'. destruct (list_set_nth_inv _ _ _ _ _ Hj') as [(-> & -> & _) | (Hne' & H)].
      + rewrite tk_slot_idle in Hj. injection Hj as <-. right. split; [left; reflexivity | right; left; reflexivity].
      + rewrite H in Hj. injection Hj as <-. left. reflexivity.
    - exact R1.
    - exact Hfr.
    - apply Z.bits_inj'. intros j Hj. rewrite Z.land_spec, Z.bits_0, tk_av_testbit by lia.
      destruct (Z.eqb_spec j i) as [-> | Hne']; [reflexivity|]. rewrite <- Z.land_spec, Hdis. apply Z.bits_0.
    - exact Haib.
    - exact R3.
    - exact Haibl.
    - intros j st Hj Hj0. rewrite Z.lor_spec, tk_av_testbit by lia. unfold tk_slots in Hj.
      destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(E & -> & _) | (Hne' & H)].
      + assert (j = i) by lia. subst j. rewrite Z.eqb_refl. cbn [orb].
        pose proof (Hidle i SIdle tk_slot_idle Hi0) as [_ X]. rewrite Z.lor_spec, Hbit in X. cbn in X.
        split; [| intros E'; discriminate E']. intros Hf. exfalso.
        pose proof Hdis as D. apply (f_equal (fun z => Z.testbit z i)) in D. rewrite Z.land_spec, Z.bits_0, Hbit in D. cbn in D. rewrite D in Hf. discriminate Hf.
      + replace (j =? i) with false by (symmetry; apply Z.eqb_neq; lia). rewrite <- Z.lor_spec. apply Hidle; [exact H | exact Hj0].
    - intros j off n Hj Hj0. unfold tk_slots in Hj. destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(_ & E & _) | (Hne' & H)]; [discriminate E|].
      exact (wf_live A HW ma mt aib slots j off n Hma Hr H Hj0).
    - intros j Hj. exact (wf_inactive A HW ma mt aib slots j Hma Hr Hj).
    - intros Hin Hne'. exfalso. apply Hne'. rewrite Hscm. exact Hhd.
    - intros H. exact H.
    - intros Hsc48 Hnz. left. intros E.
      apply (f_equal (fun z => Z.testbit z i)) in E. rewrite Z.lor_spec, Hbit, Z.bits_0 in E. discriminate E.
    - intros q k. rewrite (wf_live_map A HW q k). unfold is_live. split.
      + intros (x & mtx & aibx & slx & j & off & Hx & Hrx & Hj0 & Hj & E).
        destruct (Z.eq_dec x ma) as [-> | Hne'].
        * left. rewrite Hma in Hx. injection Hx as <-. rewrite Hr in Hrx. injection Hrx as <- <-.
          exists j, off. split; [exact Hj0|]. split; [| exact E].
          unfold tk_slots. rewrite list_set_nth_other; [exact Hj|]. intros E2. rewrite <- E2, tk_slot_idle in Hj. discriminate Hj.
        * right. exists x, mtx, aibx, slx, j, off. auto 10.
      + intros [(j & off & Hj0 & Hj & E) | (x & mtx & aibx & slx & j & off & Hne' & Hx & Hrx & Hj0 & Hj & E)].
        * exists ma, mt, aib, slots, j, off. split; [exact Hma|]. split; [exact Hr|]. split; [exact Hj0|]. split; [| exact E].
          unfold tk_slots in Hj. destruct (list_set_nth_inv _ _ _ _ _ Hj) as [(_ & Ebad & _) | (_ & H)]; [discriminate Ebad | exact H].
        * exists x, mtx, aibx, slx, j, off. auto 10.
  Qed.

  Lemma tkA_meta_same : a_meta tkA ma = Some tk_mt.
  Proof. unfold tkA, set_live, ameta_upd, set_meta. cbn. apply aupd_same. Qed.
  Lemma tkA_meta_other : forall x, x <> ma -> a_meta tkA x = a_meta A x.
  Proof. intros x Hne'. unfold tkA, set_live, ameta_upd, set_meta. cbn. apply aupd_other. exact Hne'. Qed.
  Lemma tkA_ctx : a_ctx tkA = a_ctx A. Proof. reflexivity. Qed.
  Lemma tkA_active : a_active tkA = a_active A. Proof. reflexivity. Qed.
  Lemma tkA_areas : a_areas tkA = a_areas A. Proof. reflexivity. Qed.
  Lemma tkA_freelist : a_freelist tkA = a_freelist A. Proof. reflexivity. Qed.
  Lemma tkA_live : a_live tkA = a_live A. Proof. reflexivity. Qed.
  Lemma tkA_xmaps : a_xmaps tkA = a_xmaps A. Proof. reflexivity. Qed.
  Lemma tkA_pages : a_pages tkA = a_pages A. Proof. reflexivity. Qed.
  Lemma tkA_mblocks : a_mblocks tkA = a_mblocks A. Proof. reflexivity. Qed.
  Lemma tkA_brk_lo : a_brk_lo tkA = a_brk_lo A. Proof. reflexivity. Qed.
  Lemma tk_mt_f : forall fl, mt_f tk_mt fl = if mfield_eq_dec fl FAvail then tk_av else mt_f mt fl.
  Proof. intros fl. unfold tk_mt. rewrite mt_f_MT. unfold gu_f. destruct fl; cbn; reflexivity. Qed.
  Lemma tk_mt_role : mt_role tk_mt = RGroup aib tk_slots. Proof. reflexivity. Qed.
  Lemma tk_mt_w32 : mt_w32 tk_mt = mt_w32 mt. Proof. reflexivity. Qed.
  Lemma tk_mt_mem : mt_mem tk_mt = mt_mem mt. Proof. reflexivity. Qed.
  Lemma tk_mt_sc : mt_sc tk_mt = mt_sc mt. Proof. reflexivity. Qed.
  Lemma tk_mt_cnt : mt_cnt tk_mt = mt_cnt mt. Proof. reflexivity. Qed.
  Lemma tk_mt_last : mt_last tk_mt = mt_last mt. Proof. reflexivity. Qed.
  Lemma tk_mt_stride : mt_stride tk_mt = mt_stride mt. Proof. reflexivity. Qed.
  Lemma tk_mt_maplen : mt_maplen tk_mt = mt_maplen mt. Proof. reflexivity. Qed.
  Lemma tk_slots_i : nth_error tk_slots (Z.to_nat i) = Some STaken.
  Proof. unfold tk_slots. apply list_set_nth_same. exact tk_ilt. Qed.
  Lemma tk_slots_other : forall j, j <> Z.to_nat i -> nth_error tk_slots j = nth_error slots j.
  Proof. intros j Hj. unfold tk_slots. apply list_set_nth_other. intros E. apply Hj. symmetry. exact E. Qed.

  Lemma dom_tkA : forall x, dom tkA x <-> dom A x.
  Proof. exact (dom_grp_upd A ma mt aib slots Hma Hr tk_av (mt_freed mt) aib tk_slots (a_live A)). Qed.
  Lemma VMok_tkA : forall h, VMok A h -> VMok tkA h.
  Proof. exact (VMok_grp_upd A ma mt aib slots Hma Hr tk_av (mt_freed mt) aib tk_slots (a_live A)). Qed.
  Lemma has_tkA : forall f, has tkA f -> has A f \/ f = FCT (ma + 24) 4 tk_av.
  Proof.
    intros f Hf.
    destruct (has_grp_upd A ma mt tk_av (mt_freed mt) aib tk_slots (a_live A) f Hf) as [[H _] | [(fl & ->) | [H | (j & st & Hj & Hin)]]].
    - left. exact H.
    - destruct (mfield_eq_dec fl FAvail) as [-> | Hfl]; [right; reflexivity | left].
      right; right; left. exists ma, mt, fl. split; [exact Hma|]. unfold gu_f. destruct fl; try reflexivity. contradiction.
    - left. right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. left. exact H.
    - left. right; right; right. exists ma, mt, aib, slots. split; [exact Hma|]. split; [exact Hr|]. right.
      destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne'].
      + exists (Z.to_nat i), SIdle. split; [exact tk_slot_idle|]. rewrite tk_slots_i in Hj. injection Hj as <-. exact Hin.
      + exists j, st. rewrite tk_slots_other in Hj by exact Hne'. auto.
  Qed.
  Lemma meta_usage_tkA : forall c x, meta_usage tkA c x = meta_usage A c x.
  Proof.
    intros c x. unfold meta_usage. destruct (Z.eq_dec x ma) as [-> | Hne'].
    - rewrite tkA_meta_same, Hma, Hr. unfold tk_mt. rewrite mt_role_MT. fold tk_mt. rewrite tk_mt_sc, tk_mt_cnt. reflexivity.
    - rewrite (tkA_meta_other x Hne'). reflexivity.
  Qed.
  Lemma tkA_meta_inv : forall x mtx, a_meta tkA x = Some mtx -> (x = ma /\ mtx = tk_mt) \/ (x <> ma /\ a_meta A x = Some mtx).
  Proof.
    intros x mtx Hx. destruct (Z.eq_dec x ma) as [-> | Hne']; [left; rewrite tkA_meta_same in Hx; injection Hx as <-; auto | right].
    rewrite (tkA_meta_other x Hne') in Hx. auto.
  Qed.
End Take.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma is0_w32_false : forall x, 0 < x < 2^32 -> is0 (w32 x) = false.
Proof.
  intros x Hx. rewrite w32_eq. unfold is0, w0, wlit. pose proof (sx32_range x).
  rewrite c_eq_Z by lia. apply Z.eqb_neq. unfold sx32. rewrite (Z.mod_small x (2^32)) by lia.
  destruct (x <? 2^31); lia.
Qed.

(* [comment removed for export] *)
Lemma repw_rodata : forall A m0 ws m, RepW A m0 ws m -> rodata_clear m0 -> rodata_clear m.
Proof.
  intros A m0 ws m RW HRO a Ha. pose proof layout_small as LS. pose proof layout_nums as LN.
  rewrite (rw_frame A m0 ws m RW (Z_to_bv 64 a)); [exact (HRO a Ha)|].
  rewrite uZ by lia. apply Forall_forall. intros w Hw. pose proof (rw_zone A m0 ws m RW w Hw) as Z0.
  unfold wzone, ERRNO, CTX, CTX_END, LOCKA in *. pose proof (rw_range A m0 ws m RW w Hw). lia.
Qed.

Section TakeCPS.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (A : astate) (s : mstate).
  Hypothesis HII : II sp0 argv envp cb D A s.
  Variables (sc g : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hne : a_active A sc <> [].
  Hypothesis Hhd : g = hd 0 (a_active A sc).
  Hypothesis Hg : a_meta A g = Some mt.
  Hypothesis Hr : mt_role mt = RGroup aib slots.
  Hypothesis Hav : mt_avail mt <> 0.

  Let av := mt_avail mt.
  Let i := ctz32 av.

  Lemma take_facts : 0 < av < 2^32 /\ 0 <= i < 32 /\ Z.testbit av i = true.
  Proof.
    pose proof (is_wf _ _ _ _ _ _ (ii_is HII)) as HW.
    destruct (wf_grp A HW g mt aib slots Hg Hr) as (_ & _ & _ & _ & Hav' & _). pose proof (w_last_range (mt_w32 mt)).
    assert (2 ^ mt_cnt mt <= 2^32) by (apply Z.pow_le_mono_r; unfold mt_cnt, mt_last in *; lia).
    assert (Hv : 0 < av < 2^32) by (unfold av in *; lia).
    destruct (ctz32_spec av Hv) as (_ & R1 & R2 & _). unfold i. auto.
  Qed.

  Theorem ts_as_take : forall (K : word -> M R) P,
    (forall s', II sp0 argv envp cb D (tkA A g mt aib slots i) s' -> ntframe A s s' ->
       0 <= i <= aib mod 32 -> i <= mt_last mt -> nth_error slots (Z.to_nat i) = Some SIdle ->
       tsafe (K (Z_to_bv 64 i) s') P) ->
    tsafe ((r <- as_take (Z_to_bv 64 g) (w32 av) ;; K r) s) P.
  Proof.
    intros K P HK. pose proof (ii_is HII) as HIS. destruct HIS as [HW HR HC HWIN HE HG].
    pose proof (envok_rodata _ _ _ _ HE) as HRO.
    pose proof take_facts as (Hv & Hi & Hbit).
    pose proof (meta_facts A g mt HW Hg) as (M1 & M2 & M3 & M4 & Mdom). ceil.
    pose proof (repw_init A (ms_mem s) HW HR) as RW0.
    unfold as_take. rewrite lowbit_w32 by exact Hv. rewrite v_subw_w32.
    reassoc. rewrite (at_Z g 24). unfold m_sw.
    eapply (ts_st_domW A HW s (ms_mem s) [] 4 (g + 24)); [exact RW0 | exact HWIN | lia | intros j Hj; rewrite <- Z.add_assoc; apply Mdom; lia |]. intros m1 RW1.
    pose proof (pow2_ctz_range av Hv) as Hp. fold i in Hp.
    fold i. rewrite (is0_w32_false (2 ^ i)) by exact Hp.
    eapply ts_ctz32; [exact (repw_rodata A (ms_mem s) _ m1 RW1 HRO) | exact HWIN | exact Hv |]. fold i.
    (* [comment removed for export] *)
    set (A' := tkA A g mt aib slots i).
    assert (HW' : WF A') by (apply (WF_tkA A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr ltac:(lia) Hbit)).
    change (Z.of_nat 4) with 4 in RW1.
    assert (WO : writes_ok A [FCT (g + 24) 4 (bv_unsigned (w32 (av - 2 ^ i)))]).
    { apply (writes_ok_meta A [] g mt 24 4); [exact HW | apply writes_ok_nil | exact Hg | lia | lia]. }
    assert (HR' : Rep A' m1).
    { apply (repw_commit2 A A' (ms_mem s) _ m1 HW' RW1).
      - intros f Hf. destruct (has_tkA A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr ltac:(lia) Hbit f Hf) as [Ho | ->]; [left; exact Ho | right].
        intros x Hx. cbn [f_a f_n f_v] in Hx. rewrite wlook_hit by (cbn [f_a f_n]; lia). discriminate.
      - intros x b Hw. destruct (Z.lt_ge_cases x (g + 24)) as [Hlt | Hge]; [rewrite wlook_skip in Hw by (cbn [f_a f_n]; lia); discriminate Hw|].
        destruct (Z.lt_ge_cases x (g + 28)) as [Hlt' | Hge']; [| rewrite wlook_skip in Hw by (cbn [f_a f_n]; lia); discriminate Hw].
        rewrite wlook_hit in Hw by (cbn [f_a f_n]; lia). cbn [f_a f_v] in Hw. injection Hw as <-.
        left. exists g, (tk_mt mt aib slots i), FAvail. split; [apply tkA_meta_same|]. cbn [moff mlen]. split; [lia|].
        rewrite tk_mt_f. destruct (mfield_eq_dec FAvail FAvail); [| contradiction]. unfold tk_av, av. rewrite u_w32.
        apply byte_of_sx32. lia.
      - intros x Hx. apply (proj1 (dom_tkA A g mt aib slots i Hg Hr x)). exact Hx. }
    apply HK.
    - apply II_intro.
      + apply (IS_commit sp0 argv envp cb A A' s _ m1 (ii_is HII) RW1 WO HW' HR').
      + cbn [ms_vm upd]. apply (VMok_tkA A g mt aib slots i Hg Hr). exact (ii_vm HII).
      + apply (AvOK_transfer A A' (ii_av HII)); [reflexivity | reflexivity |].
        intros x mt' Hx Hrx. destruct (tkA_meta_inv A g mt aib slots i x mt' Hx) as [(-> & ->) | (Hn & H)]; [cbn in Hrx; discriminate Hrx | eauto].
      + apply (UsOK_transfer A A' (ii_us HII)); [reflexivity | intros c Hc; reflexivity | intros c x; apply meta_usage_tkA; assumption].
      + apply (deads_transfer A A' D (ii_dd HII)). intros x. split.
        * intros (mt' & Hx & Hrx). destruct (tkA_meta_inv A g mt aib slots i x mt' Hx) as [(-> & ->) | (Hn & H)]; [cbn in Hrx; discriminate Hrx | eauto].
        * intros (mt0 & Hx & Hrx). destruct (Z.eq_dec x g) as [-> | Hn]; [rewrite Hg in Hx; injection Hx as <-; rewrite Hr in Hrx; discriminate Hrx|].
          exists mt0. unfold A'. rewrite (tkA_meta_other A g mt aib slots i x Hn). auto.
    - apply (ntframe_commit A s _ m1 HW RW1 WO).
    - pose proof (tk_i_aib A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr ltac:(lia) Hbit). lia.
    - exact (tk_i_last A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr ltac:(lia) Hbit).
    - exact (tk_slot_idle A HW sc g mt aib slots i Hsc Hhd Hne Hg Hr ltac:(lia) Hbit).
  Qed.
End TakeCPS.

End WithLayout.
