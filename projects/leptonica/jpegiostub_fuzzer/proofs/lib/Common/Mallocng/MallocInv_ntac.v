(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf
  MallocInv_wf2 MallocInv_wf3 MallocInv_dll MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh
  MallocInv_ops MallocInv_live MallocInv_getmeta MallocInv_free MallocInv_tryavail MallocInv_ameta_iface
  MallocInv_ntfree MallocInv_ntpieces MallocInv_ntpost MallocInv_ntq MallocInv_actw MallocInv_act.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
Record actrel (B B' : astate) (sc : Z) : Prop := {
  ar_live : a_live B' = a_live B;
  ar_areas : a_areas B' = a_areas B;
  ar_pages : a_pages B' = a_pages B;
  ar_mblocks : a_mblocks B' = a_mblocks B;
  ar_xmaps : a_xmaps B' = a_xmaps B;
  ar_fl : a_freelist B' = a_freelist B;
  ar_active : a_active B' = a_active B;
  ar_ctx : a_ctx B' = a_ctx B;
  ar_other : forall x, x <> hd 0 (a_active B sc) -> a_meta B' x = a_meta B x;
  ar_head : forall x mtx, x = hd 0 (a_active B sc) -> a_meta B x = Some mtx ->
    exists mtx', a_meta B' x = Some mtx' /\ mt_role mtx' = mt_role mtx /\ mt_w32 mtx' = mt_w32 mtx /\ mt_mem mtx' = mt_mem mtx /\
      mt_prev mtx' = mt_prev mtx /\ mt_next mtx' = mt_next mtx;
  ar_back : forall x mtx', a_meta B' x = Some mtx' -> exists mtx, a_meta B x = Some mtx /\ mt_role mtx' = mt_role mtx /\
    mt_w32 mtx' = mt_w32 mtx /\ mt_mem mtx' = mt_mem mtx;
  ar_dom : forall x, dom B' x <-> dom B x
}.

Lemma actrel_refl : forall B sc, actrel B B sc.
Proof.
  intros B sc. constructor; try reflexivity; try tauto.
  - intros x mtx _ Hx. exists mtx. auto 10.
  - intros x mtx' Hx. exists mtx'. auto.
Qed.

Section Act.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (B : astate) (s1 : mstate).
  Hypothesis HII : II sp0 argv envp cb D B s1.
  Variable sc : Z.
  Hypothesis Hsc : 0 <= sc < 48.
  (* [comment removed for export] *)
  Hypothesis Hhead0 : forall m2 rest mt2, a_active B sc = m2 :: rest -> a_meta B m2 = Some mt2 -> mt_avail mt2 = 0.

  Lemma AW : WF B. Proof. exact (is_wf _ _ _ _ _ _ (ii_is HII)). Qed.

  Theorem ts_nt_activate : forall (K : unit -> M R) P,
    (forall s' B', II sp0 argv envp cb D B' s' -> ntframe B s1 s' -> actrel B B' sc -> tsafe (K tt s') P) ->
    tsafe ((x <- nt_activate (v_add A_CTX (v_slli (Z_to_bv 64 sc) 3)) ;; K x) s1) P.
  Proof.
    intros K P HK. pose proof AW as HW. pose proof (is_rep _ _ _ _ _ _ (ii_is HII)) as HR. pose proof (is_win _ _ _ _ _ _ (ii_is HII)) as HWIN.
    pose proof (repw_init B (ms_mem s1) HW HR) as RW0. ceil.
    unfold nt_activate. reassoc. rewrite (addr_active sc) by llia.
    eapply (ts_ld_ctxfW B HW s1 (ms_mem s1) [] (KActive sc)); [exact RW0 | exact HWIN | cbn; llia | reflexivity | apply wfree_range_nil |].
    rewrite (wf_act_head B HW sc Hsc).
    destruct (a_active B sc) as [|m2 rest] eqn:El.
    - (* [comment removed for export] *)
      cbn [hd]. rewrite is0_Z by llia. cbn [Z.eqb]. apply ts_bind_ret. apply (HK s1 B); [exact HII | apply ntframe_refl | apply actrel_refl].
    - cbn [hd].
      destruct (wf_act_mem B HW sc m2 ltac:(rewrite El; left; reflexivity)) as (mt2 & aib2 & sl2 & Hm2 & Hr2 & Hs2).
      pose proof (meta_facts B m2 mt2 HW Hm2) as (M1 & M2 & M3 & M4 & Mdom).
      pose proof (Hhead0 m2 rest mt2 eq_refl Hm2) as Hav0.
      destruct (wf_grp B HW m2 mt2 aib2 sl2 Hm2 Hr2) as (Hw32 & _ & _ & Hlen & Hav & Hfr & _ & Haib & _ & Haibl & _ & Hal16 & Hmem & Hfit & Hce & _).
      pose proof (w_last_range (mt_w32 mt2)) as Hlr. change (w_last (mt_w32 mt2)) with (mt_last mt2) in Hlr.
      assert (Hc32 : 2 ^ mt_cnt mt2 <= 2 ^ 32) by (unfold mt_cnt; apply Z.pow_le_mono_r; llia).
      pose proof (Z.mod_pos_bound aib2 32 ltac:(lia)) as Hk.
      rewrite is0_Z by llia. replace (m2 =? 0) with false by (symmetry; apply Z.eqb_neq; llia).
      (* [comment removed for export] *)
      reassoc. rewrite at_Z. change (m2 + 24) with (m2 + moff FAvail).
      eapply (ts_lw_metaW B HW s1 (ms_mem s1) [] m2 mt2 FAvail); [exact RW0 | exact HWIN | exact Hm2 | reflexivity | apply wfree_range_nil | change (mt_f mt2 FAvail) with (mt_avail mt2); llia |].
      change (mt_f mt2 FAvail) with (mt_avail mt2). rewrite Hav0. reassoc. apply ts_assert; [reflexivity|].
      (* [comment removed for export] *)
      reassoc. rewrite at_Z. change (m2 + 16) with (m2 + moff FMem).
      eapply (ts_ld_metaW B HW s1 (ms_mem s1) [] m2 mt2 FMem); [exact RW0 | exact HWIN | exact Hm2 | reflexivity | apply wfree_range_nil | change (mt_f mt2 FMem) with (mt_mem mt2); llia |].
      change (mt_f mt2 FMem) with (mt_mem mt2).
      reassoc. rewrite at_Z.
      eapply (ts_lbu_factw B HW s1 (ms_mem s1) [] (mt_mem mt2 + 8) aib2); [exact RW0 | exact HWIN | | apply wfree_range_nil | llia |].
      { right; right; right. exists m2, mt2, aib2, sl2. split; [exact Hm2|]. split; [exact Hr2|]. left. right. left. reflexivity. }
      cbv zeta. rewrite !v_sllw_2 by llia.
      (* [comment removed for export] *)
      reassoc. rewrite !at_Z. apply ts_assert.
      { rewrite v_andi_Z by llia. rewrite is0_Z by (pose proof (Z.land_nonneg (m2 + 28) 3); pose proof (land_le_left (m2 + 28) 3); llia).
        change 3 with (2^2 - 1). rewrite land_ones_low by llia. apply Z.eqb_eq. change (2^2) with 4.
        replace (m2 + 28) with ((m2 / 8 * 2 + 7) * 4) by (pose proof (Z.div_mod m2 8 ltac:(lia)); lia). apply Z_mod_mult. }
      reassoc. change (m2 + 28) with (m2 + moff FFreed).
      eapply (ts_lw_metaW B HW s1 (ms_mem s1) [] m2 mt2 FFreed); [exact RW0 | exact HWIN | exact Hm2 | reflexivity | apply wfree_range_nil | change (mt_f mt2 FFreed) with (mt_freed mt2); llia |].
      change (mt_f mt2 FFreed) with (mt_freed mt2). cbn [moff].
      rewrite (act_mask_hi (mt_freed mt2) (aib2 mod 32)) by llia.
      reassoc. unfold m_sw at 1.
      eapply (ts_st_domW B HW s1 (ms_mem s1) [] 4 (m2 + 28)); [exact RW0 | exact HWIN | lia | intros j Hj; rewrite <- Z.add_assoc; apply Mdom; lia |].
      intros m1 RW1. rewrite u_w32 in RW1. change (Z.of_nat 4) with 4 in RW1.
      change (m2 + 24) with (m2 + 24). unfold m_sw.
      eapply (ts_st_domW B HW (upd s1 m1 (ms_vm s1)) (ms_mem s1) _ 4 (m2 + 24)); [exact RW1 | exact HWIN | lia | intros j Hj; rewrite <- Z.add_assoc; apply Mdom; lia |].
      intros mm RW2. change (Z.of_nat 4) with 4 in RW2. cbn [upd ms_vm ms_lo ms_hi].
      set (V := bv_unsigned (v_and (w32 (mt_freed mt2)) (v_addi (w32 (2 ^ (aib2 mod 32 + 1))) (-1)))) in RW2.
      assert (HV : V mod 2^32 = ac_av mt2 aib2) by (subst V; unfold ac_av; apply act_mask_lo; llia).
      (* [comment removed for export] *)
      set (B' := acA B m2 mt2 aib2 sl2).
      pose proof (WF_acA B HW sc m2 rest mt2 aib2 sl2 Hsc El Hm2 Hr2 Hav0) as HW'.
      pose proof (ac_masks B HW sc m2 rest mt2 aib2 sl2 Hsc El Hm2 Hr2 Hav0) as (A1 & A2 & A3 & A4 & A5 & A6).
      set (ws := [FCT (m2 + 24) 4 V; FCT (m2 + 28) 4 (sx32 (mt_freed mt2 - mt_freed mt2 mod 2 ^ (aib2 mod 32 + 1)))]) in RW2.
      assert (WO : writes_ok B ws).
      { unfold ws. apply (writes_ok_meta B _ m2 mt2 24 4 _ HW); [| exact Hm2 | lia | lia].
        apply (writes_ok_meta B [] m2 mt2 28 4 _ HW (writes_ok_nil B) Hm2); lia. }
      assert (HR' : Rep B' mm).
      { apply (repw_commit2 B B' (ms_mem s1) ws mm HW' RW2).
        - intros f Hf. destruct (has_acA B m2 mt2 aib2 sl2 Hm2 Hr2 f Hf) as [H | [-> | ->]]; [left; exact H | right | right]; cbn [f_a f_n]; intros x Hx.
          + apply (wlook_cov_some ws (FCT (m2 + 24) 4 V) x); [left; reflexivity | cbn [f_a f_n]; lia].
          + eapply (wlook_cov_some ws _ x); [right; left; reflexivity | cbn [f_a f_n]; unfold ac_fr, ac_av; lia].
        - intros x b Hw. left. unfold ws in Hw.
          destruct (wlook_some_cov _ _ _ Hw) as (w & Hin & Hxw). destruct Hin as [<- | [<- | []]]; cbn [f_a f_n] in Hxw.
          + rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. cbn [f_v f_a].
            exists m2, (ac_mt mt2 aib2 sl2), FAvail. split; [apply acA_meta_same|]. cbn [moff mlen]. split; [lia|].
            rewrite ac_mt_f. apply byte_of_mod32; [lia|]. rewrite HV. symmetry. apply Z.mod_small. unfold ac_av.
            pose proof (Z.mod_pos_bound (mt_freed mt2) (2 ^ (aib2 mod 32 + 1)) ltac:(apply Z.pow_pos_nonneg; lia)).
            assert (2 ^ (aib2 mod 32 + 1) <= 2 ^ 32) by (apply Z.pow_le_mono_r; lia). llia.
          + rewrite wlook_skip in Hw by (cbn [f_a f_n f_v]; lia). rewrite wlook_hit in Hw by (cbn [f_a f_n f_v]; lia). injection Hw as <-. cbn [f_v f_a].
            exists m2, (ac_mt mt2 aib2 sl2), FFreed. split; [apply acA_meta_same|]. cbn [moff mlen]. split; [lia|].
            rewrite ac_mt_f. unfold ac_fr, ac_av. apply byte_of_sx32. lia.
        - intros x Hx. apply (proj1 (dom_acA B m2 mt2 aib2 sl2 Hm2 Hr2 x)). exact Hx. }
      apply (HK _ B').
      + apply II_intro.
        * exact (IS_commit sp0 argv envp cb B B' s1 ws mm (ii_is HII) RW2 WO HW' HR').
        * cbn [ms_vm upd]. apply (VMok_acA B m2 mt2 aib2 sl2 Hm2 Hr2). exact (ii_vm HII).
        * apply (AvOK_transfer B B' (ii_av HII)); try reflexivity. intros x mt' Hx Hrl.
          destruct (acA_meta_inv B m2 mt2 aib2 sl2 x mt' Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrl; discriminate | exists mt'; auto].
        * apply (UsOK_transfer B B' (ii_us HII)); [reflexivity | intros; reflexivity | intros c x; apply (meta_usage_acA B m2 mt2 aib2 sl2 Hm2 Hr2)].
        * apply (deads_transfer B B' D (ii_dd HII)). intros x. split.
          -- intros (mt' & Hx & Hrl). destruct (acA_meta_inv B m2 mt2 aib2 sl2 x mt' Hx) as [(-> & ->) | (Hne & Hx')]; [cbn in Hrl; discriminate | exists mt'; auto].
          -- intros (mt0 & Hx & Hrl). exists mt0. destruct (Z.eq_dec x m2) as [-> | Hne].
             ++ rewrite Hm2 in Hx. injection Hx as <-. rewrite Hr2 in Hrl. discriminate.
             ++ unfold B'. rewrite (acA_meta_other B m2 mt2 aib2 sl2 x Hne). auto.
      + exact (ntframe_commit B s1 ws mm HW RW2 WO).
      + constructor; try reflexivity.
        * intros x Hx. rewrite El in Hx. cbn [hd] in Hx. unfold B'. apply (acA_meta_other B m2 mt2 aib2 sl2 x Hx).
        * intros x mtx Ex Hx. rewrite El in Ex. cbn [hd] in Ex. subst x. rewrite Hm2 in Hx. injection Hx as <-.
          exists (ac_mt mt2 aib2 sl2). split; [apply acA_meta_same|]. rewrite Hr2.
          split; [reflexivity|]. split; [apply ac_mt_w32|]. split; [apply ac_mt_mem|]. split; [apply ac_mt_prev | apply ac_mt_next].
        * intros x mtx' Hx. destruct (acA_meta_inv B m2 mt2 aib2 sl2 x mtx' Hx) as [(-> & ->) | (Hne & Hx')].
          -- exists mt2. rewrite Hr2. split; [exact Hm2|]. split; [reflexivity|]. split; [apply ac_mt_w32 | apply ac_mt_mem].
          -- exists mtx'. auto.
        * exact (dom_acA B m2 mt2 aib2 sl2 Hm2 Hr2).
  Qed.
End Act.

End WithLayout.
