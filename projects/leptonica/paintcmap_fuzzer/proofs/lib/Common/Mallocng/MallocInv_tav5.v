(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_sc MallocInv_sc2 MallocInv_ameta_iface MallocInv_tryavail MallocInv_free MallocInv_actw MallocInv_act MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_aspieces MallocInv_tav_iface MallocInv_tav2 MallocInv_tav3 MallocInv_tav4.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

Lemma snoc_hd_tl : forall (l : list Z) x, l ++ [x] = hd 0 (l ++ [x]) :: tl (l ++ [x]).
Proof. intros l x. destruct l; reflexivity. Qed.

Lemma hd_snoc_in : forall (l : list Z) x, In (hd 0 (l ++ [x])) (x :: l).
Proof. intros l x. destruct l; cbn; auto. Qed.

(* [comment removed for export] *)
Definition KSome {R : Type} (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (B : astate) (s1 : mstate) (sc : Z)
           (K : option (word * word) -> M R) (P : R -> mstate -> Prop) : Prop :=
  forall s' A' (m : Z) (mt : meta_rec) (aib : Z) (slots : list slot_st),
    II sp0 argv envp cb D A' s' -> ntframe B s1 s' -> tavrel B A' sc ->
    a_active A' sc <> [] -> m = hd 0 (a_active A' sc) ->
    a_meta A' m = Some mt -> mt_role mt = RGroup aib slots -> mt_avail mt <> 0 ->
    tsafe (K (Some (Z_to_bv 64 m, w32 (mt_avail mt))) s') P.

Lemma KSome_chain : forall {R : Type} sp0 argv envp cb D A s B s1 sc (K : option (word * word) -> M R) P,
  KSome sp0 argv envp cb D A s sc K P -> ntframe A s s1 -> tavrel A B sc -> KSome sp0 argv envp cb D B s1 sc K P.
Proof.
  intros R sp0 argv envp cb D A s B s1 sc K P HK NF TV s' A' m mt aib slots HII' NF' TV' Hne Hm Hmt Hr Hav.
  destruct (tav_chain A B A' sc s s1 s' NF TV NF' TV') as [NF2 TV2].
  exact (HK s' A' m mt aib slots HII' NF2 TV2 Hne Hm Hmt Hr Hav).
Qed.

(* [comment removed for export] *)
Lemma KSome_act : forall {R : Type} sp0 argv envp cb D B s1 sc (K : option (word * word) -> M R) P s' Bf m2 rest mt2 aib2 sl2,
  KSome sp0 argv envp cb D B s1 sc K P ->
  II sp0 argv envp cb D Bf s' -> ntframe B s1 s' -> tavrel B Bf sc ->
  a_active Bf sc = m2 :: rest -> a_meta Bf m2 = Some (ac_mt mt2 aib2 sl2) -> mt_freed mt2 mod 2 ^ (aib2 mod 32 + 1) <> 0 ->
  tsafe (K (Some (Z_to_bv 64 m2, w32 (ac_av mt2 aib2))) s') P.
Proof.
  intros R sp0 argv envp cb D B s1 sc K P s' Bf m2 rest mt2 aib2 sl2 HK HII' NF' TV' Hact' Hm' Hnz.
  exact (HK s' Bf m2 (ac_mt mt2 aib2 sl2) aib2 sl2 HII' NF' TV' ltac:(rewrite Hact'; discriminate) ltac:(rewrite Hact'; reflexivity) Hm' eq_refl Hnz).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Tail3.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (B : astate) (s1 : mstate).
  Hypothesis HII : II sp0 argv envp cb D B s1.
  Variables (sc m2 : Z) (rest : list Z) (mt2 : meta_rec) (aib2 : Z) (sl2 : list slot_st).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active B sc = m2 :: rest.
  Hypothesis Hm2 : a_meta B m2 = Some mt2.
  Hypothesis Hr2 : mt_role mt2 = RGroup aib2 sl2.
  Hypothesis HZ : allz B sc.
  Implicit Types (P : R -> mstate -> Prop).

  Theorem ts_tv_tail3 : forall (K : option (word * word) -> M R) P,
    KSome sp0 argv envp cb D B s1 sc K P ->
    tsafe ((x <- tv_tail3 (Z_to_bv 64 (caddr (KActive sc))) (Z_to_bv 64 m2) (w32 (mt_freed mt2)) ;; K x) s1) P.
  Proof.
    intros K P HK. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (repw_init B (ms_mem s1) HW HR) as RW0. ceil.
    destruct (ring_member B sc m2 HW Hsc ltac:(rewrite Hact; left; reflexivity)) as (mt' & aibx & slx & Hm' & Hr' & Hs2 & Hw32 & Hfrr & Hc32 & Haib & Haibl & Mlo & Mhi & Hmem0 & Hmem1).
    rewrite Hm2 in Hm'. injection Hm' as <-. rewrite Hr2 in Hr'. injection Hr' as <- <-.
    destruct (HZ m2 mt2 ltac:(rewrite Hact; left; reflexivity) Hm2) as [Hav0 Hfr].
    assert (Hfr32 : 0 <= mt_freed mt2 < 2^32) by (assert (2 ^ mt_cnt mt2 <= 2^32) by (apply Z.pow_le_mono_r; llia); llia).
    unfold tv_tail3. cbv zeta.
    (* [comment removed for export] *)
    apply ts_assoc. rewrite at_Z. change (m2 + 16) with (m2 + moff FMem).
    eapply (ts_ld_metaW B HW s1 (ms_mem s1) [] m2 mt2 FMem); [exact RW0 | exact HWIN | exact Hm2 | reflexivity | apply wfree_range_nil | change (mt_f mt2 FMem) with (mt_mem mt2); llia |].
    change (mt_f mt2 FMem) with (mt_mem mt2).
    apply ts_assoc. rewrite at_Z.
    eapply (ts_lbu_factw B HW s1 (ms_mem s1) [] (mt_mem mt2 + 8) aib2); [exact RW0 | exact HWIN | apply (has_aib B m2 mt2 aib2 sl2 Hm2 Hr2) | apply wfree_range_nil | llia |].
    apply ts_assoc. rewrite (act_test (mt_freed mt2) aib2) by llia.
    destruct (Z.eqb_spec (mt_freed mt2 mod 2 ^ (aib2 mod 32 + 1)) 0) as [Hlow | Hnz].
    - (* [comment removed for export] *)
      cbn [negb]. apply ts_assoc. rewrite at_Z. change (m2 + 8) with (m2 + moff FNext).
      eapply (ts_ld_metaW B HW s1 (ms_mem s1) [] m2 mt2 FNext); [exact RW0 | exact HWIN | exact Hm2 | reflexivity | apply wfree_range_nil | |].
      { change (mt_f mt2 FNext) with (mt_next mt2). pose proof (rot_next_range sp0 argv envp cb D B s1 HII sc m2 rest mt2 Hsc Hact Hm2). llia. }
      change (mt_f mt2 FNext) with (mt_next mt2).
      pose proof (rot_next_range sp0 argv envp cb D B s1 HII sc m2 rest mt2 Hsc Hact Hm2) as [N1 N2].
      rewrite c_eq_Z by llia.
      destruct (head_next B sc m2 rest mt2 HW Hsc Hact Hm2) as [Hsing Hmult].
      destruct (partial_of_masks B m2 mt2 aib2 sl2 HW Hm2 Hr2 Hfr Hlow) as (Hpart & Hsc7 & Hnzc).
      destruct (Z.eq_dec (mt_next mt2) m2) as [Enx | Hnxm].
      + (* [comment removed for export] *)
        rewrite Enx, Z.eqb_refl. cbn [negb].
        eapply (ts_tv_ext sp0 argv envp cb D B s1 HII sc m2 rest mt2 aib2 sl2 Hsc Hact Hm2 Hr2 Hav0 Hfr Hlow).
        intros s' aib' HII' NF' TV' Hab Hab' Hnz'. cbv beta iota.
        eapply (ts_tv_act sp0 argv envp cb D _ s' sc m2 rest (xa_mt mt2 sl2 aib') aib' sl2 _ _ HII' Hsc);
          [cbn; exact Hact | apply xaA_meta_same | reflexivity | rewrite xa_mt_avail; exact Hav0 | rewrite xa_mt_freed; exact Hnz' |].
        intros s'' Bf HII'' NF'' TV'' Hact'' Hm''.
        apply (KSome_act sp0 argv envp cb D (xaA B m2 mt2 sl2 aib') s' sc K P s'' Bf m2 rest (xa_mt mt2 sl2 aib') aib' sl2); try assumption.
        exact (KSome_chain sp0 argv envp cb D B s1 (xaA B m2 mt2 sl2 aib') s' sc K P HK NF' TV').
      + (* [comment removed for export] *)
        rewrite (proj2 (Z.eqb_neq _ _) Hnxm). cbn [negb].
        assert (Hrne : rest <> []) by (intros E; exact (Hnxm (Hsing E))).
        destruct (Hmult Hrne) as (Hnx & _ & Hnxin).
        apply ts_assoc.
        eapply (ts_tav_rotate sp0 argv envp cb D B s1 HII sc m2 rest mt2 Hsc Hact Hm2 Hav0 Hfr).
        intros s' HII' NF' TV'. apply ts_bind_ret. cbv beta iota.
        set (B1 := rotA B sc m2 rest) in *.
        assert (Hin : In (mt_next mt2) (a_active B sc)) by (rewrite Hact; right; exact Hnxin).
        destruct (ring_member B sc (mt_next mt2) HW Hsc Hin) as (mtr & aibr & slr & Hmr & Hrr & Hsr & Hw32r & Hfrrr & Hc32r & Haibr & Haiblr & _).
        destruct (HZ (mt_next mt2) mtr Hin Hmr) as [Havr Hfrr0].
        assert (Hfull : mt_last mtr <= aibr mod 32).
        { destruct (Z.lt_ge_cases (aibr mod 32) (mt_last mtr)) as [Hlt | Hge]; [exfalso | lia].
          apply Hnxm. symmetry.
          apply (wf_partial B HW sc m2 mt2 aib2 sl2 (mt_next mt2) mtr aibr slr); try assumption. rewrite Hact. left. reflexivity. }
        assert (Hact1 : a_active B1 sc = mt_next mt2 :: tl (rest ++ [m2])).
        { unfold B1. rewrite (rotA_active_sc B sc m2 rest). rewrite (rot_next B HW sc m2 rest mt2 Hsc Hact Hm2). apply snoc_hd_tl. }
        assert (Hmr1 : a_meta B1 (mt_next mt2) = Some mtr) by (unfold B1; rewrite (rotA_meta B sc m2 rest); exact Hmr).
        eapply (ts_tv_act sp0 argv envp cb D B1 s' sc (mt_next mt2) (tl (rest ++ [m2])) mtr aibr slr _ _ HII' Hsc Hact1 Hmr1 Hrr Havr
                  (full_nz B (mt_next mt2) mtr aibr slr HW Hmr Hrr Hfrr0 Hfull)).
        intros s'' Bf HII'' NF'' TV'' Hact'' Hm''.
        apply (KSome_act sp0 argv envp cb D B1 s' sc K P s'' Bf (mt_next mt2) (tl (rest ++ [m2])) mtr aibr slr); try assumption.
        * exact (KSome_chain sp0 argv envp cb D B s1 B1 s' sc K P HK NF' TV').
        * exact (full_nz B (mt_next mt2) mtr aibr slr HW Hmr Hrr Hfrr0 Hfull).
    - (* [comment removed for export] *)
      cbn [negb]. apply ts_bind_ret. cbv beta iota.
      eapply (ts_tv_act sp0 argv envp cb D B s1 sc m2 rest mt2 aib2 sl2 _ _ HII Hsc Hact Hm2 Hr2 Hav0 Hnz).
      intros s' Bf HII' NF' TV' Hact' Hm'.
      exact (KSome_act sp0 argv envp cb D B s1 sc K P s' Bf m2 rest mt2 aib2 sl2 HK HII' NF' TV' Hact' Hm' Hnz).
  Qed.
End Tail3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Tail2.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z) (B : astate) (s1 : mstate).
  Hypothesis HII : II sp0 argv envp cb D B s1.
  Variables (sc m : Z) (rest : list Z) (mtm : meta_rec) (aibm : Z) (slm : list slot_st).
  Hypothesis Hsc : 0 <= sc < 48.
  Hypothesis Hact : a_active B sc = m :: rest.
  Hypothesis Hm : a_meta B m = Some mtm.
  Hypothesis Hr : mt_role mtm = RGroup aibm slm.
  Hypothesis HZ : allz B sc.
  Implicit Types (P : R -> mstate -> Prop).

  Theorem ts_tv_tail2 : forall (K : option (word * word) -> M R) P,
    KSome sp0 argv envp cb D B s1 sc K P ->
    tsafe ((x <- tv_tail2 (Z_to_bv 64 (caddr (KActive sc))) (Z_to_bv 64 m) ;; K x) s1) P.
  Proof.
    intros K P HK. pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
    pose proof (repw_init B (ms_mem s1) HW HR) as RW0. ceil.
    destruct (ring_member B sc m HW Hsc ltac:(rewrite Hact; left; reflexivity)) as (mt' & aibx & slx & Hm' & Hr' & Hsm & Hw32 & Hfrr & Hc32 & Haib & Haibl & Mlo & Mhi & Hmem0 & Hmem1).
    rewrite Hm in Hm'. injection Hm' as <-. rewrite Hr in Hr'. injection Hr' as <- <-.
    destruct (HZ m mtm ltac:(rewrite Hact; left; reflexivity) Hm) as [Hav0 Hfr].
    assert (Hfr32 : 0 <= mt_freed mtm < 2^32) by (assert (2 ^ mt_cnt mtm <= 2^32) by (apply Z.pow_le_mono_r; llia); llia).
    destruct (wf_grp B HW m mtm aibm slm Hm Hr) as (_ & Hfreeable & _).
    unfold tv_tail2.
    (* [comment removed for export] *)
    apply ts_assoc. rewrite at_Z. change (m + 28) with (m + moff FFreed).
    eapply (ts_lw_metaW B HW s1 (ms_mem s1) [] m mtm FFreed); [exact RW0 | exact HWIN | exact Hm | reflexivity | apply wfree_range_nil | change (mt_f mtm FFreed) with (mt_freed mtm); llia |].
    change (mt_f mtm FFreed) with (mt_freed mtm).
    apply ts_assoc. rewrite at_Z. change (m + 32) with (m + moff FW32).
    eapply (ts_ld_metaW B HW s1 (ms_mem s1) [] m mtm FW32); [exact RW0 | exact HWIN | exact Hm | reflexivity | apply wfree_range_nil | change (mt_f mtm FW32) with (mt_w32 mtm); llia |].
    change (mt_f mtm FW32) with (mt_w32 mtm).
    apply ts_assoc. rewrite (freeable_test (mt_w32 mtm)) by (try exact Hfreeable; llia). rewrite (allfree_test (mt_freed mtm) (mt_w32 mtm)) by llia.
    cbn [andb]. change (w_last (mt_w32 mtm)) with (mt_last mtm).
    destruct (Z.eqb_spec (mt_freed mtm) (2 ^ (mt_last mtm + 1) - 1)) as [Hall | Hnotall].
    - (* [comment removed for export] *)
      apply ts_assoc. rewrite at_Z. change (m + 8) with (m + moff FNext).
      pose proof (rot_next_range sp0 argv envp cb D B s1 HII sc m rest mtm Hsc Hact Hm) as [N1 N2].
      eapply (ts_ld_metaW B HW s1 (ms_mem s1) [] m mtm FNext); [exact RW0 | exact HWIN | exact Hm | reflexivity | apply wfree_range_nil | change (mt_f mtm FNext) with (mt_next mtm); llia |].
      change (mt_f mtm FNext) with (mt_next mtm).
      apply ts_assoc.
      eapply (ts_tav_rotate sp0 argv envp cb D B s1 HII sc m rest mtm Hsc Hact Hm Hav0 Hfr).
      intros s' HII' NF' TV'. set (B1 := rotA B sc m rest) in *.
      pose proof (ii_is HII') as HI'. pose proof HI' as [HW' HR' _ HWIN' _ _]. pose proof (repw_init B1 (ms_mem s') HW' HR') as RW1.
      (* [comment removed for export] *)
      assert (Hin : In (mt_next mtm) (a_active B sc)).
      { rewrite Hact, (rot_next B HW sc m rest mtm Hsc Hact Hm). apply hd_snoc_in. }
      destruct (ring_member B sc (mt_next mtm) HW Hsc Hin) as (mtn & aibn & sln & Hmn & Hrn & Hsn & Hw32n & Hfrrn & Hc32n & _).
      destruct (HZ (mt_next mtm) mtn Hin Hmn) as [Havn Hfrn].
      assert (Hfr32n : 0 <= mt_freed mtn < 2^32) by (assert (2 ^ mt_cnt mtn <= 2^32) by (apply Z.pow_le_mono_r; llia); llia).
      assert (Hmn1 : a_meta B1 (mt_next mtm) = Some mtn) by (unfold B1; rewrite (rotA_meta B sc m rest); exact Hmn).
      assert (Hact1 : a_active B1 sc = mt_next mtm :: tl (rest ++ [m])).
      { unfold B1. rewrite (rotA_active_sc B sc m rest). rewrite (rot_next B HW sc m rest mtm Hsc Hact Hm). apply snoc_hd_tl. }
      apply ts_assoc. rewrite at_Z. change (mt_next mtm + 28) with (mt_next mtm + moff FFreed).
      eapply (ts_lw_metaW B1 HW' s' (ms_mem s') [] (mt_next mtm) mtn FFreed); [exact RW1 | exact HWIN' | exact Hmn1 | reflexivity | apply wfree_range_nil | change (mt_f mtn FFreed) with (mt_freed mtn); llia |].
      change (mt_f mtn FFreed) with (mt_freed mtn).
      apply ts_bind_ret. cbv beta iota.
      apply (ts_tv_tail3 sp0 argv envp cb D B1 s' HII' sc (mt_next mtm) (tl (rest ++ [m])) mtn aibn sln Hsc Hact1 Hmn1 Hrn).
      + unfold B1. apply (allz_rotA B sc m rest Hact HZ).
      + exact (KSome_chain sp0 argv envp cb D B s1 B1 s' sc K P HK NF' TV').
    - (* [comment removed for export] *)
      apply ts_bind_ret. cbv beta iota.
      apply (ts_tv_tail3 sp0 argv envp cb D B s1 HII sc m rest mtm aibm slm Hsc Hact Hm Hr HZ K P HK).
  Qed.
End Tail2.

End WithLayout.
