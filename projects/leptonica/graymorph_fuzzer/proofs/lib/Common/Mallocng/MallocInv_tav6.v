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
  MallocLayout MallocTree MallocOps MallocIface MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32 MallocInv_sep MallocInv_wf MallocInv_wf2 MallocInv_wf3 MallocInv_wf4 MallocInv_dll MallocInv_live MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_sc MallocInv_sc2 MallocInv_ameta_iface MallocInv_tryavail MallocInv_free MallocInv_actw MallocInv_act MallocInv_ntfree MallocInv_ntpost MallocInv_ntq MallocInv_ntg MallocInv_aspieces MallocInv_tav_iface MallocInv_tav1 MallocInv_tav2 MallocInv_tav3 MallocInv_tav4 MallocInv_tav5.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Local Notation u := bv_unsigned (only parsing).

Lemma tavrel_deqA : forall A sc h rest, WF A -> 0 <= sc < 48 -> a_active A sc = h :: rest ->
  tavrel A (deqA A sc h [] rest) sc.
Proof.
  intros A sc h rest HW Hsc Hact.
  apply (tavrel_of_tkeep A (deqA A sc h [] rest) sc (tkeep_deqA A HW sc h [] rest Hsc Hact)); try reflexivity.
  intros x Hx. rewrite (deqA_active_sc A sc h [] rest) in Hx. rewrite Hact. right. exact Hx.
Qed.

(* [comment removed for export] *)
Lemma ts_ld_nextW : forall {R : Type} A (HW : WF A) s (m0 : word -> option byte) ws x mt (k : word -> M R) P,
  RepW A m0 ws (ms_mem s) -> WIN s -> a_meta A x = Some mt -> wfree_range ws (x + moff FNext) 8 -> 0 <= mt_next mt ->
  tsafe (k (Z_to_bv 64 (mt_next mt)) s) P ->
  tsafe ((y <- m_ld (at_ (Z_to_bv 64 x) 8) ;; k y) s) P.
Proof.
  intros R A HW s m0 ws x mt k P RW HWIN Hx Hfree Hv Hk. rewrite at_Z. change (x + 8) with (x + moff FNext).
  eapply (ts_ld_metaW A HW s m0 ws x mt FNext); [exact RW | exact HWIN | exact Hx | reflexivity | exact Hfree | exact Hv | exact Hk].
Qed.

Theorem try_avail_okD : try_avail_specD.
Proof.
  intros R sp0 argv envp cb D A s sc K P HII Hsc HKnone HKsome.
  pose proof (ii_is HII) as HI. pose proof HI as [HW HR HC HWIN HE HG].
  pose proof (repw_init A (ms_mem s) HW HR) as RW0. ceil.
  rewrite as_tryavail_eq. unfold tv_all.
  rewrite (wf_act_head A HW sc Hsc).
  destruct (a_active A sc) as [|h rest] eqn:Hact.
  - (* [comment removed for export] *)
    cbn [hd]. rewrite is0_Z by llia. cbn [Z.eqb]. apply ts_bind_ret.
    exact (HKnone s A HII (ntframe_refl A s) (tavrel_refl A sc) Hact (or_introl Hact)).
  - cbn [hd].
    destruct (ring_member A sc h HW Hsc ltac:(rewrite Hact; left; reflexivity)) as (mth & aibh & slh & Hh & Hrh & Hsh & Hw32 & Hfrr & Hc32 & Haib & Haibl & Mlo & Mhi & Hmem0 & Hmem1).
    destruct (wf_grp A HW h mth aibh slh Hh Hrh) as (_ & _ & _ & _ & Hav & _).
    assert (H32 : 2 ^ mt_cnt mth <= 2^32) by (apply Z.pow_le_mono_r; llia).
    rewrite is0_Z by llia. replace (h =? 0) with false by (symmetry; apply Z.eqb_neq; llia).
    (* [comment removed for export] *)
    apply ts_assoc. rewrite at_Z. change (h + 24) with (h + moff FAvail).
    eapply (ts_lw_metaW A HW s (ms_mem s) [] h mth FAvail); [exact RW0 | exact HWIN | exact Hh | reflexivity | apply wfree_range_nil | change (mt_f mth FAvail) with (mt_avail mth); llia |].
    change (mt_f mth FAvail) with (mt_avail mth).
    rewrite is0_w32. rewrite (Z.mod_small (mt_avail mth) (2^32)) by llia.
    destruct (Z.eqb_spec (mt_avail mth) 0) as [Hav0 | Havnz].
    + (* [comment removed for export] *)
      cbn [negb].
      apply ts_assoc. rewrite at_Z. change (h + 28) with (h + moff FFreed).
      eapply (ts_lw_metaW A HW s (ms_mem s) [] h mth FFreed); [exact RW0 | exact HWIN | exact Hh | reflexivity | apply wfree_range_nil | change (mt_f mth FFreed) with (mt_freed mth); llia |].
      change (mt_f mth FFreed) with (mt_freed mth).
      pose proof (rot_next_range sp0 argv envp cb D A s HII sc h rest mth Hsc Hact Hh) as [N1 N2].
      apply ts_assoc. (* [comment removed for export] *)
      eapply (ts_ld_nextW A HW s (ms_mem s) [] h mth); [exact RW0 | exact HWIN | exact Hh | apply wfree_range_nil | llia |].
      apply ts_assoc.
      rewrite is0_w32. rewrite (Z.mod_small (mt_freed mth) (2^32)) by llia.
      destruct (Z.eqb_spec (mt_freed mth) 0) as [Hfr0 | Hfrnz].
      * (* [comment removed for export] *)
        cbn [negb].
        set (A1 := deqA A sc h [] rest).
        apply (ts_bind_split _ _ s P (fun mo s' => II sp0 argv envp cb D A1 s' /\ ntframe A s s' /\
                                                   mo = match rest with [] => None | r :: _ => Some (Z_to_bv 64 r) end)).
        -- apply (ts_tav_dequeue sp0 argv envp cb D A s HII sc h rest Hsc Hact mth Hh).
           intros s' HII' NF'. fold A1 in HII'.
           pose proof (ii_is HII') as HI'. pose proof HI' as [HW' HR' _ HWIN' _ _]. pose proof (repw_init A1 (ms_mem s') HW' HR') as RW1.
           eapply (ts_ld_ctxfW A1 HW' s' (ms_mem s') [] (KActive sc)); [exact RW1 | exact HWIN' | exact Hsc | reflexivity | apply wfree_range_nil |].
           assert (Ectx : a_ctx A1 (KActive sc) = hd 0 rest).
           { unfold A1. rewrite (deqA_ctx_valid A HW sc h [] rest Hsc (KActive sc) Hsc).
             destruct (cslot_eq_dec (KActive sc) (KActive sc)) as [_ | Hne]; [reflexivity | exfalso; exact (Hne eq_refl)]. }
           rewrite !Ectx.
           destruct rest as [|r rest'].
           ++ cbn [hd]. rewrite is0_Z by llia. cbn [Z.eqb]. apply ts_ret. auto.
           ++ cbn [hd]. destruct (ring_member A sc r HW Hsc ltac:(rewrite Hact; right; left; reflexivity)) as (mtr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Rlo & Rhi & _).
              rewrite is0_Z by llia. replace (r =? 0) with false by (symmetry; apply Z.eqb_neq; llia). apply ts_ret. auto.
        -- intros mo s' (HII' & NF' & ->).
           pose proof (tavrel_deqA A sc h rest HW Hsc Hact) as TV1. fold A1 in TV1.
           pose proof (tkeep_deqA A HW sc h [] rest Hsc Hact) as TK. fold A1 in TK.
           destruct rest as [|r rest'].
           ++ cbv beta iota. apply ts_bind_ret. apply (HKnone s' A1 HII' NF' TV1); [apply (deqA_active_sc A sc h [] []) |].
              (* [comment removed for export] *)
              right. exists h, mth. split; [exact Hact|]. split; [exact Hh|]. split; [exact Hav0 | exact Hfr0].
           ++ cbv beta iota.
              destruct (ring_member A sc r HW Hsc ltac:(rewrite Hact; right; left; reflexivity)) as (mtr & aibr & slr & Hmr & Hrr & _).
              destruct (tk_grp A A1 sc TK r mtr aibr slr Hmr Hrr) as (mtr1 & aibr1 & Hmr1 & Hrr1 & _).
              apply (ts_tv_tail2 sp0 argv envp cb D A1 s' HII' sc r rest' mtr1 aibr1 slr Hsc (deqA_active_sc A sc h [] (r :: rest')) Hmr1 Hrr1).
              ** exact (allz_deqA A sc h (r :: rest') HW Hact).
              ** exact (KSome_chain sp0 argv envp cb D A s A1 s' sc K P HKsome NF' TV1).
      * (* [comment removed for export] *)
        cbn [negb]. apply ts_assoc.
        eapply (ts_tav_rotate sp0 argv envp cb D A s HII sc h rest mth Hsc Hact Hh Hav0 Hfrnz).
        intros s' HII' NF' TV'. apply ts_bind_ret. cbv beta iota. set (A1 := rotA A sc h rest) in *.
        assert (Hin : In (mt_next mth) (a_active A sc)) by (rewrite Hact, (rot_next A HW sc h rest mth Hsc Hact Hh); apply hd_snoc_in).
        destruct (ring_member A sc (mt_next mth) HW Hsc Hin) as (mtn & aibn & sln & Hmn & Hrn & _).
        assert (Hmn1 : a_meta A1 (mt_next mth) = Some mtn) by (unfold A1; rewrite (rotA_meta A sc h rest); exact Hmn).
        assert (Hact1 : a_active A1 sc = mt_next mth :: tl (rest ++ [h])).
        { unfold A1. rewrite (rotA_active_sc A sc h rest). rewrite (rot_next A HW sc h rest mth Hsc Hact Hh). apply snoc_hd_tl. }
        apply (ts_tv_tail2 sp0 argv envp cb D A1 s' HII' sc (mt_next mth) (tl (rest ++ [h])) mtn aibn sln Hsc Hact1 Hmn1 Hrn).
        -- unfold A1. exact (allz_rotA A sc h rest Hact (allz_intro A sc h rest mth HW Hact Hh Hav0 Hfrnz)).
        -- exact (KSome_chain sp0 argv envp cb D A s A1 s' sc K P HKsome NF' TV').
    + (* [comment removed for export] *)
      cbn [negb]. apply ts_bind_ret.
      apply (HKsome s A h mth aibh slh HII (ntframe_refl A s) (tavrel_refl A sc)); [rewrite Hact; discriminate | rewrite Hact; reflexivity | exact Hh | exact Hrh | exact Havnz].
Qed.

(* [comment removed for export] *)
Theorem try_avail_ok : try_avail_spec.
Proof. exact (try_avail_specD_spec try_avail_okD). Qed.

End WithLayout.
