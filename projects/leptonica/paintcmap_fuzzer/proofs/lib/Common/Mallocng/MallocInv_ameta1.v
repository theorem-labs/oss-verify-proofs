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
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_wf4
  MallocInv_tables MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_auxv.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

Ltac cside := cbn [f_a f_n f_v caddr clen]; unfold C_INIT, C_SECRET; lia.

Section Init.
  Context {R : Type}.
  Variables (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (A : astate) (s : mstate) (sp : word).
  Hypothesis HI : IS sp0 argv envp cb A s.
  Implicit Types (P : R -> mstate -> Prop).

  Definition init_ctx (sec : word) : ctx_rec := cupd (cupd (a_ctx A) KSecret (bv_unsigned sec)) KInit 1.
  Definition initA (sec : word) : astate := set_ctx A (init_ctx sec).

  Lemma init_ctx_other : forall sec k, k <> KSecret -> k <> KInit -> init_ctx sec k = a_ctx A k.
  Proof. intros sec k H1 H2. unfold init_ctx. rewrite !cupd_other by assumption. reflexivity. Qed.

  Lemma WF_initA : forall sec, a_ctx A KInit = 0 -> WF (initA sec).
  Proof.
    intros sec H0. pose proof (is_wf _ _ _ _ _ _ HI) as HW. pose proof (u64_range sec).
    destruct (wf_uninit A HW H0) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
    apply WF_set_ctx; try exact HW; unfold init_ctx; rewrite ?cupd_same; rewrite ?cupd_other by discriminate; rewrite ?cupd_other by discriminate.
    - right. reflexivity.
    - intros X. discriminate X.
    - exact (wf_amc A HW).
    - exact (wf_am A HW).
    - exact (wf_atail A HW).
    - exact (wf_ahead A HW).
    - exact (wf_fl_head A HW).
    - intros sc Hsc. rewrite !cupd_other by discriminate. exact (wf_act_head A HW sc Hsc).
    - intros k. unfold cupd. destruct (cslot_eq_dec k KInit); [lia|]. destruct (cslot_eq_dec k KSecret); [lia|]. exact (wf_ctx_nonneg A HW k).
    - exact (wf_shift A HW).
    - exact (wf_noarea_shift A HW).
    - exact (wf_brk0 A HW).
    - exact (wf_mblocks_len A HW).
    - exact (wf_shift_mblocks A HW).
    - exact (wf_shift_acct A HW).
  Qed.

  (* [comment removed for export] *)
  Theorem init_else_ok : forall (REST : unit -> M R) P,
    a_ctx A KInit = 0 ->
    (forall s1 A1, IS sp0 argv envp cb A1 s1 -> FR A s A1 s1 -> ms_vm s1 = ms_vm s ->
       a_ctx A1 KInit = 1 -> (exists sec : word, A1 = initA sec) ->
       tsafe (REST tt s1) P) ->
    tsafe ((x <- (auxv <- m_ld (at_ A_LIBC 8) ;;
                  sec <- m_scan_auxv AUXV_FUEL auxv w0 (v_mul sp (wlit 0x41c64e6d)) ;;
                  m_sd A_CTX sec ;;
                  m_sw A_INIT_DONE (wlit 1)) ;;
            REST x) s) P.
  Proof.
    intros REST P E0 HK. destruct HI as [HW HR HC HWIN HE HG].
      reassoc.
      (* [comment removed for export] *)
      pose proof HWIN as (W1 & W2 & W3). pose proof (eo_sp0 _ _ _ _ HE) as Hhi. pose proof (u64_range sp0) as Hsp.
      assert (Hwin' : IMG_HI <= ms_lo s /\ ms_lo s <= ms_hi s /\ ms_hi s <= bv_unsigned sp0) by (ceil; llia).
      destruct (scan_auxv_ok (R:=R) sp0 s Hwin' argv envp (eo_aux _ _ _ _ HE)) as (auxv & sec & Hcell & Hauxv & SCAN).
      replace (at_ A_LIBC 8) with (Z_to_bv 64 (bv_unsigned A_LIBC + 8)) by reflexivity.
      eapply ts_ld; [apply acc_ok_heap; [exact HWIN | pose proof (u64_range A_LIBC); lia | lia | ceil; pose proof (mlo_order_libc (ML:=ML)); llia] | exact Hcell |].
      rewrite le_val_le8.
      reassoc. apply SCAN.
      reassoc. rewrite A_CTX_eq. unfold m_sd.
      eapply (ts_st_ctxw A); [apply repw_init; [exact HW | exact HR] | exact HWIN | exact I |].
      repeat reassoc. unfold m_sw. try rewrite A_INIT_DONE_eq.
      set (m1 := wbytes (ms_mem s) (Z_to_bv 64 (caddr KSecret)) (word_to_le_bytes (Z.to_nat (clen KSecret)) sec)).
      pose proof (repw_st_ctx A s (ms_mem s) [] KSecret sec (repw_init A _ HW HR) I) as RW1. fold m1 in RW1.
      eapply (ts_st_ctxw A (upd s m1 (ms_vm s)) (ms_mem s)); [exact RW1 | exact HWIN | exact I |]. cbn [ms_mem ms_vm upd].
      set (m2 := wbytes m1 (Z_to_bv 64 (caddr KInit)) (word_to_le_bytes (Z.to_nat (clen KInit)) (wlit 1))).
      pose proof (repw_st_ctx A (upd s m1 (ms_vm s)) (ms_mem s) _ KInit (wlit 1) RW1 I) as RW2. cbn [ms_mem upd] in RW2. fold m2 in RW2.
      apply ts_bind_ret.
      (* [comment removed for export] *)
      destruct (wf_uninit A HW E0) as (Ear & _).
      assert (Hsec : 0 <= bv_unsigned sec < 2^64) by apply u64_range.
      assert (H1v : bv_unsigned (wlit 1) = 1) by reflexivity.
      assert (HR2 : Rep (initA sec) m2).
      { apply (repw_final A (initA sec) (ms_mem s) _ m2 RW2).
        - intros x b (f & Hf & Hfb).
          destruct (has_set_ctx A (init_ctx sec) f Hf) as [(k & Hk & ->) | [(Har & _) | [(pg & Hpg & ->) | Hrest]]].
          + destruct Hfb as [Hx ->]. cbn [f_a f_n f_v] in Hx |- *. rewrite ?H1v, ?uZ by lia. destruct (cslot_eq_dec k KInit) as [-> | Hn1].
            * left. unfold init_ctx. rewrite cupd_same. cbn [caddr clen] in Hx. unfold C_INIT in Hx.
              rewrite wlook_hit by cside. cbn [f_a f_v caddr]. unfold C_INIT. rewrite ?H1v. reflexivity.
            * destruct (cslot_eq_dec k KSecret) as [-> | Hn2].
              -- left. unfold init_ctx. rewrite cupd_other by discriminate. rewrite cupd_same. cbn [caddr clen] in Hx. unfold C_SECRET in Hx.
                 rewrite wlook_skip by cside. rewrite wlook_hit by cside. cbn [f_a f_v caddr]. unfold C_SECRET. reflexivity.
              -- right. rewrite (init_ctx_other sec k Hn2 Hn1).
                 pose proof (ctx_slot_disj k KInit Hk I Hn1) as D1. pose proof (ctx_slot_disj k KSecret Hk I Hn2) as D2.
                 cbn [caddr clen] in D1, D2. unfold C_INIT, C_SECRET in D1, D2.
                 split; [rewrite !wlook_skip by cside; reflexivity | exists (FCT (caddr k) (clen k) (a_ctx A k)); split; [left; exists k; auto | split; [exact Hx | reflexivity]]].
          + exfalso. destruct Har as (pg & Hpg & _). rewrite Ear in Hpg. destruct Hpg.
          + exfalso. rewrite Ear in Hpg. destruct Hpg.
          + right. assert (Hold : has A f) by (destruct Hrest as [Hm | Hg]; [right; right; left; exact Hm | right; right; right; exact Hg]).
            pose proof (nonctx_fact_avoids_ctx A HW f ltac:(destruct Hrest as [Hm | Hg]; [right; left; exact Hm | right; right; exact Hg])) as AV.
            pose proof (AV KInit I) as D1. pose proof (AV KSecret I) as D2. cbn [caddr clen] in D1, D2. unfold C_INIT, C_SECRET in D1, D2. destruct Hfb as [Hx ->].
            rewrite ?H1v, ?uZ by lia.
            split; [rewrite !wlook_skip by cside; reflexivity | exists f; split; [exact Hold | split; [exact Hx | reflexivity]]].
        - intros x Hx. exact Hx. }
      assert (FRM : forall a : word, m2 a = ms_mem s a \/ (caddr KSecret <= bv_unsigned a < caddr KSecret + 8 \/ caddr KInit <= bv_unsigned a < caddr KInit + 4)).
      { intros a. pose proof (u64_range a).
        destruct (Z.lt_ge_cases (bv_unsigned a) (caddr KSecret)) as [L1|L1];
          [| destruct (Z.lt_ge_cases (bv_unsigned a) (caddr KSecret + 8)) as [L2|L2]; [right; left; lia|]];
        (destruct (Z.lt_ge_cases (bv_unsigned a) (caddr KInit)) as [L3|L3];
          [| destruct (Z.lt_ge_cases (bv_unsigned a) (caddr KInit + 4)) as [L4|L4]; [right; right; lia|]]);
        left; unfold m2, m1; cbn [caddr clen Z.to_nat Pos.to_nat] in *; unfold C_SECRET, C_INIT in *;
        rewrite !wbytes_other_Z by (rewrite ?length_N_to_le_bytes; cbn; llia); reflexivity. }
      assert (KEEP : forall a : word, ms_mem s a <> None -> m2 a <> None).
      { intros a Ha. unfold m2, m1. cbn [caddr clen Z.to_nat Pos.to_nat]. unfold C_SECRET, C_INIT.
        apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by (cbn; llia); cbn; llia|].
        apply wbytes_keeps; [rewrite length_N_to_le_bytes, uZ by (cbn; llia); cbn; llia|]. exact Ha. }
      apply (HK _ (initA sec)).
      + (* [comment removed for export] *) apply (IS_mem sp0 argv envp cb A (initA sec) s m2 ltac:(constructor; assumption) (WF_initA sec E0) HR2).
        * intros a. destruct (FRM a) as [E | X]; [left; exact E | right]. cbn [caddr] in X. unfold C_SECRET, C_INIT in X. unfold mzone, CTX, CTX_END. llia.
        * intros a Ha. destruct (FRM a) as [E | X]; [left; rewrite <- E; exact Ha | right; left]. cbn [caddr] in X. unfold C_SECRET, C_INIT in X. llia.
      + (* [comment removed for export] *) apply (FR_memA A (initA sec) s m2 HW); [intros x; reflexivity | reflexivity | | exact KEEP].
        intros a. destruct (FRM a) as [E | X]; [left; exact E | right; left]. cbn [caddr] in X. unfold C_SECRET, C_INIT in X. unfold LOCKA, CTX_END. llia.
      + reflexivity.
      + reflexivity.
      + exists sec; reflexivity.
  Qed.

  Theorem init_ok : forall (REST : unit -> M R) P,
    (forall s1 A1, IS sp0 argv envp cb A1 s1 -> FR A s A1 s1 -> ms_vm s1 = ms_vm s ->
       a_ctx A1 KInit = 1 -> (A1 = A \/ (a_ctx A KInit = 0 /\ exists sec : word, A1 = initA sec)) ->
       tsafe (REST tt s1) P) ->
    tsafe ((ini <- m_lw A_INIT_DONE ;;
            x <- (if negb (is0 ini) then mret tt
                  else auxv <- m_ld (at_ A_LIBC 8) ;;
                       sec <- m_scan_auxv AUXV_FUEL auxv w0 (v_mul sp (wlit 0x41c64e6d)) ;;
                       m_sd A_CTX sec ;;
                       m_sw A_INIT_DONE (wlit 1)) ;;
            REST x) s) P.
  Proof.
    intros REST P HK. pose proof HI as [HW HR HC HWIN HE HG].
    rewrite A_INIT_DONE_eq at 1.
    pose proof (wf_init A HW) as Hini.
    eapply (ts_lw_ctx A); [exact HR | exact HWIN | exact I | reflexivity | lia |].
    destruct Hini as [E0 | E1].
    - (* [comment removed for export] *) rewrite E0. change (negb (is0 (Z_to_bv 64 (bv_swrap 32 0)))) with false. cbn iota.
      apply (init_else_ok REST P E0). intros s1 A1 H1 H2 H3 H4 H5. apply (HK s1 A1 H1 H2 H3 H4). right. split; [exact E0 | exact H5].
    - (* [comment removed for export] *) rewrite E1. change (negb (is0 (Z_to_bv 64 (bv_swrap 32 1)))) with true. cbn iota.
      apply ts_bind_ret. apply (HK _ A); [constructor; assumption | apply FR_refl | reflexivity | exact E1 | left; reflexivity].
  Qed.
End Init.

End WithLayout.
