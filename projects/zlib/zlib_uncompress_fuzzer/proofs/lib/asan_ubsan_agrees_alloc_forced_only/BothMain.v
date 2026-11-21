(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import TopLevel ZTopC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes InitMem RunConst CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF CTreeA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import HaltsA.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import Monad CMonad Prog ProgA ProgC ProgAC EquivPA AsanProgDeps AsanOK AsanHandoffBoth ModelOKC.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg AProto CProto ATsafeMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.FO Require Import FOCore FOStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require ITreeALift.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition bmain_open (en : ExecEntry) (inp : ProcInput) (w : bool) (V : nat -> Z) (m : word -> option byte)
    (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
    ms = MS (mkR (Z_to_bv 64 BRA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 BGP) (Z_to_bv 64 BTP)
                 (Z_to_bv 64 (V 1032%nat)) (Z_to_bv 64 (V 1033%nat)) (Z_to_bv 64 (V 1034%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 1035%nat)) (Z_to_bv 64 (V 1036%nat)) (Z_to_bv 64 (V 1037%nat)) (Z_to_bv 64 (V 1038%nat))
                 (Z_to_bv 64 BMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 1039%nat)) (Z_to_bv 64 (V 1040%nat)) (Z_to_bv 64 (V 1041%nat)) (Z_to_bv 64 (V 1042%nat)))
            bvmap_empty (Z_to_bv 64 BMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wpad en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp)
        (* AS/MainEntry's amain_at, batch 4 rows b-e, copied *)
        /\ V 11%nat = Z.of_nat (StackLayout.block_items (in_argv inp) (in_envp inp) mod 2))
    /\ Forall (mfact_ok bsegs V m) (both_mem_facts ++ both_mem_facts_w w)
    /\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w)
    /\ Forall (mfact_ok bsegs V m) (both_argv_facts (AsanPlanCore.APC.rseq_z (kb_rseq (in_kernel inp))))
    /\ mem_inv bsegs m
    /\ stk bsegs m (usp - ASTK) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem inp (en_mmap_base en) b_phdrs (Z_to_bv 64 (Z.of_N b_init_pc))
                       (en_sp en) (en_draw en) (wa a))
    /\ bshadow0 V m
    /\ bmodel V (en_sp en) (in_fs inp) mo.

Lemma bmain_at_open : forall en inp ms mo,
  bmain_at en inp ms mo <-> exists w V m, bmain_open en inp w V m ms mo.
Proof. intros; reflexivity. Qed.

Definition RNG0 {rc : runConstT} (V : nat -> Z) (mo : Model) : footprint := fp_ok (m_vm_lazy (MX mo [])) (A0 V).

Definition TTC : Empty_set -> APS -> footprint -> machine_state -> Prop := fun _ _ _ _ => True.

Definition both_implC_stmt (rsA : Z) : Prop :=
  forall (rc : runConstT) en inp w V m ms mo,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    bmain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
    implMAC (RNG0 V mo) (progA_mainC AAllocAsan rsA (argv_Z (in_argv inp)))
            (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) TTC ms.

Section Assembly.
  Hypothesis plain_implC : plain_implC_stmt.
  Variable rsA : Z.
  Hypothesis both_implC : both_implC_stmt rsA.

  Lemma valid_sp_of_entry : forall en inp, valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp -> valid_sp (en_sp en).
  Proof.
    intros [sp brk mb draw] inp Hv Hi. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv. destruct Hv as (Hsp & _). exact Hsp.
  Qed.

  Lemma both_sideC_main : forall lim, 2^31 <= lim -> forall en inp,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    TAC lim inp en [] /\ forall ms mo, bmain_at en inp ms mo ->
      SpinAlg.srealizes (bsegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
        (mkCfg (TopLevel.set_rom (seg_rom (bsegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))) ms) mo)
        (TAC lim inp en).
  Proof.
    intros lim Hlim en inp Hv Hi. split.
    -
      pose proof (toP_valid _ _ _ en inp Hv) as HvP.
      destruct (plain_side_okC plain_implC lim Hlim (toP en) inp HvP Hi) as [Htr _].
      unfold TAC.
      apply (proj1 (equiv_PP_D lim Hlim (DP inp (toP en)) D0 PREAD_STAGE PREAD_STAGE (toP en) (toP en) inp HvP HvP Hi [])).
      change (tree_traces (tP inp (toP en)) (mo0 psegs lim (toP en) inp) []).
      apply Htr. rewrite run_init_config. cbn [bh_traces]. apply obs_trace_cfg_nil.
    - intros ms mo HM.
      apply bmain_at_open in HM as (w & V & m & HM).
      pose proof HM as (_ & HV & _ & _ & HP & _ & _ & _ & _ & _ & HMOD).
      apply Forall_app in HP as [HP _].
      set (rc := run_consts_of en (Z_to_bv 64 0) (valid_sp_of_entry en inp Hv Hi)).
      assert (HA : atop_of (en_sp en) = @ATOP rc) by reflexivity.
      assert (HAT : a_usp0 V - 8388608 = @ATOP rc).
      { rewrite <- HA. unfold atop_of, a_usp0. destruct HM as (_ & _ & (_ & _ & _ & E & _) & _). cbv zeta in E. lia. }
      destruct (implMAC_RES (RNG0 V mo) (progA_mainC AAllocAsan rsA (argv_Z (in_argv inp))) _ TTC ms
                  ltac:(intros; exact I) (both_implC rc en inp w V m ms mo Hv Hi HM HA)) as [D2 HD].
      assert (HT : tree_atA bsegs (at_nodeA bsegs) nstepA minvA (nsafeA NMAX) fstepS NMAX (RNG0 V mo) (A0 V)
                     (progA_treeD AAllocAsan D2 (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp)))
                     (epostF (fun (_ : unit) (_ : footprint) (_ : machine_state) => True)) ms (MX mo []) mo).
      { rewrite HA. split.
        { unfold progA_treeD, progA_mainD. eapply implF_ebind; [exact HD|]. intros [e ?] RNG' ms' _. destruct e. }
        split. { rewrite <- HA. destruct (equiv_PA_asan_toP_D lim Hlim D0 D2 PREAD_STAGE rsA V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [_ HL]. exact HL. }
        split. { rewrite m_halted_MX. exact (bm_halted _ _ _ _ HMOD). }
        (* port727 (rme's NodesA c2): minvA_std_fds takes the channel reader; bmodel's bm_rdr (MX keeps it) *)
        split. { apply minvA_std_fds; [rewrite m_fds_MX; exact (bm_fds _ _ _ _ HMOD) | reflexivity | | exact (bm_rdr _ _ _ _ HMOD)].
                 rewrite m_vmmaps_MX, (bm_top _ _ _ _ HMOD). pose proof (bm_usp _ _ _ _ HMOD). unfold sp_window_lo, sp_window_hi. lia. }
        split. { rewrite <- HA. exact (progA_tsafeD V HP HAT (en_sp en) HA D2 rsA inp mo HMOD). }
        change (MX mo []) with (canon mo). apply mrel_canon.
        - exact (bm_mat_nodup _ _ _ _ HMOD).
        - intros p Hp. destruct (bm_mat _ _ _ _ HMOD p Hp) as (Hal & _ & Hallow). apply A0_init; assumption. }
      eapply SpinAlg.srz_conseq.
      + (* the main body over the run's list, at the run's ROM, as BothMain *)
        exact (ITreeALift.implF_srealizes_run bsegs (vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)) fstepS NMAX _
                 _ _ _ ms (MX mo []) mo (vdso_nonexec (in_kernel inp) (en_sp en) (en_mmap_base en)) HT).
      +
        destruct (equiv_PA_asan_toP_D lim Hlim D0 D2 PREAD_STAGE rsA V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [HEQ _].
        intros tr. unfold TAC. symmetry. apply HEQ.
  Qed.

  Lemma both_sideC : asan_sideC_stmt bsegs b_init_pc b_phdrs.
  Proof. unfold asan_sideC_stmt. intros lim Hlim. apply both_side_ok. exact (both_sideC_main lim Hlim). Qed.

  Theorem halts_bothC : halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes (mkImage bsegs b_init_pc b_phdrs).
  Proof.
    apply (halts_of_srealizes bsegs b_init_pc b_phdrs (TAC (2^31))). intros en inp Hv Hi. cbv zeta. split.
    - exact (both_side_srz_lim (TAC (2^31)) source_alloc_limit (Z.le_refl _) (both_sideC_main (2^31) (Z.le_refl _)) en inp Hv Hi).
    - unfold TAC. apply tree_traces_ends_in_any.
  Qed.

  Theorem base_both :
    strong_universal_error_free_T_scfg_budgets alloc_forced_cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage psegs p_init_pc p_phdrs) (mkImage bsegs b_init_pc b_phdrs).
  Proof. exact (zc_base_asan plain_implC bsegs b_init_pc b_phdrs both_sideC). Qed.

  Theorem base_both_plain :
    strong_universal_error_free_T_scfg alloc_forced_cfg (mkImage psegs p_init_pc p_phdrs) (mkImage bsegs b_init_pc b_phdrs).
  Proof. exact (zc_base_asan_plain plain_implC bsegs b_init_pc b_phdrs both_sideC). Qed.
End Assembly.
