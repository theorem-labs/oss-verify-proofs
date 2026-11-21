(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound Require Import TopLevel CkTop.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.FO Require FOCore.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require HaltsB.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require ITreeALift.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import HaltsA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Spec Require Import Prog ProgA EquivPA AsanProgDeps AsanOK AsanHandoffBoth ModelOK.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Plain Require Import PImg.
Require OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Plain.PlainClosed.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.BothW Require Import BImg AProto.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma plain_impl_closed : plain_impl_stmt.
Proof. exact Plain.PlainClosed.plain_impl_closed. Qed.

Definition bmain_open (en : ExecEntry) (inp : ProcInput) (w : bool) (V : nat -> Z) (m : word -> option byte)
    (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
    ms = MS (mkR (Z_to_bv 64 BRA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 BGP) (Z_to_bv 64 BTP)
                 (Z_to_bv 64 (V 696%nat)) (Z_to_bv 64 (V 697%nat)) (Z_to_bv 64 (V 698%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 699%nat)) (Z_to_bv 64 (V 700%nat)) (Z_to_bv 64 (V 701%nat)) (Z_to_bv 64 (V 702%nat))
                 (Z_to_bv 64 BMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 703%nat)) (Z_to_bv 64 (V 704%nat)) (Z_to_bv 64 (V 705%nat)) (Z_to_bv 64 (V 706%nat)))
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

Definition both_impl_stmt (rsA : Z) : Prop :=
  forall en inp w V m ms mo,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    bmain_open en inp w V m ms mo ->
    exists NMAX RNG A Q,
      tree_atA bsegs (at_nodeA bsegs) nstepA minvA (nsafeA NMAX) fstepS NMAX RNG A
        (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp)))
        Q ms (MX mo []) mo.

Section Assembly.
  Variable rsA : Z.
  Hypothesis both_impl : both_impl_stmt rsA.

  Lemma both_side_main : forall lim, 2^31 <= lim -> forall en inp,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    TA lim inp en [] /\ forall ms mo, bmain_at en inp ms mo ->
      SpinAlg.srealizes (bsegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
        (mkCfg (TopLevel.set_rom (seg_rom (bsegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))) ms) mo)
        (TA lim inp en).
  Proof.
    intros lim Hlim en inp Hv Hi. split.
    -
      destruct (plain_side_ok plain_impl_closed lim Hlim (toP en) inp (toP_valid _ _ _ en inp Hv) Hi) as [Htr _].
      apply Htr. rewrite run_init_config. cbn [bh_traces].
      eexists [], _. split; [apply star_cfg_refl | apply is_prefix_nil].
    - intros ms mo HM.
      apply bmain_at_open in HM as (w & V & m & HM).
      pose proof HM as (_ & _ & _ & _ & HP & _ & _ & _ & _ & _ & HMOD).
      apply Forall_app in HP as [HP _].
      destruct (both_impl en inp w V m ms mo Hv Hi HM) as (NMAX & RNG & A & Q & HT).
      eapply SpinAlg.srz_conseq.
      + (* the main body over the run's list, at the run's ROM *)
        exact (ITreeALift.implF_srealizes_run bsegs (vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)) fstepS NMAX _
                 RNG A Q ms (MX mo []) mo (vdso_nonexec (in_kernel inp) (en_sp en) (en_mmap_base en)) HT).
      +
        destruct (equiv_PA_asan_toP lim Hlim PREAD_STAGE rsA V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [HEQ _].
        intros tr. unfold TA. symmetry. apply HEQ.
  Qed.

  Lemma both_side : asan_side_stmt bsegs b_init_pc b_phdrs.
  Proof. unfold asan_side_stmt. intros lim Hlim. apply both_side_ok. exact (both_side_main lim Hlim). Qed.

  Theorem halts_both :
    halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source AnyExit.codes (mkImage bsegs b_init_pc b_phdrs).
  Proof.
    apply (HaltsB.halts_B_of_srealizes bsegs b_init_pc b_phdrs (TA (2^31))). intros en inp Hv Hi. cbv zeta. split.
    - exact (both_side_srz_lim (TA (2^31)) source_alloc_limit (Z.le_refl _) (both_side_main (2^31) (Z.le_refl _)) en inp Hv Hi).
    - unfold TA. apply tree_traces_ends_in_any.
  Qed.

  Theorem base_both :
    strong_universal_error_free_T_scfg_budgets FOCore.alloc_forced_cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage psegs p_init_pc p_phdrs)
      (mkImage bsegs b_init_pc b_phdrs).
  Proof. exact (ck_base_asan plain_impl_closed bsegs b_init_pc b_phdrs both_side). Qed.

  Theorem base_both_plain :
    strong_universal_error_free_T_scfg FOCore.alloc_forced_cfg
      (mkImage psegs p_init_pc p_phdrs)
      (mkImage bsegs b_init_pc b_phdrs).
  Proof. exact (ck_base_asan_plain plain_impl_closed bsegs b_init_pc b_phdrs both_side). Qed.
End Assembly.
