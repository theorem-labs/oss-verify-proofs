(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only Require Import TopLevel ZTopC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import ITree Nodes InitMem RunConst CTree.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF CTreeA.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import HaltsA.   (* [comment removed for export] *)
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require ShapeAlg SpinAlg.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.MainExport OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AS.MainFactsAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AS.MainEntry.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.Monad OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.CMonad OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.Prog OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.ProgA OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.ProgC OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.ProgAC OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.EquivPA OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanProgDeps OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanOK OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.Spec.AsanHandoff OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.ModelOKC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Plain Require Import PImg.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AImg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.AProto OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW.CProto OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X2W.AsanW.ATsafeMain.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.FO Require Import FOCore FOStep.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require ITreeALift.   (* an earlier development run row 27 727298f3 A1, after an earlier development run's rows 1-3 AsanMain e5bd7a6e: an earlier development run b6238b32 *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition amain_open (en : ExecEntry) (inp : ProcInput) (w : bool) (V : nat -> Z) (m : word -> option byte)
    (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
    ms = MS (mkR (Z_to_bv 64 ARA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 AGP) (Z_to_bv 64 ATP)
                 (Z_to_bv 64 (V 1032%nat)) (Z_to_bv 64 (V 1033%nat)) (Z_to_bv 64 (V 1034%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 1035%nat)) (Z_to_bv 64 (V 1036%nat)) (Z_to_bv 64 (V 1037%nat)) (Z_to_bv 64 (V 1038%nat))
                 (Z_to_bv 64 AMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 1039%nat)) (Z_to_bv 64 (V 1040%nat)) (Z_to_bv 64 (V 1041%nat)) (Z_to_bv 64 (V 1042%nat)))
            bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None m (seg_rom asegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    (* [comment removed for export] *)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wpad en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp)
        (* an earlier development run row 27 727298f3: AS/MainEntry's amain_at, copied (rows 1-3: an earlier development run e5bd7a6e) *)
        /\ V 11%nat = Z.of_nat (StackLayout.block_items (in_argv inp) (in_envp inp) mod 2))
    /\ Forall (mfact_ok asegs V m) (asan_mem_facts ++ asan_mem_facts_w w)
    /\ Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w)
    /\ Forall (mfact_ok asegs V m) (asan_argv_facts (AsanPlanCore.APC.rseq_z (kb_rseq (in_kernel inp))))
    /\ mem_inv asegs m
    /\ stk asegs m (usp - ASTK) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem inp (en_mmap_base en) a_phdrs (Z_to_bv 64 (Z.of_N a_init_pc))
                       (en_sp en) (en_draw en) (wa a))
    /\ ashadow0 V m
    /\ amodel V (en_sp en) (in_fs inp) mo.

Lemma amain_at_open : forall en inp ms mo,
  amain_at en inp ms mo <-> exists w V m, amain_open en inp w V m ms mo.
Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)
Definition RNG0 {rc : runConstT} (V : nat -> Z) (mo : Model) : footprint := fp_ok (m_vm_lazy (MX mo [])) (A0 V).

(* [comment removed for export] *)
Definition TTC : Empty_set -> APS -> footprint -> machine_state -> Prop := fun _ _ _ _ => True.

(* [comment removed for export] *)
Definition asan_implC_stmt (rsA : Z) : Prop :=
  forall (rc : runConstT) en inp w V m ms mo,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
    amain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
    implMAC (RNG0 V mo) (progA_mainC AAllocAsan rsA (argv_Z (in_argv inp)))
            (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) TTC ms.

Section Assembly.
  Hypothesis plain_implC : plain_implC_stmt.
  Variable rsA : Z.
  Hypothesis asan_implC : asan_implC_stmt rsA.

  Lemma valid_sp_of_entry : forall en inp, valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> valid_sp (en_sp en).
  Proof.
    intros [sp brk mb draw] inp Hv Hi. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv. destruct Hv as (Hsp & _). exact Hsp.
  Qed.

  (* [comment removed for export] *)
  Lemma asan_sideC_main : forall lim, 2^31 <= lim -> forall en inp,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
    TAC lim inp en [] /\ forall ms mo, amain_at en inp ms mo ->
      SpinAlg.srealizes (asegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))
        (mkCfg (TopLevel.set_rom (seg_rom (asegs ++ vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en))) ms) mo)
        (TAC lim inp en).
  Proof.
    intros lim Hlim en inp Hv Hi. split.   (* [comment removed for export] *)
    - (* [comment removed for export] *)
      pose proof (toP_valid _ _ _ en inp Hv) as HvP.
      destruct (plain_side_okC plain_implC lim Hlim (toP en) inp HvP Hi) as [Htr _].
      unfold TAC.
      apply (proj1 (equiv_PP_D lim Hlim (DP inp (toP en)) D0 PREAD_STAGE PREAD_STAGE (toP en) (toP en) inp HvP HvP Hi [])).
      change (tree_traces (tP inp (toP en)) (mo0 psegs lim (toP en) inp) []).
      apply Htr. rewrite run_init_config. cbn [bh_traces]. apply obs_trace_cfg_nil.
    - intros ms mo HM.
      apply amain_at_open in HM as (w & V & m & HM).
      pose proof HM as (_ & HV & _ & _ & HP & _ & _ & _ & _ & _ & HMOD).
      apply Forall_app in HP as [HP _].
      set (rc := run_consts_of en (Z_to_bv 64 0) (valid_sp_of_entry en inp Hv Hi)).
      assert (HA : atop_of (en_sp en) = @ATOP rc) by reflexivity.
      assert (HAT : a_usp0 V - 8388608 = @ATOP rc).
      { rewrite <- HA. unfold atop_of, a_usp0. destruct HM as (_ & _ & (_ & _ & _ & E & _) & _). cbv zeta in E. lia. }
      (* [comment removed for export] *)
      destruct (implMAC_RES (RNG0 V mo) (progA_mainC AAllocAsan rsA (argv_Z (in_argv inp))) _ TTC ms
                  ltac:(intros; exact I) (asan_implC rc en inp w V m ms mo Hv Hi HM HA)) as [D2 HD].
      assert (HT : tree_atA asegs (at_nodeA asegs) nstepA minvA (nsafeA NMAX) fstepS NMAX (RNG0 V mo) (A0 V)
                     (progA_treeD AAllocAsan D2 (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp)))
                     (epostF (fun (_ : unit) (_ : footprint) (_ : machine_state) => True)) ms (MX mo []) mo).
      { rewrite HA. split.
        { unfold progA_treeD, progA_mainD. eapply implF_ebind; [exact HD|]. intros [e ?] RNG' ms' _. destruct e. }
        split. { rewrite <- HA. destruct (equiv_PA_asan_toP_D lim Hlim D0 D2 PREAD_STAGE rsA V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [_ HL]. exact HL. }
        split. { rewrite m_halted_MX. exact (am_halted _ _ _ _ HMOD). }
        (* an earlier development run row 27 727298f3: minvA_std_fds' appended premise (rt-model-equiv sem727 c2), the channel reader: amodel's am_rdr *)
        split. { apply minvA_std_fds; [rewrite m_fds_MX; exact (am_fds _ _ _ _ HMOD) | reflexivity | | exact (am_rdr _ _ _ _ HMOD)].
                 rewrite m_vmmaps_MX, (am_top _ _ _ _ HMOD). pose proof (am_usp _ _ _ _ HMOD). unfold sp_window_lo, sp_window_hi. lia. }
        split. { rewrite <- HA. exact (progA_tsafeD V HP HAT (en_sp en) HA D2 rsA inp mo HMOD). }
        change (MX mo []) with (canon mo). apply mrel_canon.
        - exact (am_mat_nodup _ _ _ _ HMOD).
        - intros p Hp. destruct (am_mat _ _ _ _ HMOD p Hp) as (Hal & _ & Hallow). apply A0_init; assumption. }
      eapply SpinAlg.srz_conseq.
      + (* an earlier development run row 27 727298f3 A1 (rows 1-3: an earlier development run e5bd7a6e): the main body over the run's list, at the run's
           ROM (an earlier development run's LibA/ITreeALift b6238b32, implF_srealizes_run) *)
        exact (ITreeALift.implF_srealizes_run asegs (vdso_segments (in_kernel inp) (en_sp en) (en_mmap_base en)) fstepS NMAX _
                 _ _ _ ms (MX mo []) mo (vdso_nonexec (in_kernel inp) (en_sp en) (en_mmap_base en)) HT).
      + (* [comment removed for export] *)
        destruct (equiv_PA_asan_toP_D lim Hlim D0 D2 PREAD_STAGE rsA V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [HEQ _].
        intros tr. unfold TAC. symmetry. apply HEQ.
  Qed.

  Lemma asan_sideC : asan_sideC_stmt asegs a_init_pc a_phdrs.
  Proof. unfold asan_sideC_stmt. intros lim Hlim. apply asan_side_ok. exact (asan_sideC_main lim Hlim). Qed.

  (* [comment removed for export] *)
  Theorem halts_asanC : halts_core alloc_forced_cfg source_alloc_limit AnyExit.codes (mkImage asegs a_init_pc a_phdrs).
  Proof.
    apply (halts_of_srealizes asegs a_init_pc a_phdrs (TAC (2^31))). intros en inp Hv Hi. cbv zeta. split.
    - exact (asan_side_srz_lim (TAC (2^31)) source_alloc_limit (Z.le_refl _) (asan_sideC_main (2^31) (Z.le_refl _)) en inp Hv Hi).
    - unfold TAC. apply tree_traces_ends_in_any.
  Qed.

  (* [comment removed for export] *)
  Theorem base_asan :
    strong_universal_error_free_T_scfg_budgets alloc_forced_cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage psegs p_init_pc p_phdrs) (mkImage asegs a_init_pc a_phdrs).
  Proof. exact (zc_base_asan plain_implC asegs a_init_pc a_phdrs asan_sideC). Qed.

  (* [comment removed for export] *)
  Theorem base_asan_plain :
    strong_universal_error_free_T_scfg alloc_forced_cfg (mkImage psegs p_init_pc p_phdrs) (mkImage asegs a_init_pc a_phdrs).
  Proof. exact (zc_base_asan_plain plain_implC asegs a_init_pc a_phdrs asan_sideC). Qed.
End Assembly.
