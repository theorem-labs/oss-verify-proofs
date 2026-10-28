(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require Import TopLevel TopLevelSB.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg ITree Nodes.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require ShapeAlg SpinAlg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import MainExport MainFactsBoth BothEntry.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import Prog ProgA EquivPA AsanProgDeps AsanInv AsanOK ImgFacts BothHandoff ModelOK.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition plain_tree_ok_stmt : Prop :=
  forall L, 2^31 <= L ->
  tree_ok psegs p_init_pc p_phdrs L
          (Prog.prog psegs PREAD_STAGE) (epost (fun (_ : unit) (_ : machine_state) => True)).

(* [comment removed for export] *)
Definition TA (L : Z) : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp (toP en)) (mo0 psegs L (toP en) inp).

(* [comment removed for export] *)
Definition TP (L : Z) : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp en) (mo0 psegs L en inp).

Lemma plain_no_kill : forall L, tfam_no_kill (TP L).
Proof. intros L. exact (tfam_no_kill_tree psegs L (Prog.prog psegs PREAD_STAGE)). Qed.

(* [comment removed for export] *)
Definition amodelH (V : nat -> Z) (sp : word) fs (mo : Model) : Prop :=
  LIMIT34 <= vm_limit (m_vmmaps mo) /\ amodelL (vm_limit (m_vmmaps mo)) V sp fs mo.

Lemma amodelH_of_amodelL : forall lim V sp fs mo, LIMIT34 <= lim -> amodelL lim V sp fs mo -> amodelH V sp fs mo.
Proof. intros lim V sp fs mo HL HM. unfold amodelH. rewrite (amL_limit _ _ _ _ _ HM). split; [exact HL| exact HM]. Qed.

Lemma amodelH_of_amodel : forall V sp fs mo, amodel V sp fs mo -> amodelH V sp fs mo.
Proof.
  intros V sp fs mo HM. apply (amodelH_of_amodelL target_alloc_limit); [| apply amodel_amodelL; exact HM].
  rewrite <- LIMIT_eq. apply LIMIT34_le_LIMIT.
Qed.

(* [comment removed for export] *)
Definition amain_open (en : ExecEntry) (inp : ProcInput) (w : bool) (V : nat -> Z) (m : word -> option byte)
    (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
    ms = MS (mkR (Z_to_bv 64 ARA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 AGP) (Z_to_bv 64 ATP)
                 (Z_to_bv 64 (V 664%nat)) (Z_to_bv 64 (V 665%nat)) (Z_to_bv 64 (V 666%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 667%nat)) (Z_to_bv 64 (V 668%nat)) (Z_to_bv 64 (V 669%nat)) (Z_to_bv 64 (V 670%nat))
                 (Z_to_bv 64 AMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 671%nat)) (Z_to_bv 64 (V 672%nat)) (Z_to_bv 64 (V 673%nat)) (Z_to_bv 64 (V 674%nat)))
            bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok bsegs V m) (asan_mem_facts ++ asan_mem_facts_w w)
    /\ Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w)
    /\ mem_inv bsegs m
    /\ stk bsegs m (usp - 8388608) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (wa a))
    /\ ashadow0 V m
    /\ amodelH V (en_sp en) (in_fs inp) mo.

Lemma amain_atL_open : forall lim en inp ms mo, LIMIT34 <= lim ->
  amain_atL lim en inp ms mo -> exists w V m, amain_open en inp w V m ms mo.
Proof.
  intros lim en inp ms mo HL (w & V & m & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). exists w, V, m.
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 _))))))))).
  exact (amodelH_of_amodelL lim _ _ _ _ HL H10).
Qed.

Lemma amain_at_open : forall en inp ms mo,
  amain_at en inp ms mo -> exists w V m, amain_open en inp w V m ms mo.
Proof.
  intros en inp ms mo HM. apply (amain_atL_open target_alloc_limit); [| apply amain_at_amain_atL; exact HM].
  rewrite <- LIMIT_eq. apply LIMIT34_le_LIMIT.
Qed.

(* [comment removed for export] *)
Definition asan_impl_stmt (rsA : Z) : Prop :=
  forall en inp w V m ms mo,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    amain_open en inp w V m ms mo ->
    exists NMAX RNG A Q,
      tree_atA bsegs (at_nodeA bsegs) nstepA minvA (nsafeA NMAX) fstepS NMAX RNG A
        (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp)))
        Q ms (MX mo []) mo.

Section Assembly.
  Variable rsA : Z.
  Hypothesis plain_ok : plain_tree_ok_stmt.   (* [comment removed for export] *)
  Hypothesis asan_impl : asan_impl_stmt rsA.

  Lemma plain_side_ok : forall L, 2^31 <= L -> side_ok psegs p_init_pc p_phdrs L (TP L).
Proof. intros L HL. exact (side_ok_of_tree_ok _ _ _ _ _ _ (plain_ok L HL)). Qed.

  (* [comment removed for export] *)
  Lemma asan_main_srealizes : forall L, 2^31 <= L -> forall en inp,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    forall ms mo, (exists w V m, amain_open en inp w V m ms mo) -> SpinAlg.srealizes bsegs (mkCfg ms mo) (TA L inp en).
Proof.
    intros L HL en inp Hv Hi ms mo (w & V & m & HM).
    pose proof HM as (_ & _ & _ & _ & HP & _ & _ & _ & _ & [HLIM HMOD]).
    apply Forall_app in HP as [HP _].
    destruct (asan_impl en inp w V m ms mo Hv Hi HM) as (NMAX & RNG & A & Q & HT).
    eapply SpinAlg.srz_conseq.
    + exact (implF_srealizes bsegs (at_nodeA bsegs) nstepA nexitA minvA (nsafeA NMAX) fstepS NMAX (nodesA_sound bsegs NMAX) _ RNG A Q ms (MX mo []) mo HT).
    +
      destruct (equiv_PA_asan_toP_LL (vm_limit (m_vmmaps mo)) HLIM L HL PREAD_STAGE rsA V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [HEQ _].
      intros tr. unfold TA. symmetry. apply HEQ.
  Qed.

  Lemma asan_side : forall L, 2^31 <= L -> side_ok bsegs b_init_pc b_phdrs target_alloc_limit (TA L).
Proof.
    intros L HL. apply asan_side_ok. intros en inp Hv Hi. split.
    -
      destruct (plain_side_ok L HL (toP en) inp (toP_valid _ _ _ en inp Hv) Hi) as [Htr _].
      apply Htr. rewrite run_init_config. cbn [bh_traces]. apply obs_trace_cfg_nil.
    - intros ms mo HM. apply amain_at_open in HM. exact (asan_main_srealizes L HL en inp Hv Hi ms mo HM).
  Qed.

  (* [comment removed for export] *)
  Theorem base_asan :
    strong_universal_error_free_T_scfg_budgets (alloc_only_cfg false) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
      (mkImage psegs p_init_pc p_phdrs)
      (mkImage bsegs b_init_pc b_phdrs).
  (* [comment removed for export] *)
  Proof.
    eapply (side_ok_equiv_sb _ _ _ _ _ _ (TP sanitizer_source_limit) (TA sanitizer_source_limit));
      [exact (plain_side_ok _ lim_sb) | exact (asan_side _ lim_sb) |].
    intros enS enT inp HvS HvT Hi. unfold TP, TA.
    apply (equiv_PP_L _ lim_sb); [exact HvS | exact (toP_valid _ _ _ enT inp HvT) | exact Hi].
  Qed.
End Assembly.
(* [comment removed for export] *)
(* [comment removed for export] *)
