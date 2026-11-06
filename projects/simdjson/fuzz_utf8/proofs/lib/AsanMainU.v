(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes InitMem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import Prog ProgA ProgZ EquivZA ModelZ ZSafe AsanProgDeps AsanOK AsanHandoff.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg.
Require OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Spec.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg AProto.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition main_open (en : ExecEntry) (inp : ProcInput) (w : bool) (V : nat -> Z) (m : word -> option byte)
    (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
      ms = MS (mkR (Z_to_bv 64 ARA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 AGP) (Z_to_bv 64 ATP)
                 (Z_to_bv 64 (V 1945%nat)) (Z_to_bv 64 (V 1946%nat)) (Z_to_bv 64 (V 1947%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 1948%nat)) (Z_to_bv 64 (V 1949%nat)) (Z_to_bv 64 (V 1950%nat)) (Z_to_bv 64 (V 1951%nat))
                 (Z_to_bv 64 AMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 1952%nat)) (Z_to_bv 64 (V 1953%nat)) (Z_to_bv 64 (V 1954%nat)) (Z_to_bv 64 (V 1955%nat)))
            bvmap_empty (Z_to_bv 64 AMAIN) (Z_to_bv 32 0) None m (seg_rom asegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    (* [comment removed for export] *)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok asegs V m) (asan_mem_facts ++ asan_mem_facts_w w)
    /\ Forall (pfact_ok V) (asan_pure_facts ++ asan_pure_facts_w w)
    /\ mem_inv asegs m
    /\ stk asegs m (usp - 8388608) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem a_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (wa a))
    /\ ashadow0 V m
    /\ amodel V (en_sp en) (in_fs inp) mo.

Lemma main_at_open : forall en inp ms mo,
  amain_at en inp ms mo <-> exists w V m, main_open en inp w V m ms mo.
Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)
Definition impl_stmt (rsA : Z) : Prop :=
  forall en inp w V m ms mo,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
    main_open en inp w V m ms mo ->
    exists NMAX RNG A Q,
      tree_atA asegs (at_nodeA asegs) nstepA minvA (nsafeA NMAX) fstepS NMAX RNG A
        (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp)))
        Q ms (MX mo []) mo.

Section Assembly.
  (* [comment removed for export] *)
  Local Notation SPEC := OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common.Spec.spec.
  Definition TS : tfam := fun inp _ => SPEC (in_argv inp) (in_fs inp).

  (* [comment removed for export] *)
  Hypothesis PLAIN : side_ok psegs p_init_pc p_phdrs source_alloc_limit TS.
  Hypothesis NOKILL : tfam_no_kill TS.
  Hypothesis SPEC_nil : forall argv fs, SPEC argv fs [].

  Variable rsA : Z.
  Hypothesis IMPL : impl_stmt rsA.

  Lemma target_side : side_ok asegs a_init_pc a_phdrs target_alloc_limit TS.
  Proof.
    apply asan_side_ok. intros en inp Hv Hi. split.
    - apply SPEC_nil.
    - intros ms mo HM.
      apply main_at_open in HM as (w & V & m & HM).
      pose proof HM as (_ & _ & _ & _ & HP & _ & _ & _ & _ & HMOD).
      apply Forall_app in HP as [HP _].
      destruct (IMPL en inp w V m ms mo Hv Hi HM) as (NMAX & RNG & A & Q & HT).
      eapply SpinAlg.srz_conseq.
      + exact (implF_srealizes asegs (at_nodeA asegs) nstepA nexitA minvA (nsafeA NMAX) fstepS NMAX (nodesA_sound asegs NMAX) _ RNG A Q ms (MX mo []) mo HT).
      + (* [comment removed for export] *)
        destruct (moZ0_ok inp) as (Z1 & Z2 & Z3 & Z4).
        destruct (equiv_ZA_asan 0 rsA V (en_sp en) inp mo (moZ0 inp) Hi HMOD HP Z1 Z2 Z3 Z4 (progZ_no_leaf inp (moZ0 inp) 0 Hi Z1 Z2 Z3 Z4)) as [HEQ _].
        intros tr. unfold TS. rewrite <- (bridgeU' inp (moZ0 inp) 0 Hi Z1 Z2 Z3 Z4 tr). symmetry. apply HEQ.
  Qed.

  (* [comment removed for export] *)
  Theorem base :
    strong_universal_error_free_T_scfg_budgets_abort ACFG ShippedBudgets.lim_source ShippedBudgets.lim_target
      (mkImage psegs p_init_pc p_phdrs)
      (mkImage asegs a_init_pc a_phdrs).
  Proof.
    eapply (side_ok_equiv_budgets_abort _ _ _ _ _ _ TS TS); [exact PLAIN | exact target_side | exact NOKILL |].
    intros enS enT inp HvS HvT Hi tr. reflexivity.
  Qed.

  (* [comment removed for export] *)
End Assembly.
