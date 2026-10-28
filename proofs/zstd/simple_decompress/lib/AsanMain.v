(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import TopLevel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require TopLevelGenB.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require ImgFacts.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require ShapeAlg SpinAlg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntryAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prog ProgA EquivPA AsanProgDeps AsanOK AsanHandoff ModelOK.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AProto.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


(* [comment removed for export] *)
Definition TB : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp (toP en)) (mo0 psegs source_alloc_limit (toP en) inp).

(* [comment removed for export] *)
Definition TP : tfam := fun inp en => tree_traces (prog psegs PREAD_STAGE inp en) (mo0 psegs source_alloc_limit en inp).

(* [comment removed for export] *)
Definition bmain_open (en : ExecEntry) (inp : ProcInput) (w : bool) (V : nat -> Z) (m : word -> option byte)
    (ms : machine_state) (mo : Model) : Prop :=
  let usp := bv_unsigned (en_sp en) in
  let argc := Z.of_nat (length (in_argv inp)) in
  let envc := Z.of_nat (length (in_envp inp)) in
    ms = MS (mkR (Z_to_bv 64 BRA) (Z_to_bv 64 (usp - 48)) (Z_to_bv 64 BGP) (Z_to_bv 64 BTP)
                 (Z_to_bv 64 (V 1128%nat)) (Z_to_bv 64 (V 1129%nat)) (Z_to_bv 64 (V 1130%nat))
                 (Z_to_bv 64 (usp + 8)) (Z_to_bv 64 argc) (Z_to_bv 64 argc) (Z_to_bv 64 (usp + 8))
                 (Z_to_bv 64 (usp + 8 * argc + 16)) (Z_to_bv 64 0x6000000000000000)
                 (Z_to_bv 64 (V 1131%nat)) (Z_to_bv 64 (V 1132%nat)) (Z_to_bv 64 (V 1133%nat)) (Z_to_bv 64 (V 1134%nat))
                 (Z_to_bv 64 BMAIN) (Z_to_bv 64 (usp + 8 * argc + 16))
                 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                 (Z_to_bv 64 (V 1135%nat)) (Z_to_bv 64 (V 1136%nat)) (Z_to_bv 64 (V 1137%nat)) (Z_to_bv 64 (V 1138%nat)))
            bvmap_empty (Z_to_bv 64 BMAIN) (Z_to_bv 32 0) None m (seg_rom bsegs)
    /\ (forall n, 0 <= V n < 2 ^ 64)
    /\ (V 0%nat = usp / 32768 /\ V 6%nat = usp mod 4096 / 16 /\ V 10%nat = usp mod 32768 / 4096
        /\ 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat = usp
        /\ V 1%nat = argc /\ V 2%nat = envc
        /\ V 3%nat = Z.of_nat (length (nth 0 (in_argv inp) [])) /\ V 7%nat = Z.of_nat (length (nth 1 (in_argv inp) []))
        /\ V 4%nat = Wblk en inp /\ V 5%nat = bv_unsigned (en_brk en) / 4096 /\ V 8%nat = bv_unsigned (in_uid inp)
        /\ V 9%nat = bv_unsigned (in_hwcap inp))
    /\ Forall (mfact_ok bsegs V m) (both_mem_facts ++ both_mem_facts_w w)
    /\ Forall (pfact_ok V) (both_pure_facts ++ both_pure_facts_w w)
    /\ mem_inv bsegs m
    /\ stk bsegs m (usp - 8388608) usp
    /\ (forall a, hidden_arg en inp a ->
          m (wa a) = wrap_mem b_phdrs (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en) (wa a))
    /\ bshadow0 V m
    /\ bmodel V (en_sp en) (in_fs inp) mo.

Lemma bmain_at_open : forall en inp ms mo,
  bmain_at en inp ms mo <-> exists w V m, bmain_open en inp w V m ms mo.
Proof. intros; reflexivity. Qed.

(* [comment removed for export] *)
Definition both_impl_stmt (rsA : Z) : Prop :=
  forall en inp w V m ms mo,
    valid_entry (mkImage bsegs b_init_pc b_phdrs) en inp -> valid_input_either inp ->
    bmain_open en inp w V m ms mo ->
    exists NMAX RNG A Q,
      tree_atA bsegs (at_nodeA bsegs) nstepA minvA (nsafeA NMAX) fstepS NMAX RNG A
        (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp)))
        Q ms (MX mo []) mo.

