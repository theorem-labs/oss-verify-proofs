(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require MmapSim.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM09. Import SM09. Import SM09.Prelim. Import SM09.STree. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import Malloc. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import KInv. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import KLink. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require SM01. Import SM01. Import SM01.KStep. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.Spec Require Import KEv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma nstep_mmap_grant : forall len mo (a : word),
  0 < len < 2^63 ->
  MmapSim.grant_ok (Z_to_bv 64 0) mo a (page_round_up_Z len) = true ->
  exists mo', nstep (NMmap 0 len PROT_RW MAPF) mo
                (mkEffectU a [] [(a, Z_to_bv 64 (page_round_up_Z len))] [] [] []) mo' [].
Proof.
  intros len mo a Hlen Hg.
  assert (Hn0 : 0 <= page_round_up_Z len) by (apply page_round_up_Z_nonneg; lia).
  pose proof (MmapSim.grant_not_errno _ _ _ _ Hn0 Hg) as Hne.
  unfold MmapSim.grant_ok in Hg.
  (* grant_ok leads with Linux's placement (linux_place_is), and check_mmap's modeled
     arm grants exactly that address (after the decline gate, which the NULL hint never takes). *)
  apply andb_prop in Hg as [Hg Hbud]. apply andb_prop in Hg as [Hg Hfree]. apply andb_prop in Hg as [Hg Htop].
  apply andb_prop in Hg as [Hg Hpos]. apply andb_prop in Hg as [Hplace Hal].
  eexists. apply nstep_mmap_iff. split; [reflexivity|].
  unfold check_mmap.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true. change (mmap_anon_b (Z_to_bv 64 MAPF)) with true. cbn [negb].
  rewrite w_is0_lit by lia. replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  change (mmap_modeled_b (Z_to_bv 64 PROT_RW) (Z_to_bv 64 MAPF) (Z_to_bv 64 0)) with true. cbv iota beta.
  replace (place_declined_b (m_kernel mo) (m_vmmaps mo) (Z_to_bv 64 0) (page_round_up_Z (bv_unsigned (Z_to_bv 64 len))))
    with false by reflexivity.
  rewrite Hne. rewrite (unsigned_lit len) by lia. cbv zeta.
  rewrite Hplace. cbn [andb].
  unfold mmap_noreserve_backed_ok. change (mmap_noreserve_b (Z_to_bv 64 MAPF)) with false. cbv iota.
  rewrite Hbud. cbn [andb]. rewrite (proj2 (listNN_eqb_eq _ _) eq_refl). reflexivity.
Qed.
