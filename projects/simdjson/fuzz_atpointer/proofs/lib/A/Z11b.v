(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Asan.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Zks Zkt Zm2 RT_rep Zl3 Zls Zm7 Zm3
  Zm4 Zm5 Zm6 Zlj Zi8 Zi9 Zl6 Zki Zis Zip Zim
  Zjl Zj1 Ziy Zju Z7w Z11a.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Z78 Z2z Z2y Z10c.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Import ProofBase TopLevelA.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Cfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem base_asan : forall CL : client_A,
  (forall h ch, HS_asan h = Some ch -> cl_hs_ok CL ch = true) ->
  impl_P_stmt ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof.
  intros CL HS_cl HP.
  exact (base_asan_rc CL HS_cl
           (rta_contracts2 (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
              (rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok))) HP).
Qed.

Theorem s3s_asan : forall CL : client_A,
  (forall h ch, HS_asan h = Some ch -> cl_hs_ok CL ch = true) ->
  S3s_stmt_e Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof.
  intros CL HS_cl.
  exact (s3s_A_rc CL HS_cl
           (rta_contracts2 (refill_ok fixed_commit_ok) (mal_core_sec grant_node_ok fixed_commit_pab_ok)
              (rta_free (drain_ok rhead_empty_ok fixed_commit_ok (fun p HOK => item_sec_ok p munmap_ok madvise_ok HOK)) fixed_commit_ok (free_pass_ok munmap_ok madvise_ok)))).
Qed.
