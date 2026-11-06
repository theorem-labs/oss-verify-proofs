(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prog Canon.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require RT_iface RT_rep D_libiface L_libA TopA_cert.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require TopLevelA.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prog Canon.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_cert.TwinB__.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require Import TopLevelA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem canon_B0_of : rt_contracts RTA -> fuzz_one_cps RTA LIB_A ->
  forall en inp,
    valid_entry (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs) en inp ->
    valid_input_either inp ->
    trace_equiv (bh_traces (Run.run_scfg (Run.alloc_only_cfg false) (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs)
                                    target_alloc_limit en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (Run.run_scfg (Run.alloc_only_cfg false) (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs)
                            target_alloc_limit en inp).
Proof. intros RC FUZZ. exact (T_canon _ _ _ (s3s_A_rc RC FUZZ)). Qed.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Asan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prog Canon.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import RT_iface RT_rep D_libiface L_libA TopA_cert.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require Import TopLevelA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem canon_A0_of : rt_contracts RTA -> fuzz_one_cps RTA LIB_A ->
  forall en inp,
    valid_entry (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs) en inp ->
    valid_input_either inp ->
    trace_equiv (bh_traces (Run.run_scfg (Run.alloc_only_cfg false) (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs)
                                    target_alloc_limit en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (Run.run_scfg (Run.alloc_only_cfg false) (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs)
                            target_alloc_limit en inp).
Proof. intros RC FUZZ. exact (T_canon _ _ _ (s3s_A_rc RC FUZZ)). Qed.
