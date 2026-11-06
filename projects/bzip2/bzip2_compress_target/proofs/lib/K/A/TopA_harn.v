(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Prog Canon.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require RT_iface RT_rep RT_closed D_libiface L_libA L_harn_defs L_harn TopA_final.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import AsanUbsan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prog Canon.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_closed.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_libA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.TopA_final.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Lib.
Variable enc_ok : list byte -> Z -> Z -> list byte -> Prop.
Variable dec_ok : list byte -> bool -> Z -> list byte -> Prop.
Hypothesis B2BC : b2bc_cps RTA LIB_A enc_ok.
Hypothesis B2BD : b2bd_cps RTA LIB_A dec_ok.
Hypothesis RTW : round_trip_weak enc_ok dec_ok.

Theorem fuzz_one_B0 : fuzz_one_cps RTA LIB_A.
Proof using B2BC B2BD RTW.
  pose proof rta_contracts_closed as RC.
  exact (harness_ok RTA LIB_A enc_ok dec_ok (rc_facts RTA RC) LIB_locA (rc_stack_malloc_0 RTA RC) (rc_malloc RTA RC) (rc_malloc0 RTA RC) (rc_free RTA RC) (rc_memcmp RTA RC) B2BC B2BD RTW).
Qed.

Theorem canon_B0_of_lib :
  forall en inp,
    valid_entry (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs) en inp ->
    valid_input_either inp ->
    trace_equiv (bh_traces (Run.run_scfg (Run.alloc_only_cfg false) (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs)
                                    target_alloc_limit en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (Run.run_scfg (Run.alloc_only_cfg false) (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs)
                            target_alloc_limit en inp).
Proof using B2BC B2BD RTW. exact (canon_B0_of rta_contracts_closed fuzz_one_B0). Qed.

End Lib.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Asan.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prog Canon.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import RT_iface RT_rep RT_closed D_libiface L_libA L_harn_defs L_harn TopA_final.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Lib.
Variable enc_ok : list byte -> Z -> Z -> list byte -> Prop.
Variable dec_ok : list byte -> bool -> Z -> list byte -> Prop.
Hypothesis B2BC : b2bc_cps RTA LIB_A enc_ok.
Hypothesis B2BD : b2bd_cps RTA LIB_A dec_ok.
Hypothesis RTW : round_trip_weak enc_ok dec_ok.

Theorem fuzz_one_A0 : fuzz_one_cps RTA LIB_A.
Proof using B2BC B2BD RTW.
  pose proof rta_contracts_closed as RC.
  exact (harness_ok RTA LIB_A enc_ok dec_ok (rc_facts RTA RC) LIB_locA (rc_stack_malloc_0 RTA RC) (rc_malloc RTA RC) (rc_malloc0 RTA RC) (rc_free RTA RC) (rc_memcmp RTA RC) B2BC B2BD RTW).
Qed.

Theorem canon_A0_of_lib :
  forall en inp,
    valid_entry (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs) en inp ->
    valid_input_either inp ->
    trace_equiv (bh_traces (Run.run_scfg (Run.alloc_only_cfg false) (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs)
                                    target_alloc_limit en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (Run.run_scfg (Run.alloc_only_cfg false) (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs)
                            target_alloc_limit en inp).
Proof using B2BC B2BD RTW. exact (canon_A0_of rta_contracts_closed fuzz_one_A0). Qed.

End Lib.
