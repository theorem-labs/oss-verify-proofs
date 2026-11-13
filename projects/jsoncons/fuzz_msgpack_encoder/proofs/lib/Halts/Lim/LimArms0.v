(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by gabelogan195, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimArms0.v at commit f92feaf8b7, whole, with the module path OSSVerify.Proofs.openssl.bndiv.lib.Lib changed to OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim and nothing else. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim Require Import LimBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

Lemma arm_17 : lim_blind (fun i => getcwd_spec (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => getcwd_spec (in_arg j 1))). intros j. lim_auto. Qed.

Lemma arm_24 : lim_blind (fun i => dup3_spec (fd32 (in_arg i 0)) (fd32 (in_arg i 1)) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => dup3_spec (fd32 (in_arg j 0)) (fd32 (in_arg j 1)) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_48 : lim_blind (fun i => faccessat_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => faccessat_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_63 : lim_blind (fun i => read_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => read_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_72 : lim_blind (fun i => pselect6_spec (nfds32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i).
Proof. apply (lim_blind_arm (fun j => pselect6_spec (nfds32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) (in_arg j 3) (in_arg j 4) (in_arg j 5))). intros j. lim_auto. Qed.

Lemma arm_83 : lim_blind (fun i => fsync_spec (fd32 (in_arg i 0)) i).
Proof. apply (lim_blind_arm (fun j => fsync_spec (fd32 (in_arg j 0)))). intros j. lim_auto. Qed.

Lemma arm_101 : lim_blind (fun i => nanosleep_spec (in_arg i 0) (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => nanosleep_spec (in_arg j 0) (in_arg j 1))). intros j. lim_auto. Qed.

Lemma arm_131 : lim_blind (fun i => tgkill_spec (pid32 (in_arg i 0)) (pid32 (in_arg i 1)) (sig32 (in_arg i 2)) i).
Proof. apply (lim_blind_arm (fun j => tgkill_spec (pid32 (in_arg j 0)) (pid32 (in_arg j 1)) (sig32 (in_arg j 2)))). intros j. lim_auto. Qed.

Lemma arm_147 : lim_blind (fun i => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2)) i).
Proof. apply (lim_blind_arm (fun j => setresid_spec cred_uids set_cred_uids true (uid32 (in_arg j 0)) (uid32 (in_arg j 1)) (uid32 (in_arg j 2)))). intros j. lim_auto. Qed.

Lemma arm_167 : lim_blind (fun i => prctl_spec (int32 (in_arg i 0)) (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => prctl_spec (int32 (in_arg j 0)) (in_arg j 1))). intros j. lim_auto. Qed.

Lemma arm_177 : lim_blind (fun i => getid_spec cr_egid i).
Proof. apply (lim_blind_arm (fun j => getid_spec cr_egid)). intros j. lim_auto. Qed.

Lemma arm_202 : lim_blind (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i).
Proof. apply (lim_blind_arm (fun j => accept4_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) (Z_to_bv 64 0))). intros j. lim_auto. Qed.

Lemma arm_208 : lim_blind (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i).
Proof. apply (lim_blind_arm (fun j => setsockopt_spec (fd32 (in_arg j 0)) (int32 (in_arg j 1)) (int32 (in_arg j 4)))). intros j. lim_auto. Qed.

Lemma arm_242 : lim_blind (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => accept4_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) (in_arg j 3))). intros j. lim_auto. Qed.

