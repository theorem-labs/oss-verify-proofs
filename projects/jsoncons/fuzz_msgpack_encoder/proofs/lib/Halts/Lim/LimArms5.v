(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by gabelogan195, 2026-11: copied from projects/openssl/bndiv/proofs/lib/Lib/LimArms5.v at commit f92feaf8b7, whole, with the module path OSSVerify.Proofs.openssl.bndiv.lib.Lib changed to OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim and nothing else. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Halts.Lim Require Import LimBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope sys_scope.

Lemma arm_23 : lim_blind (fun i => dup_spec (fd32 (in_arg i 0)) i).
Proof. apply (lim_blind_arm (fun j => dup_spec (fd32 (in_arg j 0)))). intros j. lim_auto. Qed.

Lemma arm_46 : lim_blind (fun i => ftruncate_spec (fd32 (in_arg i 0)) (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => ftruncate_spec (fd32 (in_arg j 0)) (in_arg j 1))). intros j. lim_auto. Qed.

Lemma arm_62 : lim_blind (fun i => lseek_spec (fd32 (in_arg i 0)) (in_arg i 1) (whence32 (in_arg i 2)) i).
Proof. apply (lim_blind_arm (fun j => lseek_spec (fd32 (in_arg j 0)) (in_arg j 1) (whence32 (in_arg j 2)))). intros j. lim_auto. Qed.

Lemma arm_68 : lim_blind (fun i => pwrite64_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => pwrite64_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) (in_arg j 3))). intros j. lim_auto. Qed.

Lemma arm_82 : lim_blind (fun i => fsync_spec (fd32 (in_arg i 0)) i).
Proof. apply (lim_blind_arm (fun j => fsync_spec (fd32 (in_arg j 0)))). intros j. lim_auto. Qed.

Lemma arm_98 : lim_blind (fun i => futex_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => futex_spec (in_arg j 0) (in_arg j 1) (in_arg j 2) (in_arg j 3))). intros j. lim_auto. Qed.

Lemma arm_130 : lim_blind (fun i => tkill_spec (pid32 (in_arg i 0)) (sig32 (in_arg i 1)) i).
Proof. apply (lim_blind_arm (fun j => tkill_spec (pid32 (in_arg j 0)) (sig32 (in_arg j 1)))). intros j. lim_auto. Qed.

Lemma arm_146 : lim_blind (fun i => setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) i).
Proof. apply (lim_blind_arm (fun j => setid_spec cred_uids set_cred_uids true (uid32 (in_arg j 0)))). intros j. lim_auto. Qed.

Lemma arm_160 : lim_blind (fun i => uname_spec (in_arg i 0) i).
Proof. apply (lim_blind_arm (fun j => uname_spec (in_arg j 0))). intros j. lim_auto. Qed.

Lemma arm_176 : lim_blind (fun i => getid_spec cr_gid i).
Proof. apply (lim_blind_arm (fun j => getid_spec cr_gid)). intros j. lim_auto. Qed.

Lemma arm_201 : lim_blind (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i).
Proof. apply (lim_blind_arm (fun j => listen_spec (fd32 (in_arg j 0)) (in_arg j 1))). intros j. lim_auto. Qed.

Lemma arm_207 : lim_blind (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. apply (lim_blind_arm (fun j => recvfrom_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2))). intros j. lim_auto. Qed.

Lemma arm_220 : lim_blind (fun i => clone_spec (in_arg i 0) i).
Proof. apply (lim_blind_arm (fun j => clone_spec (in_arg j 0))). intros j. lim_auto. Qed.

Lemma arm_439 : lim_blind (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. apply (lim_blind_arm (fun j => faccessat2_spec (fd32 (in_arg j 0)) (in_arg j 1) (in_arg j 2) (in_arg j 3))). intros j. lim_auto. Qed.

