(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Run Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import SyscallTable.
From OSSVerify.Proofs.openssl.punycode.lib.Common.LimSim Require Import LimSim.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope. Open Scope bv_scope. Open Scope sys_scope.
Set Default Proof Mode "Classic".

Section Arms.
Variable L0 L : Z.

Lemma sim_arm_175 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getid_spec cr_euid i) (fun i => getid_spec cr_euid i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getid_spec cr_euid) (fun i => getid_spec cr_euid)). sim_arm m HM. Qed.

Lemma sim_arm_176 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getid_spec cr_gid i) (fun i => getid_spec cr_gid i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getid_spec cr_gid) (fun i => getid_spec cr_gid)). sim_arm m HM. Qed.

Lemma sim_arm_177 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getid_spec cr_egid i) (fun i => getid_spec cr_egid i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getid_spec cr_egid) (fun i => getid_spec cr_egid)). sim_arm m HM. Qed.

Lemma sim_arm_178 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => gettid_spec i) (fun i => gettid_spec i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => gettid_spec) (fun i => gettid_spec)). sim_arm m HM. Qed.

Lemma sim_arm_198 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (fun i => socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_199 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.

Lemma sim_arm_200 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_201 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i) (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1)) (fun i => listen_spec (fd32 (in_arg i 0)) (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_202 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i) (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0)) (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0))). sim_arm m HM. Qed.

Lemma sim_arm_203 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_204 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getsockname_spec (fd32 (in_arg i 0)) i) (fun i => getsockname_spec (fd32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getsockname_spec (fd32 (in_arg i 0))) (fun i => getsockname_spec (fd32 (in_arg i 0)))). sim_arm m HM. Qed.

Lemma sim_arm_205 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getpeername_spec (fd32 (in_arg i 0)) i) (fun i => getpeername_spec (fd32 (in_arg i 0)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getpeername_spec (fd32 (in_arg i 0))) (fun i => getpeername_spec (fd32 (in_arg i 0)))). sim_arm m HM. Qed.

Lemma sim_arm_206 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i) (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)) (fun i => sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5))). sim_arm m HM. Qed.

Lemma sim_arm_207 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_208 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i) (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4))) (fun i => setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4)))). sim_arm m HM. Qed.

Lemma sim_arm_209 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i) (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4)) (fun i => getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4))). sim_arm m HM. Qed.

Lemma sim_arm_210 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i) (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1))) (fun i => shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)))). sim_arm m HM. Qed.

Lemma sim_arm_211 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i) (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (fun i => sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_212 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i) (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2)) (fun i => recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_215 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i) (fun i => munmap_spec (in_arg i 0) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => munmap_spec (in_arg i 0) (in_arg i 1)) (fun i => munmap_spec (in_arg i 0) (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_220 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => clone_spec (in_arg i 0) i) (fun i => clone_spec (in_arg i 0) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => clone_spec (in_arg i 0)) (fun i => clone_spec (in_arg i 0))). sim_arm m HM. Qed.

Lemma sim_arm_233 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i) (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2))) (fun i => madvise_spec (in_arg i 0) (in_arg i 1) (int32 (in_arg i 2)))). sim_arm m HM. Qed.

Lemma sim_arm_242 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.

Lemma sim_arm_260 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i) (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3)) (fun i => wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3))). sim_arm m HM. Qed.

Lemma sim_arm_261 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.

Lemma sim_arm_278 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i) (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (fun i => getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2))). sim_arm m HM. Qed.

Lemma sim_arm_435 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i) (fun i => clone3_spec (in_arg i 0) (in_arg i 1) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => clone3_spec (in_arg i 0) (in_arg i 1)) (fun i => clone3_spec (in_arg i 0) (in_arg i 1))). sim_arm m HM. Qed.

Lemma sim_arm_439 : forall (d : bool) i m, MOK L0 m -> DIR L0 L d i m (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i) (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) i).
Proof. intros d i m HM. apply (dir_table_form L0 L d i m (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (fun i => faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3))). sim_arm m HM. Qed.

End Arms.
