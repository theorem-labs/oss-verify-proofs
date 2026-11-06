(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import LimBase LimMonad.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Arms.
Variable L : Z.

(* [comment removed for export] *)
Lemma fr_arm_144 : forall i m, FR L i m (setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0))) (setid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0))).
Proof. intros i m. unfold setid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_146 : forall i m, FR L i m (setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0))) (setid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0))).
Proof. intros i m. unfold setid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_147 : forall i m, FR L i m (setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))) (setresid_spec cred_uids set_cred_uids true (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))).
Proof. intros i m. unfold setresid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_149 : forall i m, FR L i m (setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))) (setresid_spec cred_gids set_cred_gids false (uid32 (in_arg i 0)) (uid32 (in_arg i 1)) (uid32 (in_arg i 2))).
Proof. intros i m. unfold setresid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_157 : forall i m, FR L i m (setsid_spec) (setsid_spec).
Proof. intros i m. unfold setsid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_158 : forall i m, FR L i m (getgroups_spec (in_arg i 0)) (getgroups_spec (in_arg i 0)).
Proof. intros i m. unfold getgroups_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_159 : forall i m, FR L i m (setgroups_spec) (setgroups_spec).
Proof. intros i m. unfold setgroups_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_160 : forall i m, FR L i m (uname_spec (in_arg i 0)) (uname_spec (in_arg i 0)).
Proof. intros i m. unfold uname_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_167 : forall i m, FR L i m (prctl_spec (int32 (in_arg i 0)) (in_arg i 1)) (prctl_spec (int32 (in_arg i 0)) (in_arg i 1)).
Proof. intros i m. unfold prctl_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_169 : forall i m, FR L i m (gettimeofday_spec (in_arg i 0) (in_arg i 1)) (gettimeofday_spec (in_arg i 0) (in_arg i 1)).
Proof. intros i m. unfold gettimeofday_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_172 : forall i m, FR L i m (getpid_spec) (getpid_spec).
Proof. intros i m. unfold getpid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_174 : forall i m, FR L i m (getid_spec cr_uid) (getid_spec cr_uid).
Proof. intros i m. unfold getid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_175 : forall i m, FR L i m (getid_spec cr_euid) (getid_spec cr_euid).
Proof. intros i m. unfold getid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_176 : forall i m, FR L i m (getid_spec cr_gid) (getid_spec cr_gid).
Proof. intros i m. unfold getid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_177 : forall i m, FR L i m (getid_spec cr_egid) (getid_spec cr_egid).
Proof. intros i m. unfold getid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_178 : forall i m, FR L i m (gettid_spec) (gettid_spec).
Proof. intros i m. unfold gettid_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_198 : forall i m, FR L i m (socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (socket_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold socket_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_199 : forall i m, FR L i m (socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (socketpair_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold socketpair_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_200 : forall i m, FR L i m (bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (bind_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold bind_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_201 : forall i m, FR L i m (listen_spec (fd32 (in_arg i 0)) (in_arg i 1)) (listen_spec (fd32 (in_arg i 0)) (in_arg i 1)).
Proof. intros i m. unfold listen_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_202 : forall i m, FR L i m (accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0)) (accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (Z_to_bv 64 0)).
Proof. intros i m. unfold accept4_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_203 : forall i m, FR L i m (connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (connect_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold connect_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_204 : forall i m, FR L i m (getsockname_spec (fd32 (in_arg i 0))) (getsockname_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold getsockname_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_205 : forall i m, FR L i m (getpeername_spec (fd32 (in_arg i 0))) (getpeername_spec (fd32 (in_arg i 0))).
Proof. intros i m. unfold getpeername_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_206 : forall i m, FR L i m (sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)) (sendto_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5)).
Proof. intros i m. unfold sendto_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_207 : forall i m, FR L i m (recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (recvfrom_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold recvfrom_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_208 : forall i m, FR L i m (setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4))) (setsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (int32 (in_arg i 4))).
Proof. intros i m. unfold setsockopt_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_209 : forall i m, FR L i m (getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4)) (getsockopt_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1)) (in_arg i 4)).
Proof. intros i m. unfold getsockopt_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_210 : forall i m, FR L i m (shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1))) (shutdown_spec (fd32 (in_arg i 0)) (int32 (in_arg i 1))).
Proof. intros i m. unfold shutdown_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_211 : forall i m, FR L i m (sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)) (sendmsg_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold sendmsg_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_212 : forall i m, FR L i m (recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2)) (recvmsg_spec (fd32 (in_arg i 0)) (in_arg i 2)).
Proof. intros i m. unfold recvmsg_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_220 : forall i m, FR L i m (clone_spec (in_arg i 0)) (clone_spec (in_arg i 0)).
Proof. intros i m. unfold clone_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_242 : forall i m, FR L i m (accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (accept4_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold accept4_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_260 : forall i m, FR L i m (wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3)) (wait4_spec (pid32 (in_arg i 0)) (in_arg i 1) (waitopts32 (in_arg i 2)) (in_arg i 3)).
Proof. intros i m. unfold wait4_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_261 : forall i m, FR L i m (prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (prlimit64_spec (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold prlimit64_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_278 : forall i m, FR L i m (getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)) (getrandom_spec (in_arg i 0) (in_arg i 1) (in_arg i 2)).
Proof. intros i m. unfold getrandom_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_435 : forall i m, FR L i m (clone3_spec (in_arg i 0) (in_arg i 1)) (clone3_spec (in_arg i 0) (in_arg i 1)).
Proof. intros i m. unfold clone3_spec. fq. Qed.

(* [comment removed for export] *)
Lemma fr_arm_439 : forall i m, FR L i m (faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)) (faccessat2_spec (fd32 (in_arg i 0)) (in_arg i 1) (in_arg i 2) (in_arg i 3)).
Proof. intros i m. unfold faccessat2_spec. fq. Qed.

End Arms.
