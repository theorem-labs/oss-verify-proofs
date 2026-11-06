(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem5State09ProcInput69OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Amb~~~~~~j93Amb0h1in_abort_terminal06in_gid09in_groups08in_hwcap06in_net09in_nofile0ain_sigmask06in_uid0ain_urandom0ain_va_sizej95mkAmb" s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Class Amb : Type := mkAmb {
  a_uid : word;
  a_gid : word;
  a_groups : list word;
  a_net : NetQueue;
  a_nofile : word;
  a_sigmask : word;
  a_hwcap : word;
  a_abort_terminal : bool;
  a_va_size : VaSize;  (* [comment removed for export] *)
  a_urandom : InputStream   (* [comment removed for export] *)
  (* [comment removed for export] *)
}.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net
              a_nofile a_sigmask a_hwcap a_abort_terminal a_va_size a_urandom [].

(* [comment removed for export] *)
Definition amb_of : ltac2:(zQ "20!ie!mf>3inp$0$1") := ltac2:(zQ "c0!ie!n5!o9!p1!pc!q6!qe!r9!s5!sd!t9!u5\3inp$0@a$b@1$8^1@1$2^1@1$3^1@1$5^1@1$6^1@1$7^1@1$4^1@1$1^1@1$a^1@1$9^1").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section Proj.
  Context {AMB : Amb}.
End Proj.
(* [comment removed for export] *)
