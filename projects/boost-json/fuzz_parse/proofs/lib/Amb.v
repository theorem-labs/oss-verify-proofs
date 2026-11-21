(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, the launch's channel reader, the launch input as a ProcInput. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~" s.
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
  a_urandom : InputStream;  (* [comment removed for export] *)
  (* [comment removed for export] *)
  a_kernel : KernelBuild;
  a_execfn : list byte;
  a_channel_reader : bool;
  a_sigpipe_default : bool;
  a_sigpipe_terminal : bool
}.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkProcInputC {AMB : Amb} (argv envp : list (list byte)) (fs : Fs.Fs)
    (stdin : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin a_uid a_gid a_groups a_net
              a_nofile a_sigmask a_hwcap a_abort_terminal a_va_size a_urandom []
              a_kernel a_execfn a_channel_reader a_sigpipe_default a_sigpipe_terminal.

(* [comment removed for export] *)
Definition amb_of (inp : ProcInput) : Amb :=
  mkAmb (in_uid inp) (in_gid inp) (in_groups inp) (in_net inp)
        (in_nofile inp) (in_sigmask inp) (in_hwcap inp) (in_abort_terminal inp) (in_va_size inp)
        (in_urandom inp)
        (in_kernel inp) (in_execfn inp) (in_channel_reader inp)
        (in_sigpipe_default inp) (in_sigpipe_terminal inp).

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Section Proj.
  Context {AMB : Amb}.
End Proj.
(* [comment removed for export] *)
