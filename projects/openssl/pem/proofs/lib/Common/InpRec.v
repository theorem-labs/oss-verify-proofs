(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition the launch leaves free; the input's kernel build and exec file name; the start-up facts stated over the launch's ProcInput). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* At LPS 727298f3 [Run.valid_input] leaves the SIGPIPE disposition
   ([State.in_sigpipe_default]) free, so the record carries it as a parameter [sd]
   rather than the literal SIG_DFL. *)
Definition inp (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue)
    (nofile sigmask : word) (urnd : InputStream) (kern : KernelBuild) (execfn : list byte) (sd : bool) : ProcInput :=
  mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd []
    kern execfn true sd false.
