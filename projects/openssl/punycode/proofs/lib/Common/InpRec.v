(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: added for LPS 727298f3: the launch record inp of this unit's Common/AsanInit.v, moved out of its section with its arguments made explicit and given the launch fields that release adds, the SIGPIPE disposition among them as an argument since that release leaves it free. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [sd] is the SIGPIPE disposition at launch ([State.in_sigpipe_default]); [Run.valid_input]
   leaves it free at LPS 727298f3, so the launch record takes it as an argument. *)
Definition inp (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue)
    (nofile sigmask : word) (urnd : InputStream) (kern : KernelBuild) (execfn : list byte) (sd : bool) : ProcInput :=
  mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd []
    kern execfn true sd false.
