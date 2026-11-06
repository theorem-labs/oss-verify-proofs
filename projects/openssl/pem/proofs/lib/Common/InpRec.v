(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType Fs State.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition inp (argv envp : list (list byte)) (fs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue)
    (nofile sigmask : word) (urnd : InputStream) : ProcInput :=
  mkProcInput_full argv envp fs stdin uid gid groups net nofile sigmask hw false Sv48 urnd [].
