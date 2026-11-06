(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Module RefMemImage.
  Module Ref.
    Definition loaded_segments := Plain.M.loaded_segments.
  End Ref.
  Definition RefMemImage_loaded_segments := Plain_loaded_segments.
  Definition RefMemImage_segment_000 := Plain_segment_000.
  Definition RefMemImage_segment_001 := Plain_segment_001.
  Definition RefMemImage_segment_002 := Plain_segment_002.
  Definition RefMemImage_segment_003 := Plain_segment_003.
End RefMemImage.

Module AgentMemImage.
  Module Agent.
    Definition loaded_segments := Plain.M.loaded_segments.
  End Agent.
End AgentMemImage.

Definition rsegs := RefMemImage.Ref.loaded_segments.
