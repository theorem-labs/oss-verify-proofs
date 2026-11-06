(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.libpcap.fuzz_pcap.images Require Export Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition ssegs : list Segment := Plain.M.loaded_segments.
