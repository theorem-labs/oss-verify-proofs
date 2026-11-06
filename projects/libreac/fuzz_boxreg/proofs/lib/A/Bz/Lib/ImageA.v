(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (a working branch 86b50358d34) to libreac/fuzz_boxreg: module paths changed; the unused `bsegs` (the asan-ubsan image's segments) is dropped from this image-A file, so the A closure names no image-B content. *)
(* Ported from: a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/Lib/ImageA.v.
   Changes (a Theorem Labs lane, 2026-10-29): module path fuzz_state -> fuzz_reply; no address numerals. *)
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.A.Bz Require BvWfKernel.
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.libreac.fuzz_boxreg.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := Asan.M.loaded_segments.
