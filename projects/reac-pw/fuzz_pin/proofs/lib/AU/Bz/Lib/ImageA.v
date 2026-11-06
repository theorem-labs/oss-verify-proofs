(* Modified by Theorem Labs, 2026-10: copied from plugin-hostd/fuzz_reply (an unreleased branch at 86b50358d34) to libreac/fuzz_boxreg: module paths changed; the unused `bsegs` (the asan-ubsan image's segments) is dropped from this image-A file, so the A closure names no image-B content. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Bz/Lib/ImageA.v at origin/ossv/recipes f26f9fbd8777; module paths changed; no numeral changed; in the comments, internal branch and lane names are replaced by neutral words. *)
(* Ported from: an unreleased branch at 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Bz/Lib/ImageA.v.
   Changes (R1Str, 2026-10-29): module path fuzz_state -> fuzz_reply; no address numerals. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/Bz/Lib/ImageA.v of this library, for reac-pw/fuzz_pin's asan-ubsan image (fuzz_pin.asan-ubsan d6f83d301522) instead of its asan image (fuzz_pin.asan 3e4859aed23f): module paths lib.A -> lib.AU; image module Asan -> AsanUbsan (the asan-ubsan image's segments); no numeral changed (every address numeral checked on the asan-ubsan image). The comment lines above describe how lib/A/Bz/Lib/ImageA.v was made and quote the asan image's values; the code and comments below carry the asan-ubsan values. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Bz Require BvWfKernel.
(* [comment removed for export] *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.reac_pw.fuzz_pin.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition asegs : list Segment := AsanUbsan.M.loaded_segments.
