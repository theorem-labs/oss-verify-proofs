(* Ported from: a working branch 840c4afa7e2 proofs/omx-clap-core/fuzz_state/lib/A/Img0.v.
   Changes (R1Str, 2026-10-29): module path fuzz_state -> fuzz_reply; no address numerals. *)
Require OSSVerify.plugin_hostd.fuzz_reply.images.Asan.

Definition rsegs := OSSVerify.plugin_hostd.fuzz_reply.images.Asan.M.loaded_segments.
