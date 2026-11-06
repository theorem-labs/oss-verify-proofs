(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Img0.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Img0.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Img0.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
Require OSSVerify.omx_clap_core.fuzz_manifest.images.AsanUbsan.

Definition rsegs := OSSVerify.omx_clap_core.fuzz_manifest.images.AsanUbsan.M.loaded_segments.
