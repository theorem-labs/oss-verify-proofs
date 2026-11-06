(* The UBSan build's view of the shared pure model of reac-pw/fuzz_link.

   lib/Prog/link_spec.v holds no address, no image and no fact about either build: it is pure Rocq
   over byte lists. The harness and the library are the same source in both builds, so the two
   builds must answer the SAME model, and a second copy of the text could drift from the first.
   This file therefore re-exports the one model, as lib/U/Reusable does for lib/Reusable
   (a Theorem Labs lane's rule for U names). The per-build material -- the base addresses of g_nl, g_names,
   g_said, g_sink, g_say, `odd` and `texts`, and the views over them -- is in lib/U/Prog/link_mem.v.

   This Require does not put image-plain content in an image-ubsan closure: no term below uses a
   plain address, plain bytes, or a statement about the plain build (the image-closure ruling of
   2026-10-29 03:59Z). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Export link_spec.
