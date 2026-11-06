(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_boxreg/lib/A/Img0.v at origin/ossv/recipes f26f9fbd8777; module paths changed (boxreg's lib.Lib modules as pin's lib.Lib modules); moved from lib/A/Img0.v to lib/A/Rt/Img0.v, and the Requires of the moved files follow; the comments are boxreg's, verbatim, and name fuzz_boxreg.asan's addresses. *)
Require OSSVerify.reac_pw.fuzz_pin.images.Asan.

Definition rsegs := OSSVerify.reac_pw.fuzz_pin.images.Asan.M.loaded_segments.
