(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Img0.v; the image module is reac-pw/fuzz_role's ASan image A (fuzz_role.asan). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/Img0.v; the image module is reac-pw/fuzz_role's ASan image B (fuzz_role.asan-ubsan). *)
Require OSSVerify.reac_pw.fuzz_role.images.AsanUbsan.

Definition rsegs := OSSVerify.reac_pw.fuzz_role.images.AsanUbsan.M.loaded_segments.
