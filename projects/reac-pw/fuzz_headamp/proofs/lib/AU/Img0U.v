(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Img0.v at 7cbe5270d908; the image module is reac-pw/fuzz_role's ASan image A (fuzz_role.asan). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/Img0.v at b2957340e99; the image module is reac-pw/fuzz_headamp's ASan image A (fuzz_headamp.asan). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/Img0.v at 5ad5cc2087a; the image module is reac-pw/fuzz_headamp's ASan + UBSan image B (fuzz_headamp.asan-ubsan). *)
Require OSSVerify.reac_pw.fuzz_headamp.images.AsanUbsan.

Definition rsegs := OSSVerify.reac_pw.fuzz_headamp.images.AsanUbsan.M.loaded_segments.
