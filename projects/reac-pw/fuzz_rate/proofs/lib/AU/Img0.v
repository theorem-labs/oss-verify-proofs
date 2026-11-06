(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_disco/lib/A/Img0.v at 7cbe5270d908; the image module is reac-pw/fuzz_role's ASan image A (fuzz_role.asan). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/Img0.v at b2957340e99a; the image module is reac-pw/fuzz_rate's ASan image A (fuzz_rate.asan). *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_rate/lib/A/Img0.v at 2da83c57c6a5; the image module is reac-pw/fuzz_rate's ASan image B (fuzz_rate.asan-ubsan). *)
Require OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.

Definition rsegs := OSSVerify.reac_pw.fuzz_rate.images.AsanUbsan.M.loaded_segments.
