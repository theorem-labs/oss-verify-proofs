(* Modified by Theorem Labs: copied from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/B/Img0.v at recipes commit 88154566652a310ff96f54a5442e5c73fdaad090 (a recipes commit newer than the unit's base 25e3d17bdb50) for reac-repacer/fuzz_uci; the image module moved to fuzz_uci's ASan+UBSan image (OSSVerify.reac_repacer.fuzz_uci.images.AsanUbsan); module path OSSVerify.Proofs.reac_repacer.fuzz_uci.lib. *)
Require OSSVerify.reac_repacer.fuzz_uci.images.AsanUbsan.

Definition rsegs := OSSVerify.reac_repacer.fuzz_uci.images.AsanUbsan.M.loaded_segments.
