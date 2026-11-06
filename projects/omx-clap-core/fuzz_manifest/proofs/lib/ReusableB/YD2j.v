(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for fuzz_manifest.asan-ubsan by a Theorem Labs lane's tools/startup/gen_ad2.py from its 50 collected hand-off states (lib/ReusableB/YB01.v), its atable (YB12), segments (YB1h), owned statics (YF0m) and image; template text: the image-B core's copy (a working branch 305d8b1527f) *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD2j.v (donor image sha256 1c29845fe605), with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the regions gen_ad2.py cut around owned cells renamed to fm A's AD2j names by rename_regions.py (R_A3_1 -> R_A3p, R_A3_2 -> R_A3, R_A5a_1 -> R_A5a, R_A5a_2 -> R_A5c, R_A5a_3 -> R_A5d, R_A5a_4 -> R_A5e), each checked equal in shape to its A twin; IMG_REGIONS = A's list *)
(* Read from: fuzz_manifest.asan-ubsan (omx-clap-core/fuzz_manifest asan-ubsan) sha256 ca61e5c9eabc00501d5cebab7618d8c03e73419f52c9f0b9be51c8bedff96e5e; unstripped twin sha256 b9568e38145a50214b3744e4f26bfc2ec9f670eca737d4da9be2dca6a0cfc2de *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP09.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 66280 0 0
[ mkChunk 65536 (CImg 744) ].
Definition R_A1b : region :=
mkRegion None 66288 66312 0 0
[ mkChunk 66288 (CImg 24) ].
Definition R_A1c : region :=
mkRegion None 66320 66344 0 0
[ mkChunk 66320 (CImg 24) ].
Definition R_A1d : region :=
mkRegion None 66352 66448 0 0
[ mkChunk 66352 (CImg 96) ].
Definition R_A1e : region :=
mkRegion None 66464 66472 0 0
[ mkChunk 66464 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66480 66584 0 0
[ mkChunk 66480 (CImg 104) ].
Definition R_A1g : region :=
mkRegion None 66648 66840 0 0
[ mkChunk 66648 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66904 117855 0 0
[ mkChunk 66904 (CImg 50951) ].
Definition R_A1i : region :=
mkRegion None 117876 133768 0 0
[ mkChunk 117876 (CImg 15892) ].
Definition R_A1j : region :=
mkRegion None 133772 134407 0 0
[ mkChunk 133772 (CImg 635) ].
Definition R_A1k : region :=
mkRegion None 134432 134439 0 0
[ mkChunk 134432 (CImg 7) ].
Definition R_A1l : region :=
mkRegion None 134464 134465 0 0
[ mkChunk 134464 (CImg 1) ].
Definition R_A1m : region :=
mkRegion None 134496 134521 0 0
[ mkChunk 134496 (CImg 25) ].
Definition R_A1n : region :=
mkRegion None 134560 134586 0 0
[ mkChunk 134560 (CImg 26) ].
Definition R_A1o : region :=
mkRegion None 134624 134669 0 0
[ mkChunk 134624 (CImg 45) ].
Definition R_A1p : region :=
mkRegion None 134720 134762 0 0
[ mkChunk 134720 (CImg 42) ].
Definition R_A1q : region :=
mkRegion None 134816 134859 0 0
[ mkChunk 134816 (CImg 43) ].
Definition R_A1r : region :=
mkRegion None 134912 134958 0 0
[ mkChunk 134912 (CImg 46) ].
Definition R_A1s : region :=
mkRegion None 135008 135077 0 0
[ mkChunk 135008 (CImg 69) ].
Definition R_A1t : region :=
mkRegion None 135104 135111 0 0
[ mkChunk 135104 (CImg 7) ].
Definition R_A1u : region :=
mkRegion None 135136 135143 0 0
[ mkChunk 135136 (CImg 7) ].
Definition R_A1v : region :=
mkRegion None 135168 136580 0 0
[ mkChunk 135168 (CImg 1412) ].
Definition R_A1w : region :=
mkRegion None 136584 136680 0 0
[ mkChunk 136584 (CImg 96) ].
Definition R_A1x : region :=
mkRegion None 136682 626688 0 0
[ mkChunk 136682 (CImg 490006) ].
Definition R_A2a : region :=
mkRegion None 626688 629880 0 0
[ mkChunk 626688 (CImg 3192) ].
Definition R_A2b : region :=
mkRegion None 630008 632832 0 0
[ mkChunk 630008 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 632840 633072 0 0
[ mkChunk 632840 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 633080 633104 0 0
[ mkChunk 633080 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 633120 633208 0 0
[ mkChunk 633120 (CImg 8);
mkChunk 633128 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 633232 637344 0 0
[ mkChunk 633232 (CImg 4112) ].
Definition R_A3p : region :=
mkRegion None 647728 647784 647728 647784
[ mkChunk 647728 (CImg 56) ].
Definition R_A3 : region :=
mkRegion None 647808 648608 647808 648608
[ mkChunk 647808 (CImg 800) ].
Definition R_A4 : region :=
mkRegion None 649672 649744 649672 649744
[ mkChunk 649672 (CVal 1 (SLit 1));
mkChunk 649673 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6047440 6112976 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6112976 6113032 6112976 6113032
[ mkChunk 6112976 (CImg 4);
mkChunk 6112980 (CVal 1 (SLit 0));
mkChunk 6112981 (CImg 51) ].
Definition R_A5c : region :=
mkRegion None 6113056 6113064 6113056 6113064
[ mkChunk 6113056 (CImg 8) ].
Definition R_A5d : region :=
mkRegion None 6113088 6113096 6113088 6113096
[ mkChunk 6113088 (CImg 8) ].
Definition R_A5e : region :=
mkRegion None 6113120 6115276 6113120 6115276
[ mkChunk 6113120 (CImg 2112);
mkChunk 6115240 (CVal 8 (SLit 6115240));
mkChunk 6115248 (CVal 8 (SLit 6115240));
mkChunk 6115256 (CVal 8 (SLit 6115240));
mkChunk 6115264 (CVal 8 (SLit 0));
mkChunk 6115272 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6115280 6115352 6115280 6115352
[ mkChunk 6115280 (CVal 4 (SLit 2));
mkChunk 6115284 (CImg 6);
mkChunk 6115290 (CVal 1 (SLit 1));
mkChunk 6115291 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6115360 6115432 0 0
[ mkChunk 6115360 (CVal 8 (SLit 6115360));
mkChunk 6115368 (CImg 24);
mkChunk 6115392 (CVal 8 (SLit 6247224));
mkChunk 6115400 (CImg 24);
mkChunk 6115424 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6115500 6115512 0 0
[ mkChunk 6115500 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6246520 6247216 6246592 6247136
[ mkChunk 6246520 (CImg 16);
mkChunk 6246536 (CVal 8 (SLit 624384));
mkChunk 6246544 (CVal 8 (SLit 0));
mkChunk 6246552 (CVal 8 (SLit 24));
mkChunk 6246560 (CVal 8 (SLit 8));
mkChunk 6246568 (CVal 8 (SLit 0));
mkChunk 6246576 (CVal 8 (SOff 41 0));
mkChunk 6246584 (CImg 16);
mkChunk 6246600 (CVal 4 (SLit 1));
mkChunk 6246604 (CImg 4);
mkChunk 6246608 (CVal 8 (SLit 6246616));
mkChunk 6246616 (CImg 8);
mkChunk 6246624 (CVal 8 (SLit 561184));
mkChunk 6246632 (CImg 248);
mkChunk 6246880 (CVal 8 (SLit 458556));
mkChunk 6246888 (CImg 264);
mkChunk 6247160 (CVal 8 (SOff 1 0));
mkChunk 6247168 (CVal 1 (SLit 1));
mkChunk 6247169 (CImg 7);
mkChunk 6247176 (CVal 8 (SOff 5 0));
mkChunk 6247184 (CVal 8 (SLit 6246528));
mkChunk 6247192 (CVal 8 (SLit 248));
mkChunk 6247200 (CVal 8 (SLit 8));
mkChunk 6247208 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6247224 6247296 0 0
[ mkChunk 6247224 (CImg 48);
mkChunk 6247280 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6248224 6250440 0 0
[ mkChunk 6248224 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6250448 6251544 0 0
[ mkChunk 6250448 (CImg 8);
mkChunk 6250456 (CVal 8 (SLit 347812));
mkChunk 6250464 (CImg 1016);
mkChunk 6251480 (CVal 4 (SLit 0));
mkChunk 6251484 (CImg 4);
mkChunk 6251488 (CVal 4 (SLit 0));
mkChunk 6251492 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6251552 6254592 0 0
[ mkChunk 6251552 (CImg 3040) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3p; R_A3; R_A4; R_RS; R_A5a; R_A5c; R_A5d; R_A5e; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
