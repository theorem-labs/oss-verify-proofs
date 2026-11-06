(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/A/AD2i.v and lib/A/AD2j.v (origin/ossv/recipes c8557374ad2e) for libreac/fuzz_scene's asan image (sha256 43654a025fd0...) by a Theorem Labs lane's gen_ad2.py, with its module paths changed: sregs_main, TIDV, CANV and TFIB_MAIN from the 50 hand-off states of lib/A/AB01.v, the image bounds from lib/A/AB12.v and the rw window 0x9d000..0x5f9000; IMG_REGIONS below .data from the image and the owned static cells of the generated lib/A/AF0m.v; owned static cells come from the GENERATED f0mgen2 AF0m (af0m.py, --base the hand-assembled reference) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66352 66456 0 0
[ mkChunk 66352 (CImg 104) ].
Definition R_A1e : region :=
mkRegion None 66472 66480 0 0
[ mkChunk 66472 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66488 66592 0 0
[ mkChunk 66488 (CImg 104) ].
Definition R_A1g : region :=
mkRegion None 66656 66848 0 0
[ mkChunk 66656 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66912 117955 0 0
[ mkChunk 66912 (CImg 51043) ].
Definition R_A1i : region :=
mkRegion None 117976 133884 0 0
[ mkChunk 117976 (CImg 15908) ].
Definition R_A1j : region :=
mkRegion None 133888 134540 0 0
[ mkChunk 133888 (CImg 652) ].
Definition R_A1k : region :=
mkRegion None 134560 134610 0 0
[ mkChunk 134560 (CImg 50) ].
Definition R_A1l : region :=
mkRegion None 134656 134700 0 0
[ mkChunk 134656 (CImg 44) ].
Definition R_A1m : region :=
mkRegion None 134720 134727 0 0
[ mkChunk 134720 (CImg 7) ].
Definition R_A1n : region :=
mkRegion None 134752 143688 0 0
[ mkChunk 134752 (CImg 8936) ].
Definition R_A1o : region :=
mkRegion None 145920 147336 0 0
[ mkChunk 145920 (CImg 1416) ].
Definition R_A1p : region :=
mkRegion None 147340 147436 0 0
[ mkChunk 147340 (CImg 96) ].
Definition R_A1q : region :=
mkRegion None 147438 636656 0 0
[ mkChunk 147438 (CImg 489218) ].
Definition R_A1r : region :=
mkRegion None 636784 639608 0 0
[ mkChunk 636784 (CImg 2824) ].
Definition R_A1s : region :=
mkRegion None 639616 639848 0 0
[ mkChunk 639616 (CImg 232) ].
Definition R_A1t : region :=
mkRegion None 639856 639888 0 0
[ mkChunk 639856 (CImg 32) ].
Definition R_A1u : region :=
mkRegion None 639904 639992 0 0
[ mkChunk 639904 (CImg 8);
mkChunk 639912 (CImg 80) ].
Definition R_A1v : region :=
mkRegion None 640016 643072 0 0
[ mkChunk 640016 (CImg 3056) ].
Definition R_A2 : region :=
mkRegion None 643072 644112 0 0
[ mkChunk 643072 (CImg 1040) ].
Definition R_A3 : region :=
mkRegion None 654472 655312 654472 655312
[ mkChunk 654472 (CImg 840) ].
Definition R_A4 : region :=
mkRegion None 655688 655760 655688 655760
[ mkChunk 655688 (CVal 1 (SLit 1));
mkChunk 655689 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6053456 6118992 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6118992 6121204 6118992 6121204
[ mkChunk 6118992 (CImg 4);
mkChunk 6118996 (CVal 1 (SLit 0));
mkChunk 6118997 (CImg 43);
mkChunk 6119040 (CVal 1 (SLit 1));
mkChunk 6119041 (CImg 2119);
mkChunk 6121168 (CVal 8 (SLit 6121168));
mkChunk 6121176 (CVal 8 (SLit 6121168));
mkChunk 6121184 (CVal 8 (SLit 6121168));
mkChunk 6121192 (CVal 8 (SLit 0));
mkChunk 6121200 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6121208 6121280 6121208 6121280
[ mkChunk 6121208 (CVal 4 (SLit 2));
mkChunk 6121212 (CImg 6);
mkChunk 6121218 (CVal 1 (SLit 1));
mkChunk 6121219 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6121288 6121360 0 0
[ mkChunk 6121288 (CVal 8 (SLit 6121288));
mkChunk 6121296 (CImg 24);
mkChunk 6121320 (CVal 8 (SLit 6253152));
mkChunk 6121328 (CImg 24);
mkChunk 6121352 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6121428 6121440 0 0
[ mkChunk 6121428 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6252448 6253144 6252520 6253064
[ mkChunk 6252448 (CImg 16);
mkChunk 6252464 (CVal 8 (SLit 631160));
mkChunk 6252472 (CVal 8 (SLit 0));
mkChunk 6252480 (CVal 8 (SLit 24));
mkChunk 6252488 (CVal 8 (SLit 8));
mkChunk 6252496 (CVal 8 (SLit 0));
mkChunk 6252504 (CVal 8 (SOff 41 0));
mkChunk 6252512 (CImg 16);
mkChunk 6252528 (CVal 4 (SLit 1));
mkChunk 6252532 (CImg 4);
mkChunk 6252536 (CVal 8 (SLit 6252544));
mkChunk 6252544 (CImg 8);
mkChunk 6252552 (CVal 8 (SLit 569808));
mkChunk 6252560 (CImg 248);
mkChunk 6252808 (CVal 8 (SLit 466488));
mkChunk 6252816 (CImg 264);
mkChunk 6253088 (CVal 8 (SOff 1 0));
mkChunk 6253096 (CVal 1 (SLit 1));
mkChunk 6253097 (CImg 7);
mkChunk 6253104 (CVal 8 (SOff 5 0));
mkChunk 6253112 (CVal 8 (SLit 6252456));
mkChunk 6253120 (CVal 8 (SLit 248));
mkChunk 6253128 (CVal 8 (SLit 8));
mkChunk 6253136 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6253152 6253224 0 0
[ mkChunk 6253152 (CImg 48);
mkChunk 6253208 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6254152 6256368 0 0
[ mkChunk 6254152 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6256376 6257472 0 0
[ mkChunk 6256376 (CImg 8);
mkChunk 6256384 (CVal 8 (SLit 355744));
mkChunk 6256392 (CImg 1016);
mkChunk 6257408 (CVal 4 (SLit 0));
mkChunk 6257412 (CImg 4);
mkChunk 6257416 (CVal 4 (SLit 0));
mkChunk 6257420 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6257480 6262784 0 0
[ mkChunk 6257480 (CImg 5304) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
