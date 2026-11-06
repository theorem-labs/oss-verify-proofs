(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: AD2i / AD2j regenerated for fuzz_knock.asan by gen_ad2.py from the image, the atable, tfibsegs, the owned list and the 50 collected hand-off states *)
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.Reusable Require Import YP0m YP09.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 66264 0 0
[ mkChunk 65536 (CImg 728) ].
Definition R_A1b : region :=
mkRegion None 66272 66296 0 0
[ mkChunk 66272 (CImg 24) ].
Definition R_A1c : region :=
mkRegion None 66304 66328 0 0
[ mkChunk 66304 (CImg 24) ].
Definition R_A1d : region :=
mkRegion None 66336 66440 0 0
[ mkChunk 66336 (CImg 104) ].
Definition R_A1e : region :=
mkRegion None 66456 66464 0 0
[ mkChunk 66456 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66472 66576 0 0
[ mkChunk 66472 (CImg 104) ].
Definition R_A1g : region :=
mkRegion None 66640 66832 0 0
[ mkChunk 66640 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66896 117730 0 0
[ mkChunk 66896 (CImg 50834) ].
Definition R_A1i : region :=
mkRegion None 117751 133632 0 0
[ mkChunk 117751 (CImg 15881) ].
Definition R_A1j : region :=
mkRegion None 133636 135644 0 0
[ mkChunk 133636 (CImg 2008) ].
Definition R_A1n : region :=
mkRegion None 135648 135744 0 0
[ mkChunk 135648 (CImg 96) ].
Definition R_A1o : region :=
mkRegion None 135746 614400 0 0
[ mkChunk 135746 (CImg 478654) ].
Definition R_A2a : region :=
mkRegion None 614400 615856 0 0
[ mkChunk 614400 (CImg 1456) ].
Definition R_A2b : region :=
mkRegion None 615984 618808 0 0
[ mkChunk 615984 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 618816 619048 0 0
[ mkChunk 618816 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 619056 619080 0 0
[ mkChunk 619056 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 619096 619184 0 0
[ mkChunk 619096 (CImg 8);
mkChunk 619104 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 619208 623304 0 0
[ mkChunk 619208 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 633656 634488 633656 634488
[ mkChunk 633656 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 634504 634576 634504 634576
[ mkChunk 634504 (CVal 1 (SLit 1));
mkChunk 634505 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6032272 6097808 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6097808 6100012 6097808 6100012
[ mkChunk 6097808 (CImg 4);
mkChunk 6097812 (CVal 1 (SLit 0));
mkChunk 6097813 (CImg 2155);
mkChunk 6099976 (CVal 8 (SLit 6099976));
mkChunk 6099984 (CVal 8 (SLit 6099976));
mkChunk 6099992 (CVal 8 (SLit 6099976));
mkChunk 6100000 (CVal 8 (SLit 0));
mkChunk 6100008 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6100016 6100088 6100016 6100088
[ mkChunk 6100016 (CVal 4 (SLit 2));
mkChunk 6100020 (CImg 6);
mkChunk 6100026 (CVal 1 (SLit 1));
mkChunk 6100027 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6100096 6100168 0 0
[ mkChunk 6100096 (CVal 8 (SLit 6100096));
mkChunk 6100104 (CImg 24);
mkChunk 6100128 (CVal 8 (SLit 6231960));
mkChunk 6100136 (CImg 24);
mkChunk 6100160 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6100236 6100248 0 0
[ mkChunk 6100236 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6231256 6231952 6231328 6231872
[ mkChunk 6231256 (CImg 16);
mkChunk 6231272 (CVal 8 (SLit 610368));
mkChunk 6231280 (CVal 8 (SLit 0));
mkChunk 6231288 (CVal 8 (SLit 24));
mkChunk 6231296 (CVal 8 (SLit 8));
mkChunk 6231304 (CVal 8 (SLit 0));
mkChunk 6231312 (CVal 8 (SOff 41 0));
mkChunk 6231320 (CImg 16);
mkChunk 6231336 (CVal 4 (SLit 1));
mkChunk 6231340 (CImg 4);
mkChunk 6231344 (CVal 8 (SLit 6231352));
mkChunk 6231352 (CImg 8);
mkChunk 6231360 (CVal 8 (SLit 549024));
mkChunk 6231368 (CImg 248);
mkChunk 6231616 (CVal 8 (SLit 451728));
mkChunk 6231624 (CImg 264);
mkChunk 6231896 (CVal 8 (SOff 1 0));
mkChunk 6231904 (CVal 1 (SLit 1));
mkChunk 6231905 (CImg 7);
mkChunk 6231912 (CVal 8 (SOff 5 0));
mkChunk 6231920 (CVal 8 (SLit 6231264));
mkChunk 6231928 (CVal 8 (SLit 248));
mkChunk 6231936 (CVal 8 (SLit 8));
mkChunk 6231944 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6231960 6232032 0 0
[ mkChunk 6231960 (CImg 48);
mkChunk 6232016 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6232960 6235176 0 0
[ mkChunk 6232960 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6235184 6236280 0 0
[ mkChunk 6235184 (CImg 8);
mkChunk 6235192 (CVal 8 (SLit 340984));
mkChunk 6235200 (CImg 1016);
mkChunk 6236216 (CVal 4 (SLit 0));
mkChunk 6236220 (CImg 4);
mkChunk 6236224 (CVal 4 (SLit 0));
mkChunk 6236228 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6236288 6238208 0 0
[ mkChunk 6236288 (CImg 1920) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1n; R_A1o; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
