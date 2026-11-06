(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: YD2i / YD2j regenerated for fuzz_knock.asan-ubsan by gen_ad2.py from the image, the atable, tfibsegs, the owned list and the 50 collected hand-off states *)
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
mkRegion None 614400 615928 0 0
[ mkChunk 614400 (CImg 1528) ].
Definition R_A2b : region :=
mkRegion None 616056 618880 0 0
[ mkChunk 616056 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 618888 619120 0 0
[ mkChunk 618888 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 619128 619152 0 0
[ mkChunk 619128 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 619168 619256 0 0
[ mkChunk 619168 (CImg 8);
mkChunk 619176 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 619280 623376 0 0
[ mkChunk 619280 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 633728 634560 633728 634560
[ mkChunk 633728 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 634568 634640 634568 634640
[ mkChunk 634568 (CVal 1 (SLit 1));
mkChunk 634569 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6032336 6097872 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6097872 6100076 6097872 6100076
[ mkChunk 6097872 (CImg 4);
mkChunk 6097876 (CVal 1 (SLit 0));
mkChunk 6097877 (CImg 2155);
mkChunk 6100040 (CVal 8 (SLit 6100040));
mkChunk 6100048 (CVal 8 (SLit 6100040));
mkChunk 6100056 (CVal 8 (SLit 6100040));
mkChunk 6100064 (CVal 8 (SLit 0));
mkChunk 6100072 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6100080 6100152 6100080 6100152
[ mkChunk 6100080 (CVal 4 (SLit 2));
mkChunk 6100084 (CImg 6);
mkChunk 6100090 (CVal 1 (SLit 1));
mkChunk 6100091 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6100160 6100232 0 0
[ mkChunk 6100160 (CVal 8 (SLit 6100160));
mkChunk 6100168 (CImg 24);
mkChunk 6100192 (CVal 8 (SLit 6232024));
mkChunk 6100200 (CImg 24);
mkChunk 6100224 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6100300 6100312 0 0
[ mkChunk 6100300 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6231320 6232016 6231392 6231936
[ mkChunk 6231320 (CImg 16);
mkChunk 6231336 (CVal 8 (SLit 610440));
mkChunk 6231344 (CVal 8 (SLit 0));
mkChunk 6231352 (CVal 8 (SLit 24));
mkChunk 6231360 (CVal 8 (SLit 8));
mkChunk 6231368 (CVal 8 (SLit 0));
mkChunk 6231376 (CVal 8 (SOff 41 0));
mkChunk 6231384 (CImg 16);
mkChunk 6231400 (CVal 4 (SLit 1));
mkChunk 6231404 (CImg 4);
mkChunk 6231408 (CVal 8 (SLit 6231416));
mkChunk 6231416 (CImg 8);
mkChunk 6231424 (CVal 8 (SLit 549092));
mkChunk 6231432 (CImg 248);
mkChunk 6231680 (CVal 8 (SLit 451728));
mkChunk 6231688 (CImg 264);
mkChunk 6231960 (CVal 8 (SOff 1 0));
mkChunk 6231968 (CVal 1 (SLit 1));
mkChunk 6231969 (CImg 7);
mkChunk 6231976 (CVal 8 (SOff 5 0));
mkChunk 6231984 (CVal 8 (SLit 6231328));
mkChunk 6231992 (CVal 8 (SLit 248));
mkChunk 6232000 (CVal 8 (SLit 8));
mkChunk 6232008 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6232024 6232096 0 0
[ mkChunk 6232024 (CImg 48);
mkChunk 6232080 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6233024 6235240 0 0
[ mkChunk 6233024 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6235248 6236344 0 0
[ mkChunk 6235248 (CImg 8);
mkChunk 6235256 (CVal 8 (SLit 340984));
mkChunk 6235264 (CImg 1016);
mkChunk 6236280 (CVal 4 (SLit 0));
mkChunk 6236284 (CImg 4);
mkChunk 6236288 (CVal 4 (SLit 0));
mkChunk 6236292 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6236352 6238208 0 0
[ mkChunk 6236352 (CImg 1856) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1n; R_A1o; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
