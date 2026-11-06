(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: generated for reac-pw/fuzz_pin image A by gen_ad2.py 8a509576b937 (the start-up tool set at tools commit 96d2c32e287) from this image's 50 collected hand-off states (lib/A/AB01.v), its atable (lib/A/AB12.v) and Tfib_owned_static (lib/A/AF0m.v), templates proofs/cgif/cgif_file_fuzzer/lib/A/AD2i.v / A/AD2j.v at c8557374ad2e, module paths changed; rw window [0x9a000, 0x5f6000) = the atable's rw_lo .. img_hi *)
(* Read from: fuzz_pin.asan (reac-pw/fuzz_pin asan) sha256 3e4859aed23f78a6eb028120d664abda29bcb8a3bfdea5d6ee5b32b646de9d16; unstripped twin sha256 435309a6b12c4d3e09a8484ec253b5fab600e4f00c28694ac28db2fc7a4475ab *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66912 117915 0 0
[ mkChunk 66912 (CImg 51003) ].
Definition R_A1i : region :=
mkRegion None 117936 133880 0 0
[ mkChunk 117936 (CImg 15944) ].
Definition R_A1j : region :=
mkRegion None 133884 134530 0 0
[ mkChunk 133884 (CImg 646) ].
Definition R_A1k : region :=
mkRegion None 134560 134598 0 0
[ mkChunk 134560 (CImg 38) ].
Definition R_A1l : region :=
mkRegion None 134624 134647 0 0
[ mkChunk 134624 (CImg 23) ].
Definition R_A1m : region :=
mkRegion None 134688 134694 0 0
[ mkChunk 134688 (CImg 6) ].
Definition R_A1n : region :=
mkRegion None 134720 134742 0 0
[ mkChunk 134720 (CImg 22) ].
Definition R_A1o : region :=
mkRegion None 134784 134791 0 0
[ mkChunk 134784 (CImg 7) ].
Definition R_A1p : region :=
mkRegion None 134816 134845 0 0
[ mkChunk 134816 (CImg 29) ].
Definition R_A1q : region :=
mkRegion None 134880 134892 0 0
[ mkChunk 134880 (CImg 12) ].
Definition R_A1r : region :=
mkRegion None 134912 134941 0 0
[ mkChunk 134912 (CImg 29) ].
Definition R_A1s : region :=
mkRegion None 134976 134982 0 0
[ mkChunk 134976 (CImg 6) ].
Definition R_A1t : region :=
mkRegion None 135008 135031 0 0
[ mkChunk 135008 (CImg 23) ].
Definition R_A1u : region :=
mkRegion None 135072 135078 0 0
[ mkChunk 135072 (CImg 6) ].
Definition R_A1v : region :=
mkRegion None 135104 135128 0 0
[ mkChunk 135104 (CImg 24) ].
Definition R_A1w : region :=
mkRegion None 135168 135175 0 0
[ mkChunk 135168 (CImg 7) ].
Definition R_A1x : region :=
mkRegion None 135200 135224 0 0
[ mkChunk 135200 (CImg 24) ].
Definition R_A1y : region :=
mkRegion None 135264 135271 0 0
[ mkChunk 135264 (CImg 7) ].
Definition R_A1z : region :=
mkRegion None 135296 135320 0 0
[ mkChunk 135296 (CImg 24) ].
Definition R_A1aa : region :=
mkRegion None 135360 135367 0 0
[ mkChunk 135360 (CImg 7) ].
Definition R_A1ab : region :=
mkRegion None 135392 135415 0 0
[ mkChunk 135392 (CImg 23) ].
Definition R_A1ac : region :=
mkRegion None 135456 135463 0 0
[ mkChunk 135456 (CImg 7) ].
Definition R_A1ad : region :=
mkRegion None 135488 135511 0 0
[ mkChunk 135488 (CImg 23) ].
Definition R_A1ae : region :=
mkRegion None 135552 135559 0 0
[ mkChunk 135552 (CImg 7) ].
Definition R_A1af : region :=
mkRegion None 135584 135608 0 0
[ mkChunk 135584 (CImg 24) ].
Definition R_A1ag : region :=
mkRegion None 135648 137060 0 0
[ mkChunk 135648 (CImg 1412) ].
Definition R_A1ah : region :=
mkRegion None 137064 137160 0 0
[ mkChunk 137064 (CImg 96) ].
Definition R_A1ai : region :=
mkRegion None 137162 625560 0 0
[ mkChunk 137162 (CImg 488398) ].
Definition R_A1aj : region :=
mkRegion None 626368 626736 0 0
[ mkChunk 626368 (CImg 368) ].
Definition R_A1ak : region :=
mkRegion None 626864 629688 0 0
[ mkChunk 626864 (CImg 2824) ].
Definition R_A1al : region :=
mkRegion None 629696 629928 0 0
[ mkChunk 629696 (CImg 232) ].
Definition R_A1am : region :=
mkRegion None 629936 629960 0 0
[ mkChunk 629936 (CImg 24) ].
Definition R_A1an : region :=
mkRegion None 629976 630064 0 0
[ mkChunk 629976 (CImg 8);
mkChunk 629984 (CImg 80) ].
Definition R_A1ao : region :=
mkRegion None 630088 630784 0 0
[ mkChunk 630088 (CImg 696) ].
Definition R_A2 : region :=
mkRegion None 630784 634184 0 0
[ mkChunk 630784 (CImg 3400) ].
Definition R_A3 : region :=
mkRegion None 644560 645392 644560 645392
[ mkChunk 644560 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 646984 647056 646984 647056
[ mkChunk 646984 (CVal 1 (SLit 1));
mkChunk 646985 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6044752 6110288 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6110288 6112500 6110288 6112500
[ mkChunk 6110288 (CImg 4);
mkChunk 6110292 (CVal 1 (SLit 0));
mkChunk 6110293 (CImg 43);
mkChunk 6110336 (CVal 1 (SLit 1));
mkChunk 6110337 (CImg 2119);
mkChunk 6112464 (CVal 8 (SLit 6112464));
mkChunk 6112472 (CVal 8 (SLit 6112464));
mkChunk 6112480 (CVal 8 (SLit 6112464));
mkChunk 6112488 (CVal 8 (SLit 0));
mkChunk 6112496 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6112504 6112576 6112504 6112576
[ mkChunk 6112504 (CVal 4 (SLit 2));
mkChunk 6112508 (CImg 6);
mkChunk 6112514 (CVal 1 (SLit 1));
mkChunk 6112515 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6112584 6112656 0 0
[ mkChunk 6112584 (CVal 8 (SLit 6112584));
mkChunk 6112592 (CImg 24);
mkChunk 6112616 (CVal 8 (SLit 6244448));
mkChunk 6112624 (CImg 24);
mkChunk 6112648 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6112724 6112736 0 0
[ mkChunk 6112724 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6243744 6244440 6243816 6244360
[ mkChunk 6243744 (CImg 16);
mkChunk 6243760 (CVal 8 (SLit 617160));
mkChunk 6243768 (CVal 8 (SLit 0));
mkChunk 6243776 (CVal 8 (SLit 24));
mkChunk 6243784 (CVal 8 (SLit 8));
mkChunk 6243792 (CVal 8 (SLit 0));
mkChunk 6243800 (CVal 8 (SOff 41 0));
mkChunk 6243808 (CImg 16);
mkChunk 6243824 (CVal 4 (SLit 1));
mkChunk 6243828 (CImg 4);
mkChunk 6243832 (CVal 8 (SLit 6243840));
mkChunk 6243840 (CImg 8);
mkChunk 6243848 (CVal 8 (SLit 555432));
mkChunk 6243856 (CImg 248);
mkChunk 6244104 (CVal 8 (SLit 457844));
mkChunk 6244112 (CImg 264);
mkChunk 6244384 (CVal 8 (SOff 1 0));
mkChunk 6244392 (CVal 1 (SLit 1));
mkChunk 6244393 (CImg 7);
mkChunk 6244400 (CVal 8 (SOff 5 0));
mkChunk 6244408 (CVal 8 (SLit 6243752));
mkChunk 6244416 (CVal 8 (SLit 248));
mkChunk 6244424 (CVal 8 (SLit 8));
mkChunk 6244432 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6244448 6244520 0 0
[ mkChunk 6244448 (CImg 48);
mkChunk 6244504 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6245448 6247664 0 0
[ mkChunk 6245448 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6247672 6248768 0 0
[ mkChunk 6247672 (CImg 8);
mkChunk 6247680 (CVal 8 (SLit 347100));
mkChunk 6247688 (CImg 1016);
mkChunk 6248704 (CVal 4 (SLit 0));
mkChunk 6248708 (CImg 4);
mkChunk 6248712 (CVal 4 (SLit 0));
mkChunk 6248716 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6248776 6250496 0 0
[ mkChunk 6248776 (CImg 1720) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
