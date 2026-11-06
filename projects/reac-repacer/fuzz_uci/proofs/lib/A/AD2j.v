(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: generated for reac-repacer/fuzz_uci by tools/startup/gen_ad2.py (frozen 195f6e6ef088) from fuzz_uci.asan, its atable (A/AB12.v), its TSEGS window (A/AB1h.v), its owned statics (A/AF0m.v) and the 50 hand-off states of A/AB01.v; the donor A/AD2i.v and A/AD2j.v at origin/ossv/recipes c8557374ad2e give the text only *)
(* Read from: fuzz_uci.asan (reac-repacer/fuzz_uci asan) sha256 6ea017c24525e6946fa06dc7e3075459ad2c5146d59af49873bf3c51a46e885d; unstripped twin sha256 56822e263d767986a76ec862cbfbee7571b0e64df2413ad18d7201205a7563fb *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66912 117773 0 0
[ mkChunk 66912 (CImg 50861) ].
Definition R_A1i : region :=
mkRegion None 117794 133660 0 0
[ mkChunk 117794 (CImg 15866) ].
Definition R_A1j : region :=
mkRegion None 133664 134312 0 0
[ mkChunk 133664 (CImg 648) ].
Definition R_A1k : region :=
mkRegion None 134336 135744 0 0
[ mkChunk 134336 (CImg 1408) ].
Definition R_A1n : region :=
mkRegion None 135748 135844 0 0
[ mkChunk 135748 (CImg 96) ].
Definition R_A1o : region :=
mkRegion None 135846 614400 0 0
[ mkChunk 135846 (CImg 478554) ].
Definition R_A2a : region :=
mkRegion None 614400 618496 0 0
[ mkChunk 614400 (CImg 4096) ].
Definition R_A2b : region :=
mkRegion None 618624 621448 0 0
[ mkChunk 618624 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 621456 621688 0 0
[ mkChunk 621456 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 621696 621720 0 0
[ mkChunk 621696 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 621736 621824 0 0
[ mkChunk 621736 (CImg 8);
mkChunk 621744 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 621848 625944 0 0
[ mkChunk 621848 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 636296 637136 636296 637136
[ mkChunk 636296 (CImg 840) ].
Definition R_A4 : region :=
mkRegion None 637256 637328 637256 637328
[ mkChunk 637256 (CVal 1 (SLit 1));
mkChunk 637257 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6035024 6100560 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6100560 6102764 6100560 6102764
[ mkChunk 6100560 (CImg 4);
mkChunk 6100564 (CVal 1 (SLit 0));
mkChunk 6100565 (CImg 2155);
mkChunk 6102728 (CVal 8 (SLit 6102728));
mkChunk 6102736 (CVal 8 (SLit 6102728));
mkChunk 6102744 (CVal 8 (SLit 6102728));
mkChunk 6102752 (CVal 8 (SLit 0));
mkChunk 6102760 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6102768 6102840 6102768 6102840
[ mkChunk 6102768 (CVal 4 (SLit 2));
mkChunk 6102772 (CImg 6);
mkChunk 6102778 (CVal 1 (SLit 1));
mkChunk 6102779 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6102848 6102920 0 0
[ mkChunk 6102848 (CVal 8 (SLit 6102848));
mkChunk 6102856 (CImg 24);
mkChunk 6102880 (CVal 8 (SLit 6234712));
mkChunk 6102888 (CImg 24);
mkChunk 6102912 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6102988 6103000 0 0
[ mkChunk 6102988 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6234008 6234704 6234080 6234624
[ mkChunk 6234008 (CImg 16);
mkChunk 6234024 (CVal 8 (SLit 613000));
mkChunk 6234032 (CVal 8 (SLit 0));
mkChunk 6234040 (CVal 8 (SLit 24));
mkChunk 6234048 (CVal 8 (SLit 8));
mkChunk 6234056 (CVal 8 (SLit 0));
mkChunk 6234064 (CVal 8 (SOff 41 0));
mkChunk 6234072 (CImg 16);
mkChunk 6234088 (CVal 4 (SLit 1));
mkChunk 6234092 (CImg 4);
mkChunk 6234096 (CVal 8 (SLit 6234104));
mkChunk 6234104 (CImg 8);
mkChunk 6234112 (CVal 8 (SLit 551656));
mkChunk 6234120 (CImg 248);
mkChunk 6234368 (CVal 8 (SLit 452776));
mkChunk 6234376 (CImg 264);
mkChunk 6234648 (CVal 8 (SOff 1 0));
mkChunk 6234656 (CVal 1 (SLit 1));
mkChunk 6234657 (CImg 7);
mkChunk 6234664 (CVal 8 (SOff 5 0));
mkChunk 6234672 (CVal 8 (SLit 6234016));
mkChunk 6234680 (CVal 8 (SLit 248));
mkChunk 6234688 (CVal 8 (SLit 8));
mkChunk 6234696 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6234712 6234784 0 0
[ mkChunk 6234712 (CImg 48);
mkChunk 6234768 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6235712 6237928 0 0
[ mkChunk 6235712 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6237936 6239032 0 0
[ mkChunk 6237936 (CImg 8);
mkChunk 6237944 (CVal 8 (SLit 342032));
mkChunk 6237952 (CImg 1016);
mkChunk 6238968 (CVal 4 (SLit 0));
mkChunk 6238972 (CImg 4);
mkChunk 6238976 (CVal 4 (SLit 0));
mkChunk 6238980 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6239040 6242304 0 0
[ mkChunk 6239040 (CImg 3264) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1n; R_A1o; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
