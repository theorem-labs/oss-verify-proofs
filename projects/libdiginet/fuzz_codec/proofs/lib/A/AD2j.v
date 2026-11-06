(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec by tools/startup/gen_ad2.py (frozen 8a509576b937, the start-up tool set at commit 4453a719871) from fuzz_codec.asan, its atable (A/AB12.v), its TSEGS window (A/AB1h.v), its owned statics (A/AF0m.v) and the 50 hand-off states of A/AB01.v; the donor A/AD2i.v and A/AD2j.v at origin/ossv/recipes c8557374ad2e give the text only *)
(* Read from: fuzz_codec.asan (libdiginet/fuzz_codec asan) sha256 7d470194ffdbde8b30a9810840f8e81d620ba1c555d510c475daeff37548a422; unstripped twin sha256 b28356da1a6547814e3a3c56e2d9e065e4f5b45715ccb5a236942cda3471fe1d *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66912 118189 0 0
[ mkChunk 66912 (CImg 51277) ].
Definition R_A1i : region :=
mkRegion None 118210 134212 0 0
[ mkChunk 118210 (CImg 16002) ].
Definition R_A1j : region :=
mkRegion None 134216 134988 0 0
[ mkChunk 134216 (CImg 772) ].
Definition R_A1k : region :=
mkRegion None 135008 135017 0 0
[ mkChunk 135008 (CImg 9) ].
Definition R_A1l : region :=
mkRegion None 135040 135049 0 0
[ mkChunk 135040 (CImg 9) ].
Definition R_A1m : region :=
mkRegion None 135072 135080 0 0
[ mkChunk 135072 (CImg 8) ].
Definition R_A1n : region :=
mkRegion None 135104 135114 0 0
[ mkChunk 135104 (CImg 10) ].
Definition R_A1o : region :=
mkRegion None 135136 135137 0 0
[ mkChunk 135136 (CImg 1) ].
Definition R_A1p : region :=
mkRegion None 135168 135175 0 0
[ mkChunk 135168 (CImg 7) ].
Definition R_A1q : region :=
mkRegion None 135200 135203 0 0
[ mkChunk 135200 (CImg 3) ].
Definition R_A1r : region :=
mkRegion None 135232 135238 0 0
[ mkChunk 135232 (CImg 6) ].
Definition R_A1s : region :=
mkRegion None 135264 135270 0 0
[ mkChunk 135264 (CImg 6) ].
Definition R_A1t : region :=
mkRegion None 135296 135301 0 0
[ mkChunk 135296 (CImg 5) ].
Definition R_A1u : region :=
mkRegion None 135328 135334 0 0
[ mkChunk 135328 (CImg 6) ].
Definition R_A1v : region :=
mkRegion None 135360 135367 0 0
[ mkChunk 135360 (CImg 7) ].
Definition R_A1w : region :=
mkRegion None 135392 135396 0 0
[ mkChunk 135392 (CImg 4) ].
Definition R_A1x : region :=
mkRegion None 135424 135432 0 0
[ mkChunk 135424 (CImg 8) ].
Definition R_A1y : region :=
mkRegion None 135456 135463 0 0
[ mkChunk 135456 (CImg 7) ].
Definition R_A1z : region :=
mkRegion None 135488 135495 0 0
[ mkChunk 135488 (CImg 7) ].
Definition R_A1aa : region :=
mkRegion None 135520 135526 0 0
[ mkChunk 135520 (CImg 6) ].
Definition R_A1ab : region :=
mkRegion None 135552 135557 0 0
[ mkChunk 135552 (CImg 5) ].
Definition R_A1ac : region :=
mkRegion None 135584 135590 0 0
[ mkChunk 135584 (CImg 6) ].
Definition R_A1ad : region :=
mkRegion None 135616 135622 0 0
[ mkChunk 135616 (CImg 6) ].
Definition R_A1ae : region :=
mkRegion None 135648 135653 0 0
[ mkChunk 135648 (CImg 5) ].
Definition R_A1af : region :=
mkRegion None 135680 135686 0 0
[ mkChunk 135680 (CImg 6) ].
Definition R_A1ag : region :=
mkRegion None 135712 135717 0 0
[ mkChunk 135712 (CImg 5) ].
Definition R_A1ah : region :=
mkRegion None 135744 135749 0 0
[ mkChunk 135744 (CImg 5) ].
Definition R_A1ai : region :=
mkRegion None 135776 135780 0 0
[ mkChunk 135776 (CImg 4) ].
Definition R_A1aj : region :=
mkRegion None 135808 135813 0 0
[ mkChunk 135808 (CImg 5) ].
Definition R_A1ak : region :=
mkRegion None 135840 135846 0 0
[ mkChunk 135840 (CImg 6) ].
Definition R_A1al : region :=
mkRegion None 135872 135875 0 0
[ mkChunk 135872 (CImg 3) ].
Definition R_A1am : region :=
mkRegion None 135904 135910 0 0
[ mkChunk 135904 (CImg 6) ].
Definition R_A1an : region :=
mkRegion None 135936 135942 0 0
[ mkChunk 135936 (CImg 6) ].
Definition R_A1ao : region :=
mkRegion None 135968 135970 0 0
[ mkChunk 135968 (CImg 2) ].
Definition R_A1ap : region :=
mkRegion None 136000 136041 0 0
[ mkChunk 136000 (CImg 41) ].
Definition R_A1aq : region :=
mkRegion None 136064 136073 0 0
[ mkChunk 136064 (CImg 9) ].
Definition R_A1ar : region :=
mkRegion None 136096 136460 0 0
[ mkChunk 136096 (CImg 364) ].
Definition R_A1as : region :=
mkRegion None 136544 137956 0 0
[ mkChunk 136544 (CImg 1412) ].
Definition R_A1at : region :=
mkRegion None 137960 138056 0 0
[ mkChunk 137960 (CImg 96) ].
Definition R_A1au : region :=
mkRegion None 138058 643072 0 0
[ mkChunk 138058 (CImg 505014) ].
Definition R_A2a : region :=
mkRegion None 643072 644728 0 0
[ mkChunk 643072 (CImg 1656) ].
Definition R_A2b : region :=
mkRegion None 644768 644784 0 0
[ mkChunk 644768 (CImg 16) ].
Definition R_A2c : region :=
mkRegion None 644800 644816 0 0
[ mkChunk 644800 (CImg 16) ].
Definition R_A2d : region :=
mkRegion None 644832 645296 0 0
[ mkChunk 644832 (CImg 464) ].
Definition R_A2e : region :=
mkRegion None 645408 645456 0 0
[ mkChunk 645408 (CImg 48) ].
Definition R_A2f : region :=
mkRegion None 645504 645872 0 0
[ mkChunk 645504 (CImg 368) ].
Definition R_A2g : region :=
mkRegion None 646000 648824 0 0
[ mkChunk 646000 (CImg 2824) ].
Definition R_A2h : region :=
mkRegion None 648832 649064 0 0
[ mkChunk 648832 (CImg 232) ].
Definition R_A2i : region :=
mkRegion None 649072 649096 0 0
[ mkChunk 649072 (CImg 24) ].
Definition R_A2j : region :=
mkRegion None 649112 649200 0 0
[ mkChunk 649112 (CImg 8);
mkChunk 649120 (CImg 80) ].
Definition R_A2k : region :=
mkRegion None 649224 653320 0 0
[ mkChunk 649224 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 663680 664512 663680 664512
[ mkChunk 663680 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 667080 667152 667080 667152
[ mkChunk 667080 (CVal 1 (SLit 1));
mkChunk 667081 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6064848 6130384 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6130384 6132588 6130384 6132588
[ mkChunk 6130384 (CImg 4);
mkChunk 6130388 (CVal 1 (SLit 0));
mkChunk 6130389 (CImg 2155);
mkChunk 6132552 (CVal 8 (SLit 6132552));
mkChunk 6132560 (CVal 8 (SLit 6132552));
mkChunk 6132568 (CVal 8 (SLit 6132552));
mkChunk 6132576 (CVal 8 (SLit 0));
mkChunk 6132584 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6132592 6132664 6132592 6132664
[ mkChunk 6132592 (CVal 4 (SLit 2));
mkChunk 6132596 (CImg 6);
mkChunk 6132602 (CVal 1 (SLit 1));
mkChunk 6132603 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6132672 6132744 0 0
[ mkChunk 6132672 (CVal 8 (SLit 6132672));
mkChunk 6132680 (CImg 24);
mkChunk 6132704 (CVal 8 (SLit 6264536));
mkChunk 6132712 (CImg 24);
mkChunk 6132736 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6132812 6132824 0 0
[ mkChunk 6132812 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6263832 6264528 6263904 6264448
[ mkChunk 6263832 (CImg 16);
mkChunk 6263848 (CVal 8 (SLit 639536));
mkChunk 6263856 (CVal 8 (SLit 0));
mkChunk 6263864 (CVal 8 (SLit 24));
mkChunk 6263872 (CVal 8 (SLit 8));
mkChunk 6263880 (CVal 8 (SLit 0));
mkChunk 6263888 (CVal 8 (SOff 41 0));
mkChunk 6263896 (CImg 16);
mkChunk 6263912 (CVal 4 (SLit 1));
mkChunk 6263916 (CImg 4);
mkChunk 6263920 (CVal 8 (SLit 6263928));
mkChunk 6263928 (CImg 8);
mkChunk 6263936 (CVal 8 (SLit 578188));
mkChunk 6263944 (CImg 248);
mkChunk 6264192 (CVal 8 (SLit 458252));
mkChunk 6264200 (CImg 264);
mkChunk 6264472 (CVal 8 (SOff 1 0));
mkChunk 6264480 (CVal 1 (SLit 1));
mkChunk 6264481 (CImg 7);
mkChunk 6264488 (CVal 8 (SOff 5 0));
mkChunk 6264496 (CVal 8 (SLit 6263840));
mkChunk 6264504 (CVal 8 (SLit 248));
mkChunk 6264512 (CVal 8 (SLit 8));
mkChunk 6264520 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6264536 6264608 0 0
[ mkChunk 6264536 (CImg 48);
mkChunk 6264592 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6265536 6267752 0 0
[ mkChunk 6265536 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6267760 6268856 0 0
[ mkChunk 6267760 (CImg 8);
mkChunk 6267768 (CVal 8 (SLit 347508));
mkChunk 6267776 (CImg 1016);
mkChunk 6268792 (CVal 4 (SLit 0));
mkChunk 6268796 (CImg 4);
mkChunk 6268800 (CVal 4 (SLit 0));
mkChunk 6268804 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6268864 6270976 0 0
[ mkChunk 6268864 (CImg 2112) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A2h; R_A2i; R_A2j; R_A2k; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
