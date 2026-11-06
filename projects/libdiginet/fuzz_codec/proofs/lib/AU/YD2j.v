(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec image B by gen_ad2.py (frozen 8a509576b937, start-up tool set of commit 4453a719871) from fuzz_codec.asan-ubsan, its atable (lib/AU/YB12.v), its TSEGS window (lib/AU/YB1h.v), its owned statics (lib/AU/YF0m.v) and the 50 hand-off states of lib/AU/YB01.v; the donor lib/YD2i.v and lib/YD2j.v at commit 25e3d17bdb50 give the text only *)
(* Read from: fuzz_codec.asan-ubsan (libdiginet/fuzz_codec asan-ubsan) sha256 73109e32e77beff294d41ae6f16d607479ad1884485781b322645e6f8afa99c3; unstripped twin sha256 43feeaa314a42fe569b4443c710a74561e9077e617f7412cc54fbf4a6557b266 *)
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
mkRegion None 66912 118349 0 0
[ mkChunk 66912 (CImg 51437) ].
Definition R_A1i : region :=
mkRegion None 118370 134296 0 0
[ mkChunk 118370 (CImg 15926) ].
Definition R_A1j : region :=
mkRegion None 134300 135084 0 0
[ mkChunk 134300 (CImg 784) ].
Definition R_A1k : region :=
mkRegion None 135104 135113 0 0
[ mkChunk 135104 (CImg 9) ].
Definition R_A1l : region :=
mkRegion None 135136 135145 0 0
[ mkChunk 135136 (CImg 9) ].
Definition R_A1m : region :=
mkRegion None 135168 135176 0 0
[ mkChunk 135168 (CImg 8) ].
Definition R_A1n : region :=
mkRegion None 135200 135210 0 0
[ mkChunk 135200 (CImg 10) ].
Definition R_A1o : region :=
mkRegion None 135232 135233 0 0
[ mkChunk 135232 (CImg 1) ].
Definition R_A1p : region :=
mkRegion None 135264 135271 0 0
[ mkChunk 135264 (CImg 7) ].
Definition R_A1q : region :=
mkRegion None 135296 135299 0 0
[ mkChunk 135296 (CImg 3) ].
Definition R_A1r : region :=
mkRegion None 135328 135334 0 0
[ mkChunk 135328 (CImg 6) ].
Definition R_A1s : region :=
mkRegion None 135360 135366 0 0
[ mkChunk 135360 (CImg 6) ].
Definition R_A1t : region :=
mkRegion None 135392 135397 0 0
[ mkChunk 135392 (CImg 5) ].
Definition R_A1u : region :=
mkRegion None 135424 135430 0 0
[ mkChunk 135424 (CImg 6) ].
Definition R_A1v : region :=
mkRegion None 135456 135463 0 0
[ mkChunk 135456 (CImg 7) ].
Definition R_A1w : region :=
mkRegion None 135488 135492 0 0
[ mkChunk 135488 (CImg 4) ].
Definition R_A1x : region :=
mkRegion None 135520 135528 0 0
[ mkChunk 135520 (CImg 8) ].
Definition R_A1y : region :=
mkRegion None 135552 135559 0 0
[ mkChunk 135552 (CImg 7) ].
Definition R_A1z : region :=
mkRegion None 135584 135591 0 0
[ mkChunk 135584 (CImg 7) ].
Definition R_A1aa : region :=
mkRegion None 135616 135622 0 0
[ mkChunk 135616 (CImg 6) ].
Definition R_A1ab : region :=
mkRegion None 135648 135653 0 0
[ mkChunk 135648 (CImg 5) ].
Definition R_A1ac : region :=
mkRegion None 135680 135686 0 0
[ mkChunk 135680 (CImg 6) ].
Definition R_A1ad : region :=
mkRegion None 135712 135718 0 0
[ mkChunk 135712 (CImg 6) ].
Definition R_A1ae : region :=
mkRegion None 135744 135749 0 0
[ mkChunk 135744 (CImg 5) ].
Definition R_A1af : region :=
mkRegion None 135776 135782 0 0
[ mkChunk 135776 (CImg 6) ].
Definition R_A1ag : region :=
mkRegion None 135808 135813 0 0
[ mkChunk 135808 (CImg 5) ].
Definition R_A1ah : region :=
mkRegion None 135840 135845 0 0
[ mkChunk 135840 (CImg 5) ].
Definition R_A1ai : region :=
mkRegion None 135872 135876 0 0
[ mkChunk 135872 (CImg 4) ].
Definition R_A1aj : region :=
mkRegion None 135904 135909 0 0
[ mkChunk 135904 (CImg 5) ].
Definition R_A1ak : region :=
mkRegion None 135936 135942 0 0
[ mkChunk 135936 (CImg 6) ].
Definition R_A1al : region :=
mkRegion None 135968 135971 0 0
[ mkChunk 135968 (CImg 3) ].
Definition R_A1am : region :=
mkRegion None 136000 136006 0 0
[ mkChunk 136000 (CImg 6) ].
Definition R_A1an : region :=
mkRegion None 136032 136038 0 0
[ mkChunk 136032 (CImg 6) ].
Definition R_A1ao : region :=
mkRegion None 136064 136066 0 0
[ mkChunk 136064 (CImg 2) ].
Definition R_A1ap : region :=
mkRegion None 136096 136137 0 0
[ mkChunk 136096 (CImg 41) ].
Definition R_A1aq : region :=
mkRegion None 136160 136169 0 0
[ mkChunk 136160 (CImg 9) ].
Definition R_A1ar : region :=
mkRegion None 136192 136556 0 0
[ mkChunk 136192 (CImg 364) ].
Definition R_A1as : region :=
mkRegion None 136640 138052 0 0
[ mkChunk 136640 (CImg 1412) ].
Definition R_A1at : region :=
mkRegion None 138056 138152 0 0
[ mkChunk 138056 (CImg 96) ].
Definition R_A1au : region :=
mkRegion None 138154 643072 0 0
[ mkChunk 138154 (CImg 504918) ].
Definition R_A2a : region :=
mkRegion None 643072 647064 0 0
[ mkChunk 643072 (CImg 3992) ].
Definition R_A2b : region :=
mkRegion None 647104 647120 0 0
[ mkChunk 647104 (CImg 16) ].
Definition R_A2c : region :=
mkRegion None 647136 647152 0 0
[ mkChunk 647136 (CImg 16) ].
Definition R_A2d : region :=
mkRegion None 647168 647632 0 0
[ mkChunk 647168 (CImg 464) ].
Definition R_A2e : region :=
mkRegion None 647744 647792 0 0
[ mkChunk 647744 (CImg 48) ].
Definition R_A2f : region :=
mkRegion None 647840 648208 0 0
[ mkChunk 647840 (CImg 368) ].
Definition R_A2g : region :=
mkRegion None 648336 651160 0 0
[ mkChunk 648336 (CImg 2824) ].
Definition R_A2h : region :=
mkRegion None 651168 651400 0 0
[ mkChunk 651168 (CImg 232) ].
Definition R_A2i : region :=
mkRegion None 651408 651432 0 0
[ mkChunk 651408 (CImg 24) ].
Definition R_A2j : region :=
mkRegion None 651448 651536 0 0
[ mkChunk 651448 (CImg 8);
mkChunk 651456 (CImg 80) ].
Definition R_A2k : region :=
mkRegion None 651560 655656 0 0
[ mkChunk 651560 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 666016 666848 666016 666848
[ mkChunk 666016 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 669448 669520 669448 669520
[ mkChunk 669448 (CVal 1 (SLit 1));
mkChunk 669449 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6067216 6132752 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6132752 6134956 6132752 6134956
[ mkChunk 6132752 (CImg 4);
mkChunk 6132756 (CVal 1 (SLit 0));
mkChunk 6132757 (CImg 2155);
mkChunk 6134920 (CVal 8 (SLit 6134920));
mkChunk 6134928 (CVal 8 (SLit 6134920));
mkChunk 6134936 (CVal 8 (SLit 6134920));
mkChunk 6134944 (CVal 8 (SLit 0));
mkChunk 6134952 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6134960 6135032 6134960 6135032
[ mkChunk 6134960 (CVal 4 (SLit 2));
mkChunk 6134964 (CImg 6);
mkChunk 6134970 (CVal 1 (SLit 1));
mkChunk 6134971 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6135040 6135112 0 0
[ mkChunk 6135040 (CVal 8 (SLit 6135040));
mkChunk 6135048 (CImg 24);
mkChunk 6135072 (CVal 8 (SLit 6266904));
mkChunk 6135080 (CImg 24);
mkChunk 6135104 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6135180 6135192 0 0
[ mkChunk 6135180 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6266200 6266896 6266272 6266816
[ mkChunk 6266200 (CImg 16);
mkChunk 6266216 (CVal 8 (SLit 641896));
mkChunk 6266224 (CVal 8 (SLit 0));
mkChunk 6266232 (CVal 8 (SLit 24));
mkChunk 6266240 (CVal 8 (SLit 8));
mkChunk 6266248 (CVal 8 (SLit 0));
mkChunk 6266256 (CVal 8 (SOff 41 0));
mkChunk 6266264 (CImg 16);
mkChunk 6266280 (CVal 4 (SLit 1));
mkChunk 6266284 (CImg 4);
mkChunk 6266288 (CVal 8 (SLit 6266296));
mkChunk 6266296 (CImg 8);
mkChunk 6266304 (CVal 8 (SLit 580548));
mkChunk 6266312 (CImg 248);
mkChunk 6266560 (CVal 8 (SLit 458588));
mkChunk 6266568 (CImg 264);
mkChunk 6266840 (CVal 8 (SOff 1 0));
mkChunk 6266848 (CVal 1 (SLit 1));
mkChunk 6266849 (CImg 7);
mkChunk 6266856 (CVal 8 (SOff 5 0));
mkChunk 6266864 (CVal 8 (SLit 6266208));
mkChunk 6266872 (CVal 8 (SLit 248));
mkChunk 6266880 (CVal 8 (SLit 8));
mkChunk 6266888 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6266904 6266976 0 0
[ mkChunk 6266904 (CImg 48);
mkChunk 6266960 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6267904 6270120 0 0
[ mkChunk 6267904 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6270128 6271224 0 0
[ mkChunk 6270128 (CImg 8);
mkChunk 6270136 (CVal 8 (SLit 347844));
mkChunk 6270144 (CImg 1016);
mkChunk 6271160 (CVal 4 (SLit 0));
mkChunk 6271164 (CImg 4);
mkChunk 6271168 (CVal 4 (SLit 0));
mkChunk 6271172 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6271232 6275072 0 0
[ mkChunk 6271232 (CImg 3840) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A2h; R_A2i; R_A2j; R_A2k; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
