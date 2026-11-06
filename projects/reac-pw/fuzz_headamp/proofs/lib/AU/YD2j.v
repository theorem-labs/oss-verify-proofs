(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-pw/fuzz_headamp image B by gen_ad2.py 3665ff2a7926 (the start-up tool set at f1417943331) from this image's 50 collected hand-off states (lib/AU/YB01.v), its atable (lib/AU/YB12.v) and Tfib_owned_static (lib/AU/YF0m.v), templates proofs/cgif/cgif_file_fuzzer/lib/YD2i.v / YD2j.v at c8557374ad2e; Requires placed in lib.Reusable / lib.AU by fuzz_knock's lib/AU at origin/ossv/recipes 88154566652 *)
(* Read from: fuzz_headamp.asan-ubsan (reac-pw/fuzz_headamp asan-ubsan) sha256 53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; unstripped twin sha256 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP09.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 66280 0 0
[ mkChunk 65536 (CImg 744) ].
Definition R_A1b : region :=
mkRegion None 66288 66312 0 0
[ mkChunk 66288 (CImg 24) ].
Definition R_A1c : region :=
mkRegion None 66320 66360 0 0
[ mkChunk 66320 (CImg 40) ].
Definition R_A1d : region :=
mkRegion None 66368 66488 0 0
[ mkChunk 66368 (CImg 120) ].
Definition R_A1e : region :=
mkRegion None 66504 66512 0 0
[ mkChunk 66504 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66520 66640 0 0
[ mkChunk 66520 (CImg 120) ].
Definition R_A1g : region :=
mkRegion None 66704 66896 0 0
[ mkChunk 66704 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66960 118269 0 0
[ mkChunk 66960 (CImg 51309) ].
Definition R_A1i : region :=
mkRegion None 118290 134240 0 0
[ mkChunk 118290 (CImg 15950) ].
Definition R_A1j : region :=
mkRegion None 134244 134926 0 0
[ mkChunk 134244 (CImg 682) ].
Definition R_A1k : region :=
mkRegion None 134944 134958 0 0
[ mkChunk 134944 (CImg 14) ].
Definition R_A1l : region :=
mkRegion None 134976 134990 0 0
[ mkChunk 134976 (CImg 14) ].
Definition R_A1m : region :=
mkRegion None 135008 135023 0 0
[ mkChunk 135008 (CImg 15) ].
Definition R_A1n : region :=
mkRegion None 135040 135054 0 0
[ mkChunk 135040 (CImg 14) ].
Definition R_A1o : region :=
mkRegion None 135072 135091 0 0
[ mkChunk 135072 (CImg 19) ].
Definition R_A1p : region :=
mkRegion None 135136 135149 0 0
[ mkChunk 135136 (CImg 13) ].
Definition R_A1q : region :=
mkRegion None 135168 135184 0 0
[ mkChunk 135168 (CImg 16) ].
Definition R_A1r : region :=
mkRegion None 135200 135213 0 0
[ mkChunk 135200 (CImg 13) ].
Definition R_A1s : region :=
mkRegion None 135232 135288 0 0
[ mkChunk 135232 (CImg 56) ].
Definition R_A1t : region :=
mkRegion None 135328 135412 0 0
[ mkChunk 135328 (CImg 84) ].
Definition R_A1u : region :=
mkRegion None 135456 135472 0 0
[ mkChunk 135456 (CImg 16) ].
Definition R_A1v : region :=
mkRegion None 135488 135504 0 0
[ mkChunk 135488 (CImg 16) ].
Definition R_A1w : region :=
mkRegion None 135520 135534 0 0
[ mkChunk 135520 (CImg 14) ].
Definition R_A1x : region :=
mkRegion None 135552 135555 0 0
[ mkChunk 135552 (CImg 3) ].
Definition R_A1y : region :=
mkRegion None 135584 135587 0 0
[ mkChunk 135584 (CImg 3) ].
Definition R_A1z : region :=
mkRegion None 135616 135619 0 0
[ mkChunk 135616 (CImg 3) ].
Definition R_A1aa : region :=
mkRegion None 135648 135651 0 0
[ mkChunk 135648 (CImg 3) ].
Definition R_A1ab : region :=
mkRegion None 135680 135701 0 0
[ mkChunk 135680 (CImg 21) ].
Definition R_A1ac : region :=
mkRegion None 135744 135745 0 0
[ mkChunk 135744 (CImg 1) ].
Definition R_A1ad : region :=
mkRegion None 135776 135778 0 0
[ mkChunk 135776 (CImg 2) ].
Definition R_A1ae : region :=
mkRegion None 135808 135811 0 0
[ mkChunk 135808 (CImg 3) ].
Definition R_A1af : region :=
mkRegion None 135840 135843 0 0
[ mkChunk 135840 (CImg 3) ].
Definition R_A1ag : region :=
mkRegion None 135872 135875 0 0
[ mkChunk 135872 (CImg 3) ].
Definition R_A1ah : region :=
mkRegion None 135904 135907 0 0
[ mkChunk 135904 (CImg 3) ].
Definition R_A1ai : region :=
mkRegion None 135936 135939 0 0
[ mkChunk 135936 (CImg 3) ].
Definition R_A1aj : region :=
mkRegion None 135968 135972 0 0
[ mkChunk 135968 (CImg 4) ].
Definition R_A1ak : region :=
mkRegion None 136000 136022 0 0
[ mkChunk 136000 (CImg 22) ].
Definition R_A1al : region :=
mkRegion None 136064 136072 0 0
[ mkChunk 136064 (CImg 8) ].
Definition R_A1am : region :=
mkRegion None 136096 136100 0 0
[ mkChunk 136096 (CImg 4) ].
Definition R_A1an : region :=
mkRegion None 136128 136133 0 0
[ mkChunk 136128 (CImg 5) ].
Definition R_A1ao : region :=
mkRegion None 136160 136164 0 0
[ mkChunk 136160 (CImg 4) ].
Definition R_A1ap : region :=
mkRegion None 136192 136198 0 0
[ mkChunk 136192 (CImg 6) ].
Definition R_A1aq : region :=
mkRegion None 136224 136234 0 0
[ mkChunk 136224 (CImg 10) ].
Definition R_A1ar : region :=
mkRegion None 136256 136262 0 0
[ mkChunk 136256 (CImg 6) ].
Definition R_A1as : region :=
mkRegion None 136288 136290 0 0
[ mkChunk 136288 (CImg 2) ].
Definition R_A1at : region :=
mkRegion None 136320 136366 0 0
[ mkChunk 136320 (CImg 46) ].
Definition R_A1au : region :=
mkRegion None 136384 136392 0 0
[ mkChunk 136384 (CImg 8) ].
Definition R_A1av : region :=
mkRegion None 136416 136420 0 0
[ mkChunk 136416 (CImg 4) ].
Definition R_A1aw : region :=
mkRegion None 136448 136453 0 0
[ mkChunk 136448 (CImg 5) ].
Definition R_A1ax : region :=
mkRegion None 136480 137908 0 0
[ mkChunk 136480 (CImg 1428) ].
Definition R_A1ay : region :=
mkRegion None 137912 138008 0 0
[ mkChunk 137912 (CImg 96) ].
Definition R_A1az : region :=
mkRegion None 138010 640296 0 0
[ mkChunk 138010 (CImg 502286) ].
Definition R_A1ba : region :=
mkRegion None 640352 640464 0 0
[ mkChunk 640352 (CImg 112) ].
Definition R_A1bb : region :=
mkRegion None 640512 640576 0 0
[ mkChunk 640512 (CImg 64) ].
Definition R_A1bc : region :=
mkRegion None 640608 640976 0 0
[ mkChunk 640608 (CImg 368) ].
Definition R_A1bd : region :=
mkRegion None 641104 643928 0 0
[ mkChunk 641104 (CImg 2824) ].
Definition R_A1be : region :=
mkRegion None 643936 644168 0 0
[ mkChunk 643936 (CImg 232) ].
Definition R_A1bf : region :=
mkRegion None 644176 644200 0 0
[ mkChunk 644176 (CImg 24) ].
Definition R_A1bg : region :=
mkRegion None 644216 644304 0 0
[ mkChunk 644216 (CImg 8);
mkChunk 644224 (CImg 80) ].
Definition R_A1bh : region :=
mkRegion None 644328 647168 0 0
[ mkChunk 644328 (CImg 2840) ].
Definition R_A2 : region :=
mkRegion None 647168 648424 0 0
[ mkChunk 647168 (CImg 1256) ].
Definition R_A3 : region :=
mkRegion None 658784 659616 658784 659616
[ mkChunk 658784 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 662408 662480 662408 662480
[ mkChunk 662408 (CVal 1 (SLit 1));
mkChunk 662409 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6060176 6125712 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6125712 6127916 6125712 6127916
[ mkChunk 6125712 (CImg 4);
mkChunk 6125716 (CVal 1 (SLit 0));
mkChunk 6125717 (CImg 2155);
mkChunk 6127880 (CVal 8 (SLit 6127880));
mkChunk 6127888 (CVal 8 (SLit 6127880));
mkChunk 6127896 (CVal 8 (SLit 6127880));
mkChunk 6127904 (CVal 8 (SLit 0));
mkChunk 6127912 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6127920 6127992 6127920 6127992
[ mkChunk 6127920 (CVal 4 (SLit 2));
mkChunk 6127924 (CImg 6);
mkChunk 6127930 (CVal 1 (SLit 1));
mkChunk 6127931 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6128000 6128072 0 0
[ mkChunk 6128000 (CVal 8 (SLit 6128000));
mkChunk 6128008 (CImg 24);
mkChunk 6128032 (CVal 8 (SLit 6259864));
mkChunk 6128040 (CImg 24);
mkChunk 6128064 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6128140 6128152 0 0
[ mkChunk 6128140 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6259160 6259856 6259232 6259776
[ mkChunk 6259160 (CImg 16);
mkChunk 6259176 (CVal 8 (SLit 635072));
mkChunk 6259184 (CVal 8 (SLit 0));
mkChunk 6259192 (CVal 8 (SLit 24));
mkChunk 6259200 (CVal 8 (SLit 8));
mkChunk 6259208 (CVal 8 (SLit 0));
mkChunk 6259216 (CVal 8 (SOff 41 0));
mkChunk 6259224 (CImg 16);
mkChunk 6259240 (CVal 4 (SLit 1));
mkChunk 6259244 (CImg 4);
mkChunk 6259248 (CVal 8 (SLit 6259256));
mkChunk 6259256 (CImg 8);
mkChunk 6259264 (CVal 8 (SLit 575900));
mkChunk 6259272 (CImg 248);
mkChunk 6259520 (CVal 8 (SLit 459264));
mkChunk 6259528 (CImg 264);
mkChunk 6259800 (CVal 8 (SOff 1 0));
mkChunk 6259808 (CVal 1 (SLit 1));
mkChunk 6259809 (CImg 7);
mkChunk 6259816 (CVal 8 (SOff 5 0));
mkChunk 6259824 (CVal 8 (SLit 6259168));
mkChunk 6259832 (CVal 8 (SLit 248));
mkChunk 6259840 (CVal 8 (SLit 8));
mkChunk 6259848 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6259864 6259936 0 0
[ mkChunk 6259864 (CImg 48);
mkChunk 6259920 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6260864 6263080 0 0
[ mkChunk 6260864 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6263088 6264184 0 0
[ mkChunk 6263088 (CImg 8);
mkChunk 6263096 (CVal 8 (SLit 348520));
mkChunk 6263104 (CImg 1016);
mkChunk 6264120 (CVal 4 (SLit 0));
mkChunk 6264124 (CImg 4);
mkChunk 6264128 (CVal 4 (SLit 0));
mkChunk 6264132 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6264192 6266880 0 0
[ mkChunk 6264192 (CImg 2688) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A1bh; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
