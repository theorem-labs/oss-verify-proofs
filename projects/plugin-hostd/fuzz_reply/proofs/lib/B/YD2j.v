(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for plugin-hostd/fuzz_reply's asan-ubsan image by a Theorem Labs lane's gen_ad2.py (adopted in a Theorem Labs lane's tools/startup) from the 50 collected hand-off states (lib/B/YB01.v), the generated lib/B/YF0m.v, the atable and the image *)
(* Read from: fuzz_reply.asan-ubsan (plugin-hostd/fuzz_reply asan-ubsan) sha256 10ffb5f9202ae2bdb01b7a49df9866843a6a6a0e0c50bc67cdba6ce2f6d3cf2c; unstripped twin sha256 3389287e1d6107841f4e2bb22c691542a11433094c1a07d94fd5828afc3671f7 *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66912 118097 0 0
[ mkChunk 66912 (CImg 51185) ].
Definition R_A1i : region :=
mkRegion None 118118 134120 0 0
[ mkChunk 118118 (CImg 16002) ].
Definition R_A1j : region :=
mkRegion None 134124 134834 0 0
[ mkChunk 134124 (CImg 710) ].
Definition R_A1k : region :=
mkRegion None 134880 134881 0 0
[ mkChunk 134880 (CImg 1) ].
Definition R_A1l : region :=
mkRegion None 134912 134917 0 0
[ mkChunk 134912 (CImg 5) ].
Definition R_A1m : region :=
mkRegion None 134944 134958 0 0
[ mkChunk 134944 (CImg 14) ].
Definition R_A1n : region :=
mkRegion None 134976 134982 0 0
[ mkChunk 134976 (CImg 6) ].
Definition R_A1o : region :=
mkRegion None 135008 135012 0 0
[ mkChunk 135008 (CImg 4) ].
Definition R_A1p : region :=
mkRegion None 135040 135047 0 0
[ mkChunk 135040 (CImg 7) ].
Definition R_A1q : region :=
mkRegion None 135072 136484 0 0
[ mkChunk 135072 (CImg 1412) ].
Definition R_A1r : region :=
mkRegion None 136488 136584 0 0
[ mkChunk 136488 (CImg 96) ].
Definition R_A1s : region :=
mkRegion None 136586 643072 0 0
[ mkChunk 136586 (CImg 506486) ].
Definition R_A2a : region :=
mkRegion None 643072 646960 0 0
[ mkChunk 643072 (CImg 3888) ].
Definition R_A2b : region :=
mkRegion None 647088 649912 0 0
[ mkChunk 647088 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 649920 650152 0 0
[ mkChunk 649920 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 650160 650184 0 0
[ mkChunk 650160 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 650200 650288 0 0
[ mkChunk 650200 (CImg 8);
mkChunk 650208 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 650312 654432 0 0
[ mkChunk 650312 (CImg 4120) ].
Definition R_A3_1 : region :=
mkRegion None 664824 664872 664824 664872
[ mkChunk 664824 (CImg 48) ].
Definition R_A3_2 : region :=
mkRegion None 664896 664900 664896 664900
[ mkChunk 664896 (CImg 4) ].
Definition R_A3_3 : region :=
mkRegion None 664928 664932 664928 664932
[ mkChunk 664928 (CImg 4) ].
Definition R_A3_4 : region :=
mkRegion None 664960 665760 664960 665760
[ mkChunk 664960 (CImg 800) ].
Definition R_A4 : region :=
mkRegion None 667528 667600 667528 667600
[ mkChunk 667528 (CVal 1 (SLit 1));
mkChunk 667529 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6065296 6130832 0 0
[  ].
Definition R_A5a_1 : region :=
mkRegion None 6130832 6130888 6130832 6130888
[ mkChunk 6130832 (CImg 4);
mkChunk 6130836 (CVal 1 (SLit 0));
mkChunk 6130837 (CImg 51) ].
Definition R_A5a_2 : region :=
mkRegion None 6130912 6130913 6130912 6130913
[ mkChunk 6130912 (CImg 1) ].
Definition R_A5a_3 : region :=
mkRegion None 6130944 6130948 6130944 6130948
[ mkChunk 6130944 (CImg 4) ].
Definition R_A5a_4 : region :=
mkRegion None 6130976 6130980 6130976 6130980
[ mkChunk 6130976 (CImg 4) ].
Definition R_A5a_5 : region :=
mkRegion None 6131008 6131016 6131008 6131016
[ mkChunk 6131008 (CImg 8) ].
Definition R_A5a_6 : region :=
mkRegion None 6131040 6131041 6131040 6131041
[ mkChunk 6131040 (CImg 1) ].
Definition R_A5a_7 : region :=
mkRegion None 6131072 6131076 6131072 6131076
[ mkChunk 6131072 (CImg 4) ].
Definition R_A5a_8 : region :=
mkRegion None 6131104 6131108 6131104 6131108
[ mkChunk 6131104 (CImg 4) ].
Definition R_A5a_9 : region :=
mkRegion None 6131136 6131144 6131136 6131144
[ mkChunk 6131136 (CImg 8) ].
Definition R_A5a_10 : region :=
mkRegion None 6131168 6131169 6131168 6131169
[ mkChunk 6131168 (CImg 1) ].
Definition R_A5a_11 : region :=
mkRegion None 6131200 6131201 6131200 6131201
[ mkChunk 6131200 (CImg 1) ].
Definition R_A5a_12 : region :=
mkRegion None 6131232 6131233 6131232 6131233
[ mkChunk 6131232 (CImg 1) ].
Definition R_A5a_13 : region :=
mkRegion None 6131264 6131272 6131264 6131272
[ mkChunk 6131264 (CImg 8) ].
Definition R_A5a_14 : region :=
mkRegion None 6131296 6131680 6131296 6131680
[ mkChunk 6131296 (CImg 384) ].
Definition R_A5a_15 : region :=
mkRegion None 6131776 6131816 6131776 6131816
[ mkChunk 6131776 (CImg 40) ].
Definition R_A5a_16 : region :=
mkRegion None 6131872 6131880 6131872 6131880
[ mkChunk 6131872 (CImg 8) ].
Definition R_A5a_17 : region :=
mkRegion None 6131904 6131912 6131904 6131912
[ mkChunk 6131904 (CImg 8) ].
Definition R_A5a_18 : region :=
mkRegion None 6131936 6134092 6131936 6134092
[ mkChunk 6131936 (CImg 2112);
mkChunk 6134056 (CVal 8 (SLit 6134056));
mkChunk 6134064 (CVal 8 (SLit 6134056));
mkChunk 6134072 (CVal 8 (SLit 6134056));
mkChunk 6134080 (CVal 8 (SLit 0));
mkChunk 6134088 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6134096 6134168 6134096 6134168
[ mkChunk 6134096 (CVal 4 (SLit 2));
mkChunk 6134100 (CImg 6);
mkChunk 6134106 (CVal 1 (SLit 1));
mkChunk 6134107 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6134176 6134248 0 0
[ mkChunk 6134176 (CVal 8 (SLit 6134176));
mkChunk 6134184 (CImg 24);
mkChunk 6134208 (CVal 8 (SLit 6266040));
mkChunk 6134216 (CImg 24);
mkChunk 6134240 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6134316 6134328 0 0
[ mkChunk 6134316 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6265336 6266032 6265408 6265952
[ mkChunk 6265336 (CImg 16);
mkChunk 6265352 (CVal 8 (SLit 641464));
mkChunk 6265360 (CVal 8 (SLit 0));
mkChunk 6265368 (CVal 8 (SLit 24));
mkChunk 6265376 (CVal 8 (SLit 8));
mkChunk 6265384 (CVal 8 (SLit 0));
mkChunk 6265392 (CVal 8 (SOff 41 0));
mkChunk 6265400 (CImg 16);
mkChunk 6265416 (CVal 4 (SLit 1));
mkChunk 6265420 (CImg 4);
mkChunk 6265424 (CVal 8 (SLit 6265432));
mkChunk 6265432 (CImg 8);
mkChunk 6265440 (CVal 8 (SLit 578016));
mkChunk 6265448 (CImg 248);
mkChunk 6265696 (CVal 8 (SLit 465156));
mkChunk 6265704 (CImg 264);
mkChunk 6265976 (CVal 8 (SOff 1 0));
mkChunk 6265984 (CVal 1 (SLit 1));
mkChunk 6265985 (CImg 7);
mkChunk 6265992 (CVal 8 (SOff 5 0));
mkChunk 6266000 (CVal 8 (SLit 6265344));
mkChunk 6266008 (CVal 8 (SLit 248));
mkChunk 6266016 (CVal 8 (SLit 8));
mkChunk 6266024 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6266040 6266112 0 0
[ mkChunk 6266040 (CImg 48);
mkChunk 6266096 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6267040 6269256 0 0
[ mkChunk 6267040 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6269264 6270360 0 0
[ mkChunk 6269264 (CImg 8);
mkChunk 6269272 (CVal 8 (SLit 352788));
mkChunk 6269280 (CImg 1016);
mkChunk 6270296 (CVal 4 (SLit 0));
mkChunk 6270300 (CImg 4);
mkChunk 6270304 (CVal 4 (SLit 0));
mkChunk 6270308 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6270368 6275072 0 0
[ mkChunk 6270368 (CImg 4704) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3_1; R_A3_2; R_A3_3; R_A3_4; R_A4; R_RS; R_A5a_1; R_A5a_2; R_A5a_3; R_A5a_4; R_A5a_5; R_A5a_6; R_A5a_7; R_A5a_8; R_A5a_9; R_A5a_10; R_A5a_11; R_A5a_12; R_A5a_13; R_A5a_14; R_A5a_15; R_A5a_16; R_A5a_17; R_A5a_18; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
