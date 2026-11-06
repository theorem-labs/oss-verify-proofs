(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the start-up data of this file is generated from fuzz_disco's own asan image and its own collected hand-off states. *)
(* Read from: fuzz_disco.asan (libreac/fuzz_disco asan) sha256 5e39150dd8104df969eb360f9cc29c4f92fe12326afd23783a679e4fb4809f46; unstripped twin sha256 ec656cf105cb779da47f6e437d1c04782bfc50725d735933132c54bc98caccb4 *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66368 66384 0 0
[ mkChunk 66368 (CImg 16) ].
Definition R_A1e : region :=
mkRegion None 66392 66480 0 0
[ mkChunk 66392 (CImg 88) ].
Definition R_A1f : region :=
mkRegion None 66496 66512 0 0
[ mkChunk 66496 (CImg 16) ].
Definition R_A1g : region :=
mkRegion None 66520 66632 0 0
[ mkChunk 66520 (CImg 112) ].
Definition R_A1h : region :=
mkRegion None 66696 66888 0 0
[ mkChunk 66696 (CImg 192) ].
Definition R_A1i : region :=
mkRegion None 66952 118120 0 0
[ mkChunk 66952 (CImg 51168) ].
Definition R_A1j : region :=
mkRegion None 118141 134392 0 0
[ mkChunk 118141 (CImg 16251) ].
Definition R_A1k : region :=
mkRegion None 134396 135070 0 0
[ mkChunk 134396 (CImg 674) ].
Definition R_A1l : region :=
mkRegion None 135104 135112 0 0
[ mkChunk 135104 (CImg 8) ].
Definition R_A1m : region :=
mkRegion None 135136 135142 0 0
[ mkChunk 135136 (CImg 6) ].
Definition R_A1n : region :=
mkRegion None 135168 135173 0 0
[ mkChunk 135168 (CImg 5) ].
Definition R_A1o : region :=
mkRegion None 135200 135206 0 0
[ mkChunk 135200 (CImg 6) ].
Definition R_A1p : region :=
mkRegion None 135232 135237 0 0
[ mkChunk 135232 (CImg 5) ].
Definition R_A1q : region :=
mkRegion None 135264 135268 0 0
[ mkChunk 135264 (CImg 4) ].
Definition R_A1r : region :=
mkRegion None 135296 135301 0 0
[ mkChunk 135296 (CImg 5) ].
Definition R_A1s : region :=
mkRegion None 135328 135334 0 0
[ mkChunk 135328 (CImg 6) ].
Definition R_A1t : region :=
mkRegion None 135360 135366 0 0
[ mkChunk 135360 (CImg 6) ].
Definition R_A1u : region :=
mkRegion None 135392 135398 0 0
[ mkChunk 135392 (CImg 6) ].
Definition R_A1v : region :=
mkRegion None 135424 135431 0 0
[ mkChunk 135424 (CImg 7) ].
Definition R_A1w : region :=
mkRegion None 135456 135466 0 0
[ mkChunk 135456 (CImg 10) ].
Definition R_A1x : region :=
mkRegion None 135488 135493 0 0
[ mkChunk 135488 (CImg 5) ].
Definition R_A1y : region :=
mkRegion None 135520 135524 0 0
[ mkChunk 135520 (CImg 4) ].
Definition R_A1z : region :=
mkRegion None 135552 135559 0 0
[ mkChunk 135552 (CImg 7) ].
Definition R_A1aa : region :=
mkRegion None 135584 135623 0 0
[ mkChunk 135584 (CImg 39) ].
Definition R_A1ab : region :=
mkRegion None 135648 135655 0 0
[ mkChunk 135648 (CImg 7) ].
Definition R_A1ac : region :=
mkRegion None 135680 135688 0 0
[ mkChunk 135680 (CImg 8) ].
Definition R_A1ad : region :=
mkRegion None 135712 135717 0 0
[ mkChunk 135712 (CImg 5) ].
Definition R_A1ae : region :=
mkRegion None 135744 135747 0 0
[ mkChunk 135744 (CImg 3) ].
Definition R_A1af : region :=
mkRegion None 135776 135783 0 0
[ mkChunk 135776 (CImg 7) ].
Definition R_A1ag : region :=
mkRegion None 135808 135814 0 0
[ mkChunk 135808 (CImg 6) ].
Definition R_A1ah : region :=
mkRegion None 135840 135908 0 0
[ mkChunk 135840 (CImg 68) ].
Definition R_A1ai : region :=
mkRegion None 135936 135943 0 0
[ mkChunk 135936 (CImg 7) ].
Definition R_A1aj : region :=
mkRegion None 135968 135976 0 0
[ mkChunk 135968 (CImg 8) ].
Definition R_A1ak : region :=
mkRegion None 136000 136002 0 0
[ mkChunk 136000 (CImg 2) ].
Definition R_A1al : region :=
mkRegion None 136032 136073 0 0
[ mkChunk 136032 (CImg 41) ].
Definition R_A1am : region :=
mkRegion None 136128 136130 0 0
[ mkChunk 136128 (CImg 2) ].
Definition R_A1an : region :=
mkRegion None 136160 136161 0 0
[ mkChunk 136160 (CImg 1) ].
Definition R_A1ao : region :=
mkRegion None 136192 136205 0 0
[ mkChunk 136192 (CImg 13) ].
Definition R_A1ap : region :=
mkRegion None 136224 136238 0 0
[ mkChunk 136224 (CImg 14) ].
Definition R_A1aq : region :=
mkRegion None 136256 136273 0 0
[ mkChunk 136256 (CImg 17) ].
Definition R_A1ar : region :=
mkRegion None 136320 136339 0 0
[ mkChunk 136320 (CImg 19) ].
Definition R_A1as : region :=
mkRegion None 136384 136399 0 0
[ mkChunk 136384 (CImg 15) ].
Definition R_A1at : region :=
mkRegion None 136416 136428 0 0
[ mkChunk 136416 (CImg 12) ].
Definition R_A1au : region :=
mkRegion None 136448 136453 0 0
[ mkChunk 136448 (CImg 5) ].
Definition R_A1av : region :=
mkRegion None 136480 136486 0 0
[ mkChunk 136480 (CImg 6) ].
Definition R_A1aw : region :=
mkRegion None 136512 136528 0 0
[ mkChunk 136512 (CImg 16) ].
Definition R_A1ax : region :=
mkRegion None 136544 136546 0 0
[ mkChunk 136544 (CImg 2) ].
Definition R_A1ay : region :=
mkRegion None 136576 136615 0 0
[ mkChunk 136576 (CImg 39) ].
Definition R_A1az : region :=
mkRegion None 136640 136679 0 0
[ mkChunk 136640 (CImg 39) ].
Definition R_A1ba : region :=
mkRegion None 136704 136710 0 0
[ mkChunk 136704 (CImg 6) ].
Definition R_A1bb : region :=
mkRegion None 136736 136744 0 0
[ mkChunk 136736 (CImg 8) ].
Definition R_A1bc : region :=
mkRegion None 136768 136776 0 0
[ mkChunk 136768 (CImg 8) ].
Definition R_A1bd : region :=
mkRegion None 136800 136844 0 0
[ mkChunk 136800 (CImg 44) ].
Definition R_A1be : region :=
mkRegion None 136864 138280 0 0
[ mkChunk 136864 (CImg 1416) ].
Definition R_A1bf : region :=
mkRegion None 138284 138380 0 0
[ mkChunk 138284 (CImg 96) ].
Definition R_A1bg : region :=
mkRegion None 138382 651264 0 0
[ mkChunk 138382 (CImg 512882) ].
Definition R_A2a : region :=
mkRegion None 651264 656088 0 0
[ mkChunk 651264 (CImg 4824) ].
Definition R_A2b : region :=
mkRegion None 656128 656152 0 0
[ mkChunk 656128 (CImg 24) ].
Definition R_A2c : region :=
mkRegion None 656192 656216 0 0
[ mkChunk 656192 (CImg 24) ].
Definition R_A2d : region :=
mkRegion None 656256 656624 0 0
[ mkChunk 656256 (CImg 368) ].
Definition R_A2e : region :=
mkRegion None 656752 659576 0 0
[ mkChunk 656752 (CImg 2824) ].
Definition R_A2f : region :=
mkRegion None 659584 659816 0 0
[ mkChunk 659584 (CImg 232) ].
Definition R_A2g : region :=
mkRegion None 659824 659848 0 0
[ mkChunk 659824 (CImg 24) ].
Definition R_A2h : region :=
mkRegion None 659864 659952 0 0
[ mkChunk 659864 (CImg 8);
mkChunk 659872 (CImg 80) ].
Definition R_A2i : region :=
mkRegion None 659976 664072 0 0
[ mkChunk 659976 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 674432 675264 674432 675264
[ mkChunk 674432 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 678408 678480 678408 678480
[ mkChunk 678408 (CVal 1 (SLit 1));
mkChunk 678409 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6076176 6141712 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6141712 6143916 6141712 6143916
[ mkChunk 6141712 (CImg 4);
mkChunk 6141716 (CVal 1 (SLit 0));
mkChunk 6141717 (CImg 2155);
mkChunk 6143880 (CVal 8 (SLit 6143880));
mkChunk 6143888 (CVal 8 (SLit 6143880));
mkChunk 6143896 (CVal 8 (SLit 6143880));
mkChunk 6143904 (CVal 8 (SLit 0));
mkChunk 6143912 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6143920 6143992 6143920 6143992
[ mkChunk 6143920 (CVal 4 (SLit 2));
mkChunk 6143924 (CImg 6);
mkChunk 6143930 (CVal 1 (SLit 1));
mkChunk 6143931 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6144000 6144072 0 0
[ mkChunk 6144000 (CVal 8 (SLit 6144000));
mkChunk 6144008 (CImg 24);
mkChunk 6144032 (CVal 8 (SLit 6275864));
mkChunk 6144040 (CImg 24);
mkChunk 6144064 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6144140 6144152 0 0
[ mkChunk 6144140 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6275160 6275856 6275232 6275776
[ mkChunk 6275160 (CImg 16);
mkChunk 6275176 (CVal 8 (SLit 650920));
mkChunk 6275184 (CVal 8 (SLit 0));
mkChunk 6275192 (CVal 8 (SLit 24));
mkChunk 6275200 (CVal 8 (SLit 8));
mkChunk 6275208 (CVal 8 (SLit 0));
mkChunk 6275216 (CVal 8 (SOff 41 0));
mkChunk 6275224 (CImg 16);
mkChunk 6275240 (CVal 4 (SLit 1));
mkChunk 6275244 (CImg 4);
mkChunk 6275248 (CVal 8 (SLit 6275256));
mkChunk 6275256 (CImg 8);
mkChunk 6275264 (CVal 8 (SLit 589572));
mkChunk 6275272 (CImg 248);
mkChunk 6275520 (CVal 8 (SLit 460036));
mkChunk 6275528 (CImg 264);
mkChunk 6275800 (CVal 8 (SOff 1 0));
mkChunk 6275808 (CVal 1 (SLit 1));
mkChunk 6275809 (CImg 7);
mkChunk 6275816 (CVal 8 (SOff 5 0));
mkChunk 6275824 (CVal 8 (SLit 6275168));
mkChunk 6275832 (CVal 8 (SLit 248));
mkChunk 6275840 (CVal 8 (SLit 8));
mkChunk 6275848 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6275864 6275936 0 0
[ mkChunk 6275864 (CImg 48);
mkChunk 6275920 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6276864 6279080 0 0
[ mkChunk 6276864 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6279088 6280184 0 0
[ mkChunk 6279088 (CImg 8);
mkChunk 6279096 (CVal 8 (SLit 349292));
mkChunk 6279104 (CImg 1016);
mkChunk 6280120 (CVal 4 (SLit 0));
mkChunk 6280124 (CImg 4);
mkChunk 6280128 (CVal 4 (SLit 0));
mkChunk 6280132 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6280192 6283264 0 0
[ mkChunk 6280192 (CImg 3072) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A2h; R_A2i; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
