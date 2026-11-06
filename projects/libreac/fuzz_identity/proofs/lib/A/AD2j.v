(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: regenerated for libreac/fuzz_identity image A (fuzz_identity.asan c954b804786c) from this image, its unstripped twin, the 50 collected hand-off states, AB12 and AF0m *)
(* Read from: fuzz_identity.asan (libreac/fuzz_identity asan) sha256 c954b804786cb87fc218414447199e35235b9788453ec0db312f97cd0dc4291b; unstripped twin sha256 5b0cbe57303630895c71979f5c3209f1d343f0f42aad36e87c9f5193408da124 *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66352 66464 0 0
[ mkChunk 66352 (CImg 112) ].
Definition R_A1e : region :=
mkRegion None 66480 66488 0 0
[ mkChunk 66480 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66496 66600 0 0
[ mkChunk 66496 (CImg 104) ].
Definition R_A1g : region :=
mkRegion None 66664 66856 0 0
[ mkChunk 66664 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66920 118392 0 0
[ mkChunk 66920 (CImg 51472) ].
Definition R_A1i : region :=
mkRegion None 118413 134408 0 0
[ mkChunk 118413 (CImg 15995) ].
Definition R_A1j : region :=
mkRegion None 134412 135042 0 0
[ mkChunk 134412 (CImg 630) ].
Definition R_A1k : region :=
mkRegion None 135072 135079 0 0
[ mkChunk 135072 (CImg 7) ].
Definition R_A1l : region :=
mkRegion None 135104 135110 0 0
[ mkChunk 135104 (CImg 6) ].
Definition R_A1m : region :=
mkRegion None 135136 135172 0 0
[ mkChunk 135136 (CImg 36) ].
Definition R_A1n : region :=
mkRegion None 135232 135239 0 0
[ mkChunk 135232 (CImg 7) ].
Definition R_A1o : region :=
mkRegion None 135264 135271 0 0
[ mkChunk 135264 (CImg 7) ].
Definition R_A1p : region :=
mkRegion None 135296 135304 0 0
[ mkChunk 135296 (CImg 8) ].
Definition R_A1q : region :=
mkRegion None 135328 135333 0 0
[ mkChunk 135328 (CImg 5) ].
Definition R_A1r : region :=
mkRegion None 135360 135428 0 0
[ mkChunk 135360 (CImg 68) ].
Definition R_A1s : region :=
mkRegion None 135488 135495 0 0
[ mkChunk 135488 (CImg 7) ].
Definition R_A1t : region :=
mkRegion None 135520 135527 0 0
[ mkChunk 135520 (CImg 7) ].
Definition R_A1u : region :=
mkRegion None 135552 135560 0 0
[ mkChunk 135552 (CImg 8) ].
Definition R_A1v : region :=
mkRegion None 135584 135589 0 0
[ mkChunk 135584 (CImg 5) ].
Definition R_A1w : region :=
mkRegion None 135616 135619 0 0
[ mkChunk 135616 (CImg 3) ].
Definition R_A1x : region :=
mkRegion None 135648 135655 0 0
[ mkChunk 135648 (CImg 7) ].
Definition R_A1y : region :=
mkRegion None 135680 135686 0 0
[ mkChunk 135680 (CImg 6) ].
Definition R_A1z : region :=
mkRegion None 135712 135750 0 0
[ mkChunk 135712 (CImg 38) ].
Definition R_A1aa : region :=
mkRegion None 135776 135799 0 0
[ mkChunk 135776 (CImg 23) ].
Definition R_A1ab : region :=
mkRegion None 135840 135846 0 0
[ mkChunk 135840 (CImg 6) ].
Definition R_A1ac : region :=
mkRegion None 135872 135894 0 0
[ mkChunk 135872 (CImg 22) ].
Definition R_A1ad : region :=
mkRegion None 135936 135943 0 0
[ mkChunk 135936 (CImg 7) ].
Definition R_A1ae : region :=
mkRegion None 135968 135975 0 0
[ mkChunk 135968 (CImg 7) ].
Definition R_A1af : region :=
mkRegion None 136000 136029 0 0
[ mkChunk 136000 (CImg 29) ].
Definition R_A1ag : region :=
mkRegion None 136064 136076 0 0
[ mkChunk 136064 (CImg 12) ].
Definition R_A1ah : region :=
mkRegion None 136096 136125 0 0
[ mkChunk 136096 (CImg 29) ].
Definition R_A1ai : region :=
mkRegion None 136160 136166 0 0
[ mkChunk 136160 (CImg 6) ].
Definition R_A1aj : region :=
mkRegion None 136192 136215 0 0
[ mkChunk 136192 (CImg 23) ].
Definition R_A1ak : region :=
mkRegion None 136256 136264 0 0
[ mkChunk 136256 (CImg 8) ].
Definition R_A1al : region :=
mkRegion None 136288 136294 0 0
[ mkChunk 136288 (CImg 6) ].
Definition R_A1am : region :=
mkRegion None 136320 136344 0 0
[ mkChunk 136320 (CImg 24) ].
Definition R_A1an : region :=
mkRegion None 136384 136392 0 0
[ mkChunk 136384 (CImg 8) ].
Definition R_A1ao : region :=
mkRegion None 136416 136423 0 0
[ mkChunk 136416 (CImg 7) ].
Definition R_A1ap : region :=
mkRegion None 136448 136472 0 0
[ mkChunk 136448 (CImg 24) ].
Definition R_A1aq : region :=
mkRegion None 136512 136521 0 0
[ mkChunk 136512 (CImg 9) ].
Definition R_A1ar : region :=
mkRegion None 136544 136551 0 0
[ mkChunk 136544 (CImg 7) ].
Definition R_A1as : region :=
mkRegion None 136576 136600 0 0
[ mkChunk 136576 (CImg 24) ].
Definition R_A1at : region :=
mkRegion None 136640 136649 0 0
[ mkChunk 136640 (CImg 9) ].
Definition R_A1au : region :=
mkRegion None 136672 136679 0 0
[ mkChunk 136672 (CImg 7) ].
Definition R_A1av : region :=
mkRegion None 136704 136727 0 0
[ mkChunk 136704 (CImg 23) ].
Definition R_A1aw : region :=
mkRegion None 136768 136776 0 0
[ mkChunk 136768 (CImg 8) ].
Definition R_A1ax : region :=
mkRegion None 136800 136807 0 0
[ mkChunk 136800 (CImg 7) ].
Definition R_A1ay : region :=
mkRegion None 136832 136855 0 0
[ mkChunk 136832 (CImg 23) ].
Definition R_A1az : region :=
mkRegion None 136896 136904 0 0
[ mkChunk 136896 (CImg 8) ].
Definition R_A1ba : region :=
mkRegion None 136928 136935 0 0
[ mkChunk 136928 (CImg 7) ].
Definition R_A1bb : region :=
mkRegion None 136960 136984 0 0
[ mkChunk 136960 (CImg 24) ].
Definition R_A1bc : region :=
mkRegion None 137024 137032 0 0
[ mkChunk 137024 (CImg 8) ].
Definition R_A1bd : region :=
mkRegion None 137056 138468 0 0
[ mkChunk 137056 (CImg 1412) ].
Definition R_A1be : region :=
mkRegion None 138472 138568 0 0
[ mkChunk 138472 (CImg 96) ].
Definition R_A1bf : region :=
mkRegion None 138570 630784 0 0
[ mkChunk 138570 (CImg 492214) ].
Definition R_A2a : region :=
mkRegion None 630784 635288 0 0
[ mkChunk 630784 (CImg 4504) ].
Definition R_A2b : region :=
mkRegion None 635328 635352 0 0
[ mkChunk 635328 (CImg 24) ].
Definition R_A2c : region :=
mkRegion None 635392 635416 0 0
[ mkChunk 635392 (CImg 24) ].
Definition R_A2d : region :=
mkRegion None 635456 638712 0 0
[ mkChunk 635456 (CImg 3256) ].
Definition R_A2e : region :=
mkRegion None 639520 639888 0 0
[ mkChunk 639520 (CImg 368) ].
Definition R_A2f : region :=
mkRegion None 640016 642840 0 0
[ mkChunk 640016 (CImg 2824) ].
Definition R_A2g : region :=
mkRegion None 642848 643080 0 0
[ mkChunk 642848 (CImg 232) ].
Definition R_A2h : region :=
mkRegion None 643088 643112 0 0
[ mkChunk 643088 (CImg 24) ].
Definition R_A2i : region :=
mkRegion None 643128 643216 0 0
[ mkChunk 643128 (CImg 8);
mkChunk 643136 (CImg 80) ].
Definition R_A2j : region :=
mkRegion None 643240 647336 0 0
[ mkChunk 643240 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 657696 658528 657696 658528
[ mkChunk 657696 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 661768 661840 661768 661840
[ mkChunk 661768 (CVal 1 (SLit 1));
mkChunk 661769 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6059536 6125072 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6125072 6127276 6125072 6127276
[ mkChunk 6125072 (CImg 4);
mkChunk 6125076 (CVal 1 (SLit 0));
mkChunk 6125077 (CImg 2155);
mkChunk 6127240 (CVal 8 (SLit 6127240));
mkChunk 6127248 (CVal 8 (SLit 6127240));
mkChunk 6127256 (CVal 8 (SLit 6127240));
mkChunk 6127264 (CVal 8 (SLit 0));
mkChunk 6127272 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6127280 6127352 6127280 6127352
[ mkChunk 6127280 (CVal 4 (SLit 2));
mkChunk 6127284 (CImg 6);
mkChunk 6127290 (CVal 1 (SLit 1));
mkChunk 6127291 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6127360 6127432 0 0
[ mkChunk 6127360 (CVal 8 (SLit 6127360));
mkChunk 6127368 (CImg 24);
mkChunk 6127392 (CVal 8 (SLit 6259224));
mkChunk 6127400 (CImg 24);
mkChunk 6127424 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6127500 6127512 0 0
[ mkChunk 6127500 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6258520 6259216 6258592 6259136
[ mkChunk 6258520 (CImg 16);
mkChunk 6258536 (CVal 8 (SLit 630096));
mkChunk 6258544 (CVal 8 (SLit 0));
mkChunk 6258552 (CVal 8 (SLit 24));
mkChunk 6258560 (CVal 8 (SLit 8));
mkChunk 6258568 (CVal 8 (SLit 0));
mkChunk 6258576 (CVal 8 (SOff 41 0));
mkChunk 6258584 (CImg 16);
mkChunk 6258600 (CVal 4 (SLit 1));
mkChunk 6258604 (CImg 4);
mkChunk 6258608 (CVal 8 (SLit 6258616));
mkChunk 6258616 (CImg 8);
mkChunk 6258624 (CVal 8 (SLit 568744));
mkChunk 6258632 (CImg 248);
mkChunk 6258880 (CVal 8 (SLit 457932));
mkChunk 6258888 (CImg 264);
mkChunk 6259160 (CVal 8 (SOff 1 0));
mkChunk 6259168 (CVal 1 (SLit 1));
mkChunk 6259169 (CImg 7);
mkChunk 6259176 (CVal 8 (SOff 5 0));
mkChunk 6259184 (CVal 8 (SLit 6258528));
mkChunk 6259192 (CVal 8 (SLit 248));
mkChunk 6259200 (CVal 8 (SLit 8));
mkChunk 6259208 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6259224 6259296 0 0
[ mkChunk 6259224 (CImg 48);
mkChunk 6259280 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6260224 6262440 0 0
[ mkChunk 6260224 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6262448 6263544 0 0
[ mkChunk 6262448 (CImg 8);
mkChunk 6262456 (CVal 8 (SLit 347188));
mkChunk 6262464 (CImg 1016);
mkChunk 6263480 (CVal 4 (SLit 0));
mkChunk 6263484 (CImg 4);
mkChunk 6263488 (CVal 4 (SLit 0));
mkChunk 6263492 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6263552 6266880 0 0
[ mkChunk 6263552 (CImg 3328) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A2h; R_A2i; R_A2j; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
