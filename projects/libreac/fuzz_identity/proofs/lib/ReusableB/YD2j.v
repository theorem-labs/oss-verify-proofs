(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/A/AD2i.v and lib/A/AD2j.v (origin/ossv/recipes c8557374ad2e) for libreac/fuzz_identity's asan-ubsan image (sha256 baf1a4d065e0...) by a Theorem Labs lane's gen_ad2.py, with its module paths changed to identity's lib.B: sregs_main, TIDV, CANV and TFIB_MAIN from the 50 hand-off states of lib/ReusableB/YB01.v, the image bounds from lib/ReusableB/YB12.v and lib/ReusableB/YB1h.v; IMG_REGIONS below .data from the image and the owned static cells of lib/ReusableB/YF0m.v, from .data on cgif's regions placed at the donor's offsets from the objects of the unstripped twin (43b44d50be8a...) and cut around the same owned cells, every CVal value read from the hand-off states *)
(* Modified by Theorem Labs, 2026-10-29: re-emitted at the release's two-image path lib/ReusableB/YD2j.v with the same content as before, only its Require paths mapped to the release layout (lib.B.A* -> lib.ReusableB.Y*, image-specific Reusable modules -> lib.ReusableB). *)
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
mkRegion None 66920 118399 0 0
[ mkChunk 66920 (CImg 51479) ].
Definition R_A1i : region :=
mkRegion None 118420 134416 0 0
[ mkChunk 118420 (CImg 15996) ].
Definition R_A1j : region :=
mkRegion None 134420 135042 0 0
[ mkChunk 134420 (CImg 622) ].
Definition R_A1k : region :=
mkRegion None 135072 135075 0 0
[ mkChunk 135072 (CImg 3) ].
Definition R_A1l : region :=
mkRegion None 135104 135111 0 0
[ mkChunk 135104 (CImg 7) ].
Definition R_A1m : region :=
mkRegion None 135136 135142 0 0
[ mkChunk 135136 (CImg 6) ].
Definition R_A1n : region :=
mkRegion None 135168 135204 0 0
[ mkChunk 135168 (CImg 36) ].
Definition R_A1o : region :=
mkRegion None 135264 135271 0 0
[ mkChunk 135264 (CImg 7) ].
Definition R_A1p : region :=
mkRegion None 135296 135303 0 0
[ mkChunk 135296 (CImg 7) ].
Definition R_A1q : region :=
mkRegion None 135328 135336 0 0
[ mkChunk 135328 (CImg 8) ].
Definition R_A1r : region :=
mkRegion None 135360 135365 0 0
[ mkChunk 135360 (CImg 5) ].
Definition R_A1s : region :=
mkRegion None 135392 135460 0 0
[ mkChunk 135392 (CImg 68) ].
Definition R_A1t : region :=
mkRegion None 135520 135527 0 0
[ mkChunk 135520 (CImg 7) ].
Definition R_A1u : region :=
mkRegion None 135552 135559 0 0
[ mkChunk 135552 (CImg 7) ].
Definition R_A1v : region :=
mkRegion None 135584 135592 0 0
[ mkChunk 135584 (CImg 8) ].
Definition R_A1w : region :=
mkRegion None 135616 135621 0 0
[ mkChunk 135616 (CImg 5) ].
Definition R_A1x : region :=
mkRegion None 135648 135651 0 0
[ mkChunk 135648 (CImg 3) ].
Definition R_A1y : region :=
mkRegion None 135680 135687 0 0
[ mkChunk 135680 (CImg 7) ].
Definition R_A1z : region :=
mkRegion None 135712 135718 0 0
[ mkChunk 135712 (CImg 6) ].
Definition R_A1aa : region :=
mkRegion None 135744 135782 0 0
[ mkChunk 135744 (CImg 38) ].
Definition R_A1ab : region :=
mkRegion None 135808 135831 0 0
[ mkChunk 135808 (CImg 23) ].
Definition R_A1ac : region :=
mkRegion None 135872 135878 0 0
[ mkChunk 135872 (CImg 6) ].
Definition R_A1ad : region :=
mkRegion None 135904 135926 0 0
[ mkChunk 135904 (CImg 22) ].
Definition R_A1ae : region :=
mkRegion None 135968 135975 0 0
[ mkChunk 135968 (CImg 7) ].
Definition R_A1af : region :=
mkRegion None 136000 136007 0 0
[ mkChunk 136000 (CImg 7) ].
Definition R_A1ag : region :=
mkRegion None 136032 136061 0 0
[ mkChunk 136032 (CImg 29) ].
Definition R_A1ah : region :=
mkRegion None 136096 136108 0 0
[ mkChunk 136096 (CImg 12) ].
Definition R_A1ai : region :=
mkRegion None 136128 136157 0 0
[ mkChunk 136128 (CImg 29) ].
Definition R_A1aj : region :=
mkRegion None 136192 136198 0 0
[ mkChunk 136192 (CImg 6) ].
Definition R_A1ak : region :=
mkRegion None 136224 136247 0 0
[ mkChunk 136224 (CImg 23) ].
Definition R_A1al : region :=
mkRegion None 136288 136296 0 0
[ mkChunk 136288 (CImg 8) ].
Definition R_A1am : region :=
mkRegion None 136320 136326 0 0
[ mkChunk 136320 (CImg 6) ].
Definition R_A1an : region :=
mkRegion None 136352 136376 0 0
[ mkChunk 136352 (CImg 24) ].
Definition R_A1ao : region :=
mkRegion None 136416 136424 0 0
[ mkChunk 136416 (CImg 8) ].
Definition R_A1ap : region :=
mkRegion None 136448 136455 0 0
[ mkChunk 136448 (CImg 7) ].
Definition R_A1aq : region :=
mkRegion None 136480 136504 0 0
[ mkChunk 136480 (CImg 24) ].
Definition R_A1ar : region :=
mkRegion None 136544 136553 0 0
[ mkChunk 136544 (CImg 9) ].
Definition R_A1as : region :=
mkRegion None 136576 136583 0 0
[ mkChunk 136576 (CImg 7) ].
Definition R_A1at : region :=
mkRegion None 136608 136632 0 0
[ mkChunk 136608 (CImg 24) ].
Definition R_A1au : region :=
mkRegion None 136672 136681 0 0
[ mkChunk 136672 (CImg 9) ].
Definition R_A1av : region :=
mkRegion None 136704 136711 0 0
[ mkChunk 136704 (CImg 7) ].
Definition R_A1aw : region :=
mkRegion None 136736 136759 0 0
[ mkChunk 136736 (CImg 23) ].
Definition R_A1ax : region :=
mkRegion None 136800 136808 0 0
[ mkChunk 136800 (CImg 8) ].
Definition R_A1ay : region :=
mkRegion None 136832 136839 0 0
[ mkChunk 136832 (CImg 7) ].
Definition R_A1az : region :=
mkRegion None 136864 136887 0 0
[ mkChunk 136864 (CImg 23) ].
Definition R_A1ba : region :=
mkRegion None 136928 136936 0 0
[ mkChunk 136928 (CImg 8) ].
Definition R_A1bb : region :=
mkRegion None 136960 136967 0 0
[ mkChunk 136960 (CImg 7) ].
Definition R_A1bc : region :=
mkRegion None 136992 137016 0 0
[ mkChunk 136992 (CImg 24) ].
Definition R_A1bd : region :=
mkRegion None 137056 137064 0 0
[ mkChunk 137056 (CImg 8) ].
Definition R_A1be : region :=
mkRegion None 137088 138500 0 0
[ mkChunk 137088 (CImg 1412) ].
Definition R_A1bf : region :=
mkRegion None 138504 138600 0 0
[ mkChunk 138504 (CImg 96) ].
Definition R_A1bg : region :=
mkRegion None 138602 634880 0 0
[ mkChunk 138602 (CImg 496278) ].
Definition R_A2a : region :=
mkRegion None 634880 636024 0 0
[ mkChunk 634880 (CImg 1144) ].
Definition R_A2b : region :=
mkRegion None 636064 636088 0 0
[ mkChunk 636064 (CImg 24) ].
Definition R_A2c : region :=
mkRegion None 636128 636152 0 0
[ mkChunk 636128 (CImg 24) ].
Definition R_A2d : region :=
mkRegion None 636192 639448 0 0
[ mkChunk 636192 (CImg 3256) ].
Definition R_A2e : region :=
mkRegion None 640256 640624 0 0
[ mkChunk 640256 (CImg 368) ].
Definition R_A2f : region :=
mkRegion None 640752 643576 0 0
[ mkChunk 640752 (CImg 2824) ].
Definition R_A2g : region :=
mkRegion None 643584 643816 0 0
[ mkChunk 643584 (CImg 232) ].
Definition R_A2h : region :=
mkRegion None 643824 643848 0 0
[ mkChunk 643824 (CImg 24) ].
Definition R_A2i : region :=
mkRegion None 643864 643952 0 0
[ mkChunk 643864 (CImg 8);
mkChunk 643872 (CImg 80) ].
Definition R_A2j : region :=
mkRegion None 643976 648072 0 0
[ mkChunk 643976 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 658432 659264 658432 659264
[ mkChunk 658432 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 662536 662608 662536 662608
[ mkChunk 662536 (CVal 1 (SLit 1));
mkChunk 662537 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6060304 6125840 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6125840 6128044 6125840 6128044
[ mkChunk 6125840 (CImg 4);
mkChunk 6125844 (CVal 1 (SLit 0));
mkChunk 6125845 (CImg 2155);
mkChunk 6128008 (CVal 8 (SLit 6128008));
mkChunk 6128016 (CVal 8 (SLit 6128008));
mkChunk 6128024 (CVal 8 (SLit 6128008));
mkChunk 6128032 (CVal 8 (SLit 0));
mkChunk 6128040 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6128048 6128120 6128048 6128120
[ mkChunk 6128048 (CVal 4 (SLit 2));
mkChunk 6128052 (CImg 6);
mkChunk 6128058 (CVal 1 (SLit 1));
mkChunk 6128059 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6128128 6128200 0 0
[ mkChunk 6128128 (CVal 8 (SLit 6128128));
mkChunk 6128136 (CImg 24);
mkChunk 6128160 (CVal 8 (SLit 6259992));
mkChunk 6128168 (CImg 24);
mkChunk 6128192 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6128268 6128280 0 0
[ mkChunk 6128268 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6259288 6259984 6259360 6259904
[ mkChunk 6259288 (CImg 16);
mkChunk 6259304 (CVal 8 (SLit 630840));
mkChunk 6259312 (CVal 8 (SLit 0));
mkChunk 6259320 (CVal 8 (SLit 24));
mkChunk 6259328 (CVal 8 (SLit 8));
mkChunk 6259336 (CVal 8 (SLit 0));
mkChunk 6259344 (CVal 8 (SOff 41 0));
mkChunk 6259352 (CImg 16);
mkChunk 6259368 (CVal 4 (SLit 1));
mkChunk 6259372 (CImg 4);
mkChunk 6259376 (CVal 8 (SLit 6259384));
mkChunk 6259384 (CImg 8);
mkChunk 6259392 (CVal 8 (SLit 569492));
mkChunk 6259400 (CImg 248);
mkChunk 6259648 (CVal 8 (SLit 458036));
mkChunk 6259656 (CImg 264);
mkChunk 6259928 (CVal 8 (SOff 1 0));
mkChunk 6259936 (CVal 1 (SLit 1));
mkChunk 6259937 (CImg 7);
mkChunk 6259944 (CVal 8 (SOff 5 0));
mkChunk 6259952 (CVal 8 (SLit 6259296));
mkChunk 6259960 (CVal 8 (SLit 248));
mkChunk 6259968 (CVal 8 (SLit 8));
mkChunk 6259976 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6259992 6260064 0 0
[ mkChunk 6259992 (CImg 48);
mkChunk 6260048 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6260992 6263208 0 0
[ mkChunk 6260992 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6263216 6264312 0 0
[ mkChunk 6263216 (CImg 8);
mkChunk 6263224 (CVal 8 (SLit 347292));
mkChunk 6263232 (CImg 1016);
mkChunk 6264248 (CVal 4 (SLit 0));
mkChunk 6264252 (CImg 4);
mkChunk 6264256 (CVal 4 (SLit 0));
mkChunk 6264260 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6264320 6266880 0 0
[ mkChunk 6264320 (CImg 2560) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A2h; R_A2i; R_A2j; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
