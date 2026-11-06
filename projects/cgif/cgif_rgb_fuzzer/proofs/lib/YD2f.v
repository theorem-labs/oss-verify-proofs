(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YQ0j YQ0b.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 66280 0 0
[ mkChunk 65536 (CImg 744) ].
Definition R_A1b : region :=
mkRegion None 66288 66320 0 0
[ mkChunk 66288 (CImg 32) ].
Definition R_A1c : region :=
mkRegion None 66328 66360 0 0
[ mkChunk 66328 (CImg 32) ].
Definition R_A1d : region :=
mkRegion None 66368 66496 0 0
[ mkChunk 66368 (CImg 128) ].
Definition R_A1e : region :=
mkRegion None 66512 66528 0 0
[ mkChunk 66512 (CImg 16) ].
Definition R_A1f : region :=
mkRegion None 66536 66640 0 0
[ mkChunk 66536 (CImg 104) ].
Definition R_A1g : region :=
mkRegion None 66704 66896 0 0
[ mkChunk 66704 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66960 118182 0 0
[ mkChunk 66960 (CImg 51222) ].
Definition R_A1i : region :=
mkRegion None 118203 134196 0 0
[ mkChunk 118203 (CImg 15993) ].
Definition R_A1j : region :=
mkRegion None 134200 134848 0 0
[ mkChunk 134200 (CImg 648) ].
Definition R_A1k : region :=
mkRegion None 134880 134912 0 0
[ mkChunk 134880 (CImg 32) ].
Definition R_A1l : region :=
mkRegion None 134944 136360 0 0
[ mkChunk 134944 (CImg 1416) ].
Definition R_A1m : region :=
mkRegion None 136364 136460 0 0
[ mkChunk 136364 (CImg 96) ].
Definition R_A1n : region :=
mkRegion None 136462 663552 0 0
[ mkChunk 136462 (CImg 527090) ].
Definition R_A2a : region :=
mkRegion None 663552 668208 0 0
[ mkChunk 663552 (CImg 4656) ].
Definition R_A2b : region :=
mkRegion None 668336 671160 0 0
[ mkChunk 668336 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 671168 671400 0 0
[ mkChunk 671168 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 671408 671472 0 0
[ mkChunk 671408 (CImg 64) ].
Definition R_A2e : region :=
mkRegion None 671488 671576 0 0
[ mkChunk 671488 (CImg 8);
mkChunk 671496 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 671600 675696 0 0
[ mkChunk 671600 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 686072 686912 686072 686912
[ mkChunk 686072 (CImg 840) ].
Definition R_A4 : region :=
mkRegion None 687048 687120 687048 687120
[ mkChunk 687048 (CVal 1 (SLit 1));
mkChunk 687049 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6084816 6150352 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6150352 6152556 6150352 6152556
[ mkChunk 6150352 (CImg 4);
mkChunk 6150356 (CVal 1 (SLit 0));
mkChunk 6150357 (CImg 2155);
mkChunk 6152520 (CVal 8 (SLit 6152520));
mkChunk 6152528 (CVal 8 (SLit 6152520));
mkChunk 6152536 (CVal 8 (SLit 6152520));
mkChunk 6152544 (CVal 8 (SLit 0));
mkChunk 6152552 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6152560 6152632 6152560 6152632
[ mkChunk 6152560 (CVal 4 (SLit 2));
mkChunk 6152564 (CImg 6);
mkChunk 6152570 (CVal 1 (SLit 1));
mkChunk 6152571 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6152640 6152712 0 0
[ mkChunk 6152640 (CVal 8 (SLit 6152640));
mkChunk 6152648 (CImg 24);
mkChunk 6152672 (CVal 8 (SLit 6284504));
mkChunk 6152680 (CImg 24);
mkChunk 6152704 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6152780 6152792 0 0
[ mkChunk 6152780 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6283800 6284496 6283872 6284416
[ mkChunk 6283800 (CImg 16);
mkChunk 6283816 (CVal 8 (SLit 662712));
mkChunk 6283824 (CVal 8 (SLit 0));
mkChunk 6283832 (CVal 8 (SLit 24));
mkChunk 6283840 (CVal 8 (SLit 8));
mkChunk 6283848 (CVal 8 (SLit 0));
mkChunk 6283856 (CVal 8 (SOff 41 0));
mkChunk 6283864 (CImg 16);
mkChunk 6283880 (CVal 4 (SLit 1));
mkChunk 6283884 (CImg 4);
mkChunk 6283888 (CVal 8 (SLit 6283896));
mkChunk 6283896 (CImg 8);
mkChunk 6283904 (CVal 8 (SLit 600056));
mkChunk 6283912 (CImg 248);
mkChunk 6284160 (CVal 8 (SLit 460848));
mkChunk 6284168 (CImg 264);
mkChunk 6284440 (CVal 8 (SOff 1 0));
mkChunk 6284448 (CVal 1 (SLit 1));
mkChunk 6284449 (CImg 7);
mkChunk 6284456 (CVal 8 (SOff 5 0));
mkChunk 6284464 (CVal 8 (SLit 6283808));
mkChunk 6284472 (CVal 8 (SLit 248));
mkChunk 6284480 (CVal 8 (SLit 8));
mkChunk 6284488 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6284504 6284576 0 0
[ mkChunk 6284504 (CImg 48);
mkChunk 6284560 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6285504 6287720 0 0
[ mkChunk 6285504 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6287728 6288824 0 0
[ mkChunk 6287728 (CImg 8);
mkChunk 6287736 (CVal 8 (SLit 350104));
mkChunk 6287744 (CImg 1016);
mkChunk 6288760 (CVal 4 (SLit 0));
mkChunk 6288764 (CImg 4);
mkChunk 6288768 (CVal 4 (SLit 0));
mkChunk 6288772 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6288832 6291456 0 0
[ mkChunk 6288832 (CImg 2624) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
