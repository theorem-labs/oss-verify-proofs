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
mkRegion None 66288 66312 0 0
[ mkChunk 66288 (CImg 24) ].
Definition R_A1c : region :=
mkRegion None 66320 66344 0 0
[ mkChunk 66320 (CImg 24) ].
Definition R_A1d : region :=
mkRegion None 66352 66464 0 0
[ mkChunk 66352 (CImg 112) ].
Definition R_A1e : region :=
mkRegion None 66480 66496 0 0
[ mkChunk 66480 (CImg 16) ].
Definition R_A1f : region :=
mkRegion None 66504 66608 0 0
[ mkChunk 66504 (CImg 104) ].
Definition R_A1g : region :=
mkRegion None 66672 66864 0 0
[ mkChunk 66672 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66928 118191 0 0
[ mkChunk 66928 (CImg 51263) ].
Definition R_A1i : region :=
mkRegion None 118212 134204 0 0
[ mkChunk 118212 (CImg 15992) ].
Definition R_A1j : region :=
mkRegion None 134208 134848 0 0
[ mkChunk 134208 (CImg 640) ].
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
mkRegion None 136462 659456 0 0
[ mkChunk 136462 (CImg 522994) ].
Definition R_A2a : region :=
mkRegion None 659456 663872 0 0
[ mkChunk 659456 (CImg 4416) ].
Definition R_A2b : region :=
mkRegion None 664000 666824 0 0
[ mkChunk 664000 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 666832 667064 0 0
[ mkChunk 666832 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 667072 667136 0 0
[ mkChunk 667072 (CImg 64) ].
Definition R_A2e : region :=
mkRegion None 667152 667240 0 0
[ mkChunk 667152 (CImg 8);
mkChunk 667160 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 667264 671360 0 0
[ mkChunk 667264 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 681736 682576 681736 682576
[ mkChunk 681736 (CImg 840) ].
Definition R_A4 : region :=
mkRegion None 682760 682832 682760 682832
[ mkChunk 682760 (CVal 1 (SLit 1));
mkChunk 682761 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6080528 6146064 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6146064 6148268 6146064 6148268
[ mkChunk 6146064 (CImg 4);
mkChunk 6146068 (CVal 1 (SLit 0));
mkChunk 6146069 (CImg 2155);
mkChunk 6148232 (CVal 8 (SLit 6148232));
mkChunk 6148240 (CVal 8 (SLit 6148232));
mkChunk 6148248 (CVal 8 (SLit 6148232));
mkChunk 6148256 (CVal 8 (SLit 0));
mkChunk 6148264 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6148272 6148344 6148272 6148344
[ mkChunk 6148272 (CVal 4 (SLit 2));
mkChunk 6148276 (CImg 6);
mkChunk 6148282 (CVal 1 (SLit 1));
mkChunk 6148283 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6148352 6148424 0 0
[ mkChunk 6148352 (CVal 8 (SLit 6148352));
mkChunk 6148360 (CImg 24);
mkChunk 6148384 (CVal 8 (SLit 6280216));
mkChunk 6148392 (CImg 24);
mkChunk 6148416 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6148492 6148504 0 0
[ mkChunk 6148492 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6279512 6280208 6279584 6280128
[ mkChunk 6279512 (CImg 16);
mkChunk 6279528 (CVal 8 (SLit 658376));
mkChunk 6279536 (CVal 8 (SLit 0));
mkChunk 6279544 (CVal 8 (SLit 24));
mkChunk 6279552 (CVal 8 (SLit 8));
mkChunk 6279560 (CVal 8 (SLit 0));
mkChunk 6279568 (CVal 8 (SOff 41 0));
mkChunk 6279576 (CImg 16);
mkChunk 6279592 (CVal 4 (SLit 1));
mkChunk 6279596 (CImg 4);
mkChunk 6279600 (CVal 8 (SLit 6279608));
mkChunk 6279608 (CImg 8);
mkChunk 6279616 (CVal 8 (SLit 595884));
mkChunk 6279624 (CImg 248);
mkChunk 6279872 (CVal 8 (SLit 460140));
mkChunk 6279880 (CImg 264);
mkChunk 6280152 (CVal 8 (SOff 1 0));
mkChunk 6280160 (CVal 1 (SLit 1));
mkChunk 6280161 (CImg 7);
mkChunk 6280168 (CVal 8 (SOff 5 0));
mkChunk 6280176 (CVal 8 (SLit 6279520));
mkChunk 6280184 (CVal 8 (SLit 248));
mkChunk 6280192 (CVal 8 (SLit 8));
mkChunk 6280200 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6280216 6280288 0 0
[ mkChunk 6280216 (CImg 48);
mkChunk 6280272 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6281216 6283432 0 0
[ mkChunk 6281216 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6283440 6284536 0 0
[ mkChunk 6283440 (CImg 8);
mkChunk 6283448 (CVal 8 (SLit 349396));
mkChunk 6283456 (CImg 1016);
mkChunk 6284472 (CVal 4 (SLit 0));
mkChunk 6284476 (CImg 4);
mkChunk 6284480 (CVal 4 (SLit 0));
mkChunk 6284484 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6284544 6287360 0 0
[ mkChunk 6284544 (CImg 2816) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
