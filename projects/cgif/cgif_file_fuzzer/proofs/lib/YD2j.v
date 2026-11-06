(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP09.
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
mkRegion None 66472 66488 0 0
[ mkChunk 66472 (CImg 16) ].
Definition R_A1f : region :=
mkRegion None 66496 66600 0 0
[ mkChunk 66496 (CImg 104) ].
Definition R_A1g : region :=
mkRegion None 66664 66856 0 0
[ mkChunk 66664 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66920 117963 0 0
[ mkChunk 66920 (CImg 51043) ].
Definition R_A1i : region :=
mkRegion None 117984 133952 0 0
[ mkChunk 117984 (CImg 15968) ].
Definition R_A1j : region :=
mkRegion None 133956 134605 0 0
[ mkChunk 133956 (CImg 649) ].
Definition R_A1k : region :=
mkRegion None 134624 134691 0 0
[ mkChunk 134624 (CImg 67) ].
Definition R_A1l : region :=
mkRegion None 134720 134754 0 0
[ mkChunk 134720 (CImg 34) ].
Definition R_A1m : region :=
mkRegion None 134784 136200 0 0
[ mkChunk 134784 (CImg 1416) ].
Definition R_A1n : region :=
mkRegion None 136204 136300 0 0
[ mkChunk 136204 (CImg 96) ].
Definition R_A1o : region :=
mkRegion None 136302 643072 0 0
[ mkChunk 136302 (CImg 506770) ].
Definition R_A2a : region :=
mkRegion None 643072 647656 0 0
[ mkChunk 643072 (CImg 4584) ].
Definition R_A2b : region :=
mkRegion None 647784 650608 0 0
[ mkChunk 647784 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 650616 650848 0 0
[ mkChunk 650616 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 650856 650904 0 0
[ mkChunk 650856 (CImg 48) ].
Definition R_A2e : region :=
mkRegion None 650920 651008 0 0
[ mkChunk 650920 (CImg 8);
mkChunk 650928 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 651032 655128 0 0
[ mkChunk 651032 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 665504 666336 665504 666336
[ mkChunk 665504 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 666568 666640 666568 666640
[ mkChunk 666568 (CVal 1 (SLit 1));
mkChunk 666569 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6064336 6129872 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6129872 6132076 6129872 6132076
[ mkChunk 6129872 (CImg 4);
mkChunk 6129876 (CVal 1 (SLit 0));
mkChunk 6129877 (CImg 2155);
mkChunk 6132040 (CVal 8 (SLit 6132040));
mkChunk 6132048 (CVal 8 (SLit 6132040));
mkChunk 6132056 (CVal 8 (SLit 6132040));
mkChunk 6132064 (CVal 8 (SLit 0));
mkChunk 6132072 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6132080 6132152 6132080 6132152
[ mkChunk 6132080 (CVal 4 (SLit 2));
mkChunk 6132084 (CImg 6);
mkChunk 6132090 (CVal 1 (SLit 1));
mkChunk 6132091 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6132160 6132232 0 0
[ mkChunk 6132160 (CVal 8 (SLit 6132160));
mkChunk 6132168 (CImg 24);
mkChunk 6132192 (CVal 8 (SLit 6264024));
mkChunk 6132200 (CImg 24);
mkChunk 6132224 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6132300 6132312 0 0
[ mkChunk 6132300 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6263320 6264016 6263392 6263936
[ mkChunk 6263320 (CImg 16);
mkChunk 6263336 (CVal 8 (SLit 642160));
mkChunk 6263344 (CVal 8 (SLit 0));
mkChunk 6263352 (CVal 8 (SLit 24));
mkChunk 6263360 (CVal 8 (SLit 8));
mkChunk 6263368 (CVal 8 (SLit 0));
mkChunk 6263376 (CVal 8 (SOff 41 0));
mkChunk 6263384 (CImg 16);
mkChunk 6263400 (CVal 4 (SLit 1));
mkChunk 6263404 (CImg 4);
mkChunk 6263408 (CVal 8 (SLit 6263416));
mkChunk 6263416 (CImg 8);
mkChunk 6263424 (CVal 8 (SLit 579620));
mkChunk 6263432 (CImg 248);
mkChunk 6263680 (CVal 8 (SLit 457344));
mkChunk 6263688 (CImg 264);
mkChunk 6263960 (CVal 8 (SOff 1 0));
mkChunk 6263968 (CVal 1 (SLit 1));
mkChunk 6263969 (CImg 7);
mkChunk 6263976 (CVal 8 (SOff 5 0));
mkChunk 6263984 (CVal 8 (SLit 6263328));
mkChunk 6263992 (CVal 8 (SLit 248));
mkChunk 6264000 (CVal 8 (SLit 8));
mkChunk 6264008 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6264024 6264096 0 0
[ mkChunk 6264024 (CImg 48);
mkChunk 6264080 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6265024 6267240 0 0
[ mkChunk 6265024 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6267248 6268344 0 0
[ mkChunk 6267248 (CImg 8);
mkChunk 6267256 (CVal 8 (SLit 346600));
mkChunk 6267264 (CImg 1016);
mkChunk 6268280 (CVal 4 (SLit 0));
mkChunk 6268284 (CImg 4);
mkChunk 6268288 (CVal 4 (SLit 0));
mkChunk 6268292 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6268352 6270976 0 0
[ mkChunk 6268352 (CImg 2624) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
