(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YD2j.v, with its module paths changed; its regions are fuzz_grant.asan-ubsan's, re-derived from that image's sections, symbols and constant cells (lib/B/regen/gen_regions.py), and R_A1j, R_A1k, R_A1l and R_A2a leave out the guard bytes of the 13 globals fuzz_grant.asan-ubsan registers. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP09.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 66280 0 0
[ mkChunk 65536 (CImg 744) ].
Definition R_A1b : region :=
mkRegion None 66288 66312 0 0
[ mkChunk 66288 (CImg 24) ].
Definition R_A1c : region :=
mkRegion None 66320 66352 0 0
[ mkChunk 66320 (CImg 32) ].
Definition R_A1d : region :=
mkRegion None 66360 66464 0 0
[ mkChunk 66360 (CImg 8);
mkChunk 66376 (CImg 88) ].
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
mkRegion None 66920 118015 0 0
[ mkChunk 66920 (CImg 51095) ].
Definition R_A1i : region :=
mkRegion None 118036 134208 0 0
[ mkChunk 118036 (CImg 16172) ].
Definition R_A1j : region :=
mkRegion None 134212 135154 0 0
[ mkChunk 134212 (CImg 654);
mkChunk 134912 (CImg 34);
mkChunk 135008 (CImg 34);
mkChunk 135104 (CImg 50) ].
Definition R_A1k : region :=
mkRegion None 135200 135810 0 0
[ mkChunk 135200 (CImg 71);
mkChunk 135296 (CImg 204);
mkChunk 135552 (CImg 32);
mkChunk 135616 (CImg 32);
mkChunk 135680 (CImg 34);
mkChunk 135776 (CImg 34) ].
Definition R_A1l : region :=
mkRegion None 135872 136032 0 0
[ mkChunk 135872 (CImg 96);
mkChunk 136000 (CImg 32) ].
Definition R_A1m : region :=
mkRegion None 136064 137480 0 0
[ mkChunk 136064 (CImg 1416) ].
Definition R_A1n : region :=
mkRegion None 137484 137580 0 0
[ mkChunk 137484 (CImg 96) ].
Definition R_A1o : region :=
mkRegion None 137582 638976 0 0
[ mkChunk 137582 (CImg 501394) ].
Definition R_A2a : region :=
mkRegion None 638976 644784 0 0
[ mkChunk 638976 (CImg 5352);
mkChunk 644416 (CImg 368) ].
Definition R_A2b : region :=
mkRegion None 644912 647736 0 0
[ mkChunk 644912 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 647744 647976 0 0
[ mkChunk 647744 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 647984 648008 0 0
[ mkChunk 647984 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 648024 648112 0 0
[ mkChunk 648024 (CImg 8);
mkChunk 648032 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 648136 652232 0 0
[ mkChunk 648136 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 662592 663424 662592 663424
[ mkChunk 662592 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 664264 664336 664264 664336
[ mkChunk 664264 (CVal 1 (SLit 1));
mkChunk 664265 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6062032 6127568 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6127568 6129772 6127568 6129772
[ mkChunk 6127568 (CImg 4);
mkChunk 6127572 (CVal 1 (SLit 0));
mkChunk 6127573 (CImg 2155);
mkChunk 6129736 (CVal 8 (SLit 6129736));
mkChunk 6129744 (CVal 8 (SLit 6129736));
mkChunk 6129752 (CVal 8 (SLit 6129736));
mkChunk 6129760 (CVal 8 (SLit 0));
mkChunk 6129768 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6129776 6129848 6129776 6129848
[ mkChunk 6129776 (CVal 4 (SLit 2));
mkChunk 6129780 (CImg 6);
mkChunk 6129786 (CVal 1 (SLit 1));
mkChunk 6129787 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6129856 6129928 0 0
[ mkChunk 6129856 (CVal 8 (SLit 6129856));
mkChunk 6129864 (CImg 24);
mkChunk 6129888 (CVal 8 (SLit 6261720));
mkChunk 6129896 (CImg 24);
mkChunk 6129920 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6129996 6130008 0 0
[ mkChunk 6129996 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6261016 6261712 6261088 6261632
[ mkChunk 6261016 (CImg 16);
mkChunk 6261032 (CVal 8 (SLit 638920));
mkChunk 6261040 (CVal 8 (SLit 0));
mkChunk 6261048 (CVal 8 (SLit 24));
mkChunk 6261056 (CVal 8 (SLit 8));
mkChunk 6261064 (CVal 8 (SLit 0));
mkChunk 6261072 (CVal 8 (SOff 41 0));
mkChunk 6261080 (CImg 16);
mkChunk 6261096 (CVal 4 (SLit 1));
mkChunk 6261100 (CImg 4);
mkChunk 6261104 (CVal 8 (SLit 6261112));
mkChunk 6261112 (CImg 8);
mkChunk 6261120 (CVal 8 (SLit 577572));
mkChunk 6261128 (CImg 248);
mkChunk 6261376 (CVal 8 (SLit 458748));
mkChunk 6261384 (CImg 264);
mkChunk 6261656 (CVal 8 (SOff 1 0));
mkChunk 6261664 (CVal 1 (SLit 1));
mkChunk 6261665 (CImg 7);
mkChunk 6261672 (CVal 8 (SOff 5 0));
mkChunk 6261680 (CVal 8 (SLit 6261024));
mkChunk 6261688 (CVal 8 (SLit 248));
mkChunk 6261696 (CVal 8 (SLit 8));
mkChunk 6261704 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6261720 6261792 0 0
[ mkChunk 6261720 (CImg 48);
mkChunk 6261776 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6262720 6264936 0 0
[ mkChunk 6262720 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6264944 6266040 0 0
[ mkChunk 6264944 (CImg 8);
mkChunk 6264952 (CVal 8 (SLit 348004));
mkChunk 6264960 (CImg 1016);
mkChunk 6265976 (CVal 4 (SLit 0));
mkChunk 6265980 (CImg 4);
mkChunk 6265984 (CVal 4 (SLit 0));
mkChunk 6265988 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6266048 6270976 0 0
[ mkChunk 6266048 (CImg 4928) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
