(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2j.v, with its module paths changed; its regions are fuzz_grant.asan's, re-derived from its sections, symbols and constant cells, and R_A1j, R_A1k, R_A1l and R_A2a leave out the guard bytes of the globals fuzz_grant.asan registers. *)
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
mkRegion None 66912 118216 0 0
[ mkChunk 66912 (CImg 51304) ].
Definition R_A1i : region :=
mkRegion None 118237 134140 0 0
[ mkChunk 118237 (CImg 15903) ].
Definition R_A1j : region :=
mkRegion None 134144 135090 0 0
[ mkChunk 134144 (CImg 658);
mkChunk 134848 (CImg 34);
mkChunk 134944 (CImg 34);
mkChunk 135040 (CImg 50) ].
Definition R_A1k : region :=
mkRegion None 135136 135746 0 0
[ mkChunk 135136 (CImg 71);
mkChunk 135232 (CImg 204);
mkChunk 135488 (CImg 32);
mkChunk 135552 (CImg 32);
mkChunk 135616 (CImg 34);
mkChunk 135712 (CImg 34) ].
Definition R_A1l : region :=
mkRegion None 135808 135968 0 0
[ mkChunk 135808 (CImg 96);
mkChunk 135936 (CImg 32) ].
Definition R_A1m : region :=
mkRegion None 136000 137416 0 0
[ mkChunk 136000 (CImg 1416) ].
Definition R_A1n : region :=
mkRegion None 137420 137516 0 0
[ mkChunk 137420 (CImg 96) ].
Definition R_A1o : region :=
mkRegion None 137518 638976 0 0
[ mkChunk 137518 (CImg 501458) ].
Definition R_A2a : region :=
mkRegion None 638976 641104 0 0
[ mkChunk 638976 (CImg 1672);
mkChunk 640736 (CImg 368) ].
Definition R_A2b : region :=
mkRegion None 641232 644056 0 0
[ mkChunk 641232 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 644064 644296 0 0
[ mkChunk 644064 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 644304 644328 0 0
[ mkChunk 644304 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 644344 644432 0 0
[ mkChunk 644344 (CImg 8);
mkChunk 644352 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 644456 648552 0 0
[ mkChunk 644456 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 658912 659744 658912 659744
[ mkChunk 658912 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 660616 660688 660616 660688
[ mkChunk 660616 (CVal 1 (SLit 1));
mkChunk 660617 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6058384 6123920 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6123920 6126124 6123920 6126124
[ mkChunk 6123920 (CImg 4);
mkChunk 6123924 (CVal 1 (SLit 0));
mkChunk 6123925 (CImg 2155);
mkChunk 6126088 (CVal 8 (SLit 6126088));
mkChunk 6126096 (CVal 8 (SLit 6126088));
mkChunk 6126104 (CVal 8 (SLit 6126088));
mkChunk 6126112 (CVal 8 (SLit 0));
mkChunk 6126120 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6126128 6126200 6126128 6126200
[ mkChunk 6126128 (CVal 4 (SLit 2));
mkChunk 6126132 (CImg 6);
mkChunk 6126138 (CVal 1 (SLit 1));
mkChunk 6126139 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6126208 6126280 0 0
[ mkChunk 6126208 (CVal 8 (SLit 6126208));
mkChunk 6126216 (CImg 24);
mkChunk 6126240 (CVal 8 (SLit 6258072));
mkChunk 6126248 (CImg 24);
mkChunk 6126272 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6126348 6126360 0 0
[ mkChunk 6126348 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6257368 6258064 6257440 6257984
[ mkChunk 6257368 (CImg 16);
mkChunk 6257384 (CVal 8 (SLit 635240));
mkChunk 6257392 (CVal 8 (SLit 0));
mkChunk 6257400 (CVal 8 (SLit 24));
mkChunk 6257408 (CVal 8 (SLit 8));
mkChunk 6257416 (CVal 8 (SLit 0));
mkChunk 6257424 (CVal 8 (SOff 41 0));
mkChunk 6257432 (CImg 16);
mkChunk 6257448 (CVal 4 (SLit 1));
mkChunk 6257452 (CImg 4);
mkChunk 6257456 (CVal 8 (SLit 6257464));
mkChunk 6257464 (CImg 8);
mkChunk 6257472 (CVal 8 (SLit 573888));
mkChunk 6257480 (CImg 248);
mkChunk 6257728 (CVal 8 (SLit 457840));
mkChunk 6257736 (CImg 264);
mkChunk 6258008 (CVal 8 (SOff 1 0));
mkChunk 6258016 (CVal 1 (SLit 1));
mkChunk 6258017 (CImg 7);
mkChunk 6258024 (CVal 8 (SOff 5 0));
mkChunk 6258032 (CVal 8 (SLit 6257376));
mkChunk 6258040 (CVal 8 (SLit 248));
mkChunk 6258048 (CVal 8 (SLit 8));
mkChunk 6258056 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6258072 6258144 0 0
[ mkChunk 6258072 (CImg 48);
mkChunk 6258128 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6259072 6261288 0 0
[ mkChunk 6259072 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6261296 6262392 0 0
[ mkChunk 6261296 (CImg 8);
mkChunk 6261304 (CVal 8 (SLit 347096));
mkChunk 6261312 (CImg 1016);
mkChunk 6262328 (CVal 4 (SLit 0));
mkChunk 6262332 (CImg 4);
mkChunk 6262336 (CVal 4 (SLit 0));
mkChunk 6262340 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6262400 6266880 0 0
[ mkChunk 6262400 (CImg 4480) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
