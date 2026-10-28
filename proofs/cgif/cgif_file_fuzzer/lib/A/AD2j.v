(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP09.
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
mkRegion None 66920 118025 0 0
[ mkChunk 66920 (CImg 51105) ].
Definition R_A1i : region :=
mkRegion None 118046 134012 0 0
[ mkChunk 118046 (CImg 15966) ].
Definition R_A1j : region :=
mkRegion None 134016 134669 0 0
[ mkChunk 134016 (CImg 653) ].
Definition R_A1k : region :=
mkRegion None 134688 134755 0 0
[ mkChunk 134688 (CImg 67) ].
Definition R_A1l : region :=
mkRegion None 134784 134818 0 0
[ mkChunk 134784 (CImg 34) ].
Definition R_A1m : region :=
mkRegion None 134848 136264 0 0
[ mkChunk 134848 (CImg 1416) ].
Definition R_A1n : region :=
mkRegion None 136268 136364 0 0
[ mkChunk 136268 (CImg 96) ].
Definition R_A1o : region :=
mkRegion None 136366 643072 0 0
[ mkChunk 136366 (CImg 506706) ].
Definition R_A2a : region :=
mkRegion None 643072 647032 0 0
[ mkChunk 643072 (CImg 3960) ].
Definition R_A2b : region :=
mkRegion None 647160 649984 0 0
[ mkChunk 647160 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 649992 650224 0 0
[ mkChunk 649992 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 650232 650280 0 0
[ mkChunk 650232 (CImg 48) ].
Definition R_A2e : region :=
mkRegion None 650296 650384 0 0
[ mkChunk 650296 (CImg 8);
mkChunk 650304 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 650408 654504 0 0
[ mkChunk 650408 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 664880 665712 664880 665712
[ mkChunk 664880 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 665928 666000 665928 666000
[ mkChunk 665928 (CVal 1 (SLit 1));
mkChunk 665929 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6063696 6129232 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6129232 6131436 6129232 6131436
[ mkChunk 6129232 (CImg 4);
mkChunk 6129236 (CVal 1 (SLit 0));
mkChunk 6129237 (CImg 2155);
mkChunk 6131400 (CVal 8 (SLit 6131400));
mkChunk 6131408 (CVal 8 (SLit 6131400));
mkChunk 6131416 (CVal 8 (SLit 6131400));
mkChunk 6131424 (CVal 8 (SLit 0));
mkChunk 6131432 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6131440 6131512 6131440 6131512
[ mkChunk 6131440 (CVal 4 (SLit 2));
mkChunk 6131444 (CImg 6);
mkChunk 6131450 (CVal 1 (SLit 1));
mkChunk 6131451 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6131520 6131592 0 0
[ mkChunk 6131520 (CVal 8 (SLit 6131520));
mkChunk 6131528 (CImg 24);
mkChunk 6131552 (CVal 8 (SLit 6263384));
mkChunk 6131560 (CImg 24);
mkChunk 6131584 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6131660 6131672 0 0
[ mkChunk 6131660 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6262680 6263376 6262752 6263296
[ mkChunk 6262680 (CImg 16);
mkChunk 6262696 (CVal 8 (SLit 641536));
mkChunk 6262704 (CVal 8 (SLit 0));
mkChunk 6262712 (CVal 8 (SLit 24));
mkChunk 6262720 (CVal 8 (SLit 8));
mkChunk 6262728 (CVal 8 (SLit 0));
mkChunk 6262736 (CVal 8 (SOff 41 0));
mkChunk 6262744 (CImg 16);
mkChunk 6262760 (CVal 4 (SLit 1));
mkChunk 6262764 (CImg 4);
mkChunk 6262768 (CVal 8 (SLit 6262776));
mkChunk 6262776 (CImg 8);
mkChunk 6262784 (CVal 8 (SLit 578992));
mkChunk 6262792 (CImg 248);
mkChunk 6263040 (CVal 8 (SLit 457296));
mkChunk 6263048 (CImg 264);
mkChunk 6263320 (CVal 8 (SOff 1 0));
mkChunk 6263328 (CVal 1 (SLit 1));
mkChunk 6263329 (CImg 7);
mkChunk 6263336 (CVal 8 (SOff 5 0));
mkChunk 6263344 (CVal 8 (SLit 6262688));
mkChunk 6263352 (CVal 8 (SLit 248));
mkChunk 6263360 (CVal 8 (SLit 8));
mkChunk 6263368 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6263384 6263456 0 0
[ mkChunk 6263384 (CImg 48);
mkChunk 6263440 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6264384 6266600 0 0
[ mkChunk 6264384 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6266608 6267704 0 0
[ mkChunk 6266608 (CImg 8);
mkChunk 6266616 (CVal 8 (SLit 346552));
mkChunk 6266624 (CImg 1016);
mkChunk 6267640 (CVal 4 (SLit 0));
mkChunk 6267644 (CImg 4);
mkChunk 6267648 (CVal 4 (SLit 0));
mkChunk 6267652 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6267712 6270976 0 0
[ mkChunk 6267712 (CImg 3264) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
