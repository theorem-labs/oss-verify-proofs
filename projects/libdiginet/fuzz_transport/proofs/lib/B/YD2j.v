(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_transport image B by gen_ad2.py (frozen 3665ff2a7926, start-up tool set of commit f1417943331) from fuzz_transport.asan-ubsan, its atable (lib/B/YB12.v), its TSEGS window (lib/B/YB1h.v), its owned statics (lib/B/YF0m.v) and the 50 hand-off states of lib/B/YB01.v; the donor lib/YD2i.v and lib/YD2j.v at commit 25e3d17bdb50 give the text only *)
(* Read from: fuzz_transport.asan-ubsan (libdiginet/fuzz_transport asan-ubsan) sha256 41113a03c82fde8282db830ab5f4fbe376e392a38d22670b8cb8c9f02969ece4; unstripped twin sha256 e217cb0a84f1e1810805155304b281a259ef83a85f50efcf0c65b40697bfa4dc *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66360 66376 0 0
[ mkChunk 66360 (CImg 16) ].
Definition R_A1e : region :=
mkRegion None 66384 66488 0 0
[ mkChunk 66384 (CImg 104) ].
Definition R_A1f : region :=
mkRegion None 66504 66512 0 0
[ mkChunk 66504 (CImg 8) ].
Definition R_A1g : region :=
mkRegion None 66520 66624 0 0
[ mkChunk 66520 (CImg 104) ].
Definition R_A1h : region :=
mkRegion None 66688 66880 0 0
[ mkChunk 66688 (CImg 192) ].
Definition R_A1i : region :=
mkRegion None 66944 118344 0 0
[ mkChunk 66944 (CImg 51400) ].
Definition R_A1j : region :=
mkRegion None 118365 134384 0 0
[ mkChunk 118365 (CImg 16019) ].
Definition R_A1k : region :=
mkRegion None 134388 135104 0 0
[ mkChunk 134388 (CImg 716) ].
Definition R_A1l : region :=
mkRegion None 135136 135142 0 0
[ mkChunk 135136 (CImg 6) ].
Definition R_A1m : region :=
mkRegion None 135168 135174 0 0
[ mkChunk 135168 (CImg 6) ].
Definition R_A1n : region :=
mkRegion None 135200 135206 0 0
[ mkChunk 135200 (CImg 6) ].
Definition R_A1o : region :=
mkRegion None 135232 135235 0 0
[ mkChunk 135232 (CImg 3) ].
Definition R_A1p : region :=
mkRegion None 135264 135273 0 0
[ mkChunk 135264 (CImg 9) ].
Definition R_A1q : region :=
mkRegion None 135296 135305 0 0
[ mkChunk 135296 (CImg 9) ].
Definition R_A1r : region :=
mkRegion None 135328 135335 0 0
[ mkChunk 135328 (CImg 7) ].
Definition R_A1s : region :=
mkRegion None 135360 135366 0 0
[ mkChunk 135360 (CImg 6) ].
Definition R_A1t : region :=
mkRegion None 135392 135398 0 0
[ mkChunk 135392 (CImg 6) ].
Definition R_A1u : region :=
mkRegion None 135424 135430 0 0
[ mkChunk 135424 (CImg 6) ].
Definition R_A1v : region :=
mkRegion None 135456 135462 0 0
[ mkChunk 135456 (CImg 6) ].
Definition R_A1w : region :=
mkRegion None 135488 135526 0 0
[ mkChunk 135488 (CImg 38) ].
Definition R_A1x : region :=
mkRegion None 135552 135593 0 0
[ mkChunk 135552 (CImg 41) ].
Definition R_A1y : region :=
mkRegion None 135616 135625 0 0
[ mkChunk 135616 (CImg 9) ].
Definition R_A1z : region :=
mkRegion None 135648 137060 0 0
[ mkChunk 135648 (CImg 1412) ].
Definition R_A1aa : region :=
mkRegion None 137064 137160 0 0
[ mkChunk 137064 (CImg 96) ].
Definition R_A1ab : region :=
mkRegion None 137162 667648 0 0
[ mkChunk 137162 (CImg 530486) ].
Definition R_A2a : region :=
mkRegion None 667648 670176 0 0
[ mkChunk 667648 (CImg 2528) ].
Definition R_A2b : region :=
mkRegion None 670208 670224 0 0
[ mkChunk 670208 (CImg 16) ].
Definition R_A2c : region :=
mkRegion None 670240 670256 0 0
[ mkChunk 670240 (CImg 16) ].
Definition R_A2d : region :=
mkRegion None 670272 670304 0 0
[ mkChunk 670272 (CImg 32) ].
Definition R_A2e : region :=
mkRegion None 670336 670368 0 0
[ mkChunk 670336 (CImg 32) ].
Definition R_A2f : region :=
mkRegion None 670400 670424 0 0
[ mkChunk 670400 (CImg 24) ].
Definition R_A2g : region :=
mkRegion None 670464 670512 0 0
[ mkChunk 670464 (CImg 48) ].
Definition R_A2h : region :=
mkRegion None 670560 670928 0 0
[ mkChunk 670560 (CImg 368) ].
Definition R_A2i : region :=
mkRegion None 671056 673880 0 0
[ mkChunk 671056 (CImg 2824) ].
Definition R_A2j : region :=
mkRegion None 673888 674120 0 0
[ mkChunk 673888 (CImg 232) ].
Definition R_A2k : region :=
mkRegion None 674128 674152 0 0
[ mkChunk 674128 (CImg 24) ].
Definition R_A2l : region :=
mkRegion None 674168 674256 0 0
[ mkChunk 674168 (CImg 8);
mkChunk 674176 (CImg 80) ].
Definition R_A2m : region :=
mkRegion None 674280 678376 0 0
[ mkChunk 674280 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 688736 689568 688736 689568
[ mkChunk 688736 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 692168 692240 692168 692240
[ mkChunk 692168 (CVal 1 (SLit 1));
mkChunk 692169 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6089936 6155472 0 0
[  ].
Definition R_A5a_1 : region :=
mkRegion None 6155472 6155520 6155472 6155520
[ mkChunk 6155472 (CImg 4);
mkChunk 6155476 (CVal 1 (SLit 0));
mkChunk 6155477 (CImg 43) ].
Definition R_A5a_2 : region :=
mkRegion None 6237792 6239948 6237792 6239948
[ mkChunk 6237792 (CImg 2112);
mkChunk 6239912 (CVal 8 (SLit 6239912));
mkChunk 6239920 (CVal 8 (SLit 6239912));
mkChunk 6239928 (CVal 8 (SLit 6239912));
mkChunk 6239936 (CVal 8 (SLit 0));
mkChunk 6239944 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6239952 6240024 6239952 6240024
[ mkChunk 6239952 (CVal 4 (SLit 2));
mkChunk 6239956 (CImg 6);
mkChunk 6239962 (CVal 1 (SLit 1));
mkChunk 6239963 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6240032 6240104 0 0
[ mkChunk 6240032 (CVal 8 (SLit 6240032));
mkChunk 6240040 (CImg 24);
mkChunk 6240064 (CVal 8 (SLit 6371896));
mkChunk 6240072 (CImg 24);
mkChunk 6240096 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6240172 6240184 0 0
[ mkChunk 6240172 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6371192 6371888 6371264 6371808
[ mkChunk 6371192 (CImg 16);
mkChunk 6371208 (CVal 8 (SLit 665000));
mkChunk 6371216 (CVal 8 (SLit 0));
mkChunk 6371224 (CVal 8 (SLit 24));
mkChunk 6371232 (CVal 8 (SLit 8));
mkChunk 6371240 (CVal 8 (SLit 0));
mkChunk 6371248 (CVal 8 (SOff 41 0));
mkChunk 6371256 (CImg 16);
mkChunk 6371272 (CVal 4 (SLit 1));
mkChunk 6371276 (CImg 4);
mkChunk 6371280 (CVal 8 (SLit 6371288));
mkChunk 6371288 (CImg 8);
mkChunk 6371296 (CVal 8 (SLit 603648));
mkChunk 6371304 (CImg 248);
mkChunk 6371552 (CVal 8 (SLit 460896));
mkChunk 6371560 (CImg 264);
mkChunk 6371832 (CVal 8 (SOff 1 0));
mkChunk 6371840 (CVal 1 (SLit 1));
mkChunk 6371841 (CImg 7);
mkChunk 6371848 (CVal 8 (SOff 5 0));
mkChunk 6371856 (CVal 8 (SLit 6371200));
mkChunk 6371864 (CVal 8 (SLit 248));
mkChunk 6371872 (CVal 8 (SLit 8));
mkChunk 6371880 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6371896 6371968 0 0
[ mkChunk 6371896 (CImg 48);
mkChunk 6371952 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6372896 6375112 0 0
[ mkChunk 6372896 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6375120 6376216 0 0
[ mkChunk 6375120 (CImg 8);
mkChunk 6375128 (CVal 8 (SLit 350152));
mkChunk 6375136 (CImg 1016);
mkChunk 6376152 (CVal 4 (SLit 0));
mkChunk 6376156 (CImg 4);
mkChunk 6376160 (CVal 4 (SLit 0));
mkChunk 6376164 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6376224 6381568 0 0
[ mkChunk 6376224 (CImg 5344) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A2h; R_A2i; R_A2j; R_A2k; R_A2l; R_A2m; R_A3; R_A4; R_RS; R_A5a_1; R_A5a_2; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
