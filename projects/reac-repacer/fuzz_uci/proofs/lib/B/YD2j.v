(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: generated for reac-repacer/fuzz_uci image B by gen_ad2.py (frozen 979c52cd71c6, start-up tool set of commit dbb5a97ad14) from fuzz_uci.asan-ubsan, its atable (lib/B/YB12.v), its TSEGS window (lib/B/YB1h.v), its owned statics (lib/B/YF0m.v) and the 50 hand-off states of lib/B/YB01.v; the donor lib/YD2i.v and lib/YD2j.v at commit 25e3d17bdb50 give the text only *)
(* Read from: fuzz_uci.asan-ubsan (reac-repacer/fuzz_uci asan-ubsan) sha256 a1b86e424adde6f65d345459822690a6c21e9e606446b91b4ad25e9f3ef6e7fc; unstripped twin sha256 8d07ffcf594874884207465cc34ff9f3b1062f21f6d9b3622e0771fa76490b16 *)
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_repacer.fuzz_uci.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66912 117773 0 0
[ mkChunk 66912 (CImg 50861) ].
Definition R_A1i : region :=
mkRegion None 117794 133660 0 0
[ mkChunk 117794 (CImg 15866) ].
Definition R_A1j : region :=
mkRegion None 133664 134312 0 0
[ mkChunk 133664 (CImg 648) ].
Definition R_A1k : region :=
mkRegion None 134336 135744 0 0
[ mkChunk 134336 (CImg 1408) ].
Definition R_A1n : region :=
mkRegion None 135748 135844 0 0
[ mkChunk 135748 (CImg 96) ].
Definition R_A1o : region :=
mkRegion None 135846 614400 0 0
[ mkChunk 135846 (CImg 478554) ].
Definition R_A2a : region :=
mkRegion None 614400 618760 0 0
[ mkChunk 614400 (CImg 4360) ].
Definition R_A2b : region :=
mkRegion None 618888 621712 0 0
[ mkChunk 618888 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 621720 621952 0 0
[ mkChunk 621720 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 621960 621984 0 0
[ mkChunk 621960 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 622000 622088 0 0
[ mkChunk 622000 (CImg 8);
mkChunk 622008 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 622112 626208 0 0
[ mkChunk 622112 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 636560 637392 636560 637392
[ mkChunk 636560 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 637512 637584 637512 637584
[ mkChunk 637512 (CVal 1 (SLit 1));
mkChunk 637513 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6035280 6100816 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6100816 6103020 6100816 6103020
[ mkChunk 6100816 (CImg 4);
mkChunk 6100820 (CVal 1 (SLit 0));
mkChunk 6100821 (CImg 2155);
mkChunk 6102984 (CVal 8 (SLit 6102984));
mkChunk 6102992 (CVal 8 (SLit 6102984));
mkChunk 6103000 (CVal 8 (SLit 6102984));
mkChunk 6103008 (CVal 8 (SLit 0));
mkChunk 6103016 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6103024 6103096 6103024 6103096
[ mkChunk 6103024 (CVal 4 (SLit 2));
mkChunk 6103028 (CImg 6);
mkChunk 6103034 (CVal 1 (SLit 1));
mkChunk 6103035 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6103104 6103176 0 0
[ mkChunk 6103104 (CVal 8 (SLit 6103104));
mkChunk 6103112 (CImg 24);
mkChunk 6103136 (CVal 8 (SLit 6234968));
mkChunk 6103144 (CImg 24);
mkChunk 6103168 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6103244 6103256 0 0
[ mkChunk 6103244 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6234264 6234960 6234336 6234880
[ mkChunk 6234264 (CImg 16);
mkChunk 6234280 (CVal 8 (SLit 613264));
mkChunk 6234288 (CVal 8 (SLit 0));
mkChunk 6234296 (CVal 8 (SLit 24));
mkChunk 6234304 (CVal 8 (SLit 8));
mkChunk 6234312 (CVal 8 (SLit 0));
mkChunk 6234320 (CVal 8 (SOff 41 0));
mkChunk 6234328 (CImg 16);
mkChunk 6234344 (CVal 4 (SLit 1));
mkChunk 6234348 (CImg 4);
mkChunk 6234352 (CVal 8 (SLit 6234360));
mkChunk 6234360 (CImg 8);
mkChunk 6234368 (CVal 8 (SLit 551920));
mkChunk 6234376 (CImg 248);
mkChunk 6234624 (CVal 8 (SLit 452776));
mkChunk 6234632 (CImg 264);
mkChunk 6234904 (CVal 8 (SOff 1 0));
mkChunk 6234912 (CVal 1 (SLit 1));
mkChunk 6234913 (CImg 7);
mkChunk 6234920 (CVal 8 (SOff 5 0));
mkChunk 6234928 (CVal 8 (SLit 6234272));
mkChunk 6234936 (CVal 8 (SLit 248));
mkChunk 6234944 (CVal 8 (SLit 8));
mkChunk 6234952 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6234968 6235040 0 0
[ mkChunk 6234968 (CImg 48);
mkChunk 6235024 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6235968 6238184 0 0
[ mkChunk 6235968 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6238192 6239288 0 0
[ mkChunk 6238192 (CImg 8);
mkChunk 6238200 (CVal 8 (SLit 342032));
mkChunk 6238208 (CImg 1016);
mkChunk 6239224 (CVal 4 (SLit 0));
mkChunk 6239228 (CImg 4);
mkChunk 6239232 (CVal 4 (SLit 0));
mkChunk 6239236 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6239296 6242304 0 0
[ mkChunk 6239296 (CImg 3008) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1n; R_A1o; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
