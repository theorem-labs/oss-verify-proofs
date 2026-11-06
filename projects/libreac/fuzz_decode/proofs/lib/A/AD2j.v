(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libreac/fuzz_decode by gen_ad2.py 99d2b85d0615 (tools/startup at 7bbb2fc2bf14) from fuzz_decode.asan, its atable (A/AB12.v), its TSEGS window (A/AB1h.v), its owned statics (A/AF0m.v) and the 50 hand-off states of A/AB01.v; the donor A/AD2i.v and A/AD2j.v at origin/ossv/recipes c8557374ad2e give the text only *)
(* Read from: fuzz_decode.asan (libreac/fuzz_decode asan) sha256 5973b76807d8d2e14b82dc6afde70a2c882923658406aeca43681719cb4e8036; unstripped twin sha256 4cb0a852e8262acb5ed0fa075a6bee7b1a25192189b168e777c760a4bfd65ae2 *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YP0m YP09.
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
Definition R_A1e : region :=
mkRegion None 66368 66472 0 0
[ mkChunk 66368 (CImg 104) ].
Definition R_A1f : region :=
mkRegion None 66488 66504 0 0
[ mkChunk 66488 (CImg 16) ].
Definition R_A1g : region :=
mkRegion None 66512 66616 0 0
[ mkChunk 66512 (CImg 104) ].
Definition R_A1h : region :=
mkRegion None 66680 66872 0 0
[ mkChunk 66680 (CImg 192) ].
Definition R_A1i : region :=
mkRegion None 66936 117936 0 0
[ mkChunk 66936 (CImg 51000) ].
Definition R_A1j : region :=
mkRegion None 117957 133844 0 0
[ mkChunk 117957 (CImg 15887) ].
Definition R_A1k : region :=
mkRegion None 133848 134476 0 0
[ mkChunk 133848 (CImg 628) ].
Definition R_A1l : region :=
mkRegion None 134496 134508 0 0
[ mkChunk 134496 (CImg 12) ].
Definition R_A1m : region :=
mkRegion None 134528 134540 0 0
[ mkChunk 134528 (CImg 12) ].
Definition R_A1n : region :=
mkRegion None 134560 135972 0 0
[ mkChunk 134560 (CImg 1412) ].
Definition R_A1o : region :=
mkRegion None 135976 136072 0 0
[ mkChunk 135976 (CImg 96) ].
Definition R_A1p : region :=
mkRegion None 136074 622592 0 0
[ mkChunk 136074 (CImg 486518) ].
Definition R_A2a : region :=
mkRegion None 622592 625952 0 0
[ mkChunk 622592 (CImg 3360) ].
Definition R_A2b : region :=
mkRegion None 626080 628904 0 0
[ mkChunk 626080 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 628912 629144 0 0
[ mkChunk 628912 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 629152 629176 0 0
[ mkChunk 629152 (CImg 24) ].
Definition R_A2f : region :=
mkRegion None 629216 629304 0 0
[ mkChunk 629216 (CImg 8);
mkChunk 629224 (CImg 80) ].
Definition R_A2g : region :=
mkRegion None 629328 633424 0 0
[ mkChunk 629328 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 643784 644624 643784 644624
[ mkChunk 643784 (CImg 840) ].
Definition R_A4 : region :=
mkRegion None 644872 644944 644872 644944
[ mkChunk 644872 (CVal 1 (SLit 1));
mkChunk 644873 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6042640 6108176 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6108176 6110388 6108176 6110388
[ mkChunk 6108176 (CImg 4);
mkChunk 6108180 (CVal 1 (SLit 0));
mkChunk 6108181 (CImg 43);
mkChunk 6108224 (CVal 1 (SLit 1));
mkChunk 6108225 (CVal 1 (SLit 1));
mkChunk 6108226 (CVal 1 (SLit 1));
mkChunk 6108227 (CImg 2117);
mkChunk 6110352 (CVal 8 (SLit 6110352));
mkChunk 6110360 (CVal 8 (SLit 6110352));
mkChunk 6110368 (CVal 8 (SLit 6110352));
mkChunk 6110376 (CVal 8 (SLit 0));
mkChunk 6110384 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6110392 6110464 6110392 6110464
[ mkChunk 6110392 (CVal 4 (SLit 2));
mkChunk 6110396 (CImg 6);
mkChunk 6110402 (CVal 1 (SLit 1));
mkChunk 6110403 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6110472 6110544 0 0
[ mkChunk 6110472 (CVal 8 (SLit 6110472));
mkChunk 6110480 (CImg 24);
mkChunk 6110504 (CVal 8 (SLit 6242336));
mkChunk 6110512 (CImg 24);
mkChunk 6110536 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6110612 6110624 0 0
[ mkChunk 6110612 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6241632 6242328 6241704 6242248
[ mkChunk 6241632 (CImg 16);
mkChunk 6241648 (CVal 8 (SLit 620456));
mkChunk 6241656 (CVal 8 (SLit 0));
mkChunk 6241664 (CVal 8 (SLit 24));
mkChunk 6241672 (CVal 8 (SLit 8));
mkChunk 6241680 (CVal 8 (SLit 0));
mkChunk 6241688 (CVal 8 (SOff 41 0));
mkChunk 6241696 (CImg 16);
mkChunk 6241712 (CVal 4 (SLit 1));
mkChunk 6241716 (CImg 4);
mkChunk 6241720 (CVal 8 (SLit 6241728));
mkChunk 6241728 (CImg 8);
mkChunk 6241736 (CVal 8 (SLit 559108));
mkChunk 6241744 (CImg 248);
mkChunk 6241992 (CVal 8 (SLit 456228));
mkChunk 6242000 (CImg 264);
mkChunk 6242272 (CVal 8 (SOff 1 0));
mkChunk 6242280 (CVal 1 (SLit 1));
mkChunk 6242281 (CImg 7);
mkChunk 6242288 (CVal 8 (SOff 5 0));
mkChunk 6242296 (CVal 8 (SLit 6241640));
mkChunk 6242304 (CVal 8 (SLit 248));
mkChunk 6242312 (CVal 8 (SLit 8));
mkChunk 6242320 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6242336 6242408 0 0
[ mkChunk 6242336 (CImg 48);
mkChunk 6242392 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6243336 6245552 0 0
[ mkChunk 6243336 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6245560 6246656 0 0
[ mkChunk 6245560 (CImg 8);
mkChunk 6245568 (CVal 8 (SLit 344616));
mkChunk 6245576 (CImg 1016);
mkChunk 6246592 (CVal 4 (SLit 0));
mkChunk 6246596 (CImg 4);
mkChunk 6246600 (CVal 4 (SLit 0));
mkChunk 6246604 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6246664 6250496 0 0
[ mkChunk 6246664 (CImg 3832) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A2a; R_A2b; R_A2c; R_A2d; R_A2f; R_A2g; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
