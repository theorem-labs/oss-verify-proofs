(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-repacer/fuzz_wire image B by gen_ad2.py (sha256 979c52cd71c6, the start-up tool set at commit dbb5a97ad14) from fuzz_wire.asan-ubsan, its atable (lib/B/YB12.v), its TSEGS window (lib/B/YB1h.v), its owned statics (lib/B/YF0m.v) and the 50 hand-off states of lib/B/YB01.v; the image registers 0 ASan globals (no asan_globals section); proofs/cgif/cgif_file_fuzzer/lib/YD2i.v and YD2j.v at commit 25e3d17bdb50 give the text only *)
(* Read from: fuzz_wire.asan-ubsan (reac-repacer/fuzz_wire asan-ubsan) sha256 af4534831a4528320c7dc74ca3f64bb96e8232ed2e313f01126d10879f3417d6; unstripped twin sha256 51eb4bef24252e4df6e11baa89f653d20d74e38ae684f61bc94f4fb339ac97c3 *)
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YP0m YP09.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 66264 0 0
[ mkChunk 65536 (CImg 728) ].
Definition R_A1b : region :=
mkRegion None 66272 66296 0 0
[ mkChunk 66272 (CImg 24) ].
Definition R_A1c : region :=
mkRegion None 66304 66336 0 0
[ mkChunk 66304 (CImg 32) ].
Definition R_A1e : region :=
mkRegion None 66352 66456 0 0
[ mkChunk 66352 (CImg 104) ].
Definition R_A1f : region :=
mkRegion None 66472 66488 0 0
[ mkChunk 66472 (CImg 16) ].
Definition R_A1g : region :=
mkRegion None 66496 66600 0 0
[ mkChunk 66496 (CImg 104) ].
Definition R_A1h : region :=
mkRegion None 66664 66856 0 0
[ mkChunk 66664 (CImg 192) ].
Definition R_A1i : region :=
mkRegion None 66920 117792 0 0
[ mkChunk 66920 (CImg 50872) ].
Definition R_A1j : region :=
mkRegion None 117813 133676 0 0
[ mkChunk 117813 (CImg 15863) ].
Definition R_A1k : region :=
mkRegion None 133680 135684 0 0
[ mkChunk 133680 (CImg 2004) ].
Definition R_A1o : region :=
mkRegion None 135688 135784 0 0
[ mkChunk 135688 (CImg 96) ].
Definition R_A1p : region :=
mkRegion None 135786 622592 0 0
[ mkChunk 135786 (CImg 486806) ].
Definition R_A2a : region :=
mkRegion None 622592 624728 0 0
[ mkChunk 622592 (CImg 2136) ].
Definition R_A2b : region :=
mkRegion None 624856 627680 0 0
[ mkChunk 624856 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 627688 627920 0 0
[ mkChunk 627688 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 627928 627952 0 0
[ mkChunk 627928 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 627968 628056 0 0
[ mkChunk 627968 (CImg 8);
mkChunk 627976 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 628080 632176 0 0
[ mkChunk 628080 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 642536 643368 642536 643368
[ mkChunk 642536 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 643400 643472 643400 643472
[ mkChunk 643400 (CVal 1 (SLit 1));
mkChunk 643401 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6041168 6106704 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6106704 6108908 6106704 6108908
[ mkChunk 6106704 (CImg 4);
mkChunk 6106708 (CVal 1 (SLit 0));
mkChunk 6106709 (CImg 2155);
mkChunk 6108872 (CVal 8 (SLit 6108872));
mkChunk 6108880 (CVal 8 (SLit 6108872));
mkChunk 6108888 (CVal 8 (SLit 6108872));
mkChunk 6108896 (CVal 8 (SLit 0));
mkChunk 6108904 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6108912 6108984 6108912 6108984
[ mkChunk 6108912 (CVal 4 (SLit 2));
mkChunk 6108916 (CImg 6);
mkChunk 6108922 (CVal 1 (SLit 1));
mkChunk 6108923 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6108992 6109064 0 0
[ mkChunk 6108992 (CVal 8 (SLit 6108992));
mkChunk 6109000 (CImg 24);
mkChunk 6109024 (CVal 8 (SLit 6240856));
mkChunk 6109032 (CImg 24);
mkChunk 6109056 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6109132 6109144 0 0
[ mkChunk 6109132 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6240152 6240848 6240224 6240768
[ mkChunk 6240152 (CImg 16);
mkChunk 6240168 (CVal 8 (SLit 619232));
mkChunk 6240176 (CVal 8 (SLit 0));
mkChunk 6240184 (CVal 8 (SLit 24));
mkChunk 6240192 (CVal 8 (SLit 8));
mkChunk 6240200 (CVal 8 (SLit 0));
mkChunk 6240208 (CVal 8 (SOff 41 0));
mkChunk 6240216 (CImg 16);
mkChunk 6240232 (CVal 4 (SLit 1));
mkChunk 6240236 (CImg 4);
mkChunk 6240240 (CVal 8 (SLit 6240248));
mkChunk 6240248 (CImg 8);
mkChunk 6240256 (CVal 8 (SLit 557884));
mkChunk 6240264 (CImg 248);
mkChunk 6240512 (CVal 8 (SLit 455096));
mkChunk 6240520 (CImg 264);
mkChunk 6240792 (CVal 8 (SOff 1 0));
mkChunk 6240800 (CVal 1 (SLit 1));
mkChunk 6240801 (CImg 7);
mkChunk 6240808 (CVal 8 (SOff 5 0));
mkChunk 6240816 (CVal 8 (SLit 6240160));
mkChunk 6240824 (CVal 8 (SLit 248));
mkChunk 6240832 (CVal 8 (SLit 8));
mkChunk 6240840 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6240856 6240928 0 0
[ mkChunk 6240856 (CImg 48);
mkChunk 6240912 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6241856 6244072 0 0
[ mkChunk 6241856 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6244080 6245176 0 0
[ mkChunk 6244080 (CImg 8);
mkChunk 6244088 (CVal 8 (SLit 344352));
mkChunk 6244096 (CImg 1016);
mkChunk 6245112 (CVal 4 (SLit 0));
mkChunk 6245116 (CImg 4);
mkChunk 6245120 (CVal 4 (SLit 0));
mkChunk 6245124 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6245184 6250496 0 0
[ mkChunk 6245184 (CImg 5312) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1o; R_A1p; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
