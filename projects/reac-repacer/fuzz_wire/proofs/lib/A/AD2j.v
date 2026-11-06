(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-repacer/fuzz_wire by gen_ad2.py (frozen 979c52cd71c6) from fuzz_wire.asan, its atable (A/AB12.v), its TSEGS window (A/AB1h.v), its owned statics (A/AF0m.v) and the 50 hand-off states of A/AB01.v; fuzz_wire.asan registers 0 asan_globals descriptors, so the .data-frame region R_A3 ends at the .data end; the donor A/AD2i.v and A/AD2j.v at origin/ossv/recipes c8557374ad2e give the text only *)
(* Read from: fuzz_wire.asan (reac-repacer/fuzz_wire asan) sha256 2f8f8697cd4f99bd15999cce4963a6fcc39b308444bd58e2bf526ec7c1ad5fa1; unstripped twin sha256 d2f662a229626fd402f1018631498190e800834bad837fa4027204b79088b128 *)
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
mkRegion None 622592 624584 0 0
[ mkChunk 622592 (CImg 1992) ].
Definition R_A2b : region :=
mkRegion None 624712 627536 0 0
[ mkChunk 624712 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 627544 627776 0 0
[ mkChunk 627544 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 627784 627808 0 0
[ mkChunk 627784 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 627824 627912 0 0
[ mkChunk 627824 (CImg 8);
mkChunk 627832 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 627936 632032 0 0
[ mkChunk 627936 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 642392 643224 642392 643224
[ mkChunk 642392 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 643272 643344 643272 643344
[ mkChunk 643272 (CVal 1 (SLit 1));
mkChunk 643273 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6041040 6106576 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6106576 6108780 6106576 6108780
[ mkChunk 6106576 (CImg 4);
mkChunk 6106580 (CVal 1 (SLit 0));
mkChunk 6106581 (CImg 2155);
mkChunk 6108744 (CVal 8 (SLit 6108744));
mkChunk 6108752 (CVal 8 (SLit 6108744));
mkChunk 6108760 (CVal 8 (SLit 6108744));
mkChunk 6108768 (CVal 8 (SLit 0));
mkChunk 6108776 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6108784 6108856 6108784 6108856
[ mkChunk 6108784 (CVal 4 (SLit 2));
mkChunk 6108788 (CImg 6);
mkChunk 6108794 (CVal 1 (SLit 1));
mkChunk 6108795 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6108864 6108936 0 0
[ mkChunk 6108864 (CVal 8 (SLit 6108864));
mkChunk 6108872 (CImg 24);
mkChunk 6108896 (CVal 8 (SLit 6240728));
mkChunk 6108904 (CImg 24);
mkChunk 6108928 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6109004 6109016 0 0
[ mkChunk 6109004 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6240024 6240720 6240096 6240640
[ mkChunk 6240024 (CImg 16);
mkChunk 6240040 (CVal 8 (SLit 619088));
mkChunk 6240048 (CVal 8 (SLit 0));
mkChunk 6240056 (CVal 8 (SLit 24));
mkChunk 6240064 (CVal 8 (SLit 8));
mkChunk 6240072 (CVal 8 (SLit 0));
mkChunk 6240080 (CVal 8 (SOff 41 0));
mkChunk 6240088 (CImg 16);
mkChunk 6240104 (CVal 4 (SLit 1));
mkChunk 6240108 (CImg 4);
mkChunk 6240112 (CVal 8 (SLit 6240120));
mkChunk 6240120 (CImg 8);
mkChunk 6240128 (CVal 8 (SLit 557736));
mkChunk 6240136 (CImg 248);
mkChunk 6240384 (CVal 8 (SLit 455704));
mkChunk 6240392 (CImg 264);
mkChunk 6240664 (CVal 8 (SOff 1 0));
mkChunk 6240672 (CVal 1 (SLit 1));
mkChunk 6240673 (CImg 7);
mkChunk 6240680 (CVal 8 (SOff 5 0));
mkChunk 6240688 (CVal 8 (SLit 6240032));
mkChunk 6240696 (CVal 8 (SLit 248));
mkChunk 6240704 (CVal 8 (SLit 8));
mkChunk 6240712 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6240728 6240800 0 0
[ mkChunk 6240728 (CImg 48);
mkChunk 6240784 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6241728 6243944 0 0
[ mkChunk 6241728 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6243952 6245048 0 0
[ mkChunk 6243952 (CImg 8);
mkChunk 6243960 (CVal 8 (SLit 344960));
mkChunk 6243968 (CImg 1016);
mkChunk 6244984 (CVal 4 (SLit 0));
mkChunk 6244988 (CImg 4);
mkChunk 6244992 (CVal 4 (SLit 0));
mkChunk 6244996 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6245056 6246400 0 0
[ mkChunk 6245056 (CImg 1344) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1o; R_A1p; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
