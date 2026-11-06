(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_transport by gen_ad2.py (start-up set of record, sha256 3665ff2a7926) from fuzz_transport.asan, its atable (A/AB12.v), its TSEGS window (A/AB1h.v), its owned statics (A/AF0m.v) and the 50 hand-off states of A/AB01.v; the donor A/AD2i.v and A/AD2j.v at origin/ossv/recipes 25e3d17bdb50 give the text only; the cut set it was given is Tfib_owned_static of A/AF0m.v with the payload bodies of the image's .bss asan_globals appended (18 harness globals; prep_owned.py --globals-bss, a parse copy: A/AF0m.v itself is unchanged) *)
(* Read from: fuzz_transport.asan (libdiginet/fuzz_transport asan) sha256 e89be137db17b720e0310addc2dcc601998945478a9102e6a9850b0566106350; unstripped twin sha256 86efc3a80314981197619c115e313dbde50e8b86a6c5fefad4e5cc420250c792 *)
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
mkRegion None 66320 66344 0 0
[ mkChunk 66320 (CImg 24) ].
Definition R_A1d : region :=
mkRegion None 66352 66360 0 0
[ mkChunk 66352 (CImg 8) ].
Definition R_A1e : region :=
mkRegion None 66368 66472 0 0
[ mkChunk 66368 (CImg 104) ].
Definition R_A1f : region :=
mkRegion None 66488 66496 0 0
[ mkChunk 66488 (CImg 8) ].
Definition R_A1g : region :=
mkRegion None 66504 66608 0 0
[ mkChunk 66504 (CImg 104) ].
Definition R_A1h : region :=
mkRegion None 66672 66864 0 0
[ mkChunk 66672 (CImg 192) ].
Definition R_A1i : region :=
mkRegion None 66928 118353 0 0
[ mkChunk 66928 (CImg 51425) ].
Definition R_A1j : region :=
mkRegion None 118374 134464 0 0
[ mkChunk 118374 (CImg 16090) ].
Definition R_A1k : region :=
mkRegion None 134468 135200 0 0
[ mkChunk 134468 (CImg 732) ].
Definition R_A1l : region :=
mkRegion None 135232 135238 0 0
[ mkChunk 135232 (CImg 6) ].
Definition R_A1m : region :=
mkRegion None 135264 135270 0 0
[ mkChunk 135264 (CImg 6) ].
Definition R_A1n : region :=
mkRegion None 135296 135302 0 0
[ mkChunk 135296 (CImg 6) ].
Definition R_A1o : region :=
mkRegion None 135328 135331 0 0
[ mkChunk 135328 (CImg 3) ].
Definition R_A1p : region :=
mkRegion None 135360 135369 0 0
[ mkChunk 135360 (CImg 9) ].
Definition R_A1q : region :=
mkRegion None 135392 135401 0 0
[ mkChunk 135392 (CImg 9) ].
Definition R_A1r : region :=
mkRegion None 135424 135431 0 0
[ mkChunk 135424 (CImg 7) ].
Definition R_A1s : region :=
mkRegion None 135456 135462 0 0
[ mkChunk 135456 (CImg 6) ].
Definition R_A1t : region :=
mkRegion None 135488 135494 0 0
[ mkChunk 135488 (CImg 6) ].
Definition R_A1u : region :=
mkRegion None 135520 135526 0 0
[ mkChunk 135520 (CImg 6) ].
Definition R_A1v : region :=
mkRegion None 135552 135558 0 0
[ mkChunk 135552 (CImg 6) ].
Definition R_A1w : region :=
mkRegion None 135584 135622 0 0
[ mkChunk 135584 (CImg 38) ].
Definition R_A1x : region :=
mkRegion None 135648 135689 0 0
[ mkChunk 135648 (CImg 41) ].
Definition R_A1y : region :=
mkRegion None 135712 135721 0 0
[ mkChunk 135712 (CImg 9) ].
Definition R_A1z : region :=
mkRegion None 135744 137156 0 0
[ mkChunk 135744 (CImg 1412) ].
Definition R_A1aa : region :=
mkRegion None 137160 137256 0 0
[ mkChunk 137160 (CImg 96) ].
Definition R_A1ab : region :=
mkRegion None 137258 667648 0 0
[ mkChunk 137258 (CImg 530390) ].
Definition R_A2a : region :=
mkRegion None 667648 671104 0 0
[ mkChunk 667648 (CImg 3456) ].
Definition R_A2b : region :=
mkRegion None 671136 671152 0 0
[ mkChunk 671136 (CImg 16) ].
Definition R_A2c : region :=
mkRegion None 671168 671184 0 0
[ mkChunk 671168 (CImg 16) ].
Definition R_A2d : region :=
mkRegion None 671200 671232 0 0
[ mkChunk 671200 (CImg 32) ].
Definition R_A2e : region :=
mkRegion None 671264 671296 0 0
[ mkChunk 671264 (CImg 32) ].
Definition R_A2f : region :=
mkRegion None 671328 671352 0 0
[ mkChunk 671328 (CImg 24) ].
Definition R_A2g : region :=
mkRegion None 671392 671440 0 0
[ mkChunk 671392 (CImg 48) ].
Definition R_A2h : region :=
mkRegion None 671488 671856 0 0
[ mkChunk 671488 (CImg 368) ].
Definition R_A2i : region :=
mkRegion None 671984 674808 0 0
[ mkChunk 671984 (CImg 2824) ].
Definition R_A2j : region :=
mkRegion None 674816 675048 0 0
[ mkChunk 674816 (CImg 232) ].
Definition R_A2k : region :=
mkRegion None 675056 675080 0 0
[ mkChunk 675056 (CImg 24) ].
Definition R_A2l : region :=
mkRegion None 675096 675184 0 0
[ mkChunk 675096 (CImg 8);
mkChunk 675104 (CImg 80) ].
Definition R_A2m : region :=
mkRegion None 675208 679304 0 0
[ mkChunk 675208 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 689664 690496 689664 690496
[ mkChunk 689664 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 693064 693136 693064 693136
[ mkChunk 693064 (CVal 1 (SLit 1));
mkChunk 693065 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6090832 6156368 0 0
[  ].
Definition R_A5a_1 : region :=
mkRegion None 6156368 6156416 6156368 6156416
[ mkChunk 6156368 (CImg 4);
mkChunk 6156372 (CVal 1 (SLit 0));
mkChunk 6156373 (CImg 43) ].
Definition R_A5a_2 : region :=
mkRegion None 6238688 6240844 6238688 6240844
[ mkChunk 6238688 (CImg 2112);
mkChunk 6240808 (CVal 8 (SLit 6240808));
mkChunk 6240816 (CVal 8 (SLit 6240808));
mkChunk 6240824 (CVal 8 (SLit 6240808));
mkChunk 6240832 (CVal 8 (SLit 0));
mkChunk 6240840 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6240848 6240920 6240848 6240920
[ mkChunk 6240848 (CVal 4 (SLit 2));
mkChunk 6240852 (CImg 6);
mkChunk 6240858 (CVal 1 (SLit 1));
mkChunk 6240859 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6240928 6241000 0 0
[ mkChunk 6240928 (CVal 8 (SLit 6240928));
mkChunk 6240936 (CImg 24);
mkChunk 6240960 (CVal 8 (SLit 6372792));
mkChunk 6240968 (CImg 24);
mkChunk 6240992 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6241068 6241080 0 0
[ mkChunk 6241068 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6372088 6372784 6372160 6372704
[ mkChunk 6372088 (CImg 16);
mkChunk 6372104 (CVal 8 (SLit 665928));
mkChunk 6372112 (CVal 8 (SLit 0));
mkChunk 6372120 (CVal 8 (SLit 24));
mkChunk 6372128 (CVal 8 (SLit 8));
mkChunk 6372136 (CVal 8 (SLit 0));
mkChunk 6372144 (CVal 8 (SOff 41 0));
mkChunk 6372152 (CImg 16);
mkChunk 6372168 (CVal 4 (SLit 1));
mkChunk 6372172 (CImg 4);
mkChunk 6372176 (CVal 8 (SLit 6372184));
mkChunk 6372184 (CImg 8);
mkChunk 6372192 (CVal 8 (SLit 604580));
mkChunk 6372200 (CImg 248);
mkChunk 6372448 (CVal 8 (SLit 460836));
mkChunk 6372456 (CImg 264);
mkChunk 6372728 (CVal 8 (SOff 1 0));
mkChunk 6372736 (CVal 1 (SLit 1));
mkChunk 6372737 (CImg 7);
mkChunk 6372744 (CVal 8 (SOff 5 0));
mkChunk 6372752 (CVal 8 (SLit 6372096));
mkChunk 6372760 (CVal 8 (SLit 248));
mkChunk 6372768 (CVal 8 (SLit 8));
mkChunk 6372776 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6372792 6372864 0 0
[ mkChunk 6372792 (CImg 48);
mkChunk 6372848 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6373792 6376008 0 0
[ mkChunk 6373792 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6376016 6377112 0 0
[ mkChunk 6376016 (CImg 8);
mkChunk 6376024 (CVal 8 (SLit 350092));
mkChunk 6376032 (CImg 1016);
mkChunk 6377048 (CVal 4 (SLit 0));
mkChunk 6377052 (CImg 4);
mkChunk 6377056 (CVal 4 (SLit 0));
mkChunk 6377060 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6377120 6381568 0 0
[ mkChunk 6377120 (CImg 4448) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A2h; R_A2i; R_A2j; R_A2k; R_A2l; R_A2m; R_A3; R_A4; R_RS; R_A5a_1; R_A5a_2; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
