(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/YD2i.v and lib/YD2j.v (origin/ossv/recipes c8557374ad2e) for fuzz_ctrl's asan-ubsan image (sha256 12136677c5cf...) by a Theorem Labs lane's gen_ad2.py, with its module paths changed: sregs_main, TIDV, CANV and TFIB_MAIN from the 50 hand-off states of lib/Reusable/YB01.v, the image bounds from lib/Reusable/YB12.v and lib/Reusable/YB1h.v; IMG_REGIONS below .data from the image and the owned static cells of lib/Reusable/YF0m.v, from .data on cgif's regions placed at the donor's offsets from the objects of the unstripped twin (ee07e2c38d94...: oft_arg0, read_stage, target_run.initialized, builtin_tls, __thread_list_lock, ...) and cut around the same owned cells, every CVal value read from the hand-off states *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66368 66456 0 0
[ mkChunk 66368 (CImg 88) ].
Definition R_A1f : region :=
mkRegion None 66472 66480 0 0
[ mkChunk 66472 (CImg 8) ].
Definition R_A1g : region :=
mkRegion None 66488 66592 0 0
[ mkChunk 66488 (CImg 104) ].
Definition R_A1h : region :=
mkRegion None 66656 66848 0 0
[ mkChunk 66656 (CImg 192) ].
Definition R_A1i : region :=
mkRegion None 66912 118904 0 0
[ mkChunk 66912 (CImg 51992) ].
Definition R_A1j : region :=
mkRegion None 118925 134860 0 0
[ mkChunk 118925 (CImg 15935) ].
Definition R_A1k : region :=
mkRegion None 134864 135494 0 0
[ mkChunk 134864 (CImg 630) ].
Definition R_A1l : region :=
mkRegion None 135520 135521 0 0
[ mkChunk 135520 (CImg 1) ].
Definition R_A1m : region :=
mkRegion None 135552 135564 0 0
[ mkChunk 135552 (CImg 12) ].
Definition R_A1n : region :=
mkRegion None 135584 135650 0 0
[ mkChunk 135584 (CImg 66) ].
Definition R_A1o : region :=
mkRegion None 135680 135687 0 0
[ mkChunk 135680 (CImg 7) ].
Definition R_A1p : region :=
mkRegion None 135712 135717 0 0
[ mkChunk 135712 (CImg 5) ].
Definition R_A1q : region :=
mkRegion None 135744 135751 0 0
[ mkChunk 135744 (CImg 7) ].
Definition R_A1r : region :=
mkRegion None 135776 135791 0 0
[ mkChunk 135776 (CImg 15) ].
Definition R_A1s : region :=
mkRegion None 135808 135818 0 0
[ mkChunk 135808 (CImg 10) ].
Definition R_A1t : region :=
mkRegion None 135840 135856 0 0
[ mkChunk 135840 (CImg 16) ].
Definition R_A1u : region :=
mkRegion None 135872 135878 0 0
[ mkChunk 135872 (CImg 6) ].
Definition R_A1v : region :=
mkRegion None 135904 135912 0 0
[ mkChunk 135904 (CImg 8) ].
Definition R_A1w : region :=
mkRegion None 135936 135943 0 0
[ mkChunk 135936 (CImg 7) ].
Definition R_A1x : region :=
mkRegion None 135968 135983 0 0
[ mkChunk 135968 (CImg 15) ].
Definition R_A1y : region :=
mkRegion None 136000 136016 0 0
[ mkChunk 136000 (CImg 16) ].
Definition R_A1z : region :=
mkRegion None 136032 136042 0 0
[ mkChunk 136032 (CImg 10) ].
Definition R_A1aa : region :=
mkRegion None 136064 136080 0 0
[ mkChunk 136064 (CImg 16) ].
Definition R_A1ab : region :=
mkRegion None 136096 136102 0 0
[ mkChunk 136096 (CImg 6) ].
Definition R_A1ac : region :=
mkRegion None 136128 136141 0 0
[ mkChunk 136128 (CImg 13) ].
Definition R_A1ad : region :=
mkRegion None 136160 136166 0 0
[ mkChunk 136160 (CImg 6) ].
Definition R_A1ae : region :=
mkRegion None 136192 136215 0 0
[ mkChunk 136192 (CImg 23) ].
Definition R_A1af : region :=
mkRegion None 136256 136262 0 0
[ mkChunk 136256 (CImg 6) ].
Definition R_A1ag : region :=
mkRegion None 136288 136310 0 0
[ mkChunk 136288 (CImg 22) ].
Definition R_A1ah : region :=
mkRegion None 136352 136359 0 0
[ mkChunk 136352 (CImg 7) ].
Definition R_A1ai : region :=
mkRegion None 136384 136391 0 0
[ mkChunk 136384 (CImg 7) ].
Definition R_A1aj : region :=
mkRegion None 136416 136445 0 0
[ mkChunk 136416 (CImg 29) ].
Definition R_A1ak : region :=
mkRegion None 136480 136492 0 0
[ mkChunk 136480 (CImg 12) ].
Definition R_A1al : region :=
mkRegion None 136512 136541 0 0
[ mkChunk 136512 (CImg 29) ].
Definition R_A1am : region :=
mkRegion None 136576 136582 0 0
[ mkChunk 136576 (CImg 6) ].
Definition R_A1an : region :=
mkRegion None 136608 136631 0 0
[ mkChunk 136608 (CImg 23) ].
Definition R_A1ao : region :=
mkRegion None 136672 136680 0 0
[ mkChunk 136672 (CImg 8) ].
Definition R_A1ap : region :=
mkRegion None 136704 136710 0 0
[ mkChunk 136704 (CImg 6) ].
Definition R_A1aq : region :=
mkRegion None 136736 136760 0 0
[ mkChunk 136736 (CImg 24) ].
Definition R_A1ar : region :=
mkRegion None 136800 136808 0 0
[ mkChunk 136800 (CImg 8) ].
Definition R_A1as : region :=
mkRegion None 136832 136839 0 0
[ mkChunk 136832 (CImg 7) ].
Definition R_A1at : region :=
mkRegion None 136864 136888 0 0
[ mkChunk 136864 (CImg 24) ].
Definition R_A1au : region :=
mkRegion None 136928 136937 0 0
[ mkChunk 136928 (CImg 9) ].
Definition R_A1av : region :=
mkRegion None 136960 136967 0 0
[ mkChunk 136960 (CImg 7) ].
Definition R_A1aw : region :=
mkRegion None 136992 137016 0 0
[ mkChunk 136992 (CImg 24) ].
Definition R_A1ax : region :=
mkRegion None 137056 137065 0 0
[ mkChunk 137056 (CImg 9) ].
Definition R_A1ay : region :=
mkRegion None 137088 137095 0 0
[ mkChunk 137088 (CImg 7) ].
Definition R_A1az : region :=
mkRegion None 137120 137143 0 0
[ mkChunk 137120 (CImg 23) ].
Definition R_A1ba : region :=
mkRegion None 137184 137192 0 0
[ mkChunk 137184 (CImg 8) ].
Definition R_A1bb : region :=
mkRegion None 137216 137223 0 0
[ mkChunk 137216 (CImg 7) ].
Definition R_A1bc : region :=
mkRegion None 137248 137271 0 0
[ mkChunk 137248 (CImg 23) ].
Definition R_A1bd : region :=
mkRegion None 137312 137320 0 0
[ mkChunk 137312 (CImg 8) ].
Definition R_A1be : region :=
mkRegion None 137344 137351 0 0
[ mkChunk 137344 (CImg 7) ].
Definition R_A1bf : region :=
mkRegion None 137376 137400 0 0
[ mkChunk 137376 (CImg 24) ].
Definition R_A1bg : region :=
mkRegion None 137440 137448 0 0
[ mkChunk 137440 (CImg 8) ].
Definition R_A1bh : region :=
mkRegion None 137472 137504 0 0
[ mkChunk 137472 (CImg 32) ].
Definition R_A1bi : region :=
mkRegion None 137536 137568 0 0
[ mkChunk 137536 (CImg 32) ].
Definition R_A1bj : region :=
mkRegion None 137600 137656 0 0
[ mkChunk 137600 (CImg 56) ].
Definition R_A1bk : region :=
mkRegion None 137696 137792 0 0
[ mkChunk 137696 (CImg 96) ].
Definition R_A1bl : region :=
mkRegion None 137824 137856 0 0
[ mkChunk 137824 (CImg 32) ].
Definition R_A1bm : region :=
mkRegion None 137888 139312 0 0
[ mkChunk 137888 (CImg 1424) ].
Definition R_A1bn : region :=
mkRegion None 139316 139412 0 0
[ mkChunk 139316 (CImg 96) ].
Definition R_A1bo : region :=
mkRegion None 139414 651264 0 0
[ mkChunk 139414 (CImg 511850) ].
Definition R_A2a : region :=
mkRegion None 651264 652784 0 0
[ mkChunk 651264 (CImg 1520) ].
Definition R_A2b : region :=
mkRegion None 652832 656088 0 0
[ mkChunk 652832 (CImg 3256) ].
Definition R_A2c : region :=
mkRegion None 656896 657160 0 0
[ mkChunk 656896 (CImg 264) ].
Definition R_A2d : region :=
mkRegion None 657248 657616 0 0
[ mkChunk 657248 (CImg 368) ].
Definition R_A2e : region :=
mkRegion None 657744 660568 0 0
[ mkChunk 657744 (CImg 2824) ].
Definition R_A2f : region :=
mkRegion None 660576 660808 0 0
[ mkChunk 660576 (CImg 232) ].
Definition R_A2g : region :=
mkRegion None 660816 660840 0 0
[ mkChunk 660816 (CImg 24) ].
Definition R_A2h : region :=
mkRegion None 660856 660944 0 0
[ mkChunk 660856 (CImg 8);
mkChunk 660864 (CImg 80) ].
Definition R_A2i : region :=
mkRegion None 660968 665064 0 0
[ mkChunk 660968 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 675424 676256 675424 676256
[ mkChunk 675424 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 679944 680016 679944 680016
[ mkChunk 679944 (CVal 1 (SLit 1));
mkChunk 679945 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6077712 6143248 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6143248 6145452 6143248 6145452
[ mkChunk 6143248 (CImg 4);
mkChunk 6143252 (CVal 1 (SLit 0));
mkChunk 6143253 (CImg 2155);
mkChunk 6145416 (CVal 8 (SLit 6145416));
mkChunk 6145424 (CVal 8 (SLit 6145416));
mkChunk 6145432 (CVal 8 (SLit 6145416));
mkChunk 6145440 (CVal 8 (SLit 0));
mkChunk 6145448 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6145456 6145528 6145456 6145528
[ mkChunk 6145456 (CVal 4 (SLit 2));
mkChunk 6145460 (CImg 6);
mkChunk 6145466 (CVal 1 (SLit 1));
mkChunk 6145467 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6145536 6145608 0 0
[ mkChunk 6145536 (CVal 8 (SLit 6145536));
mkChunk 6145544 (CImg 24);
mkChunk 6145568 (CVal 8 (SLit 6277400));
mkChunk 6145576 (CImg 24);
mkChunk 6145600 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6145676 6145688 0 0
[ mkChunk 6145676 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6276696 6277392 6276768 6277312
[ mkChunk 6276696 (CImg 16);
mkChunk 6276712 (CVal 8 (SLit 647528));
mkChunk 6276720 (CVal 8 (SLit 0));
mkChunk 6276728 (CVal 8 (SLit 24));
mkChunk 6276736 (CVal 8 (SLit 8));
mkChunk 6276744 (CVal 8 (SLit 0));
mkChunk 6276752 (CVal 8 (SOff 41 0));
mkChunk 6276760 (CImg 16);
mkChunk 6276776 (CVal 4 (SLit 1));
mkChunk 6276780 (CImg 4);
mkChunk 6276784 (CVal 8 (SLit 6276792));
mkChunk 6276792 (CImg 8);
mkChunk 6276800 (CVal 8 (SLit 586180));
mkChunk 6276808 (CImg 248);
mkChunk 6277056 (CVal 8 (SLit 460248));
mkChunk 6277064 (CImg 264);
mkChunk 6277336 (CVal 8 (SOff 1 0));
mkChunk 6277344 (CVal 1 (SLit 1));
mkChunk 6277345 (CImg 7);
mkChunk 6277352 (CVal 8 (SOff 5 0));
mkChunk 6277360 (CVal 8 (SLit 6276704));
mkChunk 6277368 (CVal 8 (SLit 248));
mkChunk 6277376 (CVal 8 (SLit 8));
mkChunk 6277384 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6277400 6277472 0 0
[ mkChunk 6277400 (CImg 48);
mkChunk 6277456 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6278400 6280616 0 0
[ mkChunk 6278400 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6280624 6281720 0 0
[ mkChunk 6280624 (CImg 8);
mkChunk 6280632 (CVal 8 (SLit 349504));
mkChunk 6280640 (CImg 1016);
mkChunk 6281656 (CVal 4 (SLit 0));
mkChunk 6281660 (CImg 4);
mkChunk 6281664 (CVal 4 (SLit 0));
mkChunk 6281668 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6281728 6283264 0 0
[ mkChunk 6281728 (CImg 1536) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A1bh; R_A1bi; R_A1bj; R_A1bk; R_A1bl; R_A1bm; R_A1bn; R_A1bo; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A2h; R_A2i; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
