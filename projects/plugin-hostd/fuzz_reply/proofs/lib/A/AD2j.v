(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for plugin-hostd/fuzz_reply's asan image by a Theorem Labs lane's gen_ad2.py (adopted in a Theorem Labs lane's tools/startup) from the 50 collected hand-off states (lib/A/AB01.v), the generated lib/A/AF0m.v, the atable and the image *)
(* Read from: fuzz_reply.asan (plugin-hostd/fuzz_reply asan) sha256 42c58610e125e0b47770217f7175ffe2f23ed5ee1399b3e81539eff364611d5a; unstripped twin sha256 d751b179ea493ead8cda011f65c1503ba46920e9d4eefe8638cf412fb1a55709 *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66912 118075 0 0
[ mkChunk 66912 (CImg 51163) ].
Definition R_A1i : region :=
mkRegion None 118096 134120 0 0
[ mkChunk 118096 (CImg 16024) ].
Definition R_A1j : region :=
mkRegion None 134124 134834 0 0
[ mkChunk 134124 (CImg 710) ].
Definition R_A1k : region :=
mkRegion None 134880 134881 0 0
[ mkChunk 134880 (CImg 1) ].
Definition R_A1l : region :=
mkRegion None 134912 134917 0 0
[ mkChunk 134912 (CImg 5) ].
Definition R_A1m : region :=
mkRegion None 134944 134958 0 0
[ mkChunk 134944 (CImg 14) ].
Definition R_A1n : region :=
mkRegion None 134976 134982 0 0
[ mkChunk 134976 (CImg 6) ].
Definition R_A1o : region :=
mkRegion None 135008 135012 0 0
[ mkChunk 135008 (CImg 4) ].
Definition R_A1p : region :=
mkRegion None 135040 135047 0 0
[ mkChunk 135040 (CImg 7) ].
Definition R_A1q : region :=
mkRegion None 135072 136484 0 0
[ mkChunk 135072 (CImg 1412) ].
Definition R_A1r : region :=
mkRegion None 136488 136584 0 0
[ mkChunk 136488 (CImg 96) ].
Definition R_A1s : region :=
mkRegion None 136586 643072 0 0
[ mkChunk 136586 (CImg 506486) ].
Definition R_A2a : region :=
mkRegion None 643072 645552 0 0
[ mkChunk 643072 (CImg 2480) ].
Definition R_A2b : region :=
mkRegion None 645680 648504 0 0
[ mkChunk 645680 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 648512 648744 0 0
[ mkChunk 648512 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 648752 648776 0 0
[ mkChunk 648752 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 648792 648880 0 0
[ mkChunk 648792 (CImg 8);
mkChunk 648800 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 648904 653024 0 0
[ mkChunk 648904 (CImg 4120) ].
Definition R_A3_1 : region :=
mkRegion None 663416 663464 663416 663464
[ mkChunk 663416 (CImg 48) ].
Definition R_A3_2 : region :=
mkRegion None 663488 663492 663488 663492
[ mkChunk 663488 (CImg 4) ].
Definition R_A3_3 : region :=
mkRegion None 663520 663524 663520 663524
[ mkChunk 663520 (CImg 4) ].
Definition R_A3_4 : region :=
mkRegion None 663552 664352 663552 664352
[ mkChunk 663552 (CImg 800) ].
Definition R_A4 : region :=
mkRegion None 666120 666192 666120 666192
[ mkChunk 666120 (CVal 1 (SLit 1));
mkChunk 666121 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6063888 6129424 0 0
[  ].
Definition R_A5a_1 : region :=
mkRegion None 6129424 6129480 6129424 6129480
[ mkChunk 6129424 (CImg 4);
mkChunk 6129428 (CVal 1 (SLit 0));
mkChunk 6129429 (CImg 51) ].
Definition R_A5a_2 : region :=
mkRegion None 6129504 6129505 6129504 6129505
[ mkChunk 6129504 (CImg 1) ].
Definition R_A5a_3 : region :=
mkRegion None 6129536 6129540 6129536 6129540
[ mkChunk 6129536 (CImg 4) ].
Definition R_A5a_4 : region :=
mkRegion None 6129568 6129572 6129568 6129572
[ mkChunk 6129568 (CImg 4) ].
Definition R_A5a_5 : region :=
mkRegion None 6129600 6129608 6129600 6129608
[ mkChunk 6129600 (CImg 8) ].
Definition R_A5a_6 : region :=
mkRegion None 6129632 6129633 6129632 6129633
[ mkChunk 6129632 (CImg 1) ].
Definition R_A5a_7 : region :=
mkRegion None 6129664 6129668 6129664 6129668
[ mkChunk 6129664 (CImg 4) ].
Definition R_A5a_8 : region :=
mkRegion None 6129696 6129700 6129696 6129700
[ mkChunk 6129696 (CImg 4) ].
Definition R_A5a_9 : region :=
mkRegion None 6129728 6129736 6129728 6129736
[ mkChunk 6129728 (CImg 8) ].
Definition R_A5a_10 : region :=
mkRegion None 6129760 6129761 6129760 6129761
[ mkChunk 6129760 (CImg 1) ].
Definition R_A5a_11 : region :=
mkRegion None 6129792 6129793 6129792 6129793
[ mkChunk 6129792 (CImg 1) ].
Definition R_A5a_12 : region :=
mkRegion None 6129824 6129825 6129824 6129825
[ mkChunk 6129824 (CImg 1) ].
Definition R_A5a_13 : region :=
mkRegion None 6129856 6129864 6129856 6129864
[ mkChunk 6129856 (CImg 8) ].
Definition R_A5a_14 : region :=
mkRegion None 6129888 6130272 6129888 6130272
[ mkChunk 6129888 (CImg 384) ].
Definition R_A5a_15 : region :=
mkRegion None 6130368 6130408 6130368 6130408
[ mkChunk 6130368 (CImg 40) ].
Definition R_A5a_16 : region :=
mkRegion None 6130464 6130472 6130464 6130472
[ mkChunk 6130464 (CImg 8) ].
Definition R_A5a_17 : region :=
mkRegion None 6130496 6130504 6130496 6130504
[ mkChunk 6130496 (CImg 8) ].
Definition R_A5a_18 : region :=
mkRegion None 6130528 6132684 6130528 6132684
[ mkChunk 6130528 (CImg 2112);
mkChunk 6132648 (CVal 8 (SLit 6132648));
mkChunk 6132656 (CVal 8 (SLit 6132648));
mkChunk 6132664 (CVal 8 (SLit 6132648));
mkChunk 6132672 (CVal 8 (SLit 0));
mkChunk 6132680 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6132688 6132760 6132688 6132760
[ mkChunk 6132688 (CVal 4 (SLit 2));
mkChunk 6132692 (CImg 6);
mkChunk 6132698 (CVal 1 (SLit 1));
mkChunk 6132699 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6132768 6132840 0 0
[ mkChunk 6132768 (CVal 8 (SLit 6132768));
mkChunk 6132776 (CImg 24);
mkChunk 6132800 (CVal 8 (SLit 6264632));
mkChunk 6132808 (CImg 24);
mkChunk 6132832 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6132908 6132920 0 0
[ mkChunk 6132908 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6263928 6264624 6264000 6264544
[ mkChunk 6263928 (CImg 16);
mkChunk 6263944 (CVal 8 (SLit 640056));
mkChunk 6263952 (CVal 8 (SLit 0));
mkChunk 6263960 (CVal 8 (SLit 24));
mkChunk 6263968 (CVal 8 (SLit 8));
mkChunk 6263976 (CVal 8 (SLit 0));
mkChunk 6263984 (CVal 8 (SOff 41 0));
mkChunk 6263992 (CImg 16);
mkChunk 6264008 (CVal 4 (SLit 1));
mkChunk 6264012 (CImg 4);
mkChunk 6264016 (CVal 8 (SLit 6264024));
mkChunk 6264024 (CImg 8);
mkChunk 6264032 (CVal 8 (SLit 576608));
mkChunk 6264040 (CImg 248);
mkChunk 6264288 (CVal 8 (SLit 465068));
mkChunk 6264296 (CImg 264);
mkChunk 6264568 (CVal 8 (SOff 1 0));
mkChunk 6264576 (CVal 1 (SLit 1));
mkChunk 6264577 (CImg 7);
mkChunk 6264584 (CVal 8 (SOff 5 0));
mkChunk 6264592 (CVal 8 (SLit 6263936));
mkChunk 6264600 (CVal 8 (SLit 248));
mkChunk 6264608 (CVal 8 (SLit 8));
mkChunk 6264616 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6264632 6264704 0 0
[ mkChunk 6264632 (CImg 48);
mkChunk 6264688 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6265632 6267848 0 0
[ mkChunk 6265632 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6267856 6268952 0 0
[ mkChunk 6267856 (CImg 8);
mkChunk 6267864 (CVal 8 (SLit 352700));
mkChunk 6267872 (CImg 1016);
mkChunk 6268888 (CVal 4 (SLit 0));
mkChunk 6268892 (CImg 4);
mkChunk 6268896 (CVal 4 (SLit 0));
mkChunk 6268900 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6268960 6270976 0 0
[ mkChunk 6268960 (CImg 2016) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3_1; R_A3_2; R_A3_3; R_A3_4; R_A4; R_RS; R_A5a_1; R_A5a_2; R_A5a_3; R_A5a_4; R_A5a_5; R_A5a_6; R_A5a_7; R_A5a_8; R_A5a_9; R_A5a_10; R_A5a_11; R_A5a_12; R_A5a_13; R_A5a_14; R_A5a_15; R_A5a_16; R_A5a_17; R_A5a_18; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
