(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-pw/fuzz_qdisc image A by gen_ad2.py 195f6e6ef088 (port-reply start-up set startup-set-2026-10-29) from this image's 50 collected hand-off states (lib/A/AB01.v), its atable (lib/A/AB12.v) and Tfib_owned_static (lib/A/AF0m.v), templates cgif_file_fuzzer A/AD2i.v / A/AD2j.v at c8557374ad2e (h-small-a3) *)
(* Read from: fuzz_qdisc.asan (reac-pw/fuzz_qdisc asan) sha256 980e2b8458528060633e6c98fff20d2f46b97738c06eae4307d09f59c82c890e; unstripped twin sha256 d77ead7cec5c42ebc28aff0443565f333cbb4dd08f5f1101d3deb805d5e34aac *)
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_qdisc.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66352 66448 0 0
[ mkChunk 66352 (CImg 96) ].
Definition R_A1e : region :=
mkRegion None 66464 66472 0 0
[ mkChunk 66464 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66480 66584 0 0
[ mkChunk 66480 (CImg 104) ].
Definition R_A1g : region :=
mkRegion None 66648 66840 0 0
[ mkChunk 66648 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66904 117738 0 0
[ mkChunk 66904 (CImg 50834) ].
Definition R_A1i : region :=
mkRegion None 117759 133652 0 0
[ mkChunk 117759 (CImg 15893) ].
Definition R_A1j : region :=
mkRegion None 133656 134296 0 0
[ mkChunk 133656 (CImg 640) ].
Definition R_A1k : region :=
mkRegion None 134336 135748 0 0
[ mkChunk 134336 (CImg 1412) ].
Definition R_A1n : region :=
mkRegion None 135752 135848 0 0
[ mkChunk 135752 (CImg 96) ].
Definition R_A1o : region :=
mkRegion None 135850 612520 0 0
[ mkChunk 135850 (CImg 476670) ].
Definition R_A1p : region :=
mkRegion None 612648 615472 0 0
[ mkChunk 612648 (CImg 2824) ].
Definition R_A1q : region :=
mkRegion None 615480 615712 0 0
[ mkChunk 615480 (CImg 232) ].
Definition R_A1r : region :=
mkRegion None 615720 615744 0 0
[ mkChunk 615720 (CImg 24) ].
Definition R_A1s : region :=
mkRegion None 615760 615848 0 0
[ mkChunk 615760 (CImg 8);
mkChunk 615768 (CImg 80) ].
Definition R_A1t : region :=
mkRegion None 615872 618496 0 0
[ mkChunk 615872 (CImg 2624) ].
Definition R_A2 : region :=
mkRegion None 618496 619968 0 0
[ mkChunk 618496 (CImg 1472) ].
Definition R_A3 : region :=
mkRegion None 630320 631152 630320 631152
[ mkChunk 630320 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 631240 631312 631240 631312
[ mkChunk 631240 (CVal 1 (SLit 1));
mkChunk 631241 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6029008 6094544 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6094544 6096748 6094544 6096748
[ mkChunk 6094544 (CImg 4);
mkChunk 6094548 (CVal 1 (SLit 0));
mkChunk 6094549 (CImg 2155);
mkChunk 6096712 (CVal 8 (SLit 6096712));
mkChunk 6096720 (CVal 8 (SLit 6096712));
mkChunk 6096728 (CVal 8 (SLit 6096712));
mkChunk 6096736 (CVal 8 (SLit 0));
mkChunk 6096744 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6096752 6096824 6096752 6096824
[ mkChunk 6096752 (CVal 4 (SLit 2));
mkChunk 6096756 (CImg 6);
mkChunk 6096762 (CVal 1 (SLit 1));
mkChunk 6096763 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6096832 6096904 0 0
[ mkChunk 6096832 (CVal 8 (SLit 6096832));
mkChunk 6096840 (CImg 24);
mkChunk 6096864 (CVal 8 (SLit 6228696));
mkChunk 6096872 (CImg 24);
mkChunk 6096896 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6096972 6096984 0 0
[ mkChunk 6096972 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6227992 6228688 6228064 6228608
[ mkChunk 6227992 (CImg 16);
mkChunk 6228008 (CVal 8 (SLit 607024));
mkChunk 6228016 (CVal 8 (SLit 0));
mkChunk 6228024 (CVal 8 (SLit 24));
mkChunk 6228032 (CVal 8 (SLit 8));
mkChunk 6228040 (CVal 8 (SLit 0));
mkChunk 6228048 (CVal 8 (SOff 41 0));
mkChunk 6228056 (CImg 16);
mkChunk 6228072 (CVal 4 (SLit 1));
mkChunk 6228076 (CImg 4);
mkChunk 6228080 (CVal 8 (SLit 6228088));
mkChunk 6228088 (CImg 8);
mkChunk 6228096 (CVal 8 (SLit 545680));
mkChunk 6228104 (CImg 248);
mkChunk 6228352 (CVal 8 (SLit 449612));
mkChunk 6228360 (CImg 264);
mkChunk 6228632 (CVal 8 (SOff 1 0));
mkChunk 6228640 (CVal 1 (SLit 1));
mkChunk 6228641 (CImg 7);
mkChunk 6228648 (CVal 8 (SOff 5 0));
mkChunk 6228656 (CVal 8 (SLit 6228000));
mkChunk 6228664 (CVal 8 (SLit 248));
mkChunk 6228672 (CVal 8 (SLit 8));
mkChunk 6228680 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6228696 6228768 0 0
[ mkChunk 6228696 (CImg 48);
mkChunk 6228752 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6229696 6231912 0 0
[ mkChunk 6229696 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6231920 6233016 0 0
[ mkChunk 6231920 (CImg 8);
mkChunk 6231928 (CVal 8 (SLit 338868));
mkChunk 6231936 (CImg 1016);
mkChunk 6232952 (CVal 4 (SLit 0));
mkChunk 6232956 (CImg 4);
mkChunk 6232960 (CVal 4 (SLit 0));
mkChunk 6232964 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6233024 6238208 0 0
[ mkChunk 6233024 (CImg 5184) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
