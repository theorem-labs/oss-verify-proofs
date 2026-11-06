(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: regenerated for fuzz_manifest.asan: the read-only and relro regions are the gaps between fuzz_manifest's owned static pieces, the .data tail and the .bss block before the thread block are split at the owned redzones of fuzz_manifest's instrumented globals, the other regions moved by the address map of the two binaries. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66904 117848 0 0
[ mkChunk 66904 (CImg 50944) ].
Definition R_A1i : region :=
mkRegion None 117869 133760 0 0
[ mkChunk 117869 (CImg 15891) ].
Definition R_A1j : region :=
mkRegion None 133764 134407 0 0
[ mkChunk 133764 (CImg 643) ].
Definition R_A1k : region :=
mkRegion None 134432 134439 0 0
[ mkChunk 134432 (CImg 7) ].
Definition R_A1l : region :=
mkRegion None 134464 134465 0 0
[ mkChunk 134464 (CImg 1) ].
Definition R_A1m : region :=
mkRegion None 134496 134521 0 0
[ mkChunk 134496 (CImg 25) ].
Definition R_A1n : region :=
mkRegion None 134560 134586 0 0
[ mkChunk 134560 (CImg 26) ].
Definition R_A1o : region :=
mkRegion None 134624 134669 0 0
[ mkChunk 134624 (CImg 45) ].
Definition R_A1p : region :=
mkRegion None 134720 134762 0 0
[ mkChunk 134720 (CImg 42) ].
Definition R_A1q : region :=
mkRegion None 134816 134859 0 0
[ mkChunk 134816 (CImg 43) ].
Definition R_A1r : region :=
mkRegion None 134912 134958 0 0
[ mkChunk 134912 (CImg 46) ].
Definition R_A1s : region :=
mkRegion None 135008 135077 0 0
[ mkChunk 135008 (CImg 69) ].
Definition R_A1t : region :=
mkRegion None 135104 135111 0 0
[ mkChunk 135104 (CImg 7) ].
Definition R_A1u : region :=
mkRegion None 135136 135143 0 0
[ mkChunk 135136 (CImg 7) ].
Definition R_A1v : region :=
mkRegion None 135168 136580 0 0
[ mkChunk 135168 (CImg 1412) ].
Definition R_A1w : region :=
mkRegion None 136584 136680 0 0
[ mkChunk 136584 (CImg 96) ].
Definition R_A1x : region :=
mkRegion None 136682 626688 0 0
[ mkChunk 136682 (CImg 490006) ].
Definition R_A2a : region :=
mkRegion None 626688 629136 0 0
[ mkChunk 626688 (CImg 2448) ].
Definition R_A2b : region :=
mkRegion None 629264 632088 0 0
[ mkChunk 629264 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 632096 632328 0 0
[ mkChunk 632096 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 632336 632360 0 0
[ mkChunk 632336 (CImg 24) ].
Definition R_A2e : region :=
mkRegion None 632376 632464 0 0
[ mkChunk 632376 (CImg 8);
mkChunk 632384 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 632488 636608 0 0
[ mkChunk 632488 (CImg 4120) ].
Definition R_A3p : region :=
mkRegion None 646992 647048 646992 647048
[ mkChunk 646992 (CImg 56) ].
Definition R_A3 : region :=
mkRegion None 647072 647872 647072 647872
[ mkChunk 647072 (CImg 800) ].
Definition R_A4 : region :=
mkRegion None 648904 648976 648904 648976
[ mkChunk 648904 (CVal 1 (SLit 1));
mkChunk 648905 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6046672 6112208 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6112208 6112264 6112208 6112264
[ mkChunk 6112208 (CImg 4);
mkChunk 6112212 (CVal 1 (SLit 0));
mkChunk 6112213 (CImg 51) ].
Definition R_A5c : region :=
mkRegion None 6112288 6112296 6112288 6112296
[ mkChunk 6112288 (CImg 8) ].
Definition R_A5d : region :=
mkRegion None 6112320 6112328 6112320 6112328
[ mkChunk 6112320 (CImg 8) ].
Definition R_A5e : region :=
mkRegion None 6112352 6114508 6112352 6114508
[ mkChunk 6112352 (CImg 2112);
mkChunk 6114472 (CVal 8 (SLit 6114472));
mkChunk 6114480 (CVal 8 (SLit 6114472));
mkChunk 6114488 (CVal 8 (SLit 6114472));
mkChunk 6114496 (CVal 8 (SLit 0));
mkChunk 6114504 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6114512 6114584 6114512 6114584
[ mkChunk 6114512 (CVal 4 (SLit 2));
mkChunk 6114516 (CImg 6);
mkChunk 6114522 (CVal 1 (SLit 1));
mkChunk 6114523 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6114592 6114664 0 0
[ mkChunk 6114592 (CVal 8 (SLit 6114592));
mkChunk 6114600 (CImg 24);
mkChunk 6114624 (CVal 8 (SLit 6246456));
mkChunk 6114632 (CImg 24);
mkChunk 6114656 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6114732 6114744 0 0
[ mkChunk 6114732 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6245752 6246448 6245824 6246368
[ mkChunk 6245752 (CImg 16);
mkChunk 6245768 (CVal 8 (SLit 623640));
mkChunk 6245776 (CVal 8 (SLit 0));
mkChunk 6245784 (CVal 8 (SLit 24));
mkChunk 6245792 (CVal 8 (SLit 8));
mkChunk 6245800 (CVal 8 (SLit 0));
mkChunk 6245808 (CVal 8 (SOff 41 0));
mkChunk 6245816 (CImg 16);
mkChunk 6245832 (CVal 4 (SLit 1));
mkChunk 6245836 (CImg 4);
mkChunk 6245840 (CVal 8 (SLit 6245848));
mkChunk 6245848 (CImg 8);
mkChunk 6245856 (CVal 8 (SLit 560440));
mkChunk 6245864 (CImg 248);
mkChunk 6246112 (CVal 8 (SLit 458460));
mkChunk 6246120 (CImg 264);
mkChunk 6246392 (CVal 8 (SOff 1 0));
mkChunk 6246400 (CVal 1 (SLit 1));
mkChunk 6246401 (CImg 7);
mkChunk 6246408 (CVal 8 (SOff 5 0));
mkChunk 6246416 (CVal 8 (SLit 6245760));
mkChunk 6246424 (CVal 8 (SLit 248));
mkChunk 6246432 (CVal 8 (SLit 8));
mkChunk 6246440 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6246456 6246528 0 0
[ mkChunk 6246456 (CImg 48);
mkChunk 6246512 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6247456 6249672 0 0
[ mkChunk 6247456 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6249680 6250776 0 0
[ mkChunk 6249680 (CImg 8);
mkChunk 6249688 (CVal 8 (SLit 347716));
mkChunk 6249696 (CImg 1016);
mkChunk 6250712 (CVal 4 (SLit 0));
mkChunk 6250716 (CImg 4);
mkChunk 6250720 (CVal 4 (SLit 0));
mkChunk 6250724 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6250784 6254592 0 0
[ mkChunk 6250784 (CImg 3808) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3p; R_A3; R_A4; R_RS; R_A5a; R_A5c; R_A5d; R_A5e; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
