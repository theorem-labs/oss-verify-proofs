(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/YD2i.v and lib/YD2j.v (origin/ossv/recipes c8557374ad2e) for libreac/fuzz_scene's asan-ubsan image (sha256 e98b1ed286c1...) by a Theorem Labs lane's gen_ad2.py, with its module paths changed: sregs_main, TIDV, CANV and TFIB_MAIN from the 50 hand-off states of lib/AU/YB01.v, the image bounds from lib/AU/YB12.v and the rw window 0x9d000..0x5f9000; IMG_REGIONS below .data from the image and the owned static cells of the generated lib/AU/YF0m.v; owned static cells come from the GENERATED f0mgen2 AF0m (af0m.py, --base the hand-assembled reference) *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66912 117955 0 0
[ mkChunk 66912 (CImg 51043) ].
Definition R_A1i : region :=
mkRegion None 117976 133884 0 0
[ mkChunk 117976 (CImg 15908) ].
Definition R_A1j : region :=
mkRegion None 133888 134540 0 0
[ mkChunk 133888 (CImg 652) ].
Definition R_A1k : region :=
mkRegion None 134560 134610 0 0
[ mkChunk 134560 (CImg 50) ].
Definition R_A1l : region :=
mkRegion None 134656 134700 0 0
[ mkChunk 134656 (CImg 44) ].
Definition R_A1m : region :=
mkRegion None 134720 134727 0 0
[ mkChunk 134720 (CImg 7) ].
Definition R_A1n : region :=
mkRegion None 134752 143688 0 0
[ mkChunk 134752 (CImg 8936) ].
Definition R_A1o : region :=
mkRegion None 145920 147336 0 0
[ mkChunk 145920 (CImg 1416) ].
Definition R_A1p : region :=
mkRegion None 147340 147436 0 0
[ mkChunk 147340 (CImg 96) ].
Definition R_A1q : region :=
mkRegion None 147438 637472 0 0
[ mkChunk 147438 (CImg 490034) ].
Definition R_A1r : region :=
mkRegion None 637600 640424 0 0
[ mkChunk 637600 (CImg 2824) ].
Definition R_A1s : region :=
mkRegion None 640432 640664 0 0
[ mkChunk 640432 (CImg 232) ].
Definition R_A1t : region :=
mkRegion None 640672 640704 0 0
[ mkChunk 640672 (CImg 32) ].
Definition R_A1u : region :=
mkRegion None 640720 640808 0 0
[ mkChunk 640720 (CImg 8);
mkChunk 640728 (CImg 80) ].
Definition R_A1v : region :=
mkRegion None 640832 643072 0 0
[ mkChunk 640832 (CImg 2240) ].
Definition R_A2 : region :=
mkRegion None 643072 644928 0 0
[ mkChunk 643072 (CImg 1856) ].
Definition R_A3 : region :=
mkRegion None 655288 656128 655288 656128
[ mkChunk 655288 (CImg 840) ].
Definition R_A4 : region :=
mkRegion None 656456 656528 656456 656528
[ mkChunk 656456 (CVal 1 (SLit 1));
mkChunk 656457 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6054224 6119760 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6119760 6121972 6119760 6121972
[ mkChunk 6119760 (CImg 4);
mkChunk 6119764 (CVal 1 (SLit 0));
mkChunk 6119765 (CImg 43);
mkChunk 6119808 (CVal 1 (SLit 1));
mkChunk 6119809 (CImg 2119);
mkChunk 6121936 (CVal 8 (SLit 6121936));
mkChunk 6121944 (CVal 8 (SLit 6121936));
mkChunk 6121952 (CVal 8 (SLit 6121936));
mkChunk 6121960 (CVal 8 (SLit 0));
mkChunk 6121968 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6121976 6122048 6121976 6122048
[ mkChunk 6121976 (CVal 4 (SLit 2));
mkChunk 6121980 (CImg 6);
mkChunk 6121986 (CVal 1 (SLit 1));
mkChunk 6121987 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6122056 6122128 0 0
[ mkChunk 6122056 (CVal 8 (SLit 6122056));
mkChunk 6122064 (CImg 24);
mkChunk 6122088 (CVal 8 (SLit 6253920));
mkChunk 6122096 (CImg 24);
mkChunk 6122120 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6122196 6122208 0 0
[ mkChunk 6122196 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6253216 6253912 6253288 6253832
[ mkChunk 6253216 (CImg 16);
mkChunk 6253232 (CVal 8 (SLit 631976));
mkChunk 6253240 (CVal 8 (SLit 0));
mkChunk 6253248 (CVal 8 (SLit 24));
mkChunk 6253256 (CVal 8 (SLit 8));
mkChunk 6253264 (CVal 8 (SLit 0));
mkChunk 6253272 (CVal 8 (SOff 41 0));
mkChunk 6253280 (CImg 16);
mkChunk 6253296 (CVal 4 (SLit 1));
mkChunk 6253300 (CImg 4);
mkChunk 6253304 (CVal 8 (SLit 6253312));
mkChunk 6253312 (CImg 8);
mkChunk 6253320 (CVal 8 (SLit 570628));
mkChunk 6253328 (CImg 248);
mkChunk 6253576 (CVal 8 (SLit 466532));
mkChunk 6253584 (CImg 264);
mkChunk 6253856 (CVal 8 (SOff 1 0));
mkChunk 6253864 (CVal 1 (SLit 1));
mkChunk 6253865 (CImg 7);
mkChunk 6253872 (CVal 8 (SOff 5 0));
mkChunk 6253880 (CVal 8 (SLit 6253224));
mkChunk 6253888 (CVal 8 (SLit 248));
mkChunk 6253896 (CVal 8 (SLit 8));
mkChunk 6253904 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6253920 6253992 0 0
[ mkChunk 6253920 (CImg 48);
mkChunk 6253976 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6254920 6257136 0 0
[ mkChunk 6254920 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6257144 6258240 0 0
[ mkChunk 6257144 (CImg 8);
mkChunk 6257152 (CVal 8 (SLit 355788));
mkChunk 6257160 (CImg 1016);
mkChunk 6258176 (CVal 4 (SLit 0));
mkChunk 6258180 (CImg 4);
mkChunk 6258184 (CVal 4 (SLit 0));
mkChunk 6258188 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6258248 6262784 0 0
[ mkChunk 6258248 (CImg 4536) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
