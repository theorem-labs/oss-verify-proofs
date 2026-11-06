(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-pw/fuzz_qdisc image B by gen_ad2.py 195f6e6ef088 (port-reply start-up set startup-set-2026-10-29) from this image's 50 collected hand-off states (lib/AU/YB01.v), its atable (lib/AU/YB12.v) and Tfib_owned_static (lib/AU/YF0m.v), templates cgif_file_fuzzer YD2i.v / YD2j.v at c8557374ad2e; Requires placed in lib.Reusable / lib.AU by fuzz_knock's lib/AU at origin/ossv/recipes 88154566652 (h-small-q1) *)
(* Read from: fuzz_qdisc.asan-ubsan (reac-pw/fuzz_qdisc asan-ubsan) sha256 eb657d77bd4b27038d93f75626dcc6b37a48be09c889fda664b4f451c6602062; unstripped twin sha256 a8f38ed20eaa71da2be09efbc294ab6854786e94e1564acbf2a11cdbdf8585f1 *)
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
mkRegion None 135850 612576 0 0
[ mkChunk 135850 (CImg 476726) ].
Definition R_A1p : region :=
mkRegion None 612704 615528 0 0
[ mkChunk 612704 (CImg 2824) ].
Definition R_A1q : region :=
mkRegion None 615536 615768 0 0
[ mkChunk 615536 (CImg 232) ].
Definition R_A1r : region :=
mkRegion None 615776 615800 0 0
[ mkChunk 615776 (CImg 24) ].
Definition R_A1s : region :=
mkRegion None 615816 615904 0 0
[ mkChunk 615816 (CImg 8);
mkChunk 615824 (CImg 80) ].
Definition R_A1t : region :=
mkRegion None 615928 618496 0 0
[ mkChunk 615928 (CImg 2568) ].
Definition R_A2 : region :=
mkRegion None 618496 620024 0 0
[ mkChunk 618496 (CImg 1528) ].
Definition R_A3 : region :=
mkRegion None 630376 631216 630376 631216
[ mkChunk 630376 (CImg 840) ].
Definition R_A4 : region :=
mkRegion None 631304 631376 631304 631376
[ mkChunk 631304 (CVal 1 (SLit 1));
mkChunk 631305 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6029072 6094608 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6094608 6096812 6094608 6096812
[ mkChunk 6094608 (CImg 4);
mkChunk 6094612 (CVal 1 (SLit 0));
mkChunk 6094613 (CImg 2155);
mkChunk 6096776 (CVal 8 (SLit 6096776));
mkChunk 6096784 (CVal 8 (SLit 6096776));
mkChunk 6096792 (CVal 8 (SLit 6096776));
mkChunk 6096800 (CVal 8 (SLit 0));
mkChunk 6096808 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6096816 6096888 6096816 6096888
[ mkChunk 6096816 (CVal 4 (SLit 2));
mkChunk 6096820 (CImg 6);
mkChunk 6096826 (CVal 1 (SLit 1));
mkChunk 6096827 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6096896 6096968 0 0
[ mkChunk 6096896 (CVal 8 (SLit 6096896));
mkChunk 6096904 (CImg 24);
mkChunk 6096928 (CVal 8 (SLit 6228760));
mkChunk 6096936 (CImg 24);
mkChunk 6096960 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6097036 6097048 0 0
[ mkChunk 6097036 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6228056 6228752 6228128 6228672
[ mkChunk 6228056 (CImg 16);
mkChunk 6228072 (CVal 8 (SLit 607080));
mkChunk 6228080 (CVal 8 (SLit 0));
mkChunk 6228088 (CVal 8 (SLit 24));
mkChunk 6228096 (CVal 8 (SLit 8));
mkChunk 6228104 (CVal 8 (SLit 0));
mkChunk 6228112 (CVal 8 (SOff 41 0));
mkChunk 6228120 (CImg 16);
mkChunk 6228136 (CVal 4 (SLit 1));
mkChunk 6228140 (CImg 4);
mkChunk 6228144 (CVal 8 (SLit 6228152));
mkChunk 6228152 (CImg 8);
mkChunk 6228160 (CVal 8 (SLit 545736));
mkChunk 6228168 (CImg 248);
mkChunk 6228416 (CVal 8 (SLit 449620));
mkChunk 6228424 (CImg 264);
mkChunk 6228696 (CVal 8 (SOff 1 0));
mkChunk 6228704 (CVal 1 (SLit 1));
mkChunk 6228705 (CImg 7);
mkChunk 6228712 (CVal 8 (SOff 5 0));
mkChunk 6228720 (CVal 8 (SLit 6228064));
mkChunk 6228728 (CVal 8 (SLit 248));
mkChunk 6228736 (CVal 8 (SLit 8));
mkChunk 6228744 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6228760 6228832 0 0
[ mkChunk 6228760 (CImg 48);
mkChunk 6228816 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6229760 6231976 0 0
[ mkChunk 6229760 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6231984 6233080 0 0
[ mkChunk 6231984 (CImg 8);
mkChunk 6231992 (CVal 8 (SLit 338876));
mkChunk 6232000 (CImg 1016);
mkChunk 6233016 (CVal 4 (SLit 0));
mkChunk 6233020 (CImg 4);
mkChunk 6233024 (CVal 4 (SLit 0));
mkChunk 6233028 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6233088 6238208 0 0
[ mkChunk 6233088 (CImg 5120) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
