(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-pw/fuzz_rate image B by gen_ad2.py 3665ff2a7926 from this image's 50 collected hand-off states (lib/AU/YB01.v), its atable (lib/AU/YB12.v, read through atable.py e88affcf0526's numeral emission of the same table) and Tfib_owned_static (lib/AU/YF0m.v), templates cgif_file_fuzzer YD2i.v / YD2j.v at c8557374ad2e; Requires placed in lib.Reusable / lib.AU by this tree's lib/Reusable *)
(* Read from: fuzz_rate.asan-ubsan (reac-pw/fuzz_rate asan-ubsan) sha256 c30584a7214902c43e35abebe35194418b7fdefacb6e7ed16fe0492228ec1d14; unstripped twin sha256 a1e5fa55ae27e657ea2719297ec4c037110f10fa9047c3ea7bb6ea7fcb358cb1 *)
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_rate.lib.Reusable Require Import YP0m YP09.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 66280 0 0
[ mkChunk 65536 (CImg 744) ].
Definition R_A1b : region :=
mkRegion None 66288 66312 0 0
[ mkChunk 66288 (CImg 24) ].
Definition R_A1c : region :=
mkRegion None 66320 66376 0 0
[ mkChunk 66320 (CImg 56) ].
Definition R_A1d : region :=
mkRegion None 66384 66496 0 0
[ mkChunk 66384 (CImg 112) ].
Definition R_A1e : region :=
mkRegion None 66512 66520 0 0
[ mkChunk 66512 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66528 66656 0 0
[ mkChunk 66528 (CImg 128) ].
Definition R_A1g : region :=
mkRegion None 66720 66912 0 0
[ mkChunk 66720 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66976 118428 0 0
[ mkChunk 66976 (CImg 51452) ].
Definition R_A1i : region :=
mkRegion None 118449 134404 0 0
[ mkChunk 118449 (CImg 15955) ].
Definition R_A1j : region :=
mkRegion None 134408 135086 0 0
[ mkChunk 134408 (CImg 678) ].
Definition R_A1k : region :=
mkRegion None 135104 135118 0 0
[ mkChunk 135104 (CImg 14) ].
Definition R_A1l : region :=
mkRegion None 135136 135150 0 0
[ mkChunk 135136 (CImg 14) ].
Definition R_A1m : region :=
mkRegion None 135168 135183 0 0
[ mkChunk 135168 (CImg 15) ].
Definition R_A1n : region :=
mkRegion None 135200 135214 0 0
[ mkChunk 135200 (CImg 14) ].
Definition R_A1o : region :=
mkRegion None 135232 135251 0 0
[ mkChunk 135232 (CImg 19) ].
Definition R_A1p : region :=
mkRegion None 135296 135309 0 0
[ mkChunk 135296 (CImg 13) ].
Definition R_A1q : region :=
mkRegion None 135328 135344 0 0
[ mkChunk 135328 (CImg 16) ].
Definition R_A1r : region :=
mkRegion None 135360 135373 0 0
[ mkChunk 135360 (CImg 13) ].
Definition R_A1s : region :=
mkRegion None 135392 135448 0 0
[ mkChunk 135392 (CImg 56) ].
Definition R_A1t : region :=
mkRegion None 135488 135572 0 0
[ mkChunk 135488 (CImg 84) ].
Definition R_A1u : region :=
mkRegion None 135616 135632 0 0
[ mkChunk 135616 (CImg 16) ].
Definition R_A1v : region :=
mkRegion None 135648 135664 0 0
[ mkChunk 135648 (CImg 16) ].
Definition R_A1w : region :=
mkRegion None 135680 135694 0 0
[ mkChunk 135680 (CImg 14) ].
Definition R_A1x : region :=
mkRegion None 135712 135715 0 0
[ mkChunk 135712 (CImg 3) ].
Definition R_A1y : region :=
mkRegion None 135744 135747 0 0
[ mkChunk 135744 (CImg 3) ].
Definition R_A1z : region :=
mkRegion None 135776 135779 0 0
[ mkChunk 135776 (CImg 3) ].
Definition R_A1aa : region :=
mkRegion None 135808 135811 0 0
[ mkChunk 135808 (CImg 3) ].
Definition R_A1ab : region :=
mkRegion None 135840 135861 0 0
[ mkChunk 135840 (CImg 21) ].
Definition R_A1ac : region :=
mkRegion None 135904 135905 0 0
[ mkChunk 135904 (CImg 1) ].
Definition R_A1ad : region :=
mkRegion None 135936 135938 0 0
[ mkChunk 135936 (CImg 2) ].
Definition R_A1ae : region :=
mkRegion None 135968 135971 0 0
[ mkChunk 135968 (CImg 3) ].
Definition R_A1af : region :=
mkRegion None 136000 136003 0 0
[ mkChunk 136000 (CImg 3) ].
Definition R_A1ag : region :=
mkRegion None 136032 136035 0 0
[ mkChunk 136032 (CImg 3) ].
Definition R_A1ah : region :=
mkRegion None 136064 136067 0 0
[ mkChunk 136064 (CImg 3) ].
Definition R_A1ai : region :=
mkRegion None 136096 136099 0 0
[ mkChunk 136096 (CImg 3) ].
Definition R_A1aj : region :=
mkRegion None 136128 136132 0 0
[ mkChunk 136128 (CImg 4) ].
Definition R_A1ak : region :=
mkRegion None 136160 136182 0 0
[ mkChunk 136160 (CImg 22) ].
Definition R_A1al : region :=
mkRegion None 136224 136232 0 0
[ mkChunk 136224 (CImg 8) ].
Definition R_A1am : region :=
mkRegion None 136256 136260 0 0
[ mkChunk 136256 (CImg 4) ].
Definition R_A1an : region :=
mkRegion None 136288 136293 0 0
[ mkChunk 136288 (CImg 5) ].
Definition R_A1ao : region :=
mkRegion None 136320 136324 0 0
[ mkChunk 136320 (CImg 4) ].
Definition R_A1ap : region :=
mkRegion None 136352 136358 0 0
[ mkChunk 136352 (CImg 6) ].
Definition R_A1aq : region :=
mkRegion None 136384 136394 0 0
[ mkChunk 136384 (CImg 10) ].
Definition R_A1ar : region :=
mkRegion None 136416 136422 0 0
[ mkChunk 136416 (CImg 6) ].
Definition R_A1as : region :=
mkRegion None 136448 136450 0 0
[ mkChunk 136448 (CImg 2) ].
Definition R_A1at : region :=
mkRegion None 136480 136492 0 0
[ mkChunk 136480 (CImg 12) ].
Definition R_A1au : region :=
mkRegion None 136512 136523 0 0
[ mkChunk 136512 (CImg 11) ].
Definition R_A1av : region :=
mkRegion None 136544 136557 0 0
[ mkChunk 136544 (CImg 13) ].
Definition R_A1aw : region :=
mkRegion None 136576 136587 0 0
[ mkChunk 136576 (CImg 11) ].
Definition R_A1ax : region :=
mkRegion None 136608 136618 0 0
[ mkChunk 136608 (CImg 10) ].
Definition R_A1ay : region :=
mkRegion None 136640 136645 0 0
[ mkChunk 136640 (CImg 5) ].
Definition R_A1az : region :=
mkRegion None 136672 136709 0 0
[ mkChunk 136672 (CImg 37) ].
Definition R_A1ba : region :=
mkRegion None 136736 136747 0 0
[ mkChunk 136736 (CImg 11) ].
Definition R_A1bb : region :=
mkRegion None 136768 136781 0 0
[ mkChunk 136768 (CImg 13) ].
Definition R_A1bc : region :=
mkRegion None 136800 136811 0 0
[ mkChunk 136800 (CImg 11) ].
Definition R_A1bd : region :=
mkRegion None 136832 136842 0 0
[ mkChunk 136832 (CImg 10) ].
Definition R_A1be : region :=
mkRegion None 136864 136876 0 0
[ mkChunk 136864 (CImg 12) ].
Definition R_A1bf : region :=
mkRegion None 136896 136901 0 0
[ mkChunk 136896 (CImg 5) ].
Definition R_A1bg : region :=
mkRegion None 136928 136930 0 0
[ mkChunk 136928 (CImg 2) ].
Definition R_A1bh : region :=
mkRegion None 136960 136961 0 0
[ mkChunk 136960 (CImg 1) ].
Definition R_A1bi : region :=
mkRegion None 136992 137006 0 0
[ mkChunk 136992 (CImg 14) ].
Definition R_A1bj : region :=
mkRegion None 137024 138448 0 0
[ mkChunk 137024 (CImg 1424) ].
Definition R_A1bk : region :=
mkRegion None 138452 138548 0 0
[ mkChunk 138452 (CImg 96) ].
Definition R_A1bl : region :=
mkRegion None 138550 638472 0 0
[ mkChunk 138550 (CImg 499922) ].
Definition R_A1bm : region :=
mkRegion None 638528 638640 0 0
[ mkChunk 638528 (CImg 112) ].
Definition R_A1bn : region :=
mkRegion None 638688 638752 0 0
[ mkChunk 638688 (CImg 64) ].
Definition R_A1bo : region :=
mkRegion None 638784 638816 0 0
[ mkChunk 638784 (CImg 32) ].
Definition R_A1bp : region :=
mkRegion None 638848 638888 0 0
[ mkChunk 638848 (CImg 40) ].
Definition R_A1bq : region :=
mkRegion None 638944 639312 0 0
[ mkChunk 638944 (CImg 368) ].
Definition R_A1br : region :=
mkRegion None 639440 642264 0 0
[ mkChunk 639440 (CImg 2824) ].
Definition R_A1bs : region :=
mkRegion None 642272 642504 0 0
[ mkChunk 642272 (CImg 232) ].
Definition R_A1bt : region :=
mkRegion None 642512 642536 0 0
[ mkChunk 642512 (CImg 24) ].
Definition R_A1bu : region :=
mkRegion None 642552 642640 0 0
[ mkChunk 642552 (CImg 8);
mkChunk 642560 (CImg 80) ].
Definition R_A1bv : region :=
mkRegion None 642664 643072 0 0
[ mkChunk 642664 (CImg 408) ].
Definition R_A2 : region :=
mkRegion None 643072 646760 0 0
[ mkChunk 643072 (CImg 3688) ].
Definition R_A3 : region :=
mkRegion None 657120 657952 657120 657952
[ mkChunk 657120 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 661640 661712 661640 661712
[ mkChunk 661640 (CVal 1 (SLit 1));
mkChunk 661641 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6059408 6124944 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6124944 6127148 6124944 6127148
[ mkChunk 6124944 (CImg 4);
mkChunk 6124948 (CVal 1 (SLit 0));
mkChunk 6124949 (CImg 2155);
mkChunk 6127112 (CVal 8 (SLit 6127112));
mkChunk 6127120 (CVal 8 (SLit 6127112));
mkChunk 6127128 (CVal 8 (SLit 6127112));
mkChunk 6127136 (CVal 8 (SLit 0));
mkChunk 6127144 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6127152 6127224 6127152 6127224
[ mkChunk 6127152 (CVal 4 (SLit 2));
mkChunk 6127156 (CImg 6);
mkChunk 6127162 (CVal 1 (SLit 1));
mkChunk 6127163 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6127232 6127304 0 0
[ mkChunk 6127232 (CVal 8 (SLit 6127232));
mkChunk 6127240 (CImg 24);
mkChunk 6127264 (CVal 8 (SLit 6259096));
mkChunk 6127272 (CImg 24);
mkChunk 6127296 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6127372 6127384 0 0
[ mkChunk 6127372 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6258392 6259088 6258464 6259008
[ mkChunk 6258392 (CImg 16);
mkChunk 6258408 (CVal 8 (SLit 633240));
mkChunk 6258416 (CVal 8 (SLit 0));
mkChunk 6258424 (CVal 8 (SLit 24));
mkChunk 6258432 (CVal 8 (SLit 8));
mkChunk 6258440 (CVal 8 (SLit 0));
mkChunk 6258448 (CVal 8 (SOff 41 0));
mkChunk 6258456 (CImg 16);
mkChunk 6258472 (CVal 4 (SLit 1));
mkChunk 6258476 (CImg 4);
mkChunk 6258480 (CVal 8 (SLit 6258488));
mkChunk 6258488 (CImg 8);
mkChunk 6258496 (CVal 8 (SLit 574160));
mkChunk 6258504 (CImg 248);
mkChunk 6258752 (CVal 8 (SLit 458028));
mkChunk 6258760 (CImg 264);
mkChunk 6259032 (CVal 8 (SOff 1 0));
mkChunk 6259040 (CVal 1 (SLit 1));
mkChunk 6259041 (CImg 7);
mkChunk 6259048 (CVal 8 (SOff 5 0));
mkChunk 6259056 (CVal 8 (SLit 6258400));
mkChunk 6259064 (CVal 8 (SLit 248));
mkChunk 6259072 (CVal 8 (SLit 8));
mkChunk 6259080 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6259096 6259168 0 0
[ mkChunk 6259096 (CImg 48);
mkChunk 6259152 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6260096 6262312 0 0
[ mkChunk 6260096 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6262320 6263416 0 0
[ mkChunk 6262320 (CImg 8);
mkChunk 6262328 (CVal 8 (SLit 347284));
mkChunk 6262336 (CImg 1016);
mkChunk 6263352 (CVal 4 (SLit 0));
mkChunk 6263356 (CImg 4);
mkChunk 6263360 (CVal 4 (SLit 0));
mkChunk 6263364 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6263424 6266880 0 0
[ mkChunk 6263424 (CImg 3456) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A1bh; R_A1bi; R_A1bj; R_A1bk; R_A1bl; R_A1bm; R_A1bn; R_A1bo; R_A1bp; R_A1bq; R_A1br; R_A1bs; R_A1bt; R_A1bu; R_A1bv; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
