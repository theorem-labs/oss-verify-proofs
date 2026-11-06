(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs: generated for reac-pw/fuzz_role image B by gen_ad2.py 8a509576b937 from this image's 50 collected hand-off states (lib/AU/YB01.v), its atable (lib/AU/YB12.v) and Tfib_owned_static (lib/AU/YF0m.v), templates proofs/cgif/cgif_file_fuzzer/lib/YD2i.v and YD2j.v at c8557374ad2e; Requires placed in lib.Reusable / lib.AU by proofs/libreac/fuzz_knock/lib/AU at origin/ossv/recipes 88154566652; the atable values read from atable.py 6a35bb77e745's numeral emission of the same table (gen_ad2 resolves only a Definition-form YImgTop.v, the unit's image-B layer takes the Notation form) *)
(* Read from: fuzz_role.asan-ubsan (reac-pw/fuzz_role asan-ubsan) sha256 b255d4935da5af137a3967dbe33380ea43be8e78bfe05d1e356e0a2be8a69ff0; unstripped twin sha256 dc791783f32962615e18a5f5cffae758ba56eb5dc87f70913c3579b101b4406a *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP09.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 66280 0 0
[ mkChunk 65536 (CImg 744) ].
Definition R_A1b : region :=
mkRegion None 66288 66312 0 0
[ mkChunk 66288 (CImg 24) ].
Definition R_A1c : region :=
mkRegion None 66320 66368 0 0
[ mkChunk 66320 (CImg 48) ].
Definition R_A1d : region :=
mkRegion None 66376 66488 0 0
[ mkChunk 66376 (CImg 112) ].
Definition R_A1e : region :=
mkRegion None 66504 66512 0 0
[ mkChunk 66504 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66520 66648 0 0
[ mkChunk 66520 (CImg 128) ].
Definition R_A1g : region :=
mkRegion None 66712 66904 0 0
[ mkChunk 66712 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66968 118271 0 0
[ mkChunk 66968 (CImg 51303) ].
Definition R_A1i : region :=
mkRegion None 118292 134248 0 0
[ mkChunk 118292 (CImg 15956) ].
Definition R_A1j : region :=
mkRegion None 134252 134926 0 0
[ mkChunk 134252 (CImg 674) ].
Definition R_A1k : region :=
mkRegion None 134944 134958 0 0
[ mkChunk 134944 (CImg 14) ].
Definition R_A1l : region :=
mkRegion None 134976 134990 0 0
[ mkChunk 134976 (CImg 14) ].
Definition R_A1m : region :=
mkRegion None 135008 135023 0 0
[ mkChunk 135008 (CImg 15) ].
Definition R_A1n : region :=
mkRegion None 135040 135054 0 0
[ mkChunk 135040 (CImg 14) ].
Definition R_A1o : region :=
mkRegion None 135072 135091 0 0
[ mkChunk 135072 (CImg 19) ].
Definition R_A1p : region :=
mkRegion None 135136 135149 0 0
[ mkChunk 135136 (CImg 13) ].
Definition R_A1q : region :=
mkRegion None 135168 135184 0 0
[ mkChunk 135168 (CImg 16) ].
Definition R_A1r : region :=
mkRegion None 135200 135213 0 0
[ mkChunk 135200 (CImg 13) ].
Definition R_A1s : region :=
mkRegion None 135232 135288 0 0
[ mkChunk 135232 (CImg 56) ].
Definition R_A1t : region :=
mkRegion None 135328 135412 0 0
[ mkChunk 135328 (CImg 84) ].
Definition R_A1u : region :=
mkRegion None 135456 135472 0 0
[ mkChunk 135456 (CImg 16) ].
Definition R_A1v : region :=
mkRegion None 135488 135504 0 0
[ mkChunk 135488 (CImg 16) ].
Definition R_A1w : region :=
mkRegion None 135520 135534 0 0
[ mkChunk 135520 (CImg 14) ].
Definition R_A1x : region :=
mkRegion None 135552 135555 0 0
[ mkChunk 135552 (CImg 3) ].
Definition R_A1y : region :=
mkRegion None 135584 135587 0 0
[ mkChunk 135584 (CImg 3) ].
Definition R_A1z : region :=
mkRegion None 135616 135619 0 0
[ mkChunk 135616 (CImg 3) ].
Definition R_A1aa : region :=
mkRegion None 135648 135651 0 0
[ mkChunk 135648 (CImg 3) ].
Definition R_A1ab : region :=
mkRegion None 135680 135701 0 0
[ mkChunk 135680 (CImg 21) ].
Definition R_A1ac : region :=
mkRegion None 135744 135745 0 0
[ mkChunk 135744 (CImg 1) ].
Definition R_A1ad : region :=
mkRegion None 135776 135778 0 0
[ mkChunk 135776 (CImg 2) ].
Definition R_A1ae : region :=
mkRegion None 135808 135811 0 0
[ mkChunk 135808 (CImg 3) ].
Definition R_A1af : region :=
mkRegion None 135840 135843 0 0
[ mkChunk 135840 (CImg 3) ].
Definition R_A1ag : region :=
mkRegion None 135872 135875 0 0
[ mkChunk 135872 (CImg 3) ].
Definition R_A1ah : region :=
mkRegion None 135904 135907 0 0
[ mkChunk 135904 (CImg 3) ].
Definition R_A1ai : region :=
mkRegion None 135936 135939 0 0
[ mkChunk 135936 (CImg 3) ].
Definition R_A1aj : region :=
mkRegion None 135968 135972 0 0
[ mkChunk 135968 (CImg 4) ].
Definition R_A1ak : region :=
mkRegion None 136000 136022 0 0
[ mkChunk 136000 (CImg 22) ].
Definition R_A1al : region :=
mkRegion None 136064 136072 0 0
[ mkChunk 136064 (CImg 8) ].
Definition R_A1am : region :=
mkRegion None 136096 136100 0 0
[ mkChunk 136096 (CImg 4) ].
Definition R_A1an : region :=
mkRegion None 136128 136133 0 0
[ mkChunk 136128 (CImg 5) ].
Definition R_A1ao : region :=
mkRegion None 136160 136164 0 0
[ mkChunk 136160 (CImg 4) ].
Definition R_A1ap : region :=
mkRegion None 136192 136198 0 0
[ mkChunk 136192 (CImg 6) ].
Definition R_A1aq : region :=
mkRegion None 136224 136234 0 0
[ mkChunk 136224 (CImg 10) ].
Definition R_A1ar : region :=
mkRegion None 136256 136262 0 0
[ mkChunk 136256 (CImg 6) ].
Definition R_A1as : region :=
mkRegion None 136288 136290 0 0
[ mkChunk 136288 (CImg 2) ].
Definition R_A1at : region :=
mkRegion None 136320 136345 0 0
[ mkChunk 136320 (CImg 25) ].
Definition R_A1au : region :=
mkRegion None 136384 136392 0 0
[ mkChunk 136384 (CImg 8) ].
Definition R_A1av : region :=
mkRegion None 136416 136421 0 0
[ mkChunk 136416 (CImg 5) ].
Definition R_A1aw : region :=
mkRegion None 136448 136458 0 0
[ mkChunk 136448 (CImg 10) ].
Definition R_A1ax : region :=
mkRegion None 136480 136517 0 0
[ mkChunk 136480 (CImg 37) ].
Definition R_A1ay : region :=
mkRegion None 136544 136554 0 0
[ mkChunk 136544 (CImg 10) ].
Definition R_A1az : region :=
mkRegion None 136576 136601 0 0
[ mkChunk 136576 (CImg 25) ].
Definition R_A1ba : region :=
mkRegion None 136640 136648 0 0
[ mkChunk 136640 (CImg 8) ].
Definition R_A1bb : region :=
mkRegion None 136672 136686 0 0
[ mkChunk 136672 (CImg 14) ].
Definition R_A1bc : region :=
mkRegion None 136704 138128 0 0
[ mkChunk 136704 (CImg 1424) ].
Definition R_A1bd : region :=
mkRegion None 138132 138228 0 0
[ mkChunk 138132 (CImg 96) ].
Definition R_A1be : region :=
mkRegion None 138230 632808 0 0
[ mkChunk 138230 (CImg 494578) ].
Definition R_A1bf : region :=
mkRegion None 632864 632976 0 0
[ mkChunk 632864 (CImg 112) ].
Definition R_A1bg : region :=
mkRegion None 633024 633088 0 0
[ mkChunk 633024 (CImg 64) ].
Definition R_A1bh : region :=
mkRegion None 633120 633136 0 0
[ mkChunk 633120 (CImg 16) ].
Definition R_A1bi : region :=
mkRegion None 633152 633520 0 0
[ mkChunk 633152 (CImg 368) ].
Definition R_A1bj : region :=
mkRegion None 633648 636472 0 0
[ mkChunk 633648 (CImg 2824) ].
Definition R_A1bk : region :=
mkRegion None 636480 636712 0 0
[ mkChunk 636480 (CImg 232) ].
Definition R_A1bl : region :=
mkRegion None 636720 636744 0 0
[ mkChunk 636720 (CImg 24) ].
Definition R_A1bm : region :=
mkRegion None 636760 636848 0 0
[ mkChunk 636760 (CImg 8);
mkChunk 636768 (CImg 80) ].
Definition R_A1bn : region :=
mkRegion None 636872 638976 0 0
[ mkChunk 636872 (CImg 2104) ].
Definition R_A2 : region :=
mkRegion None 638976 640968 0 0
[ mkChunk 638976 (CImg 1992) ].
Definition R_A3 : region :=
mkRegion None 651320 652160 651320 652160
[ mkChunk 651320 (CImg 840) ].
Definition R_A4 : region :=
mkRegion None 655304 655376 655304 655376
[ mkChunk 655304 (CVal 1 (SLit 1));
mkChunk 655305 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6053072 6118608 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6118608 6120812 6118608 6120812
[ mkChunk 6118608 (CImg 4);
mkChunk 6118612 (CVal 1 (SLit 0));
mkChunk 6118613 (CImg 2155);
mkChunk 6120776 (CVal 8 (SLit 6120776));
mkChunk 6120784 (CVal 8 (SLit 6120776));
mkChunk 6120792 (CVal 8 (SLit 6120776));
mkChunk 6120800 (CVal 8 (SLit 0));
mkChunk 6120808 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6120816 6120888 6120816 6120888
[ mkChunk 6120816 (CVal 4 (SLit 2));
mkChunk 6120820 (CImg 6);
mkChunk 6120826 (CVal 1 (SLit 1));
mkChunk 6120827 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6120896 6120968 0 0
[ mkChunk 6120896 (CVal 8 (SLit 6120896));
mkChunk 6120904 (CImg 24);
mkChunk 6120928 (CVal 8 (SLit 6252760));
mkChunk 6120936 (CImg 24);
mkChunk 6120960 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6121036 6121048 0 0
[ mkChunk 6121036 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6252056 6252752 6252128 6252672
[ mkChunk 6252056 (CImg 16);
mkChunk 6252072 (CVal 8 (SLit 627592));
mkChunk 6252080 (CVal 8 (SLit 0));
mkChunk 6252088 (CVal 8 (SLit 24));
mkChunk 6252096 (CVal 8 (SLit 8));
mkChunk 6252104 (CVal 8 (SLit 0));
mkChunk 6252112 (CVal 8 (SOff 41 0));
mkChunk 6252120 (CImg 16);
mkChunk 6252136 (CVal 4 (SLit 1));
mkChunk 6252140 (CImg 4);
mkChunk 6252144 (CVal 8 (SLit 6252152));
mkChunk 6252152 (CImg 8);
mkChunk 6252160 (CVal 8 (SLit 568516));
mkChunk 6252168 (CImg 248);
mkChunk 6252416 (CVal 8 (SLit 456160));
mkChunk 6252424 (CImg 264);
mkChunk 6252696 (CVal 8 (SOff 1 0));
mkChunk 6252704 (CVal 1 (SLit 1));
mkChunk 6252705 (CImg 7);
mkChunk 6252712 (CVal 8 (SOff 5 0));
mkChunk 6252720 (CVal 8 (SLit 6252064));
mkChunk 6252728 (CVal 8 (SLit 248));
mkChunk 6252736 (CVal 8 (SLit 8));
mkChunk 6252744 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6252760 6252832 0 0
[ mkChunk 6252760 (CImg 48);
mkChunk 6252816 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6253760 6255976 0 0
[ mkChunk 6253760 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6255984 6257080 0 0
[ mkChunk 6255984 (CImg 8);
mkChunk 6255992 (CVal 8 (SLit 345416));
mkChunk 6256000 (CImg 1016);
mkChunk 6257016 (CVal 4 (SLit 0));
mkChunk 6257020 (CImg 4);
mkChunk 6257024 (CVal 4 (SLit 0));
mkChunk 6257028 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6257088 6258688 0 0
[ mkChunk 6257088 (CImg 1600) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A1bh; R_A1bi; R_A1bj; R_A1bk; R_A1bl; R_A1bm; R_A1bn; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
