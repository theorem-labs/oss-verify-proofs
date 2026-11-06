(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs: generated for reac-pw/fuzz_role image A by gen_ad2.py 8a509576b937 from this image's 50 collected hand-off states (lib/A/AB01.v), its atable (lib/A/AB12.v) and Tfib_owned_static (lib/A/AF0m.v), templates proofs/cgif/cgif_file_fuzzer/lib/A/AD2i.v and A/AD2j.v at c8557374ad2e; the atable values read from atable.py 6a35bb77e745's numeral emission of the same table (gen_ad2 resolves only a Definition-form YImgTop.v, the unit's is the Notation form) *)
(* Read from: fuzz_role.asan (reac-pw/fuzz_role asan) sha256 614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; unstripped twin sha256 6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6 *)
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
mkRegion None 66376 66480 0 0
[ mkChunk 66376 (CImg 104) ].
Definition R_A1e : region :=
mkRegion None 66496 66504 0 0
[ mkChunk 66496 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66512 66632 0 0
[ mkChunk 66512 (CImg 120) ].
Definition R_A1g : region :=
mkRegion None 66696 66888 0 0
[ mkChunk 66696 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66952 118209 0 0
[ mkChunk 66952 (CImg 51257) ].
Definition R_A1i : region :=
mkRegion None 118230 134184 0 0
[ mkChunk 118230 (CImg 15954) ].
Definition R_A1j : region :=
mkRegion None 134188 134862 0 0
[ mkChunk 134188 (CImg 674) ].
Definition R_A1k : region :=
mkRegion None 134880 134894 0 0
[ mkChunk 134880 (CImg 14) ].
Definition R_A1l : region :=
mkRegion None 134912 134926 0 0
[ mkChunk 134912 (CImg 14) ].
Definition R_A1m : region :=
mkRegion None 134944 134959 0 0
[ mkChunk 134944 (CImg 15) ].
Definition R_A1n : region :=
mkRegion None 134976 134990 0 0
[ mkChunk 134976 (CImg 14) ].
Definition R_A1o : region :=
mkRegion None 135008 135027 0 0
[ mkChunk 135008 (CImg 19) ].
Definition R_A1p : region :=
mkRegion None 135072 135085 0 0
[ mkChunk 135072 (CImg 13) ].
Definition R_A1q : region :=
mkRegion None 135104 135120 0 0
[ mkChunk 135104 (CImg 16) ].
Definition R_A1r : region :=
mkRegion None 135136 135149 0 0
[ mkChunk 135136 (CImg 13) ].
Definition R_A1s : region :=
mkRegion None 135168 135224 0 0
[ mkChunk 135168 (CImg 56) ].
Definition R_A1t : region :=
mkRegion None 135264 135348 0 0
[ mkChunk 135264 (CImg 84) ].
Definition R_A1u : region :=
mkRegion None 135392 135408 0 0
[ mkChunk 135392 (CImg 16) ].
Definition R_A1v : region :=
mkRegion None 135424 135440 0 0
[ mkChunk 135424 (CImg 16) ].
Definition R_A1w : region :=
mkRegion None 135456 135470 0 0
[ mkChunk 135456 (CImg 14) ].
Definition R_A1x : region :=
mkRegion None 135488 135491 0 0
[ mkChunk 135488 (CImg 3) ].
Definition R_A1y : region :=
mkRegion None 135520 135523 0 0
[ mkChunk 135520 (CImg 3) ].
Definition R_A1z : region :=
mkRegion None 135552 135555 0 0
[ mkChunk 135552 (CImg 3) ].
Definition R_A1aa : region :=
mkRegion None 135584 135587 0 0
[ mkChunk 135584 (CImg 3) ].
Definition R_A1ab : region :=
mkRegion None 135616 135637 0 0
[ mkChunk 135616 (CImg 21) ].
Definition R_A1ac : region :=
mkRegion None 135680 135681 0 0
[ mkChunk 135680 (CImg 1) ].
Definition R_A1ad : region :=
mkRegion None 135712 135714 0 0
[ mkChunk 135712 (CImg 2) ].
Definition R_A1ae : region :=
mkRegion None 135744 135747 0 0
[ mkChunk 135744 (CImg 3) ].
Definition R_A1af : region :=
mkRegion None 135776 135779 0 0
[ mkChunk 135776 (CImg 3) ].
Definition R_A1ag : region :=
mkRegion None 135808 135811 0 0
[ mkChunk 135808 (CImg 3) ].
Definition R_A1ah : region :=
mkRegion None 135840 135843 0 0
[ mkChunk 135840 (CImg 3) ].
Definition R_A1ai : region :=
mkRegion None 135872 135875 0 0
[ mkChunk 135872 (CImg 3) ].
Definition R_A1aj : region :=
mkRegion None 135904 135908 0 0
[ mkChunk 135904 (CImg 4) ].
Definition R_A1ak : region :=
mkRegion None 135936 135958 0 0
[ mkChunk 135936 (CImg 22) ].
Definition R_A1al : region :=
mkRegion None 136000 136008 0 0
[ mkChunk 136000 (CImg 8) ].
Definition R_A1am : region :=
mkRegion None 136032 136036 0 0
[ mkChunk 136032 (CImg 4) ].
Definition R_A1an : region :=
mkRegion None 136064 136069 0 0
[ mkChunk 136064 (CImg 5) ].
Definition R_A1ao : region :=
mkRegion None 136096 136100 0 0
[ mkChunk 136096 (CImg 4) ].
Definition R_A1ap : region :=
mkRegion None 136128 136134 0 0
[ mkChunk 136128 (CImg 6) ].
Definition R_A1aq : region :=
mkRegion None 136160 136170 0 0
[ mkChunk 136160 (CImg 10) ].
Definition R_A1ar : region :=
mkRegion None 136192 136198 0 0
[ mkChunk 136192 (CImg 6) ].
Definition R_A1as : region :=
mkRegion None 136224 136226 0 0
[ mkChunk 136224 (CImg 2) ].
Definition R_A1at : region :=
mkRegion None 136256 136281 0 0
[ mkChunk 136256 (CImg 25) ].
Definition R_A1au : region :=
mkRegion None 136320 136328 0 0
[ mkChunk 136320 (CImg 8) ].
Definition R_A1av : region :=
mkRegion None 136352 136357 0 0
[ mkChunk 136352 (CImg 5) ].
Definition R_A1aw : region :=
mkRegion None 136384 136394 0 0
[ mkChunk 136384 (CImg 10) ].
Definition R_A1ax : region :=
mkRegion None 136416 136453 0 0
[ mkChunk 136416 (CImg 37) ].
Definition R_A1ay : region :=
mkRegion None 136480 136490 0 0
[ mkChunk 136480 (CImg 10) ].
Definition R_A1az : region :=
mkRegion None 136512 136537 0 0
[ mkChunk 136512 (CImg 25) ].
Definition R_A1ba : region :=
mkRegion None 136576 136584 0 0
[ mkChunk 136576 (CImg 8) ].
Definition R_A1bb : region :=
mkRegion None 136608 136622 0 0
[ mkChunk 136608 (CImg 14) ].
Definition R_A1bc : region :=
mkRegion None 136640 138064 0 0
[ mkChunk 136640 (CImg 1424) ].
Definition R_A1bd : region :=
mkRegion None 138068 138164 0 0
[ mkChunk 138068 (CImg 96) ].
Definition R_A1be : region :=
mkRegion None 138166 632136 0 0
[ mkChunk 138166 (CImg 493970) ].
Definition R_A1bf : region :=
mkRegion None 632192 632304 0 0
[ mkChunk 632192 (CImg 112) ].
Definition R_A1bg : region :=
mkRegion None 632352 632416 0 0
[ mkChunk 632352 (CImg 64) ].
Definition R_A1bh : region :=
mkRegion None 632448 632464 0 0
[ mkChunk 632448 (CImg 16) ].
Definition R_A1bi : region :=
mkRegion None 632480 632848 0 0
[ mkChunk 632480 (CImg 368) ].
Definition R_A1bj : region :=
mkRegion None 632976 635800 0 0
[ mkChunk 632976 (CImg 2824) ].
Definition R_A1bk : region :=
mkRegion None 635808 636040 0 0
[ mkChunk 635808 (CImg 232) ].
Definition R_A1bl : region :=
mkRegion None 636048 636072 0 0
[ mkChunk 636048 (CImg 24) ].
Definition R_A1bm : region :=
mkRegion None 636088 636176 0 0
[ mkChunk 636088 (CImg 8);
mkChunk 636096 (CImg 80) ].
Definition R_A1bn : region :=
mkRegion None 636200 638976 0 0
[ mkChunk 636200 (CImg 2776) ].
Definition R_A2 : region :=
mkRegion None 638976 640296 0 0
[ mkChunk 638976 (CImg 1320) ].
Definition R_A3 : region :=
mkRegion None 650648 651488 650648 651488
[ mkChunk 650648 (CImg 840) ].
Definition R_A4 : region :=
mkRegion None 654664 654736 654664 654736
[ mkChunk 654664 (CVal 1 (SLit 1));
mkChunk 654665 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6052432 6117968 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6117968 6120172 6117968 6120172
[ mkChunk 6117968 (CImg 4);
mkChunk 6117972 (CVal 1 (SLit 0));
mkChunk 6117973 (CImg 2155);
mkChunk 6120136 (CVal 8 (SLit 6120136));
mkChunk 6120144 (CVal 8 (SLit 6120136));
mkChunk 6120152 (CVal 8 (SLit 6120136));
mkChunk 6120160 (CVal 8 (SLit 0));
mkChunk 6120168 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6120176 6120248 6120176 6120248
[ mkChunk 6120176 (CVal 4 (SLit 2));
mkChunk 6120180 (CImg 6);
mkChunk 6120186 (CVal 1 (SLit 1));
mkChunk 6120187 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6120256 6120328 0 0
[ mkChunk 6120256 (CVal 8 (SLit 6120256));
mkChunk 6120264 (CImg 24);
mkChunk 6120288 (CVal 8 (SLit 6252120));
mkChunk 6120296 (CImg 24);
mkChunk 6120320 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6120396 6120408 0 0
[ mkChunk 6120396 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6251416 6252112 6251488 6252032
[ mkChunk 6251416 (CImg 16);
mkChunk 6251432 (CVal 8 (SLit 626920));
mkChunk 6251440 (CVal 8 (SLit 0));
mkChunk 6251448 (CVal 8 (SLit 24));
mkChunk 6251456 (CVal 8 (SLit 8));
mkChunk 6251464 (CVal 8 (SLit 0));
mkChunk 6251472 (CVal 8 (SOff 41 0));
mkChunk 6251480 (CImg 16);
mkChunk 6251496 (CVal 4 (SLit 1));
mkChunk 6251500 (CImg 4);
mkChunk 6251504 (CVal 8 (SLit 6251512));
mkChunk 6251512 (CImg 8);
mkChunk 6251520 (CVal 8 (SLit 567844));
mkChunk 6251528 (CImg 248);
mkChunk 6251776 (CVal 8 (SLit 456008));
mkChunk 6251784 (CImg 264);
mkChunk 6252056 (CVal 8 (SOff 1 0));
mkChunk 6252064 (CVal 1 (SLit 1));
mkChunk 6252065 (CImg 7);
mkChunk 6252072 (CVal 8 (SOff 5 0));
mkChunk 6252080 (CVal 8 (SLit 6251424));
mkChunk 6252088 (CVal 8 (SLit 248));
mkChunk 6252096 (CVal 8 (SLit 8));
mkChunk 6252104 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6252120 6252192 0 0
[ mkChunk 6252120 (CImg 48);
mkChunk 6252176 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6253120 6255336 0 0
[ mkChunk 6253120 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6255344 6256440 0 0
[ mkChunk 6255344 (CImg 8);
mkChunk 6255352 (CVal 8 (SLit 345264));
mkChunk 6255360 (CImg 1016);
mkChunk 6256376 (CVal 4 (SLit 0));
mkChunk 6256380 (CImg 4);
mkChunk 6256384 (CVal 4 (SLit 0));
mkChunk 6256388 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6256448 6258688 0 0
[ mkChunk 6256448 (CImg 2240) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A1bh; R_A1bi; R_A1bj; R_A1bk; R_A1bl; R_A1bm; R_A1bn; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
