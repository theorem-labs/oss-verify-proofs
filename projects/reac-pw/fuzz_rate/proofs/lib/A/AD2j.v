(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-pw/fuzz_rate image A by gen_ad2.py 3665ff2a7926 from this image's 50 collected hand-off states (lib/A/AB01.v), its atable (lib/A/AB12.v, read through atable.py e88affcf0526's numeral emission of the same table) and Tfib_owned_static (lib/A/AF0m.v), templates proofs/cgif/cgif_file_fuzzer/lib/A/AD2i.v and A/AD2j.v at c8557374ad2e *)
(* Read from: fuzz_rate.asan (reac-pw/fuzz_rate asan) sha256 22bc8613d780c9a99353dc86368f9401311ef5c8358882651217836298529b6a; unstripped twin sha256 0d508f2c65c249840b6c8fe3c1960824f2548b175c23583632f06bb7956458c3 *)
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
mkRegion None 66384 66488 0 0
[ mkChunk 66384 (CImg 104) ].
Definition R_A1e : region :=
mkRegion None 66504 66512 0 0
[ mkChunk 66504 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66520 66640 0 0
[ mkChunk 66520 (CImg 120) ].
Definition R_A1g : region :=
mkRegion None 66704 66896 0 0
[ mkChunk 66704 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66960 118283 0 0
[ mkChunk 66960 (CImg 51323) ].
Definition R_A1i : region :=
mkRegion None 118304 134392 0 0
[ mkChunk 118304 (CImg 16088) ].
Definition R_A1j : region :=
mkRegion None 134396 135086 0 0
[ mkChunk 134396 (CImg 690) ].
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
mkRegion None 138550 637704 0 0
[ mkChunk 138550 (CImg 499154) ].
Definition R_A1bm : region :=
mkRegion None 637760 637872 0 0
[ mkChunk 637760 (CImg 112) ].
Definition R_A1bn : region :=
mkRegion None 637920 637984 0 0
[ mkChunk 637920 (CImg 64) ].
Definition R_A1bo : region :=
mkRegion None 638016 638048 0 0
[ mkChunk 638016 (CImg 32) ].
Definition R_A1bp : region :=
mkRegion None 638080 638120 0 0
[ mkChunk 638080 (CImg 40) ].
Definition R_A1bq : region :=
mkRegion None 638176 638544 0 0
[ mkChunk 638176 (CImg 368) ].
Definition R_A1br : region :=
mkRegion None 638672 641496 0 0
[ mkChunk 638672 (CImg 2824) ].
Definition R_A1bs : region :=
mkRegion None 641504 641736 0 0
[ mkChunk 641504 (CImg 232) ].
Definition R_A1bt : region :=
mkRegion None 641744 641768 0 0
[ mkChunk 641744 (CImg 24) ].
Definition R_A1bu : region :=
mkRegion None 641784 641872 0 0
[ mkChunk 641784 (CImg 8);
mkChunk 641792 (CImg 80) ].
Definition R_A1bv : region :=
mkRegion None 641896 643072 0 0
[ mkChunk 641896 (CImg 1176) ].
Definition R_A2 : region :=
mkRegion None 643072 645992 0 0
[ mkChunk 643072 (CImg 2920) ].
Definition R_A3 : region :=
mkRegion None 656352 657184 656352 657184
[ mkChunk 656352 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 660872 660944 660872 660944
[ mkChunk 660872 (CVal 1 (SLit 1));
mkChunk 660873 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6058640 6124176 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6124176 6126380 6124176 6126380
[ mkChunk 6124176 (CImg 4);
mkChunk 6124180 (CVal 1 (SLit 0));
mkChunk 6124181 (CImg 2155);
mkChunk 6126344 (CVal 8 (SLit 6126344));
mkChunk 6126352 (CVal 8 (SLit 6126344));
mkChunk 6126360 (CVal 8 (SLit 6126344));
mkChunk 6126368 (CVal 8 (SLit 0));
mkChunk 6126376 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6126384 6126456 6126384 6126456
[ mkChunk 6126384 (CVal 4 (SLit 2));
mkChunk 6126388 (CImg 6);
mkChunk 6126394 (CVal 1 (SLit 1));
mkChunk 6126395 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6126464 6126536 0 0
[ mkChunk 6126464 (CVal 8 (SLit 6126464));
mkChunk 6126472 (CImg 24);
mkChunk 6126496 (CVal 8 (SLit 6258328));
mkChunk 6126504 (CImg 24);
mkChunk 6126528 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6126604 6126616 0 0
[ mkChunk 6126604 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6257624 6258320 6257696 6258240
[ mkChunk 6257624 (CImg 16);
mkChunk 6257640 (CVal 8 (SLit 632464));
mkChunk 6257648 (CVal 8 (SLit 0));
mkChunk 6257656 (CVal 8 (SLit 24));
mkChunk 6257664 (CVal 8 (SLit 8));
mkChunk 6257672 (CVal 8 (SLit 0));
mkChunk 6257680 (CVal 8 (SOff 41 0));
mkChunk 6257688 (CImg 16);
mkChunk 6257704 (CVal 4 (SLit 1));
mkChunk 6257708 (CImg 4);
mkChunk 6257712 (CVal 8 (SLit 6257720));
mkChunk 6257720 (CImg 8);
mkChunk 6257728 (CVal 8 (SLit 573384));
mkChunk 6257736 (CImg 248);
mkChunk 6257984 (CVal 8 (SLit 457940));
mkChunk 6257992 (CImg 264);
mkChunk 6258264 (CVal 8 (SOff 1 0));
mkChunk 6258272 (CVal 1 (SLit 1));
mkChunk 6258273 (CImg 7);
mkChunk 6258280 (CVal 8 (SOff 5 0));
mkChunk 6258288 (CVal 8 (SLit 6257632));
mkChunk 6258296 (CVal 8 (SLit 248));
mkChunk 6258304 (CVal 8 (SLit 8));
mkChunk 6258312 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6258328 6258400 0 0
[ mkChunk 6258328 (CImg 48);
mkChunk 6258384 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6259328 6261544 0 0
[ mkChunk 6259328 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6261552 6262648 0 0
[ mkChunk 6261552 (CImg 8);
mkChunk 6261560 (CVal 8 (SLit 347196));
mkChunk 6261568 (CImg 1016);
mkChunk 6262584 (CVal 4 (SLit 0));
mkChunk 6262588 (CImg 4);
mkChunk 6262592 (CVal 4 (SLit 0));
mkChunk 6262596 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6262656 6266880 0 0
[ mkChunk 6262656 (CImg 4224) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A1bh; R_A1bi; R_A1bj; R_A1bk; R_A1bl; R_A1bm; R_A1bn; R_A1bo; R_A1bp; R_A1bq; R_A1br; R_A1bs; R_A1bt; R_A1bu; R_A1bv; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
