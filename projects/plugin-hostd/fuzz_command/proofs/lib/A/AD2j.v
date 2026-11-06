(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2j.v with its module paths changed; the regions are generated from plugin-hostd/fuzz_command's image: the read-only, relro and data regions are its runs between A/AF0m.v's owned statics, the program statics carry only the chunks the driver's proofs read, every start-up word is the paired object of cgif's, no chunk or write window meets an owned static (R_A5a's write window is the driver's own statics [0x5e3710, 0x5e3740)), and no image chunk holds a byte that a start-up hand-off state of A/AB01.v writes with another value. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66352 66368 0 0
[ mkChunk 66352 (CImg 16) ].
Definition R_A1e : region :=
mkRegion None 66376 66464 0 0
[ mkChunk 66376 (CImg 88) ].
Definition R_A1f : region :=
mkRegion None 66480 66488 0 0
[ mkChunk 66480 (CImg 8) ].
Definition R_A1g : region :=
mkRegion None 66496 66600 0 0
[ mkChunk 66496 (CImg 104) ].
Definition R_A1h : region :=
mkRegion None 66664 66856 0 0
[ mkChunk 66664 (CImg 192) ].
Definition R_A1i : region :=
mkRegion None 66920 118562 0 0
[ mkChunk 66920 (CImg 51642) ].
Definition R_A1j : region :=
mkRegion None 118583 134696 0 0
[ mkChunk 118583 (CImg 16113) ].
Definition R_A1k : region :=
mkRegion None 134700 135331 0 0
[ mkChunk 134700 (CImg 631) ].
Definition R_A1l : region :=
mkRegion None 135360 144156 0 0
[ mkChunk 135360 (CImg 8);
mkChunk 135392 (CImg 7);
mkChunk 135424 (CImg 5);
mkChunk 135456 (CImg 2);
mkChunk 135488 (CImg 11);
mkChunk 135520 (CImg 11);
mkChunk 135552 (CImg 14);
mkChunk 135584 (CImg 17);
mkChunk 135648 (CImg 4);
mkChunk 135680 (CImg 61);
mkChunk 135776 (CImg 12);
mkChunk 135808 (CImg 1);
mkChunk 135840 (CImg 14);
mkChunk 135872 (CImg 11);
mkChunk 135904 (CImg 17);
mkChunk 135968 (CImg 17);
mkChunk 136032 (CImg 17);
mkChunk 136096 (CImg 17);
mkChunk 136160 (CImg 11);
mkChunk 136192 (CImg 31);
mkChunk 136256 (CImg 12);
mkChunk 136288 (CImg 23);
mkChunk 136352 (CImg 11);
mkChunk 136384 (CImg 35);
mkChunk 136480 (CImg 8);
mkChunk 136512 (CImg 81);
mkChunk 136640 (CImg 10);
mkChunk 136672 (CImg 12);
mkChunk 136704 (CImg 15);
mkChunk 136736 (CImg 44);
mkChunk 136832 (CImg 11);
mkChunk 136864 (CImg 6);
mkChunk 136896 (CImg 29);
mkChunk 136960 (CImg 6);
mkChunk 136992 (CImg 36);
mkChunk 137088 (CImg 12);
mkChunk 137120 (CImg 8);
mkChunk 137152 (CImg 15);
mkChunk 137184 (CImg 10);
mkChunk 137216 (CImg 7);
mkChunk 137248 (CImg 10);
mkChunk 137280 (CImg 8);
mkChunk 137312 (CImg 11);
mkChunk 137344 (CImg 4);
mkChunk 137376 (CImg 3);
mkChunk 137408 (CImg 9);
mkChunk 137440 (CImg 5);
mkChunk 137472 (CImg 3);
mkChunk 137504 (CImg 8);
mkChunk 137536 (CImg 2);
mkChunk 137568 (CImg 6);
mkChunk 137600 (CImg 4);
mkChunk 137632 (CImg 3);
mkChunk 137664 (CImg 2);
mkChunk 137696 (CImg 4);
mkChunk 137728 (CImg 5);
mkChunk 137760 (CImg 6);
mkChunk 137792 (CImg 7);
mkChunk 137824 (CImg 5);
mkChunk 137856 (CImg 8);
mkChunk 137888 (CImg 2);
mkChunk 137920 (CImg 2);
mkChunk 137952 (CImg 4);
mkChunk 137984 (CImg 8);
mkChunk 138016 (CImg 6);
mkChunk 138048 (CImg 4);
mkChunk 138080 (CImg 9);
mkChunk 138112 (CImg 264);
mkChunk 138432 (CImg 4);
mkChunk 138464 (CImg 7);
mkChunk 138496 (CImg 8);
mkChunk 138528 (CImg 6);
mkChunk 138560 (CImg 2);
mkChunk 138592 (CImg 3);
mkChunk 138624 (CImg 12);
mkChunk 138656 (CImg 14);
mkChunk 138688 (CImg 17);
mkChunk 138752 (CImg 17);
mkChunk 138816 (CImg 11);
mkChunk 138848 (CImg 11);
mkChunk 138880 (CImg 12);
mkChunk 138912 (CImg 15);
mkChunk 138944 (CImg 11);
mkChunk 138976 (CImg 4);
mkChunk 139008 (CImg 3);
mkChunk 139040 (CImg 6);
mkChunk 139072 (CImg 12);
mkChunk 139104 (CImg 15);
mkChunk 139136 (CImg 10);
mkChunk 139168 (CImg 2);
mkChunk 139200 (CImg 4);
mkChunk 139232 (CImg 16);
mkChunk 139264 (CImg 61);
mkChunk 139360 (CImg 54);
mkChunk 139456 (CImg 8);
mkChunk 139488 (CImg 10);
mkChunk 139520 (CImg 11);
mkChunk 139552 (CImg 25);
mkChunk 139616 (CImg 11);
mkChunk 139648 (CImg 16);
mkChunk 139680 (CImg 11);
mkChunk 139712 (CImg 13);
mkChunk 139744 (CImg 13);
mkChunk 139776 (CImg 16);
mkChunk 139808 (CImg 79);
mkChunk 139936 (CImg 11);
mkChunk 139968 (CImg 67);
mkChunk 140096 (CImg 12);
mkChunk 140128 (CImg 11);
mkChunk 140160 (CImg 25);
mkChunk 140224 (CImg 11);
mkChunk 140256 (CImg 18);
mkChunk 140320 (CImg 8);
mkChunk 140352 (CImg 9);
mkChunk 140384 (CImg 14);
mkChunk 140416 (CImg 7);
mkChunk 140448 (CImg 35);
mkChunk 140512 (CImg 18);
mkChunk 140576 (CImg 19);
mkChunk 140640 (CImg 4);
mkChunk 140672 (CImg 15);
mkChunk 140704 (CImg 10);
mkChunk 140736 (CImg 10);
mkChunk 140768 (CImg 12);
mkChunk 140800 (CImg 14);
mkChunk 140832 (CImg 17);
mkChunk 140896 (CImg 4);
mkChunk 140928 (CImg 17);
mkChunk 140992 (CImg 11);
mkChunk 141024 (CImg 15);
mkChunk 141056 (CImg 12);
mkChunk 141088 (CImg 11);
mkChunk 141120 (CImg 6);
mkChunk 141152 (CImg 12);
mkChunk 141184 (CImg 8);
mkChunk 141216 (CImg 11);
mkChunk 141248 (CImg 10);
mkChunk 141280 (CImg 5);
mkChunk 141312 (CImg 14);
mkChunk 141344 (CImg 17);
mkChunk 141408 (CImg 4);
mkChunk 141440 (CImg 8);
mkChunk 141472 (CImg 6);
mkChunk 141504 (CImg 9);
mkChunk 141536 (CImg 11);
mkChunk 141568 (CImg 13);
mkChunk 141600 (CImg 16);
mkChunk 141632 (CImg 11);
mkChunk 141664 (CImg 12);
mkChunk 141696 (CImg 11);
mkChunk 141728 (CImg 11);
mkChunk 141760 (CImg 8);
mkChunk 141792 (CImg 9);
mkChunk 141824 (CImg 14);
mkChunk 141856 (CImg 24);
mkChunk 141920 (CImg 13);
mkChunk 141952 (CImg 19);
mkChunk 142016 (CImg 16);
mkChunk 142048 (CImg 26);
mkChunk 142112 (CImg 16);
mkChunk 142144 (CImg 12);
mkChunk 142176 (CImg 21);
mkChunk 142240 (CImg 23);
mkChunk 142304 (CImg 27);
mkChunk 142368 (CImg 17);
mkChunk 142432 (CImg 47);
mkChunk 142528 (CImg 15);
mkChunk 142560 (CImg 22);
mkChunk 142624 (CImg 25);
mkChunk 142688 (CImg 15);
mkChunk 142720 (CImg 2);
mkChunk 142752 (CImg 1404) ].
Definition R_A1m : region :=
mkRegion None 144160 144256 0 0
[ mkChunk 144160 (CImg 96) ].
Definition R_A1n : region :=
mkRegion None 144258 149156 0 0
[ mkChunk 144258 (CImg 4898) ].
Definition R_A1o : region :=
mkRegion None 149156 675840 0 0
[ mkChunk 149156 (CImg 526684) ].
Definition R_A2a : region :=
mkRegion None 675840 680912 0 0
[ mkChunk 675840 (CImg 3376);
mkChunk 679360 (CImg 208);
mkChunk 679616 (CImg 448);
mkChunk 680160 (CImg 160);
mkChunk 680352 (CImg 144);
mkChunk 680544 (CImg 368) ].
Definition R_A2b : region :=
mkRegion None 681040 683864 0 0
[ mkChunk 681040 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 683872 684104 0 0
[ mkChunk 683872 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 684112 684168 0 0
[ mkChunk 684112 (CImg 56) ].
Definition R_A2e : region :=
mkRegion None 684184 684272 0 0
[ mkChunk 684184 (CImg 8);
mkChunk 684192 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 684296 688392 0 0
[ mkChunk 684296 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 698808 699640 698808 699640
[ mkChunk 698808 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 711176 711248 711176 711248
[ mkChunk 711176 (CVal 1 (SLit 1));
mkChunk 711177 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6108944 6174480 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6174480 6178036 6174480 6174528
[ mkChunk 6174480 (CImg 4);
mkChunk 6174484 (CVal 1 (SLit 0));
mkChunk 6174485 (CImg 43);
mkChunk 6174536 (CImg 4);
mkChunk 6175440 (CImg 12);
mkChunk 6175456 (CImg 16);
mkChunk 6175712 (CImg 8);
mkChunk 6175811 (CImg 29);
mkChunk 6175840 (CImg 4);
mkChunk 6175873 (CImg 2119);
mkChunk 6178000 (CVal 8 (SLit 6178000));
mkChunk 6178008 (CVal 8 (SLit 6178000));
mkChunk 6178016 (CVal 8 (SLit 6178000));
mkChunk 6178024 (CVal 8 (SLit 0));
mkChunk 6178032 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6178040 6178112 6178040 6178112
[ mkChunk 6178040 (CVal 4 (SLit 2));
mkChunk 6178044 (CImg 6);
mkChunk 6178050 (CVal 1 (SLit 1));
mkChunk 6178051 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6178120 6178192 0 0
[ mkChunk 6178120 (CVal 8 (SLit 6178120));
mkChunk 6178128 (CImg 24);
mkChunk 6178152 (CVal 8 (SLit 6309984));
mkChunk 6178160 (CImg 24);
mkChunk 6178184 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6178260 6178272 0 0
[ mkChunk 6178260 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6309280 6309976 6309352 6309896
[ mkChunk 6309280 (CImg 16);
mkChunk 6309296 (CVal 8 (SLit 673536));
mkChunk 6309304 (CVal 8 (SLit 0));
mkChunk 6309312 (CVal 8 (SLit 24));
mkChunk 6309320 (CVal 8 (SLit 8));
mkChunk 6309328 (CVal 8 (SLit 0));
mkChunk 6309336 (CVal 8 (SOff 41 0));
mkChunk 6309344 (CImg 16);
mkChunk 6309360 (CVal 4 (SLit 1));
mkChunk 6309364 (CImg 4);
mkChunk 6309368 (CVal 8 (SLit 6309376));
mkChunk 6309376 (CImg 8);
mkChunk 6309384 (CVal 8 (SLit 611004));
mkChunk 6309392 (CImg 248);
mkChunk 6309640 (CVal 8 (SLit 481956));
mkChunk 6309648 (CImg 264);
mkChunk 6309920 (CVal 8 (SOff 1 0));
mkChunk 6309928 (CVal 1 (SLit 1));
mkChunk 6309929 (CImg 7);
mkChunk 6309936 (CVal 8 (SOff 5 0));
mkChunk 6309944 (CVal 8 (SLit 6309288));
mkChunk 6309952 (CVal 8 (SLit 248));
mkChunk 6309960 (CVal 8 (SLit 8));
mkChunk 6309968 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6309984 6310056 0 0
[ mkChunk 6309984 (CImg 48);
mkChunk 6310040 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6310984 6313200 0 0
[ mkChunk 6310984 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6313208 6314304 0 0
[ mkChunk 6313208 (CImg 8);
mkChunk 6313216 (CVal 8 (SLit 371212));
mkChunk 6313224 (CImg 1016);
mkChunk 6314240 (CVal 4 (SLit 0));
mkChunk 6314244 (CImg 4);
mkChunk 6314248 (CVal 4 (SLit 0));
mkChunk 6314252 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6314312 6316032 0 0
[ mkChunk 6314312 (CImg 1720) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
