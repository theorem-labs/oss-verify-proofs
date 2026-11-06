(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD2j.v with its module paths changed; the regions are generated from plugin-hostd/fuzz_command's image: the read-only, relro and data regions are its runs between A/AF0m.v's owned statics, the program statics carry only the chunks the driver's proofs read, every start-up word is the paired object of cgif's, and no chunk or write window meets an owned static (R_A5a's write window is the driver's own statics [0x5e3710, 0x5e3740)). *)
(* Modified by Theorem Labs, 2026-10: regenerated for plugin-hostd/fuzz_command's ASan+UBSan build by the rule of this harness's lib/A/AD2j.v (the twin of cgif_file_fuzzer's lib/YD2j.v), from that image: the read-only, relro and data regions are its runs between lib/B/YF0m.v's owned statics, the program statics carry only GI_cmdA's sub-ranges (lib/B/Prog/CmdGlob.v), no chunk or write window meets an owned static or an ODR indicator byte, and the run-time regions are the A regions at the B twins of their objects, their start-up words checked against lib/B/YB01.v's first hand-off state; no image chunk holds a byte that one of YB01.v's 50 hand-off states writes with a symbolic value or a value other than the image byte. *)
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
mkRegion None 118583 134768 0 0
[ mkChunk 118583 (CImg 16185) ].
Definition R_A1k : region :=
mkRegion None 134772 135395 0 0
[ mkChunk 134772 (CImg 623) ].
Definition R_A1l : region :=
mkRegion None 135424 144220 0 0
[ mkChunk 135424 (CImg 8);
mkChunk 135456 (CImg 7);
mkChunk 135488 (CImg 5);
mkChunk 135520 (CImg 2);
mkChunk 135552 (CImg 11);
mkChunk 135584 (CImg 11);
mkChunk 135616 (CImg 14);
mkChunk 135648 (CImg 17);
mkChunk 135712 (CImg 4);
mkChunk 135744 (CImg 61);
mkChunk 135840 (CImg 12);
mkChunk 135872 (CImg 1);
mkChunk 135904 (CImg 14);
mkChunk 135936 (CImg 11);
mkChunk 135968 (CImg 17);
mkChunk 136032 (CImg 17);
mkChunk 136096 (CImg 17);
mkChunk 136160 (CImg 17);
mkChunk 136224 (CImg 11);
mkChunk 136256 (CImg 31);
mkChunk 136320 (CImg 12);
mkChunk 136352 (CImg 23);
mkChunk 136416 (CImg 11);
mkChunk 136448 (CImg 35);
mkChunk 136544 (CImg 8);
mkChunk 136576 (CImg 81);
mkChunk 136704 (CImg 10);
mkChunk 136736 (CImg 12);
mkChunk 136768 (CImg 15);
mkChunk 136800 (CImg 44);
mkChunk 136896 (CImg 11);
mkChunk 136928 (CImg 6);
mkChunk 136960 (CImg 29);
mkChunk 137024 (CImg 6);
mkChunk 137056 (CImg 36);
mkChunk 137152 (CImg 12);
mkChunk 137184 (CImg 8);
mkChunk 137216 (CImg 15);
mkChunk 137248 (CImg 10);
mkChunk 137280 (CImg 7);
mkChunk 137312 (CImg 10);
mkChunk 137344 (CImg 8);
mkChunk 137376 (CImg 11);
mkChunk 137408 (CImg 4);
mkChunk 137440 (CImg 3);
mkChunk 137472 (CImg 9);
mkChunk 137504 (CImg 5);
mkChunk 137536 (CImg 3);
mkChunk 137568 (CImg 8);
mkChunk 137600 (CImg 2);
mkChunk 137632 (CImg 6);
mkChunk 137664 (CImg 4);
mkChunk 137696 (CImg 3);
mkChunk 137728 (CImg 2);
mkChunk 137760 (CImg 4);
mkChunk 137792 (CImg 5);
mkChunk 137824 (CImg 6);
mkChunk 137856 (CImg 7);
mkChunk 137888 (CImg 5);
mkChunk 137920 (CImg 8);
mkChunk 137952 (CImg 2);
mkChunk 137984 (CImg 2);
mkChunk 138016 (CImg 4);
mkChunk 138048 (CImg 8);
mkChunk 138080 (CImg 6);
mkChunk 138112 (CImg 4);
mkChunk 138144 (CImg 9);
mkChunk 138176 (CImg 264);
mkChunk 138496 (CImg 4);
mkChunk 138528 (CImg 7);
mkChunk 138560 (CImg 8);
mkChunk 138592 (CImg 6);
mkChunk 138624 (CImg 2);
mkChunk 138656 (CImg 3);
mkChunk 138688 (CImg 12);
mkChunk 138720 (CImg 14);
mkChunk 138752 (CImg 17);
mkChunk 138816 (CImg 17);
mkChunk 138880 (CImg 11);
mkChunk 138912 (CImg 11);
mkChunk 138944 (CImg 12);
mkChunk 138976 (CImg 15);
mkChunk 139008 (CImg 11);
mkChunk 139040 (CImg 4);
mkChunk 139072 (CImg 3);
mkChunk 139104 (CImg 6);
mkChunk 139136 (CImg 12);
mkChunk 139168 (CImg 15);
mkChunk 139200 (CImg 10);
mkChunk 139232 (CImg 2);
mkChunk 139264 (CImg 4);
mkChunk 139296 (CImg 16);
mkChunk 139328 (CImg 61);
mkChunk 139424 (CImg 54);
mkChunk 139520 (CImg 8);
mkChunk 139552 (CImg 10);
mkChunk 139584 (CImg 11);
mkChunk 139616 (CImg 25);
mkChunk 139680 (CImg 11);
mkChunk 139712 (CImg 16);
mkChunk 139744 (CImg 11);
mkChunk 139776 (CImg 13);
mkChunk 139808 (CImg 13);
mkChunk 139840 (CImg 16);
mkChunk 139872 (CImg 79);
mkChunk 140000 (CImg 11);
mkChunk 140032 (CImg 67);
mkChunk 140160 (CImg 12);
mkChunk 140192 (CImg 11);
mkChunk 140224 (CImg 25);
mkChunk 140288 (CImg 11);
mkChunk 140320 (CImg 18);
mkChunk 140384 (CImg 8);
mkChunk 140416 (CImg 9);
mkChunk 140448 (CImg 14);
mkChunk 140480 (CImg 7);
mkChunk 140512 (CImg 35);
mkChunk 140576 (CImg 18);
mkChunk 140640 (CImg 19);
mkChunk 140704 (CImg 4);
mkChunk 140736 (CImg 15);
mkChunk 140768 (CImg 10);
mkChunk 140800 (CImg 10);
mkChunk 140832 (CImg 12);
mkChunk 140864 (CImg 14);
mkChunk 140896 (CImg 17);
mkChunk 140960 (CImg 4);
mkChunk 140992 (CImg 17);
mkChunk 141056 (CImg 11);
mkChunk 141088 (CImg 15);
mkChunk 141120 (CImg 12);
mkChunk 141152 (CImg 11);
mkChunk 141184 (CImg 6);
mkChunk 141216 (CImg 12);
mkChunk 141248 (CImg 8);
mkChunk 141280 (CImg 11);
mkChunk 141312 (CImg 10);
mkChunk 141344 (CImg 5);
mkChunk 141376 (CImg 14);
mkChunk 141408 (CImg 17);
mkChunk 141472 (CImg 4);
mkChunk 141504 (CImg 8);
mkChunk 141536 (CImg 6);
mkChunk 141568 (CImg 9);
mkChunk 141600 (CImg 11);
mkChunk 141632 (CImg 13);
mkChunk 141664 (CImg 16);
mkChunk 141696 (CImg 11);
mkChunk 141728 (CImg 12);
mkChunk 141760 (CImg 11);
mkChunk 141792 (CImg 11);
mkChunk 141824 (CImg 8);
mkChunk 141856 (CImg 9);
mkChunk 141888 (CImg 14);
mkChunk 141920 (CImg 24);
mkChunk 141984 (CImg 13);
mkChunk 142016 (CImg 19);
mkChunk 142080 (CImg 16);
mkChunk 142112 (CImg 26);
mkChunk 142176 (CImg 16);
mkChunk 142208 (CImg 12);
mkChunk 142240 (CImg 21);
mkChunk 142304 (CImg 23);
mkChunk 142368 (CImg 27);
mkChunk 142432 (CImg 17);
mkChunk 142496 (CImg 47);
mkChunk 142592 (CImg 15);
mkChunk 142624 (CImg 22);
mkChunk 142688 (CImg 25);
mkChunk 142752 (CImg 15);
mkChunk 142784 (CImg 2);
mkChunk 142816 (CImg 1404) ].
Definition R_A1m : region :=
mkRegion None 144224 144320 0 0
[ mkChunk 144224 (CImg 96) ].
Definition R_A1n : region :=
mkRegion None 144322 149220 0 0
[ mkChunk 144322 (CImg 4898) ].
Definition R_A1o : region :=
mkRegion None 149220 675840 0 0
[ mkChunk 149220 (CImg 526620) ].
Definition R_A2a : region :=
mkRegion None 675840 679728 0 0
[ mkChunk 675840 (CImg 2192);
mkChunk 678176 (CImg 208);
mkChunk 678432 (CImg 448);
mkChunk 678976 (CImg 160);
mkChunk 679168 (CImg 144);
mkChunk 679360 (CImg 368) ].
Definition R_A2b : region :=
mkRegion None 679856 682680 0 0
[ mkChunk 679856 (CImg 2824) ].
Definition R_A2c : region :=
mkRegion None 682688 682920 0 0
[ mkChunk 682688 (CImg 232) ].
Definition R_A2d : region :=
mkRegion None 682928 682984 0 0
[ mkChunk 682928 (CImg 56) ].
Definition R_A2e : region :=
mkRegion None 683000 683088 0 0
[ mkChunk 683000 (CImg 8);
mkChunk 683008 (CImg 80) ].
Definition R_A2f : region :=
mkRegion None 683112 687208 0 0
[ mkChunk 683112 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 697624 698456 697624 698456
[ mkChunk 697624 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 710024 710096 710024 710096
[ mkChunk 710024 (CVal 1 (SLit 1));
mkChunk 710025 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6107792 6173328 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6173328 6176884 6173328 6173376
[ mkChunk 6173328 (CImg 4);
mkChunk 6173332 (CVal 1 (SLit 0));
mkChunk 6173333 (CImg 43);
mkChunk 6173384 (CImg 4);
mkChunk 6174288 (CImg 12);
mkChunk 6174304 (CImg 16);
mkChunk 6174560 (CImg 8);
mkChunk 6174659 (CImg 29);
mkChunk 6174688 (CImg 4);
mkChunk 6174721 (CImg 2119);
mkChunk 6176848 (CVal 8 (SLit 6176848));
mkChunk 6176856 (CVal 8 (SLit 6176848));
mkChunk 6176864 (CVal 8 (SLit 6176848));
mkChunk 6176872 (CVal 8 (SLit 0));
mkChunk 6176880 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6176888 6176960 6176888 6176960
[ mkChunk 6176888 (CVal 4 (SLit 2));
mkChunk 6176892 (CImg 6);
mkChunk 6176898 (CVal 1 (SLit 1));
mkChunk 6176899 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6176968 6177040 0 0
[ mkChunk 6176968 (CVal 8 (SLit 6176968));
mkChunk 6176976 (CImg 24);
mkChunk 6177000 (CVal 8 (SLit 6308832));
mkChunk 6177008 (CImg 24);
mkChunk 6177032 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6177108 6177120 0 0
[ mkChunk 6177108 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6308128 6308824 6308200 6308744
[ mkChunk 6308128 (CImg 16);
mkChunk 6308144 (CVal 8 (SLit 672344));
mkChunk 6308152 (CVal 8 (SLit 0));
mkChunk 6308160 (CVal 8 (SLit 24));
mkChunk 6308168 (CVal 8 (SLit 8));
mkChunk 6308176 (CVal 8 (SLit 0));
mkChunk 6308184 (CVal 8 (SOff 41 0));
mkChunk 6308192 (CImg 16);
mkChunk 6308208 (CVal 4 (SLit 1));
mkChunk 6308212 (CImg 4);
mkChunk 6308216 (CVal 8 (SLit 6308224));
mkChunk 6308224 (CImg 8);
mkChunk 6308232 (CVal 8 (SLit 609816));
mkChunk 6308240 (CImg 248);
mkChunk 6308488 (CVal 8 (SLit 482032));
mkChunk 6308496 (CImg 264);
mkChunk 6308768 (CVal 8 (SOff 1 0));
mkChunk 6308776 (CVal 1 (SLit 1));
mkChunk 6308777 (CImg 7);
mkChunk 6308784 (CVal 8 (SOff 5 0));
mkChunk 6308792 (CVal 8 (SLit 6308136));
mkChunk 6308800 (CVal 8 (SLit 248));
mkChunk 6308808 (CVal 8 (SLit 8));
mkChunk 6308816 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6308832 6308904 0 0
[ mkChunk 6308832 (CImg 48);
mkChunk 6308888 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6309832 6312048 0 0
[ mkChunk 6309832 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6312056 6313152 0 0
[ mkChunk 6312056 (CImg 8);
mkChunk 6312064 (CVal 8 (SLit 371288));
mkChunk 6312072 (CImg 1016);
mkChunk 6313088 (CVal 4 (SLit 0));
mkChunk 6313092 (CImg 4);
mkChunk 6313096 (CVal 4 (SLit 0));
mkChunk 6313100 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6313160 6316032 0 0
[ mkChunk 6313160 (CImg 2872) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
