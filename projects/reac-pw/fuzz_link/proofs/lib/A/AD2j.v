(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/A/AD2i.v and AD2j.v (origin/ossv/recipes c8557374ad2e) for reac-pw/fuzz_link's asan image (sha256 059dae63e07c...) by gen_ad2.py 8a509576b937 of the start-up tool set (sha256 c99b47f502d4; internal record): sregs_main, TIDV, CANV and TFIB_MAIN from the 50 hand-off states of lib/A/AB01.v, the image bounds from lib/A/AB12.v and lib/A/AB1h.v, IMG_REGIONS below .data from the image and the owned static cells of lib/A/AF0m.v, from .data on cgif's regions placed on this image's symbols, every CVal value read from the hand-off states; the cut set given to the generator is Tfib_owned_static of lib/A/AF0m.v with the bodies of the six harness globals registered in .bss (g_nl, g_names, msg_build.long_alias, g_sink, g_said, g_say: provenance/evidence/startgen/AF0m.owned-with-bss-globals.v) *)
(* Read from: fuzz_link.asan (reac-pw/fuzz_link asan) sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d; unstripped twin sha256 66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YP0m YP09.
Import ListNotations.
Open Scope Z_scope.
Definition R_A1a : region :=
mkRegion None 65536 66280 0 0
[ mkChunk 65536 (CImg 744) ].
Definition R_A1b : region :=
mkRegion None 66288 66312 0 0
[ mkChunk 66288 (CImg 24) ].
Definition R_A1c : region :=
mkRegion None 66320 66360 0 0
[ mkChunk 66320 (CImg 40) ].
Definition R_A1d : region :=
mkRegion None 66368 66480 0 0
[ mkChunk 66368 (CImg 112) ].
Definition R_A1e : region :=
mkRegion None 66496 66504 0 0
[ mkChunk 66496 (CImg 8) ].
Definition R_A1f : region :=
mkRegion None 66512 66616 0 0
[ mkChunk 66512 (CImg 104) ].
Definition R_A1g : region :=
mkRegion None 66680 66872 0 0
[ mkChunk 66680 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66936 118392 0 0
[ mkChunk 66936 (CImg 51456) ].
Definition R_A1i : region :=
mkRegion None 118413 134396 0 0
[ mkChunk 118413 (CImg 15983) ].
Definition R_A1j : region :=
mkRegion None 134400 135077 0 0
[ mkChunk 134400 (CImg 677) ].
Definition R_A1k : region :=
mkRegion None 135104 135105 0 0
[ mkChunk 135104 (CImg 1) ].
Definition R_A1l : region :=
mkRegion None 135136 135148 0 0
[ mkChunk 135136 (CImg 12) ].
Definition R_A1m : region :=
mkRegion None 135168 135173 0 0
[ mkChunk 135168 (CImg 5) ].
Definition R_A1n : region :=
mkRegion None 135200 135206 0 0
[ mkChunk 135200 (CImg 6) ].
Definition R_A1o : region :=
mkRegion None 135232 135241 0 0
[ mkChunk 135232 (CImg 9) ].
Definition R_A1p : region :=
mkRegion None 135264 135270 0 0
[ mkChunk 135264 (CImg 6) ].
Definition R_A1q : region :=
mkRegion None 135296 135320 0 0
[ mkChunk 135296 (CImg 24) ].
Definition R_A1r : region :=
mkRegion None 135360 135362 0 0
[ mkChunk 135360 (CImg 2) ].
Definition R_A1s : region :=
mkRegion None 135392 135408 0 0
[ mkChunk 135392 (CImg 16) ].
Definition R_A1t : region :=
mkRegion None 135424 135439 0 0
[ mkChunk 135424 (CImg 15) ].
Definition R_A1u : region :=
mkRegion None 135456 135471 0 0
[ mkChunk 135456 (CImg 15) ].
Definition R_A1v : region :=
mkRegion None 135488 135499 0 0
[ mkChunk 135488 (CImg 11) ].
Definition R_A1w : region :=
mkRegion None 135520 135529 0 0
[ mkChunk 135520 (CImg 9) ].
Definition R_A1x : region :=
mkRegion None 135552 135568 0 0
[ mkChunk 135552 (CImg 16) ].
Definition R_A1y : region :=
mkRegion None 135584 135592 0 0
[ mkChunk 135584 (CImg 8) ].
Definition R_A1z : region :=
mkRegion None 135616 135621 0 0
[ mkChunk 135616 (CImg 5) ].
Definition R_A1aa : region :=
mkRegion None 135648 135653 0 0
[ mkChunk 135648 (CImg 5) ].
Definition R_A1ab : region :=
mkRegion None 135680 135686 0 0
[ mkChunk 135680 (CImg 6) ].
Definition R_A1ac : region :=
mkRegion None 135712 135716 0 0
[ mkChunk 135712 (CImg 4) ].
Definition R_A1ad : region :=
mkRegion None 135744 135747 0 0
[ mkChunk 135744 (CImg 3) ].
Definition R_A1ae : region :=
mkRegion None 135776 135778 0 0
[ mkChunk 135776 (CImg 2) ].
Definition R_A1af : region :=
mkRegion None 135808 135849 0 0
[ mkChunk 135808 (CImg 41) ].
Definition R_A1ag : region :=
mkRegion None 135872 135877 0 0
[ mkChunk 135872 (CImg 5) ].
Definition R_A1ah : region :=
mkRegion None 135904 135912 0 0
[ mkChunk 135904 (CImg 8) ].
Definition R_A1ai : region :=
mkRegion None 135936 136084 0 0
[ mkChunk 135936 (CImg 148) ].
Definition R_A1aj : region :=
mkRegion None 136128 136143 0 0
[ mkChunk 136128 (CImg 15) ].
Definition R_A1ak : region :=
mkRegion None 136160 136263 0 0
[ mkChunk 136160 (CImg 103) ].
Definition R_A1al : region :=
mkRegion None 136320 136355 0 0
[ mkChunk 136320 (CImg 35) ].
Definition R_A1am : region :=
mkRegion None 136416 136417 0 0
[ mkChunk 136416 (CImg 1) ].
Definition R_A1an : region :=
mkRegion None 136448 136566 0 0
[ mkChunk 136448 (CImg 118) ].
Definition R_A1ao : region :=
mkRegion None 136608 136730 0 0
[ mkChunk 136608 (CImg 122) ].
Definition R_A1ap : region :=
mkRegion None 136768 136776 0 0
[ mkChunk 136768 (CImg 8) ].
Definition R_A1aq : region :=
mkRegion None 136800 136813 0 0
[ mkChunk 136800 (CImg 13) ].
Definition R_A1ar : region :=
mkRegion None 136832 136835 0 0
[ mkChunk 136832 (CImg 3) ].
Definition R_A1as : region :=
mkRegion None 136864 138280 0 0
[ mkChunk 136864 (CImg 1416) ].
Definition R_A1at : region :=
mkRegion None 138284 138380 0 0
[ mkChunk 138284 (CImg 96) ].
Definition R_A1au : region :=
mkRegion None 138382 659456 0 0
[ mkChunk 138382 (CImg 521074) ].
Definition R_A2a : region :=
mkRegion None 659456 661392 0 0
[ mkChunk 659456 (CImg 1936) ].
Definition R_A2b : region :=
mkRegion None 661440 661528 0 0
[ mkChunk 661440 (CImg 88) ].
Definition R_A2c : region :=
mkRegion None 661568 661936 0 0
[ mkChunk 661568 (CImg 368) ].
Definition R_A2d : region :=
mkRegion None 662064 664888 0 0
[ mkChunk 662064 (CImg 2824) ].
Definition R_A2e : region :=
mkRegion None 664896 665128 0 0
[ mkChunk 664896 (CImg 232) ].
Definition R_A2f : region :=
mkRegion None 665136 665160 0 0
[ mkChunk 665136 (CImg 24) ].
Definition R_A2g : region :=
mkRegion None 665176 665264 0 0
[ mkChunk 665176 (CImg 8);
mkChunk 665184 (CImg 80) ].
Definition R_A2h : region :=
mkRegion None 665288 669384 0 0
[ mkChunk 665288 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 679768 680608 679768 680608
[ mkChunk 679768 (CImg 840) ].
Definition R_A4 : region :=
mkRegion None 683400 683472 683400 683472
[ mkChunk 683400 (CVal 1 (SLit 1));
mkChunk 683401 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6081168 6146704 0 0
[  ].
Definition R_A5a_1 : region :=
mkRegion None 6146704 6146752 6146704 6146752
[ mkChunk 6146704 (CImg 4);
mkChunk 6146708 (CVal 1 (SLit 0));
mkChunk 6146709 (CImg 43) ].
Definition R_A5a_2 : region :=
mkRegion None 6492928 6495084 6492928 6495084
[ mkChunk 6492928 (CImg 2112);
mkChunk 6495048 (CVal 8 (SLit 6495048));
mkChunk 6495056 (CVal 8 (SLit 6495048));
mkChunk 6495064 (CVal 8 (SLit 6495048));
mkChunk 6495072 (CVal 8 (SLit 0));
mkChunk 6495080 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6495088 6495160 6495088 6495160
[ mkChunk 6495088 (CVal 4 (SLit 2));
mkChunk 6495092 (CImg 6);
mkChunk 6495098 (CVal 1 (SLit 1));
mkChunk 6495099 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6495168 6495240 0 0
[ mkChunk 6495168 (CVal 8 (SLit 6495168));
mkChunk 6495176 (CImg 24);
mkChunk 6495200 (CVal 8 (SLit 6627032));
mkChunk 6495208 (CImg 24);
mkChunk 6495232 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6495308 6495320 0 0
[ mkChunk 6495308 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6626328 6627024 6626400 6626944
[ mkChunk 6626328 (CImg 16);
mkChunk 6626344 (CVal 8 (SLit 656192));
mkChunk 6626352 (CVal 8 (SLit 0));
mkChunk 6626360 (CVal 8 (SLit 24));
mkChunk 6626368 (CVal 8 (SLit 8));
mkChunk 6626376 (CVal 8 (SLit 0));
mkChunk 6626384 (CVal 8 (SOff 41 0));
mkChunk 6626392 (CImg 16);
mkChunk 6626408 (CVal 4 (SLit 1));
mkChunk 6626412 (CImg 4);
mkChunk 6626416 (CVal 8 (SLit 6626424));
mkChunk 6626424 (CImg 8);
mkChunk 6626432 (CVal 8 (SLit 593204));
mkChunk 6626440 (CImg 248);
mkChunk 6626688 (CVal 8 (SLit 464780));
mkChunk 6626696 (CImg 264);
mkChunk 6626968 (CVal 8 (SOff 1 0));
mkChunk 6626976 (CVal 1 (SLit 1));
mkChunk 6626977 (CImg 7);
mkChunk 6626984 (CVal 8 (SOff 5 0));
mkChunk 6626992 (CVal 8 (SLit 6626336));
mkChunk 6627000 (CVal 8 (SLit 248));
mkChunk 6627008 (CVal 8 (SLit 8));
mkChunk 6627016 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6627032 6627104 0 0
[ mkChunk 6627032 (CImg 48);
mkChunk 6627088 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6628032 6630248 0 0
[ mkChunk 6628032 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6630256 6631352 0 0
[ mkChunk 6630256 (CImg 8);
mkChunk 6630264 (CVal 8 (SLit 353168));
mkChunk 6630272 (CImg 1016);
mkChunk 6631288 (CVal 4 (SLit 0));
mkChunk 6631292 (CImg 4);
mkChunk 6631296 (CVal 4 (SLit 0));
mkChunk 6631300 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6631360 6635520 0 0
[ mkChunk 6631360 (CImg 4160) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A2h; R_A3; R_A4; R_RS; R_A5a_1; R_A5a_2; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
