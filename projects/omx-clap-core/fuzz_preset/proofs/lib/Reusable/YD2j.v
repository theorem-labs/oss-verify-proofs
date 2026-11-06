(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib (origin/ossv/recipes c8557374ad2e) for fuzz_preset's asan-ubsan image of harness fix #102 (pin sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b) on 2026-10-29 by h-pre-b2's startA/ad2gen/gen_ad2_ww.py, with its module paths changed: IMG_REGIONS below .data is [img_lo, .data) minus the owned static cells of lib/Reusable/YF0m.v, split at the rw window of lib/Reusable/YB1h.v; from .data on, cgif's regions at the same offsets from their section anchors, checked against the unstripped twin, cut where owned static cells fall inside and then cut again around the SEVEN alloc.c ledger cells of this build, taken by name at the field widths lib/A/PRH_ImgB.v states (blob 3216eca68342) and each re-verified against this image's .symtab - g_ran_out 0x5dde00+1, g_live 0x5ddda0+8, g_peak 0x5dddc0+8, g_count 0x5ddde0+8, g_fail_at 0xa6e00+8, g_own_ran_out 0x5ddd80+1, g_most 0xa6e20+8 - a piece wholly inside one of them being dropped; R_A5a's write window is the driver's measured stores [0x5ddd50, 0x5ddd55) and R_A3's is [0xa6e40, 0xa7160), so the ledger-cell piece R_A3_1 has none; the region ending at the image top is written YImgTop.IMG_TOP_B (0x601000 on this image); every CVal value read from the 50 hand-off states of lib/Reusable/YB01.v. CONTROL: the same generator and rule on the PREVIOUS pin (f8f98a95, twin 3b5e1a09) with that pin's inputs reproduces the old-pin YD2i.v and YD2j.v of cold/h-mani-a4-preset-relocB a30609ab47eb byte for byte apart from this header line. sources (sha256): generator gen_ad2_ww.py ff72904f5f714f72; states YB01.v 3effd41b425715f0; atable YB12.v 39932a75b5d5e273; tsegs YB1h.v 8f2742d386d4cbc5; owned YF0m.v 645b677dba043bd7; image fuzz_preset.asan-ubsan d663f82d7f488d30; twin fuzz_preset.asan-ubsan c90d4fa54d43160b; tmpl_ad2i YD2i.tmpl.v 73f04b66f4c6f759; tmpl_ad2j YD2j.tmpl.v c3cd15e52d644b35; ya02 YA02.v 0024da644af19323 *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP09.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop.
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
mkRegion None 66352 66480 0 0
[ mkChunk 66352 (CImg 128) ].
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
mkRegion None 66936 118379 0 0
[ mkChunk 66936 (CImg 51443) ].
Definition R_A1i : region :=
mkRegion None 118400 134344 0 0
[ mkChunk 118400 (CImg 15944) ].
Definition R_A1j : region :=
mkRegion None 134348 135013 0 0
[ mkChunk 134348 (CImg 665) ].
Definition R_A1k : region :=
mkRegion None 135040 135046 0 0
[ mkChunk 135040 (CImg 6) ].
Definition R_A1l : region :=
mkRegion None 135072 135077 0 0
[ mkChunk 135072 (CImg 5) ].
Definition R_A1m : region :=
mkRegion None 135104 135160 0 0
[ mkChunk 135104 (CImg 56) ].
Definition R_A1n : region :=
mkRegion None 135200 135207 0 0
[ mkChunk 135200 (CImg 7) ].
Definition R_A1o : region :=
mkRegion None 135232 135235 0 0
[ mkChunk 135232 (CImg 3) ].
Definition R_A1p : region :=
mkRegion None 135264 135269 0 0
[ mkChunk 135264 (CImg 5) ].
Definition R_A1q : region :=
mkRegion None 135296 135304 0 0
[ mkChunk 135296 (CImg 8) ].
Definition R_A1r : region :=
mkRegion None 135328 135338 0 0
[ mkChunk 135328 (CImg 10) ].
Definition R_A1s : region :=
mkRegion None 135360 135371 0 0
[ mkChunk 135360 (CImg 11) ].
Definition R_A1t : region :=
mkRegion None 135392 135399 0 0
[ mkChunk 135392 (CImg 7) ].
Definition R_A1u : region :=
mkRegion None 135424 135430 0 0
[ mkChunk 135424 (CImg 6) ].
Definition R_A1v : region :=
mkRegion None 135456 135463 0 0
[ mkChunk 135456 (CImg 7) ].
Definition R_A1w : region :=
mkRegion None 135488 135495 0 0
[ mkChunk 135488 (CImg 7) ].
Definition R_A1x : region :=
mkRegion None 135520 135526 0 0
[ mkChunk 135520 (CImg 6) ].
Definition R_A1y : region :=
mkRegion None 135552 135561 0 0
[ mkChunk 135552 (CImg 9) ].
Definition R_A1z : region :=
mkRegion None 135584 135590 0 0
[ mkChunk 135584 (CImg 6) ].
Definition R_A1aa : region :=
mkRegion None 135616 135617 0 0
[ mkChunk 135616 (CImg 1) ].
Definition R_A1ab : region :=
mkRegion None 135648 135650 0 0
[ mkChunk 135648 (CImg 2) ].
Definition R_A1ac : region :=
mkRegion None 135680 135682 0 0
[ mkChunk 135680 (CImg 2) ].
Definition R_A1ad : region :=
mkRegion None 135712 135714 0 0
[ mkChunk 135712 (CImg 2) ].
Definition R_A1ae : region :=
mkRegion None 135744 135746 0 0
[ mkChunk 135744 (CImg 2) ].
Definition R_A1af : region :=
mkRegion None 135776 135778 0 0
[ mkChunk 135776 (CImg 2) ].
Definition R_A1ag : region :=
mkRegion None 135808 135810 0 0
[ mkChunk 135808 (CImg 2) ].
Definition R_A1ah : region :=
mkRegion None 135840 135842 0 0
[ mkChunk 135840 (CImg 2) ].
Definition R_A1ai : region :=
mkRegion None 135872 135874 0 0
[ mkChunk 135872 (CImg 2) ].
Definition R_A1aj : region :=
mkRegion None 135904 135921 0 0
[ mkChunk 135904 (CImg 17) ].
Definition R_A1ak : region :=
mkRegion None 135968 135970 0 0
[ mkChunk 135968 (CImg 2) ].
Definition R_A1al : region :=
mkRegion None 136000 136002 0 0
[ mkChunk 136000 (CImg 2) ].
Definition R_A1am : region :=
mkRegion None 136032 136035 0 0
[ mkChunk 136032 (CImg 3) ].
Definition R_A1an : region :=
mkRegion None 136064 136085 0 0
[ mkChunk 136064 (CImg 21) ].
Definition R_A1ao : region :=
mkRegion None 136128 136225 0 0
[ mkChunk 136128 (CImg 97) ].
Definition R_A1ap : region :=
mkRegion None 136256 136258 0 0
[ mkChunk 136256 (CImg 2) ].
Definition R_A1aq : region :=
mkRegion None 136288 136293 0 0
[ mkChunk 136288 (CImg 5) ].
Definition R_A1ar : region :=
mkRegion None 136320 136326 0 0
[ mkChunk 136320 (CImg 6) ].
Definition R_A1as : region :=
mkRegion None 136352 136357 0 0
[ mkChunk 136352 (CImg 5) ].
Definition R_A1at : region :=
mkRegion None 136384 136386 0 0
[ mkChunk 136384 (CImg 2) ].
Definition R_A1au : region :=
mkRegion None 136416 136418 0 0
[ mkChunk 136416 (CImg 2) ].
Definition R_A1av : region :=
mkRegion None 136448 136450 0 0
[ mkChunk 136448 (CImg 2) ].
Definition R_A1aw : region :=
mkRegion None 136480 136482 0 0
[ mkChunk 136480 (CImg 2) ].
Definition R_A1ax : region :=
mkRegion None 136512 136515 0 0
[ mkChunk 136512 (CImg 3) ].
Definition R_A1ay : region :=
mkRegion None 136544 136546 0 0
[ mkChunk 136544 (CImg 2) ].
Definition R_A1az : region :=
mkRegion None 136576 136578 0 0
[ mkChunk 136576 (CImg 2) ].
Definition R_A1ba : region :=
mkRegion None 136608 136610 0 0
[ mkChunk 136608 (CImg 2) ].
Definition R_A1bb : region :=
mkRegion None 136640 136642 0 0
[ mkChunk 136640 (CImg 2) ].
Definition R_A1bc : region :=
mkRegion None 136672 136676 0 0
[ mkChunk 136672 (CImg 4) ].
Definition R_A1bd : region :=
mkRegion None 136704 136707 0 0
[ mkChunk 136704 (CImg 3) ].
Definition R_A1be : region :=
mkRegion None 136736 136739 0 0
[ mkChunk 136736 (CImg 3) ].
Definition R_A1bf : region :=
mkRegion None 136768 136771 0 0
[ mkChunk 136768 (CImg 3) ].
Definition R_A1bg : region :=
mkRegion None 136800 136807 0 0
[ mkChunk 136800 (CImg 7) ].
Definition R_A1bh : region :=
mkRegion None 136832 136835 0 0
[ mkChunk 136832 (CImg 3) ].
Definition R_A1bi : region :=
mkRegion None 136864 138276 0 0
[ mkChunk 136864 (CImg 1412) ].
Definition R_A1bj : region :=
mkRegion None 138280 138376 0 0
[ mkChunk 138280 (CImg 96) ].
Definition R_A1bk : region :=
mkRegion None 138378 663552 0 0
[ mkChunk 138378 (CImg 525174) ].
Definition R_A2a : region :=
mkRegion None 663552 665232 0 0
[ mkChunk 663552 (CImg 1680) ].
Definition R_A2b : region :=
mkRegion None 665280 665648 0 0
[ mkChunk 665280 (CImg 368) ].
Definition R_A2c : region :=
mkRegion None 665776 668600 0 0
[ mkChunk 665776 (CImg 2824) ].
Definition R_A2d : region :=
mkRegion None 668608 668840 0 0
[ mkChunk 668608 (CImg 232) ].
Definition R_A2e : region :=
mkRegion None 668848 668872 0 0
[ mkChunk 668848 (CImg 24) ].
Definition R_A2f : region :=
mkRegion None 668888 668976 0 0
[ mkChunk 668888 (CImg 8);
mkChunk 668896 (CImg 80) ].
Definition R_A2g : region :=
mkRegion None 669000 673120 0 0
[ mkChunk 669000 (CImg 4120) ].
Definition R_A3_1 : region :=
mkRegion None 683480 683520 0 0
[ mkChunk 683480 (CImg 40) ].
Definition R_A3_3 : region :=
mkRegion None 683584 684384 683584 684384
[ mkChunk 683584 (CImg 800) ].
Definition R_A4 : region :=
mkRegion None 688200 688272 688200 688272
[ mkChunk 688200 (CVal 1 (SLit 1));
mkChunk 688201 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6085968 6151504 0 0
[  ].
Definition R_A5a_1 : region :=
mkRegion None 6151504 6151552 6151504 6151509
[ mkChunk 6151504 (CImg 4);
mkChunk 6151508 (CVal 1 (SLit 0));
mkChunk 6151509 (CImg 43) ].
Definition R_A5a_6 : region :=
mkRegion None 6151712 6153868 0 0
[ mkChunk 6151712 (CImg 2112);
mkChunk 6153832 (CVal 8 (SLit 6153832));
mkChunk 6153840 (CVal 8 (SLit 6153832));
mkChunk 6153848 (CVal 8 (SLit 6153832));
mkChunk 6153856 (CVal 8 (SLit 0));
mkChunk 6153864 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6153872 6153944 6153872 6153944
[ mkChunk 6153872 (CVal 4 (SLit 2));
mkChunk 6153876 (CImg 6);
mkChunk 6153882 (CVal 1 (SLit 1));
mkChunk 6153883 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6153952 6154024 0 0
[ mkChunk 6153952 (CVal 8 (SLit 6153952));
mkChunk 6153960 (CImg 24);
mkChunk 6153984 (CVal 8 (SLit 6285816));
mkChunk 6153992 (CImg 24);
mkChunk 6154016 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6154092 6154104 0 0
[ mkChunk 6154092 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6285112 6285808 6285184 6285728
[ mkChunk 6285112 (CImg 16);
mkChunk 6285128 (CVal 8 (SLit 660032));
mkChunk 6285136 (CVal 8 (SLit 0));
mkChunk 6285144 (CVal 8 (SLit 24));
mkChunk 6285152 (CVal 8 (SLit 8));
mkChunk 6285160 (CVal 8 (SLit 0));
mkChunk 6285168 (CVal 8 (SOff 41 0));
mkChunk 6285176 (CImg 16);
mkChunk 6285192 (CVal 4 (SLit 1));
mkChunk 6285196 (CImg 4);
mkChunk 6285200 (CVal 8 (SLit 6285208));
mkChunk 6285208 (CImg 8);
mkChunk 6285216 (CVal 8 (SLit 588512));
mkChunk 6285224 (CImg 248);
mkChunk 6285472 (CVal 8 (SLit 461964));
mkChunk 6285480 (CImg 264);
mkChunk 6285752 (CVal 8 (SOff 1 0));
mkChunk 6285760 (CVal 1 (SLit 1));
mkChunk 6285761 (CImg 7);
mkChunk 6285768 (CVal 8 (SOff 5 0));
mkChunk 6285776 (CVal 8 (SLit 6285120));
mkChunk 6285784 (CVal 8 (SLit 248));
mkChunk 6285792 (CVal 8 (SLit 8));
mkChunk 6285800 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6285816 6285888 0 0
[ mkChunk 6285816 (CImg 48);
mkChunk 6285872 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6286816 6289032 0 0
[ mkChunk 6286816 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6289040 6290136 0 0
[ mkChunk 6289040 (CImg 8);
mkChunk 6289048 (CVal 8 (SLit 351220));
mkChunk 6289056 (CImg 1016);
mkChunk 6290072 (CVal 4 (SLit 0));
mkChunk 6290076 (CImg 4);
mkChunk 6290080 (CVal 4 (SLit 0));
mkChunk 6290084 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6290144 YImgTop.IMG_TOP_B 0 0
[ mkChunk 6290144 (CImg 5408) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A1bh; R_A1bi; R_A1bj; R_A1bk; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A3_1; R_A3_3; R_A4; R_RS; R_A5a_1; R_A5a_6; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
