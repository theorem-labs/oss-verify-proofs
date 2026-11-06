(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated from proofs/cgif/cgif_file_fuzzer/lib/A/AD2j.v (origin/ossv/recipes c8557374ad2e) for fuzz_preset's #102 asan image A' (sha256 1be0f53d96cb...) on 2026-10-29 by gen_ad2_ww.py ff72904f5f71 (h-pre-b3's startb/gen/gen_ad2.py 88e14f1935fe... + --write-window, --img-top-name; hsform a93ebaea058f of startup-set-2026-10-29, the shared tools repository 312c48f0da3), the argv of run_a7.sh with every image A address re-derived by symbol on A''s twin, with its module paths changed: IMG_REGIONS below .data is [img_lo, .data) minus the owned static cells of A/AF0m.v, split at the rw window of A/AB1h.v; from .data on, cgif's regions at the same offsets from their section anchors, checked against the unstripped twin (sha256 bff8519bbe3e...) and cut where owned static cells fall inside; R_A5a's write window is the driver's stores to target_run.initialized and oft_in_callback [0x5dd510, 0x5dd515), R_A3's the .data tail from libunwind's DwarfFDECache _buffer to asan_globals [0xa6600, 0xa6920); the seven ledger cells of lib/Prog/LedgerCells.v (rows 1-5: g_live 0x5dd560, g_peak 0x5dd580, g_count 0x5dd5a0, g_fail_at 0xa65c0 8 bytes, g_ran_out 0x5dd5c0 1 byte; #102 rows 6-7: g_most 0xa65e0 8 bytes, g_own_ran_out 0x5dd540 1 byte), all in the entry's write set ent_W of lib/Prog/EntBase.v:35-38, are cut out of every region (h-pre-b1 rule: IMG_REGIONS = image regions minus owned pieces minus ledger cells); every CVal value read from the 50 hand-off states of A/AB01.v sources (sha256): generator gen_ad2_ww.py ff72904f5f714f72; states AB01.v f5b5317dcf520771; atable AB12.v 33d5feb7660c9f0f; tsegs AB1h.v ccce3ab1d0018bd4; owned AF0m.v 5b0398ece1838602; image fuzz_preset.asan 1be0f53d96cb9d6c; twin fuzz_preset.asan bff8519bbe3ea0e4; tmpl_ad2i AD2i.v c58fc65041856ec0; tmpl_ad2j AD2j.v ff356cba568fba3c *)
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
mkRegion None 66936 118373 0 0
[ mkChunk 66936 (CImg 51437) ].
Definition R_A1i : region :=
mkRegion None 118394 134340 0 0
[ mkChunk 118394 (CImg 15946) ].
Definition R_A1j : region :=
mkRegion None 134344 135013 0 0
[ mkChunk 134344 (CImg 669) ].
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
mkRegion None 138378 659456 0 0
[ mkChunk 138378 (CImg 521078) ].
Definition R_A2a : region :=
mkRegion None 659456 663120 0 0
[ mkChunk 659456 (CImg 3664) ].
Definition R_A2b : region :=
mkRegion None 663168 663536 0 0
[ mkChunk 663168 (CImg 368) ].
Definition R_A2c : region :=
mkRegion None 663664 666488 0 0
[ mkChunk 663664 (CImg 2824) ].
Definition R_A2d : region :=
mkRegion None 666496 666728 0 0
[ mkChunk 666496 (CImg 232) ].
Definition R_A2e : region :=
mkRegion None 666736 666760 0 0
[ mkChunk 666736 (CImg 24) ].
Definition R_A2f : region :=
mkRegion None 666776 666864 0 0
[ mkChunk 666776 (CImg 8);
mkChunk 666784 (CImg 80) ].
Definition R_A2g : region :=
mkRegion None 666888 671008 0 0
[ mkChunk 666888 (CImg 4120) ].
Definition R_A3_1 : region :=
mkRegion None 681368 681408 0 0
[ mkChunk 681368 (CImg 40) ].
Definition R_A3_3 : region :=
mkRegion None 681472 682272 681472 682272
[ mkChunk 681472 (CImg 800) ].
Definition R_A4 : region :=
mkRegion None 686088 686160 686088 686160
[ mkChunk 686088 (CVal 1 (SLit 1));
mkChunk 686089 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6083856 6149392 0 0
[  ].
Definition R_A5a_1 : region :=
mkRegion None 6149392 6149440 6149392 6149397
[ mkChunk 6149392 (CImg 4);
mkChunk 6149396 (CVal 1 (SLit 0));
mkChunk 6149397 (CImg 43) ].
Definition R_A5a_6 : region :=
mkRegion None 6149600 6151756 0 0
[ mkChunk 6149600 (CImg 2112);
mkChunk 6151720 (CVal 8 (SLit 6151720));
mkChunk 6151728 (CVal 8 (SLit 6151720));
mkChunk 6151736 (CVal 8 (SLit 6151720));
mkChunk 6151744 (CVal 8 (SLit 0));
mkChunk 6151752 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6151760 6151832 6151760 6151832
[ mkChunk 6151760 (CVal 4 (SLit 2));
mkChunk 6151764 (CImg 6);
mkChunk 6151770 (CVal 1 (SLit 1));
mkChunk 6151771 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6151840 6151912 0 0
[ mkChunk 6151840 (CVal 8 (SLit 6151840));
mkChunk 6151848 (CImg 24);
mkChunk 6151872 (CVal 8 (SLit 6283704));
mkChunk 6151880 (CImg 24);
mkChunk 6151904 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6151980 6151992 0 0
[ mkChunk 6151980 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6283000 6283696 6283072 6283616
[ mkChunk 6283000 (CImg 16);
mkChunk 6283016 (CVal 8 (SLit 657904));
mkChunk 6283024 (CVal 8 (SLit 0));
mkChunk 6283032 (CVal 8 (SLit 24));
mkChunk 6283040 (CVal 8 (SLit 8));
mkChunk 6283048 (CVal 8 (SLit 0));
mkChunk 6283056 (CVal 8 (SOff 41 0));
mkChunk 6283064 (CImg 16);
mkChunk 6283080 (CVal 4 (SLit 1));
mkChunk 6283084 (CImg 4);
mkChunk 6283088 (CVal 8 (SLit 6283096));
mkChunk 6283096 (CImg 8);
mkChunk 6283104 (CVal 8 (SLit 586384));
mkChunk 6283112 (CImg 248);
mkChunk 6283360 (CVal 8 (SLit 461728));
mkChunk 6283368 (CImg 264);
mkChunk 6283640 (CVal 8 (SOff 1 0));
mkChunk 6283648 (CVal 1 (SLit 1));
mkChunk 6283649 (CImg 7);
mkChunk 6283656 (CVal 8 (SOff 5 0));
mkChunk 6283664 (CVal 8 (SLit 6283008));
mkChunk 6283672 (CVal 8 (SLit 248));
mkChunk 6283680 (CVal 8 (SLit 8));
mkChunk 6283688 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6283704 6283776 0 0
[ mkChunk 6283704 (CImg 48);
mkChunk 6283760 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6284704 6286920 0 0
[ mkChunk 6284704 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6286928 6288024 0 0
[ mkChunk 6286928 (CImg 8);
mkChunk 6286936 (CVal 8 (SLit 350984));
mkChunk 6286944 (CImg 1016);
mkChunk 6287960 (CVal 4 (SLit 0));
mkChunk 6287964 (CImg 4);
mkChunk 6287968 (CVal 4 (SLit 0));
mkChunk 6287972 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6288032 YImgTop.IMG_TOP 0 0
[ mkChunk 6288032 (CImg 3424) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A1bh; R_A1bi; R_A1bj; R_A1bk; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A3_1; R_A3_3; R_A4; R_RS; R_A5a_1; R_A5a_6; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
