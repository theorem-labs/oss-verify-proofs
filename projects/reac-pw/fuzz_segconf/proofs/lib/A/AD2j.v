(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-pw/fuzz_segconf image A by gen_ad2.py 8e0a1d365e83 (3665ff2a7926 with the bridged-argH0, driver-window and program-static rules; the start-up tool set of record at commit d9aa42da992) from this image's 50 collected hand-off states (lib/A/AB01.v), its atable (lib/A/AB12.v), its segment table and rw window (lib/A/AB1h.v) and Tfib_owned_static (lib/A/AF0m.v), templates proofs/cgif/cgif_file_fuzzer/lib/A/AD2i.v and AD2j.v at c8557374ad2e; the world record of the kit (Reusable/YA0n.v, field w_H8) reaches W1 through the section hypothesis H1_8, and argH_range2's step is the one the kit's Reusable/YA02.v argH0 selects. *)
(* Read from: fuzz_segconf.asan (reac-pw/fuzz_segconf asan) sha256 48c5355bdacbc5ba2e0a9ff843627969cb5d2913316654369904b549fc904ef8; unstripped twin sha256 4362701197e4cecdb46108f7694774021f7b8d5e7bd85cfe200fa90ad7a63c32 *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66352 66360 0 0
[ mkChunk 66352 (CImg 8) ].
Definition R_A1e : region :=
mkRegion None 66368 66456 0 0
[ mkChunk 66368 (CImg 88) ].
Definition R_A1f : region :=
mkRegion None 66472 66480 0 0
[ mkChunk 66472 (CImg 8) ].
Definition R_A1g : region :=
mkRegion None 66488 66600 0 0
[ mkChunk 66488 (CImg 112) ].
Definition R_A1h : region :=
mkRegion None 66664 66856 0 0
[ mkChunk 66664 (CImg 192) ].
Definition R_A1i : region :=
mkRegion None 66920 118506 0 0
[ mkChunk 66920 (CImg 51586) ].
Definition R_A1j : region :=
mkRegion None 118527 134500 0 0
[ mkChunk 118527 (CImg 15973) ].
Definition R_A1k : region :=
mkRegion None 134504 135161 0 0
[ mkChunk 134504 (CImg 657) ].
Definition R_A1l : region :=
mkRegion None 135200 135204 0 0
[ mkChunk 135200 (CImg 4) ].
Definition R_A1m : region :=
mkRegion None 135232 135240 0 0
[ mkChunk 135232 (CImg 8) ].
Definition R_A1n : region :=
mkRegion None 135264 135271 0 0
[ mkChunk 135264 (CImg 7) ].
Definition R_A1o : region :=
mkRegion None 135296 135299 0 0
[ mkChunk 135296 (CImg 3) ].
Definition R_A1p : region :=
mkRegion None 135328 135341 0 0
[ mkChunk 135328 (CImg 13) ].
Definition R_A1q : region :=
mkRegion None 135360 135368 0 0
[ mkChunk 135360 (CImg 8) ].
Definition R_A1r : region :=
mkRegion None 135392 135397 0 0
[ mkChunk 135392 (CImg 5) ].
Definition R_A1s : region :=
mkRegion None 135424 135432 0 0
[ mkChunk 135424 (CImg 8) ].
Definition R_A1t : region :=
mkRegion None 135456 135461 0 0
[ mkChunk 135456 (CImg 5) ].
Definition R_A1u : region :=
mkRegion None 135488 135493 0 0
[ mkChunk 135488 (CImg 5) ].
Definition R_A1v : region :=
mkRegion None 135520 135527 0 0
[ mkChunk 135520 (CImg 7) ].
Definition R_A1w : region :=
mkRegion None 135552 135558 0 0
[ mkChunk 135552 (CImg 6) ].
Definition R_A1x : region :=
mkRegion None 135584 135588 0 0
[ mkChunk 135584 (CImg 4) ].
Definition R_A1y : region :=
mkRegion None 135616 135620 0 0
[ mkChunk 135616 (CImg 4) ].
Definition R_A1z : region :=
mkRegion None 135648 135668 0 0
[ mkChunk 135648 (CImg 20) ].
Definition R_A1aa : region :=
mkRegion None 135712 135718 0 0
[ mkChunk 135712 (CImg 6) ].
Definition R_A1ab : region :=
mkRegion None 135744 135751 0 0
[ mkChunk 135744 (CImg 7) ].
Definition R_A1ac : region :=
mkRegion None 135776 135780 0 0
[ mkChunk 135776 (CImg 4) ].
Definition R_A1ad : region :=
mkRegion None 135808 135813 0 0
[ mkChunk 135808 (CImg 5) ].
Definition R_A1ae : region :=
mkRegion None 135840 135843 0 0
[ mkChunk 135840 (CImg 3) ].
Definition R_A1af : region :=
mkRegion None 135872 135878 0 0
[ mkChunk 135872 (CImg 6) ].
Definition R_A1ag : region :=
mkRegion None 135904 135910 0 0
[ mkChunk 135904 (CImg 6) ].
Definition R_A1ah : region :=
mkRegion None 135936 135950 0 0
[ mkChunk 135936 (CImg 14) ].
Definition R_A1ai : region :=
mkRegion None 135968 136003 0 0
[ mkChunk 135968 (CImg 35) ].
Definition R_A1aj : region :=
mkRegion None 136032 136045 0 0
[ mkChunk 136032 (CImg 13) ].
Definition R_A1ak : region :=
mkRegion None 136064 136068 0 0
[ mkChunk 136064 (CImg 4) ].
Definition R_A1al : region :=
mkRegion None 136096 136143 0 0
[ mkChunk 136096 (CImg 47) ].
Definition R_A1am : region :=
mkRegion None 136192 136220 0 0
[ mkChunk 136192 (CImg 28) ].
Definition R_A1an : region :=
mkRegion None 136256 136291 0 0
[ mkChunk 136256 (CImg 35) ].
Definition R_A1ao : region :=
mkRegion None 136352 136360 0 0
[ mkChunk 136352 (CImg 8) ].
Definition R_A1ap : region :=
mkRegion None 136384 136445 0 0
[ mkChunk 136384 (CImg 61) ].
Definition R_A1aq : region :=
mkRegion None 136480 136507 0 0
[ mkChunk 136480 (CImg 27) ].
Definition R_A1ar : region :=
mkRegion None 136544 136602 0 0
[ mkChunk 136544 (CImg 58) ].
Definition R_A1as : region :=
mkRegion None 136640 136699 0 0
[ mkChunk 136640 (CImg 59) ].
Definition R_A1at : region :=
mkRegion None 136736 136806 0 0
[ mkChunk 136736 (CImg 70) ].
Definition R_A1au : region :=
mkRegion None 136864 136924 0 0
[ mkChunk 136864 (CImg 60) ].
Definition R_A1av : region :=
mkRegion None 136960 137005 0 0
[ mkChunk 136960 (CImg 45) ].
Definition R_A1aw : region :=
mkRegion None 137056 137061 0 0
[ mkChunk 137056 (CImg 5) ].
Definition R_A1ax : region :=
mkRegion None 137088 137153 0 0
[ mkChunk 137088 (CImg 65) ].
Definition R_A1ay : region :=
mkRegion None 137216 137222 0 0
[ mkChunk 137216 (CImg 6) ].
Definition R_A1az : region :=
mkRegion None 137248 137253 0 0
[ mkChunk 137248 (CImg 5) ].
Definition R_A1ba : region :=
mkRegion None 137280 137282 0 0
[ mkChunk 137280 (CImg 2) ].
Definition R_A1bb : region :=
mkRegion None 137312 137313 0 0
[ mkChunk 137312 (CImg 1) ].
Definition R_A1bc : region :=
mkRegion None 137344 137396 0 0
[ mkChunk 137344 (CImg 52) ].
Definition R_A1bd : region :=
mkRegion None 137440 137447 0 0
[ mkChunk 137440 (CImg 7) ].
Definition R_A1be : region :=
mkRegion None 137472 137513 0 0
[ mkChunk 137472 (CImg 41) ].
Definition R_A1bf : region :=
mkRegion None 137568 137574 0 0
[ mkChunk 137568 (CImg 6) ].
Definition R_A1bg : region :=
mkRegion None 137600 137746 0 0
[ mkChunk 137600 (CImg 146) ].
Definition R_A1bh : region :=
mkRegion None 137792 137845 0 0
[ mkChunk 137792 (CImg 53) ].
Definition R_A1bi : region :=
mkRegion None 137888 137896 0 0
[ mkChunk 137888 (CImg 8) ].
Definition R_A1bj : region :=
mkRegion None 137920 137925 0 0
[ mkChunk 137920 (CImg 5) ].
Definition R_A1bk : region :=
mkRegion None 137952 137957 0 0
[ mkChunk 137952 (CImg 5) ].
Definition R_A1bl : region :=
mkRegion None 137984 137991 0 0
[ mkChunk 137984 (CImg 7) ].
Definition R_A1bm : region :=
mkRegion None 138016 138022 0 0
[ mkChunk 138016 (CImg 6) ].
Definition R_A1bn : region :=
mkRegion None 138048 138052 0 0
[ mkChunk 138048 (CImg 4) ].
Definition R_A1bo : region :=
mkRegion None 138080 138084 0 0
[ mkChunk 138080 (CImg 4) ].
Definition R_A1bp : region :=
mkRegion None 138112 138116 0 0
[ mkChunk 138112 (CImg 4) ].
Definition R_A1bq : region :=
mkRegion None 138144 138149 0 0
[ mkChunk 138144 (CImg 5) ].
Definition R_A1br : region :=
mkRegion None 138176 138179 0 0
[ mkChunk 138176 (CImg 3) ].
Definition R_A1bs : region :=
mkRegion None 138208 138214 0 0
[ mkChunk 138208 (CImg 6) ].
Definition R_A1bt : region :=
mkRegion None 138240 138344 0 0
[ mkChunk 138240 (CImg 104) ].
Definition R_A1bu : region :=
mkRegion None 138400 138492 0 0
[ mkChunk 138400 (CImg 92) ].
Definition R_A1bv : region :=
mkRegion None 138528 138566 0 0
[ mkChunk 138528 (CImg 38) ].
Definition R_A1bw : region :=
mkRegion None 138592 138615 0 0
[ mkChunk 138592 (CImg 23) ].
Definition R_A1bx : region :=
mkRegion None 138656 138662 0 0
[ mkChunk 138656 (CImg 6) ].
Definition R_A1by : region :=
mkRegion None 138688 138710 0 0
[ mkChunk 138688 (CImg 22) ].
Definition R_A1bz : region :=
mkRegion None 138752 138759 0 0
[ mkChunk 138752 (CImg 7) ].
Definition R_A1ca : region :=
mkRegion None 138784 138813 0 0
[ mkChunk 138784 (CImg 29) ].
Definition R_A1cb : region :=
mkRegion None 138848 138860 0 0
[ mkChunk 138848 (CImg 12) ].
Definition R_A1cc : region :=
mkRegion None 138880 138909 0 0
[ mkChunk 138880 (CImg 29) ].
Definition R_A1cd : region :=
mkRegion None 138944 138950 0 0
[ mkChunk 138944 (CImg 6) ].
Definition R_A1ce : region :=
mkRegion None 138976 138999 0 0
[ mkChunk 138976 (CImg 23) ].
Definition R_A1cf : region :=
mkRegion None 139040 139046 0 0
[ mkChunk 139040 (CImg 6) ].
Definition R_A1cg : region :=
mkRegion None 139072 139096 0 0
[ mkChunk 139072 (CImg 24) ].
Definition R_A1ch : region :=
mkRegion None 139136 139143 0 0
[ mkChunk 139136 (CImg 7) ].
Definition R_A1ci : region :=
mkRegion None 139168 139192 0 0
[ mkChunk 139168 (CImg 24) ].
Definition R_A1cj : region :=
mkRegion None 139232 139239 0 0
[ mkChunk 139232 (CImg 7) ].
Definition R_A1ck : region :=
mkRegion None 139264 139288 0 0
[ mkChunk 139264 (CImg 24) ].
Definition R_A1cl : region :=
mkRegion None 139328 139335 0 0
[ mkChunk 139328 (CImg 7) ].
Definition R_A1cm : region :=
mkRegion None 139360 139383 0 0
[ mkChunk 139360 (CImg 23) ].
Definition R_A1cn : region :=
mkRegion None 139424 139431 0 0
[ mkChunk 139424 (CImg 7) ].
Definition R_A1co : region :=
mkRegion None 139456 139479 0 0
[ mkChunk 139456 (CImg 23) ].
Definition R_A1cp : region :=
mkRegion None 139520 139527 0 0
[ mkChunk 139520 (CImg 7) ].
Definition R_A1cq : region :=
mkRegion None 139552 139576 0 0
[ mkChunk 139552 (CImg 24) ].
Definition R_A1cr : region :=
mkRegion None 139616 141028 0 0
[ mkChunk 139616 (CImg 1412) ].
Definition R_A1cs : region :=
mkRegion None 141032 141128 0 0
[ mkChunk 141032 (CImg 96) ].
Definition R_A1ct : region :=
mkRegion None 141130 659456 0 0
[ mkChunk 141130 (CImg 518326) ].
Definition R_A2a : region :=
mkRegion None 659456 661672 0 0
[ mkChunk 659456 (CImg 2216) ].
Definition R_A2b : region :=
mkRegion None 661728 664984 0 0
[ mkChunk 661728 (CImg 3256) ].
Definition R_A2c : region :=
mkRegion None 665792 666160 0 0
[ mkChunk 665792 (CImg 368) ].
Definition R_A2d : region :=
mkRegion None 666288 669112 0 0
[ mkChunk 666288 (CImg 2824) ].
Definition R_A2e : region :=
mkRegion None 669120 669352 0 0
[ mkChunk 669120 (CImg 232) ].
Definition R_A2f : region :=
mkRegion None 669360 669384 0 0
[ mkChunk 669360 (CImg 24) ].
Definition R_A2g : region :=
mkRegion None 669400 669488 0 0
[ mkChunk 669400 (CImg 8);
mkChunk 669408 (CImg 80) ].
Definition R_A2h : region :=
mkRegion None 669512 673608 0 0
[ mkChunk 669512 (CImg 4096) ].
Definition R_A3 : region :=
mkRegion None 684016 684848 684016 684848
[ mkChunk 684016 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 690504 690576 690504 690576
[ mkChunk 690504 (CVal 1 (SLit 1));
mkChunk 690505 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6088272 6153808 0 0
[  ].
Definition R_A5a_1 : region :=
mkRegion None 6153808 6153977 6153808 6153856
[ mkChunk 6153808 (CImg 4);
mkChunk 6153812 (CVal 1 (SLit 0));
mkChunk 6153813 (CImg 43);
mkChunk 6153976 (CImg 1) ].
Definition R_A5a_2 : region :=
mkRegion None 6154016 6156180 0 0
[ mkChunk 6154016 (CVal 1 (SLit 1));
mkChunk 6154017 (CImg 2119);
mkChunk 6156144 (CVal 8 (SLit 6156144));
mkChunk 6156152 (CVal 8 (SLit 6156144));
mkChunk 6156160 (CVal 8 (SLit 6156144));
mkChunk 6156168 (CVal 8 (SLit 0));
mkChunk 6156176 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6156184 6156256 6156184 6156256
[ mkChunk 6156184 (CVal 4 (SLit 2));
mkChunk 6156188 (CImg 6);
mkChunk 6156194 (CVal 1 (SLit 1));
mkChunk 6156195 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6156264 6156336 0 0
[ mkChunk 6156264 (CVal 8 (SLit 6156264));
mkChunk 6156272 (CImg 24);
mkChunk 6156296 (CVal 8 (SLit 6288128));
mkChunk 6156304 (CImg 24);
mkChunk 6156328 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6156404 6156416 0 0
[ mkChunk 6156404 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6287424 6288120 6287496 6288040
[ mkChunk 6287424 (CImg 16);
mkChunk 6287440 (CVal 8 (SLit 656488));
mkChunk 6287448 (CVal 8 (SLit 0));
mkChunk 6287456 (CVal 8 (SLit 24));
mkChunk 6287464 (CVal 8 (SLit 8));
mkChunk 6287472 (CVal 8 (SLit 0));
mkChunk 6287480 (CVal 8 (SOff 41 0));
mkChunk 6287488 (CImg 16);
mkChunk 6287504 (CVal 4 (SLit 1));
mkChunk 6287508 (CImg 4);
mkChunk 6287512 (CVal 8 (SLit 6287520));
mkChunk 6287520 (CImg 8);
mkChunk 6287528 (CVal 8 (SLit 592776));
mkChunk 6287536 (CImg 248);
mkChunk 6287784 (CVal 8 (SLit 475892));
mkChunk 6287792 (CImg 264);
mkChunk 6288064 (CVal 8 (SOff 1 0));
mkChunk 6288072 (CVal 1 (SLit 1));
mkChunk 6288073 (CImg 7);
mkChunk 6288080 (CVal 8 (SOff 5 0));
mkChunk 6288088 (CVal 8 (SLit 6287432));
mkChunk 6288096 (CVal 8 (SLit 248));
mkChunk 6288104 (CVal 8 (SLit 8));
mkChunk 6288112 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6288128 6288200 0 0
[ mkChunk 6288128 (CImg 48);
mkChunk 6288184 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6289128 6291344 0 0
[ mkChunk 6289128 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6291352 6292448 0 0
[ mkChunk 6291352 (CImg 8);
mkChunk 6291360 (CVal 8 (SLit 364280));
mkChunk 6291368 (CImg 1016);
mkChunk 6292384 (CVal 4 (SLit 0));
mkChunk 6292388 (CImg 4);
mkChunk 6292392 (CVal 4 (SLit 0));
mkChunk 6292396 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6292456 6295552 0 0
[ mkChunk 6292456 (CImg 3096) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A1bh; R_A1bi; R_A1bj; R_A1bk; R_A1bl; R_A1bm; R_A1bn; R_A1bo; R_A1bp; R_A1bq; R_A1br; R_A1bs; R_A1bt; R_A1bu; R_A1bv; R_A1bw; R_A1bx; R_A1by; R_A1bz; R_A1ca; R_A1cb; R_A1cc; R_A1cd; R_A1ce; R_A1cf; R_A1cg; R_A1ch; R_A1ci; R_A1cj; R_A1ck; R_A1cl; R_A1cm; R_A1cn; R_A1co; R_A1cp; R_A1cq; R_A1cr; R_A1cs; R_A1ct; R_A2a; R_A2b; R_A2c; R_A2d; R_A2e; R_A2f; R_A2g; R_A2h; R_A3; R_A4; R_RS; R_A5a_1; R_A5a_2; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
