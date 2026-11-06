(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: proofs/cgif/cgif_file_fuzzer/lib/A/AD2i.v and A/AD2j.v at c8557374ad2e (templates); generated for reac-pw/fuzz_headamp image A by gen_ad2.py from this image's 50 collected hand-off states (lib/A/AB01.v), its atable (lib/A/AB12.v) and Tfib_owned_static (lib/A/AF0m.v); module paths changed *)
(* Read from: fuzz_headamp.asan (reac-pw/fuzz_headamp asan) sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; unstripped twin sha256 b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP09.
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
mkRegion None 66512 66624 0 0
[ mkChunk 66512 (CImg 112) ].
Definition R_A1g : region :=
mkRegion None 66688 66880 0 0
[ mkChunk 66688 (CImg 192) ].
Definition R_A1h : region :=
mkRegion None 66944 118207 0 0
[ mkChunk 66944 (CImg 51263) ].
Definition R_A1i : region :=
mkRegion None 118228 134192 0 0
[ mkChunk 118228 (CImg 15964) ].
Definition R_A1j : region :=
mkRegion None 134196 134862 0 0
[ mkChunk 134196 (CImg 666) ].
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
mkRegion None 136256 136302 0 0
[ mkChunk 136256 (CImg 46) ].
Definition R_A1au : region :=
mkRegion None 136320 136328 0 0
[ mkChunk 136320 (CImg 8) ].
Definition R_A1av : region :=
mkRegion None 136352 136356 0 0
[ mkChunk 136352 (CImg 4) ].
Definition R_A1aw : region :=
mkRegion None 136384 136389 0 0
[ mkChunk 136384 (CImg 5) ].
Definition R_A1ax : region :=
mkRegion None 136416 137844 0 0
[ mkChunk 136416 (CImg 1428) ].
Definition R_A1ay : region :=
mkRegion None 137848 137944 0 0
[ mkChunk 137848 (CImg 96) ].
Definition R_A1az : region :=
mkRegion None 137946 639144 0 0
[ mkChunk 137946 (CImg 501198) ].
Definition R_A1ba : region :=
mkRegion None 639200 639312 0 0
[ mkChunk 639200 (CImg 112) ].
Definition R_A1bb : region :=
mkRegion None 639360 639424 0 0
[ mkChunk 639360 (CImg 64) ].
Definition R_A1bc : region :=
mkRegion None 639456 639824 0 0
[ mkChunk 639456 (CImg 368) ].
Definition R_A1bd : region :=
mkRegion None 639952 642776 0 0
[ mkChunk 639952 (CImg 2824) ].
Definition R_A1be : region :=
mkRegion None 642784 643016 0 0
[ mkChunk 642784 (CImg 232) ].
Definition R_A1bf : region :=
mkRegion None 643024 643048 0 0
[ mkChunk 643024 (CImg 24) ].
Definition R_A1bg : region :=
mkRegion None 643064 643152 0 0
[ mkChunk 643064 (CImg 8);
mkChunk 643072 (CImg 80) ].
Definition R_A1bh : region :=
mkRegion None 643176 647168 0 0
[ mkChunk 643176 (CImg 3992) ].
Definition R_A2 : region :=
mkRegion None 647168 647272 0 0
[ mkChunk 647168 (CImg 104) ].
Definition R_A3 : region :=
mkRegion None 657632 658464 657632 658464
[ mkChunk 657632 (CImg 832) ].
Definition R_A4 : region :=
mkRegion None 661256 661328 661256 661328
[ mkChunk 661256 (CVal 1 (SLit 1));
mkChunk 661257 (CImg 71) ].
Definition R_RS : region :=
mkRegion None 6059024 6124560 0 0
[  ].
Definition R_A5a : region :=
mkRegion None 6124560 6126764 6124560 6126764
[ mkChunk 6124560 (CImg 4);
mkChunk 6124564 (CVal 1 (SLit 0));
mkChunk 6124565 (CImg 2155);
mkChunk 6126728 (CVal 8 (SLit 6126728));
mkChunk 6126736 (CVal 8 (SLit 6126728));
mkChunk 6126744 (CVal 8 (SLit 6126728));
mkChunk 6126752 (CVal 8 (SLit 0));
mkChunk 6126760 (CVal 4 (SOff 8 0)) ].
Definition R_A5b : region :=
mkRegion None 6126768 6126840 6126768 6126840
[ mkChunk 6126768 (CVal 4 (SLit 2));
mkChunk 6126772 (CImg 6);
mkChunk 6126778 (CVal 1 (SLit 1));
mkChunk 6126779 (CImg 61) ].
Definition R_A6 : region :=
mkRegion None 6126848 6126920 0 0
[ mkChunk 6126848 (CVal 8 (SLit 6126848));
mkChunk 6126856 (CImg 24);
mkChunk 6126880 (CVal 8 (SLit 6258712));
mkChunk 6126888 (CImg 24);
mkChunk 6126912 (CVal 8 (SOff 41 0)) ].
Definition R_A7a : region :=
mkRegion None 6126988 6127000 0 0
[ mkChunk 6126988 (CImg 12) ].
Definition R_A7b : region :=
mkRegion None 6258008 6258704 6258080 6258624
[ mkChunk 6258008 (CImg 16);
mkChunk 6258024 (CVal 8 (SLit 633928));
mkChunk 6258032 (CVal 8 (SLit 0));
mkChunk 6258040 (CVal 8 (SLit 24));
mkChunk 6258048 (CVal 8 (SLit 8));
mkChunk 6258056 (CVal 8 (SLit 0));
mkChunk 6258064 (CVal 8 (SOff 41 0));
mkChunk 6258072 (CImg 16);
mkChunk 6258088 (CVal 4 (SLit 1));
mkChunk 6258092 (CImg 4);
mkChunk 6258096 (CVal 8 (SLit 6258104));
mkChunk 6258104 (CImg 8);
mkChunk 6258112 (CVal 8 (SLit 574756));
mkChunk 6258120 (CImg 248);
mkChunk 6258368 (CVal 8 (SLit 459136));
mkChunk 6258376 (CImg 264);
mkChunk 6258648 (CVal 8 (SOff 1 0));
mkChunk 6258656 (CVal 1 (SLit 1));
mkChunk 6258657 (CImg 7);
mkChunk 6258664 (CVal 8 (SOff 5 0));
mkChunk 6258672 (CVal 8 (SLit 6258016));
mkChunk 6258680 (CVal 8 (SLit 248));
mkChunk 6258688 (CVal 8 (SLit 8));
mkChunk 6258696 (CVal 8 (SLit 1)) ].
Definition R_A7c : region :=
mkRegion None 6258712 6258784 0 0
[ mkChunk 6258712 (CImg 48);
mkChunk 6258768 (CImg 16) ].
Definition R_A8 : region :=
mkRegion None 6259712 6261928 0 0
[ mkChunk 6259712 (CImg 2216) ].
Definition R_A9a : region :=
mkRegion None 6261936 6263032 0 0
[ mkChunk 6261936 (CImg 8);
mkChunk 6261944 (CVal 8 (SLit 348392));
mkChunk 6261952 (CImg 1016);
mkChunk 6262968 (CVal 4 (SLit 0));
mkChunk 6262972 (CImg 4);
mkChunk 6262976 (CVal 4 (SLit 0));
mkChunk 6262980 (CImg 52) ].
Definition R_A9b : region :=
mkRegion None 6263040 6266880 0 0
[ mkChunk 6263040 (CImg 3840) ].
Definition IMG_REGIONS : smem := [R_A1a; R_A1b; R_A1c; R_A1d; R_A1e; R_A1f; R_A1g; R_A1h; R_A1i; R_A1j; R_A1k; R_A1l; R_A1m; R_A1n; R_A1o; R_A1p; R_A1q; R_A1r; R_A1s; R_A1t; R_A1u; R_A1v; R_A1w; R_A1x; R_A1y; R_A1z; R_A1aa; R_A1ab; R_A1ac; R_A1ad; R_A1ae; R_A1af; R_A1ag; R_A1ah; R_A1ai; R_A1aj; R_A1ak; R_A1al; R_A1am; R_A1an; R_A1ao; R_A1ap; R_A1aq; R_A1ar; R_A1as; R_A1at; R_A1au; R_A1av; R_A1aw; R_A1ax; R_A1ay; R_A1az; R_A1ba; R_A1bb; R_A1bc; R_A1bd; R_A1be; R_A1bf; R_A1bg; R_A1bh; R_A2; R_A3; R_A4; R_RS; R_A5a; R_A5b; R_A6; R_A7a; R_A7b; R_A7c; R_A8; R_A9a; R_A9b].
