(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import AxSymExec3 AsanPlan MainExport MainHint StartupHS2Both.
(* the hand-off states and the plans' variable rename *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import StartupHSBoth727 AsanRenum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* port727: the r30q2 list, kept under this name; both_mem_facts () is defined from it below *)
Definition both_mem_facts_r30 : list mfact := [
  MCell (ZLit 877696) 8 (ZLit 1)
  ; MCell (ZLit 877704) 1 (ZLit 1)
  ; MCell (ZLit 877784) 8 (ZMul (ZLit 4096) (ZV 208))
  ; MCell (ZLit 877792) 8 (ZLit 137439023104)
  ; MCell (ZLit 877800) 8 (ZLit 95006)
  ; MCell (ZLit 877816) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))
  ; MCell (ZLit 877824) 4 (ZLit 18446744073709551615)
  ; MCell (ZLit 877832) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))
  ; MCell (ZLit 877840) 1 (ZLit 0)
  ; MCell (ZLit 877848) 8 (ZLit 4096)
  ; MCell (ZLit 877856) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 877864) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 877872) 8 (ZLit 8388608)
  ; MCell (ZLit 877880) 8 (ZLit 106643)
  ; MCell (ZLit 878464) 1 (ZLit 0)
  ; MZeroC (ZLit 878465) 3
  ; MCell (ZLit 878576) 8 (ZLit 268435456)
  ; MCell (ZLit 878584) 8 (ZLit 241591905)
  ; MCell (ZLit 878592) 8 (ZLit 1048576)
  ; MCell (ZLit 878664) 1 (ZLit 0)
  ; MCell (ZLit 878665) 1 (ZLit 0)
  ; MCell (ZLit 881400) 8 (ZLit 1099511627776)
  ; MCell (ZLit 881408) 2 (ZLit 16)
  ; MCell (ZLit 881410) 2 (ZLit 2048)
  ; MCell (ZLit 881412) 1 (ZLit 1)
  ; MCell (ZLit 881464) 4 (ZLit 4294967295)
  ; MCell (ZLit 881468) 4 (ZLit 256)
  ; MCell (ZLit 881472) 4 (ZLit 1024)
  ; MCell (ZLit 881476) 4 (ZLit 16)
  ; MCell (ZLit 881480) 4 (ZLit 2048)
  ; MCell (ZLit 881484) 1 (ZLit 0)
  ; MCell (ZLit 881488) 8 (ZLit 72340168526266369)
  ; MCell (ZLit 881496) 8 (ZLit 85899345936)
  ; MCell (ZLit 881504) 1 (ZLit 0)
  ; MCell (ZLit 881508) 4 (ZLit 4096)
  ; MCell (ZLit 881512) 8 (ZLit 816043786240)
  ; MCell (ZLit 881520) 4 (ZLit 85)
  ; MCell (ZLit 881524) 1 (ZLit 1)
  ; MCell (ZLit 881528) 8 (ZLit 0)
  ; MRo (ZLit 881536) 6 (ZLit 4294967296)
  ; MCell (ZLit 881542) 1 (ZLit 1)
  ; MCell (ZLit 881543) 1 (ZLit 0)
  ; MCell (ZLit 881544) 8 (ZLit 72340172838010881)
  ; MCell (ZLit 881552) 2 (ZLit 1)
  ; MCell (ZLit 881554) 1 (ZLit 0)
  ; MCell (ZLit 881556) 4 (ZLit 0)
  ; MCell (ZLit 881560) 1 (ZLit 1)
  ; MCell (ZLit 881564) 4 (ZLit 2)
  ; MCell (ZLit 881568) 8 (ZLit 82674)
  ; MCell (ZLit 881576) 4 (ZLit 65793)
  ; MCell (ZLit 881584) 1 (ZLit 1)
  ; MCell (ZLit 881592) 8 (ZLit 32)
  ; MCell (ZLit 881600) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20400))
  ; MCell (ZLit 881608) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZLit 881616) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19880))
  ; MCell (ZLit 881648) 8 (ZLit 0)
  ; MCell (ZLit 889720) 1 (ZLit 1)
  ; MCell (ZLit 889721) 1 (ZLit 1)
  ; MCell (ZLit 889722) 1 (ZLit 1)
  ; MCell (ZLit 889724) 4 (ZLit 299)
  ; MCell (ZLit 889728) 8 (ZLit 889736)
  ; MCell (ZLit 889736) 8 (ZMul (ZLit 4096) (ZV 207))
  ; MCell (ZLit 889752) 4 (ZLit 2)
  ; MCell (ZLit 889756) 1 (ZLit 1)
  ; MCell (ZLit 889760) 1 (ZLit 1)
  ; MCell (ZLit 889764) 4 (ZLit 0)
  ; MCell (ZLit 891704) 8 (ZLit 2147450880)
  ; MCell (ZLit 891712) 4 (ZLit 1)
  ; MCell (ZLit 895000) 1 (ZLit 1)
  ; MCell (ZLit 895001) 1 (ZLit 1)
  ; MCell (ZLit 895002) 1 (ZLit 0)
  ; MCell (ZLit 895003) 1 (ZLit 0)
  ; MCell (ZLit 895008) 8 (ZLit 140737488355327)
  ; MCell (ZLit 895032) 1 (ZLit 1)
  ; MCell (ZLit 895036) 4 (ZLit 30)
  ; MCell (ZLit 895152) 8 (ZLit 1)
  ; MCell (ZLit 895160) 8 (ZLit 4096)
  ; MCell (ZLit 895872) 8 (ZLit 895936)
  ; MCell (ZLit 895936) 8 (ZLit 864776)
  ; MCell (ZLit 895944) 4 (ZLit 5)
  ; MCell (ZLit 895952) 8 (ZLit 0)
  ; MCell (ZLit 895960) 8 (ZLit 0)
  ; MCell (ZLit 895968) 8 (ZLit 0)
  ; MZeroC (ZLit 895976) 5
  ; MCell (ZLit 896040) 1 (ZLit 1)
  ; MCell (ZLit 896048) 1 (ZLit 1)
  ; MCell (ZLit 896056) 8 (ZLit 896152)
  ; MCell (ZLit 896064) 8 (ZLit 896104)
  ; MCell (ZLit 896072) 8 (ZLit 0)
  ; MCell (ZLit 896088) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 65536))
  ; MCell (ZLit 896096) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 160))
  ; MCell (ZLit 896104) 8 (ZLit 0)
  ; MCell (ZLit 896112) 4 (ZLit 0)
  ; MCell (ZLit 896116) 4 (ZLit 0)
  ; MCell (ZLit 896120) 8 (ZLit 0)
  ; MCell (ZLit 896128) 8 (ZLit 0)
  ; MCell (ZLit 896136) 4 (ZLit 0)
  ; MCell (ZLit 896140) 4 (ZLit 0)
  ; MCell (ZLit 896144) 4 (ZLit 0)
  ; MCell (ZLit 896148) 4 (ZLit 0)
  ; MCell (ZLit 896152) 8 (ZLit 433820)
  ; MCell (ZLit 896160) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 896168) 4 (ZLit 0)
  ; MCell (ZLit 896176) 8 (ZLit 0)
  ; MCell (ZLit 896184) 4 (ZLit 0)
  ; MCell (ZLit 896188) 4 (ZLit 0)
  ; MCell (ZLit 896192) 8 (ZLit 1)
  ; MCell (ZLit 896200) 8 (ZLit 1)
  ; MCell (ZLit 896208) 8 (ZLit 1)
  ; MCell (ZLit 896216) 8 (ZLit 1)
  ; MCell (ZLit 896224) 8 (ZMul (ZLit 4096) (ZV 245))
  ; MCell (ZLit 896232) 8 (ZLit 4096)
  ; MCell (ZLit 896240) 8 (ZLit 1)
  ; MCell (ZLit 896248) 8 (ZLit 0)
  ; MCell (ZLit 896256) 8 (ZLit 0)
  ; MCell (ZLit 896264) 8 (ZLit 0)
  ; MCell (ZLit 896272) 8 (ZLit 0)
  ; MCell (ZLit 896280) 8 (ZLit 0)
  ; MCell (ZLit 896288) 8 (ZLit 0)
  ; MCell (ZLit 896296) 8 (ZLit 0)
  ; MCell (ZLit 896304) 8 (ZLit 0)
  ; MCell (ZLit 896312) 4 (ZLit 0)
  ; MCell (ZLit 1424776) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 65536))
  ; MCell (ZLit 1424784) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20416))
  ; MCell (ZLit 1424792) 8 (ZLit 417680)
  ; MCell (ZLit 1424801) 1 (ZLit 1)
  ; MCell (ZLit 1480144) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-160)))
  ; MCell (ZLit 1480152) 4 (ZLit 0)
  ; MCell (ZLit 1480160) 8 (ZLit 4096)
  ; MCell (ZLit 1488480) 1 (ZLit 0)
  ; MZeroC (ZLit 1488481) 3
  ; MCell (ZLit 1488488) 8 (ZLit 1)
  ; MCell (ZLit 1488496) 8 (ZLit 0)
  ; MCell (ZLit 1488504) 8 (ZLit 0)
  ; MCell (ZLit 1488512) 8 (ZLit 82674)
  ; MCell (ZLit 1488520) 8 (ZLit 128849084416)
  ; MCell (ZLit 1488528) 8 (ZLit 0)
  ; MCell (ZLit 1488536) 8 (ZLit 0)
  ; MCell (ZLit 1488544) 8 (ZLit 0)
  ; MCell (ZLit 1488552) 8 (ZLit 0)
  ; MCell (ZLit 1488560) 8 (ZLit 1103823372545)
  ; MCell (ZLit 1488568) 8 (ZLit 4294967296)
  ; MCell (ZLit 1488576) 8 (ZLit 0)
  ; MCell (ZLit 1488584) 8 (ZLit 0)
  ; MCell (ZLit 1488592) 8 (ZLit 0)
  ; MCell (ZLit 1488600) 8 (ZLit 65537)
  ; MCell (ZLit 1488608) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 1488616) 8 (ZLit 72176)
  ; MCell (ZLit 1488624) 8 (ZLit 256)
  ; MCell (ZLit 1488632) 8 (ZLit 0)
  ; MCell (ZLit 1488640) 8 (ZLit 0)
  ; MCell (ZLit 1488648) 8 (ZLit 0)
  ; MCell (ZLit 1488656) 8 (ZLit 0)
  ; MCell (ZLit 1488664) 8 (ZLit 18446744069414584320)
  ; MCell (ZLit 1488672) 8 (ZLit 1)
  ; MCell (ZLit 1488680) 8 (ZLit 83534)
  ; MCell (ZLit 1488688) 8 (ZLit 82674)
  ; MCell (ZLit 1488696) 8 (ZLit 82674)
  ; MCell (ZLit 1488704) 8 (ZLit 1103823372544)
  ; MCell (ZLit 1488712) 8 (ZLit 0)
  ; MCell (ZLit 1488720) 8 (ZLit 126686)
  ; MCell (ZLit 1488728) 8 (ZLit 72339073309605888)
  ; MCell (ZLit 1488736) 8 (ZLit 72340172838076673)
  ; MCell (ZLit 1488744) 8 (ZLit 16843009)
  ; MCell (ZLit 1488752) 8 (ZLit 1103806595073)
  ; MCell (ZLit 1488760) 8 (ZLit 104707)
  ; MCell (ZLit 1488768) 8 (ZLit 281474976710912)
  ; MCell (ZLit 1488976) 8 (ZLit 396852)
  ; MCell (ZLit 1489016) 8 (ZLit 1)
  ; MCell (ZLit 1489040) 8 (ZLit 417540)
  ; MCell (ZLit 1489048) 8 (ZLit 417308)
  ; MCell (ZLit 1489056) 8 (ZLit 507672)
  ; MCell (ZLit 1489096) 1 (ZLit 1)
  ; MCell (ZLit 1489368) 1 (ZLit 0)
  ; MCell (ZLit 1751568) 8 (ZLit 8388608)
  ; MCell (ZLit 1751576) 8 (ZMul (ZLit 4096) (ZV 454))
  ; MCell (ZLit 1751588) 1 (ZLit 0)
  ; MZeroC (ZLit 1751589) 3
  ; MCell (ZLit 6011416) 4 (ZLit 1)
  ; MCell (ZLit 6011424) 1 (ZLit 0)
  ; MZeroC (ZLit 6011425) 3
  ; MCell (ZLit 6011432) 8 (ZMul (ZLit 4096) (ZV 453))
  ; MCell (ZLit 6274816) 1 (ZLit 0)
  ; MCell (ZLit 6274820) 4 (ZLit 0)
  ; MCell (ZLit 6274824) 8 (ZLit 72340172821233664)
  ; MCell (ZLit 6274832) 4 (ZLit 257)
  ; MCell (ZLit 6274836) 2 (ZLit 0)
  ; MCell (ZLit 6274838) 1 (ZLit 0)
  ; MCell (ZLit 6274840) 4 (ZLit 1)
  ; MCell (ZLit 6274848) 8 (ZLit 82674)
  ; MCell (ZLit 6274856) 4 (ZLit 1)
  ; MCell (ZLit 6275264) 8 (ZLit 6275328)
  ; MCell (ZLit 6275328) 8 (ZLit 874456)
  ; MCell (ZLit 6275336) 4 (ZLit 38)
  ; MCell (ZLit 6275344) 8 (ZLit 0)
  ; MCell (ZLit 6275352) 8 (ZLit 0)
  ; MCell (ZLit 6275360) 8 (ZLit 0)
  ; MZeroC (ZLit 6275368) 38
  ; MCell (ZLit 6275432) 1 (ZLit 1)
  ; MCell (ZLit 6275440) 1 (ZLit 0)
  ; MCell (ZLit 6275441) 1 (ZLit 1)
  ; MCell (ZLit 6275442) 2 (ZLit 0)
  ; MCell (ZLit 6275448) 2 (ZLit 0)
  ; MCell (ZLit 6275456) 8 (ZLit 82674)
  ; MCell (ZLit 6275464) 2 (ZLit 0)
  ; MCell (ZLit 6671400) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))) (ZLit 16))
  ; MCell (ZLit 6671424) 8 (ZLit 839400)
  ; MCell (ZLit 6671432) 8 (ZLit 0)
  ; MCell (ZLit 6671440) 8 (ZLit 24)
  ; MCell (ZLit 6671448) 8 (ZLit 8)
  ; MCell (ZLit 6671456) 8 (ZLit 0)
  ; MCell (ZLit 6671464) 8 (ZLit 6671464)
  ; MCell (ZLit 6671472) 8 (ZLit 6671464)
  ; MCell (ZLit 6671480) 8 (ZLit 6671464)
  ; MCell (ZLit 6671488) 8 (ZLit 0)
  ; MCell (ZLit 6671496) 4 (ZV 44)
  ; MCell (ZLit 6671504) 4 (ZLit 2)
  ; MCell (ZLit 6671514) 1 (ZLit 1)
  ; MCell (ZLit 6671576) 8 (ZLit 6676768)
  ; MCell (ZLit 6671584) 8 (ZLit 6671584)
  ; MCell (ZLit 6671616) 8 (ZLit 6672448)
  ; MCell (ZLit 6671648) 8 (ZV 45)
  ; MCell (ZLit 6671656) 8 (ZLit 6671696)
  ; MCell (ZLit 6671664) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MCell (ZLit 6671672) 8 (ZMul (ZLit 4096) (ZV 310))
  ; MCell (ZLit 6671696) 8 (ZLit 1)
  ; MCell (ZLit 6671704) 8 (ZLit 6673712)
  ; MRo (ZLit 6671800) 8 (ZV 45)
  ; MWr (ZLit 6671808) 8768
  ; MCell (ZLit 6671824) 4 (ZLit 1)
  ; MCell (ZLit 6671832) 8 (ZLit 6671840)
  ; MCell (ZLit 6671848) 8 (ZLit 777208)
  ; MCell (ZLit 6672104) 8 (ZLit 507672)
  ; MCell (ZLit 6672384) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))
  ; MCell (ZLit 6672392) 1 (ZLit 1)
  ; MCell (ZLit 6672400) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24))
  ; MCell (ZLit 6672408) 8 (ZLit 6671416)
  ; MCell (ZLit 6672416) 8 (ZLit 248)
  ; MCell (ZLit 6672424) 8 (ZLit 8)
  ; MCell (ZLit 6672432) 8 (ZLit 1)
  ; MCell (ZLit 6672440) 8 (ZLit 4096)
  ; MCell (ZLit 6672496) 8 (ZV 9)
  ; MCell (ZLit 6672528) 4 (ZLit 1)
  ; MCell (ZLit 6672532) 4 (ZLit 1)
  ; MCell (ZLit 6672552) 8 (ZLit 97)
  ; MCell (ZLit 6672560) 8 (ZLit 0)
  ; MCell (ZLit 6673000) 8 (ZLit 10)
  ; MCell (ZLit 6673104) 8 (ZLit 2)
  ; MCell (ZLit 6673136) 8 (ZLit 2)
  ; MCell (ZLit 6673168) 8 (ZLit 2)
  ; MCell (ZLit 6673432) 1 (ZLit 1)
  ; MCell (ZLit 6675680) 8 (ZLit 396336)
  ; MCell (ZLit 6676704) 4 (ZLit 0)
  ; MCell (ZLit 6676712) 4 (ZLit 0)
  ; MCell (ZLit 6676768) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MCell (ZLit 864832) 8 (ZLit 8)
  ; MCell (ZLit 864840) 8 (ZLit 138074)
  ; MCell (ZLit 864856) 4 (ZLit 2)
  ; MWr (ZLit 839680) 5832120
  ; MImg 877705 877784
  ; MImg 877808 877816
  ; MImg 877828 877832
  ; MImg 877841 877848
  ; MImg 877888 878464
  ; MImg 878468 878576
  ; MImg 878600 878664
  ; MImg 878666 881400
  ; MImg 881413 881464
  ; MImg 881485 881488
  ; MImg 881505 881508
  ; MImg 881525 881528
  ; MImg 881555 881556
  ; MImg 881561 881564
  ; MImg 881580 881584
  ; MImg 881585 881592
  ; MImg 881624 881648
  ; MImg 881656 881720
  ; MImg 886504 889720
  ; MImg 889723 889724
  ; MImg 889744 889752
  ; MImg 889757 889760
  ; MImg 889761 889764
  ; MImg 889768 891704
  ; MImg 891716 895000
  ; MImg 895004 895008
  ; MImg 895016 895032
  ; MImg 895033 895036
  ; MImg 895040 895152
  ; MImg 895168 895872
  ; MImg 895880 895936
  ; MImg 895948 895952
  ; MImg 895981 896040
  ; MImg 896041 896048
  ; MImg 896049 896056
  ; MImg 896080 896088
  ; MImg 896172 896176
  ; MImg 896316 1424776
  ; MImg 1424800 1424801
  ; MImg 1424802 1480144
  ; MImg 1480156 1480160
  ; MImg 1480168 1480192
  ; MImg 1484287 1484288
  ; MImg 1488383 1488480
  ; MImg 1488484 1488488
  ; MImg 1488776 1488976
  ; MImg 1488984 1489016
  ; MImg 1489024 1489040
  ; MImg 1489064 1489096
  ; MImg 1489097 1489368
  ; MImg 1489369 1751560
  ; MImg 6011420 6011424
  ; MImg 6011428 6011432
  ; MImg 6011440 6274816
  ; MImg 6274817 6274820
  ; MImg 6274839 6274840
  ; MImg 6274844 6274848
  ; MImg 6274860 6275264
  ; MImg 6275272 6275328
  ; MImg 6275340 6275344
  ; MImg 6275406 6275432
  ; MImg 6275433 6275440
  ; MImg 6275444 6275448
  ; MImg 6275450 6275456
  ; MImg 6275466 6671400
  ; MImg 6671408 6671424
  ; MImg 6671500 6671504
  ; MImg 6671508 6671514
  ; MImg 6671515 6671576
  ; MImg 6671592 6671616
  ; MImg 6671624 6671648
  ; MImg 6671680 6671696
  ; MImg 6671712 6671800
  ; MImg 6671808 6671824
  ; MImg 6671828 6671832
  ; MImg 6671840 6671848
  ; MImg 6671856 6672104
  ; MImg 6672112 6672376
  ; MImg 6672393 6672400
  ; MImg 6672448 6672496
  ; MImg 6672504 6672520
  ; MImg 6672536 6672544
  ; MImg 6672600 6672616
  ; MImg 6672624 6672720
  ; MImg 6672728 6672752
  ; MImg 6672760 6672784
  ; MImg 6672792 6673000
  ; MImg 6673008 6673104
  ; MImg 6673112 6673136
  ; MImg 6673144 6673168
  ; MImg 6673176 6673432
  ; MImg 6673433 6673440
  ; MImg 6673448 6675664
  ; MImg 6675672 6675680
  ; MImg 6675688 6676704
  ; MImg 6676708 6676712
  ; MImg 6676716 6676768
  ; MImg 6676776 6680576
  ; MImg 864848 864856
  ; MImg 864860 877696
  ; MImg 65536 864832
  ; MWr (ZLit 2147459072) 826880
  ; MZero (ZLit 2147459072) 9452
  ; MCell (ZLit 2147468524) 1 (ZLit 4)
  ; MFill (ZLit 2147468525) 3 249
  ; MZeroC (ZLit 2147468528) 28
  ; MCell (ZLit 2147468556) 1 (ZLit 6)
  ; MFill (ZLit 2147468557) 7 249
  ; MZeroC (ZLit 2147468564) 2
  ; MCell (ZLit 2147468566) 1 (ZLit 7)
  ; MFill (ZLit 2147468567) 5 249
  ; MZeroC (ZLit 2147468572) 3
  ; MCell (ZLit 2147468575) 1 (ZLit 3)
  ; MFill (ZLit 2147468576) 4 249
  ; MZeroC (ZLit 2147468580) 2
  ; MCell (ZLit 2147468582) 1 (ZLit 4)
  ; MFill (ZLit 2147468583) 5 249
  ; MZeroC (ZLit 2147468588) 3
  ; MCell (ZLit 2147468591) 1 (ZLit 1)
  ; MFill (ZLit 2147468592) 4 249
  ; MZeroC (ZLit 2147468596) 2
  ; MCell (ZLit 2147468598) 1 (ZLit 4)
  ; MFill (ZLit 2147468599) 5 249
  ; MZeroC (ZLit 2147468604) 2
  ; MCell (ZLit 2147468606) 1 (ZLit 3)
  ; MFill (ZLit 2147468607) 5 249
  ; MZeroC (ZLit 2147468612) 3
  ; MCell (ZLit 2147468615) 1 (ZLit 5)
  ; MFill (ZLit 2147468616) 4 249
  ; MZeroC (ZLit 2147468620) 4
  ; MCell (ZLit 2147468624) 1 (ZLit 4)
  ; MFill (ZLit 2147468625) 7 249
  ; MZeroC (ZLit 2147468632) 3
  ; MCell (ZLit 2147468635) 1 (ZLit 1)
  ; MFill (ZLit 2147468636) 4 249
  ; MZeroC (ZLit 2147468640) 3
  ; MCell (ZLit 2147468643) 1 (ZLit 2)
  ; MFill (ZLit 2147468644) 4 249
  ; MZeroC (ZLit 2147468648) 4
  ; MCell (ZLit 2147468652) 1 (ZLit 5)
  ; MFill (ZLit 2147468653) 7 249
  ; MZeroC (ZLit 2147468660) 3
  ; MCell (ZLit 2147468663) 1 (ZLit 4)
  ; MFill (ZLit 2147468664) 4 249
  ; MZeroC (ZLit 2147468668) 2
  ; MCell (ZLit 2147468670) 1 (ZLit 6)
  ; MFill (ZLit 2147468671) 5 249
  ; MZeroC (ZLit 2147468676) 3
  ; MCell (ZLit 2147468679) 1 (ZLit 4)
  ; MFill (ZLit 2147468680) 4 249
  ; MZeroC (ZLit 2147468684) 2
  ; MCell (ZLit 2147468686) 1 (ZLit 6)
  ; MFill (ZLit 2147468687) 5 249
  ; MZeroC (ZLit 2147468692) 3
  ; MCell (ZLit 2147468695) 1 (ZLit 6)
  ; MFill (ZLit 2147468696) 4 249
  ; MZeroC (ZLit 2147468700) 2
  ; MCell (ZLit 2147468702) 1 (ZLit 5)
  ; MFill (ZLit 2147468703) 5 249
  ; MZeroC (ZLit 2147468708) 2
  ; MCell (ZLit 2147468710) 1 (ZLit 7)
  ; MFill (ZLit 2147468711) 5 249
  ; MZeroC (ZLit 2147469588) 256
  ; MFill (ZLit 2147469844) 64 249
  ; MZeroC (ZLit 2147469908) 16
  ; MFill (ZLit 2147469924) 4 249
  ; MZeroC (ZLit 2147468716) 140
  ; MFill (ZLit 2147468856) 32 249
  ; MZero (ZLit 2147468888) 512
  ; MFill (ZLit 2147469400) 128 249
  ; MZeroC (ZLit 2147469528) 19
  ; MCell (ZLit 2147469547) 1 (ZLit 6)
  ; MFill (ZLit 2147469548) 4 249
  ; MZeroC (ZLit 2147469552) 7
  ; MCell (ZLit 2147469559) 1 (ZLit 6)
  ; MFill (ZLit 2147469560) 4 249
  ; MZeroC (ZLit 2147469564) 8
  ; MFill (ZLit 2147469572) 4 249
  ; MZeroC (ZLit 2147469576) 8
  ; MFill (ZLit 2147469584) 4 249
  ; MZeroC (ZLit 2147469928) 15
  ; MCell (ZLit 2147469943) 1 (ZLit 6)
  ; MFill (ZLit 2147469944) 4 249
  ; MZeroC (ZLit 2147469948) 2
  ; MCell (ZLit 2147469950) 1 (ZLit 6)
  ; MFill (ZLit 2147469951) 5 249
  ; MZeroC (ZLit 2147469956) 3
  ; MCell (ZLit 2147469959) 1 (ZLit 4)
  ; MFill (ZLit 2147469960) 4 249
  ; MZero (ZLit 2147469964) 90370
  ; MFill (ZLit 2147560334) 256 249
  ; MZero (ZLit 2147560590) 715690
  ; MFill (ZLit 2148276280) 8192 249
  ; MZero (ZLit 2148284472) 1480
  ; MWr (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 8388608
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-48))) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 8))
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-40))) 8 (ZLit 0)
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-32))) 8 (ZLit 0)
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-24))) 8 (ZLit 0)
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-16))) 8 (ZLit 0)
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8))) 8 (ZLit 0)
  ; MRo (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) 8 (ZV 1)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 8)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 16)) 8 (ZMul (ZLtu (ZLit 1) (ZV 1)) (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 3) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 185)))
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24)) 8 (ZLit 3)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 32)) 8 (ZLit 65600)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 40)) 8 (ZLit 4)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 48)) 8 (ZLit 56)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 56)) 8 (ZLit 5)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 64)) 8 (ZLit 11)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 72)) 8 (ZLit 16)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 80)) 8 (ZV 9)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 88)) 8 (ZLit 6)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 96)) 8 (ZLit 4096)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 104)) 8 (ZLit 11)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 112)) 8 (ZV 8)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 120)) 8 (ZLit 12)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 128)) 8 (ZV 8)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 136)) 8 (ZLit 23)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 144)) 8 (ZLit 0)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 152)) 8 (ZLit 25)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 160)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 8) (ZV 4)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 184))
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 168)) 8 (ZLit 0)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 176)) 8 (ZLit 0)
  ; MWrS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; MWr (ZMul (ZLit 4096) (ZV 78)) 65536
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19880)) 8 (ZMul (ZLit 4096) (ZV 471))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19888)) 8 (ZLit 4096)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19896)) 8 (ZLit 1)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904)) 8 (ZLit 875632)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19912)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920)) 8 (ZLit 875696)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19928)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936)) 8 (ZLit 875760)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19944)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952)) 8 (ZLit 875824)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19960)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968)) 8 (ZLit 875888)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19976)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984)) 8 (ZLit 875952)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19992)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000)) 8 (ZLit 876016)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20008)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016)) 8 (ZLit 876080)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20024)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032)) 8 (ZLit 876144)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20040)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048)) 8 (ZLit 876208)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20056)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064)) 8 (ZLit 876272)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20072)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080)) 8 (ZLit 876336)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20088)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096)) 8 (ZLit 876400)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20104)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20112)) 8 (ZLit 876464)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20120)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20128)) 8 (ZLit 876528)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20136)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20112))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20144)) 8 (ZLit 876592)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20152)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20128))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20160)) 8 (ZLit 876656)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20168)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20144))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20176)) 8 (ZLit 876720)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20184)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20160))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20192)) 8 (ZLit 876784)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20200)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20176))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20208)) 8 (ZLit 876848)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20216)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20192))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20224)) 8 (ZLit 876912)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20232)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20208))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20240)) 8 (ZLit 876976)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20248)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20224))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20256)) 8 (ZLit 877040)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20264)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20240))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20272)) 8 (ZLit 877104)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20280)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20256))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20288)) 8 (ZLit 877168)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20296)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20272))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20304)) 8 (ZLit 877232)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20312)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20288))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20320)) 8 (ZLit 877296)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20328)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20304))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20336)) 8 (ZLit 877360)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20344)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20320))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20352)) 8 (ZLit 877424)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20360)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20336))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20368)) 8 (ZLit 877488)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20376)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20352))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20384)) 8 (ZLit 877552)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20392)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20368))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20400)) 8 (ZLit 877616)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20408)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20384))
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192
  ; MWr (ZMul (ZLit 4096) (ZV 207)) 3727360
  ; MZero (ZMul (ZLit 4096) (ZV 207)) 3727360
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) 465920
  ; MWr (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096
  ; MZero (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096
  ; MWr (ZAdd (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZMul (ZLit (-512)) (ZV 209))) (ZLit 19327328256)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 227)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 227)) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 8)) 8 (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344))))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 16)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344)))) (ZLit (-8388608)))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 24)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 32)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 40)) 1 (ZLit 0)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 41)) 7
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6673512)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6673732)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 64)) 8 (ZLit 6671672)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 72)) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3169)) 927
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 228)) 65536
  ; MCell (ZMul (ZLit 4096) (ZV 228)) 8 (ZLit 843688)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 8)) 4 (ZLit 0)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 12)) 4
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 16)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 24)) 4 (ZLit 0)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 28)) 4
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 32)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 40)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 48)) 1 (ZLit 0)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 49)) 63
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 112)) 4 (ZLit 2)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 116)) 1 (ZLit 1)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 117)) 3
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 120)) 4 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 124)) 4 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 128)) 4 (ZLit 0)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 132)) 4
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 136)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 144)) 4 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 148)) 2 (ZLit 1024)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 150)) 2
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 152)) 8 (ZMul (ZLit 4096) (ZV 227))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 160)) 65376
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192
  ; MFill (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 254
  ; MZeroC (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147459072)) 0
  ; MWr (ZMul (ZLit 4096) (ZV 245)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 245)) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 245)) (ZLit 8)) 4088
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 310)) 4096
  ; MZeroC (ZMul (ZLit 4096) (ZV 310)) 24
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6671664)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 32)) 8 (ZLit 0)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 40)) 4056
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; MZeroC (ZMul (ZLit 4096) (ZV 377)) 88
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 377)) (ZLit 88)) 8 (ZLit 20)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 377)) (ZLit 96)) 11571104
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400
  ; MWr (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; MZeroC (ZMul (ZLit 4096) (ZV 453)) 16
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 24)) 4 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 28)) 4 (ZLit 1)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 32)) 1048544
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 453)) (ZLit 2147450880)) 131072
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 453)) (ZLit 2147450880)) 131072
  ; MWr (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 8)) 8 (ZLit 304132)
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MWr (ZMul (ZLit 4096) (ZV 471)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 471)) 8 (ZLit 12297829379609722881)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 8)) 8 (ZLit 875632)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 16)) 8 (ZLit 877616)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 24)) 4072
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 471)) (ZLit 2147450880)) 512
].

(* #1390: both_mem_facts_r30 with each item just727 refuses on the #1390 hand-off states moved to the value those states hold (pl3_mf_cure_1390_g1.py); the r30 lemmas keep both_mem_facts_r30 *)
Definition both_mem_facts_r30_1390 : list mfact := [
  MCell (ZLit 877696) 8 (ZLit 1)
  ; MCell (ZLit 877704) 1 (ZLit 1)
  ; MCell (ZLit 877784) 8 (ZMul (ZLit 4096) (ZV 208))
  ; MCell (ZLit 877792) 8 (ZLit 137439023104)
  ; MCell (ZLit 877800) 8 (ZLit 95006)
  ; MCell (ZLit 877816) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))
  ; MCell (ZLit 877824) 4 (ZLit 18446744073709551615)
  ; MCell (ZLit 877832) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))
  ; MCell (ZLit 877840) 1 (ZLit 0)
  ; MCell (ZLit 877848) 8 (ZLit 4096)
  ; MCell (ZLit 877856) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 877864) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 877872) 8 (ZLit 8388608)
  ; MCell (ZLit 877880) 8 (ZLit 106643)
  ; MCell (ZLit 878464) 1 (ZLit 0)
  ; MZeroC (ZLit 878465) 3
  ; MCell (ZLit 878576) 8 (ZLit 268435456)
  ; MCell (ZLit 878584) 8 (ZLit 241591905)
  ; MCell (ZLit 878592) 8 (ZLit 1048576)
  ; MCell (ZLit 878664) 1 (ZLit 0)
  ; MCell (ZLit 878665) 1 (ZLit 0)
  ; MCell (ZLit 881400) 8 (ZLit 1099511627776)
  ; MCell (ZLit 881408) 2 (ZLit 16)
  ; MCell (ZLit 881410) 2 (ZLit 2048)
  ; MCell (ZLit 881412) 1 (ZLit 1)
  ; MCell (ZLit 881464) 4 (ZLit 4294967295)
  ; MCell (ZLit 881468) 4 (ZLit 256)
  ; MCell (ZLit 881472) 4 (ZLit 1024)
  ; MCell (ZLit 881476) 4 (ZLit 16)
  ; MCell (ZLit 881480) 4 (ZLit 2048)
  ; MCell (ZLit 881484) 1 (ZLit 0)
  ; MCell (ZLit 881488) 8 (ZLit 72340168526266369)
  ; MCell (ZLit 881496) 8 (ZLit 85899345936)
  ; MCell (ZLit 881504) 1 (ZLit 0)
  ; MCell (ZLit 881508) 4 (ZLit 4096)
  ; MCell (ZLit 881512) 8 (ZLit 816043786240)
  ; MCell (ZLit 881520) 4 (ZLit 85)
  ; MCell (ZLit 881524) 1 (ZLit 1)
  ; MCell (ZLit 881528) 8 (ZLit 0)
  ; MRo (ZLit 881536) 6 (ZLit 4294967296)
  ; MCell (ZLit 881542) 1 (ZLit 1)
  ; MCell (ZLit 881543) 1 (ZLit 0)
  ; MCell (ZLit 881544) 8 (ZLit 72340172838010881)
  ; MCell (ZLit 881552) 2 (ZLit 1)
  ; MCell (ZLit 881554) 1 (ZLit 0)
  ; MCell (ZLit 881556) 4 (ZLit 0)
  ; MCell (ZLit 881560) 1 (ZLit 1)
  ; MCell (ZLit 881564) 4 (ZLit 2)
  ; MCell (ZLit 881568) 8 (ZLit 82674)
  ; MCell (ZLit 881576) 4 (ZLit 65793)
  ; MCell (ZLit 881584) 1 (ZLit 1)
  ; MCell (ZLit 881592) 8 (ZLit 32)
  ; MCell (ZLit 881600) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20400))
  ; MCell (ZLit 881608) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZLit 881616) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19880))
  ; MCell (ZLit 881648) 8 (ZLit 0)
  ; MCell (ZLit 889720) 1 (ZLit 1)
  ; MCell (ZLit 889721) 1 (ZLit 1)
  ; MCell (ZLit 889722) 1 (ZLit 1)
  ; MCell (ZLit 889724) 4 (ZLit 299)
  ; MCell (ZLit 889728) 8 (ZLit 889736)
  ; MCell (ZLit 889736) 8 (ZMul (ZLit 4096) (ZV 207))
  ; MCell (ZLit 889752) 4 (ZLit 2)
  ; MCell (ZLit 889756) 1 (ZLit 1)
  ; MCell (ZLit 889760) 1 (ZLit 1)
  ; MCell (ZLit 889764) 4 (ZLit 0)
  ; MCell (ZLit 891704) 8 (ZLit 2147450880)
  ; MCell (ZLit 891712) 4 (ZLit 1)
  ; MCell (ZLit 895000) 1 (ZLit 1)
  ; MCell (ZLit 895001) 1 (ZLit 1)
  ; MCell (ZLit 895002) 1 (ZLit 0)
  ; MCell (ZLit 895003) 1 (ZLit 0)
  ; MCell (ZLit 895008) 8 (ZLit 140737488355327)
  ; MCell (ZLit 895032) 1 (ZLit 1)
  ; MCell (ZLit 895036) 4 (ZLit 30)
  ; MCell (ZLit 895152) 8 (ZLit 1)
  ; MCell (ZLit 895160) 8 (ZLit 4096)
  ; MCell (ZLit 895872) 8 (ZLit 895936)
  ; MCell (ZLit 895936) 8 (ZLit 864752)
  ; MCell (ZLit 895944) 4 (ZLit 5)
  ; MCell (ZLit 895952) 8 (ZLit 0)
  ; MCell (ZLit 895960) 8 (ZLit 0)
  ; MCell (ZLit 895968) 8 (ZLit 0)
  ; MZeroC (ZLit 895976) 5
  ; MCell (ZLit 896040) 1 (ZLit 1)
  ; MCell (ZLit 896048) 1 (ZLit 1)
  ; MCell (ZLit 896056) 8 (ZLit 896152)
  ; MCell (ZLit 896064) 8 (ZLit 896104)
  ; MCell (ZLit 896072) 8 (ZLit 0)
  ; MCell (ZLit 896088) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 65536))
  ; MCell (ZLit 896096) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 160))
  ; MCell (ZLit 896104) 8 (ZLit 0)
  ; MCell (ZLit 896112) 4 (ZLit 0)
  ; MCell (ZLit 896116) 4 (ZLit 0)
  ; MCell (ZLit 896120) 8 (ZLit 0)
  ; MCell (ZLit 896128) 8 (ZLit 0)
  ; MCell (ZLit 896136) 4 (ZLit 0)
  ; MCell (ZLit 896140) 4 (ZLit 0)
  ; MCell (ZLit 896144) 4 (ZLit 0)
  ; MCell (ZLit 896148) 4 (ZLit 0)
  ; MCell (ZLit 896152) 8 (ZLit 433804)
  ; MCell (ZLit 896160) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 896168) 4 (ZLit 0)
  ; MCell (ZLit 896176) 8 (ZLit 0)
  ; MCell (ZLit 896184) 4 (ZLit 0)
  ; MCell (ZLit 896188) 4 (ZLit 0)
  ; MCell (ZLit 896192) 8 (ZLit 1)
  ; MCell (ZLit 896200) 8 (ZLit 1)
  ; MCell (ZLit 896208) 8 (ZLit 1)
  ; MCell (ZLit 896216) 8 (ZLit 1)
  ; MCell (ZLit 896224) 8 (ZMul (ZLit 4096) (ZV 245))
  ; MCell (ZLit 896232) 8 (ZLit 4096)
  ; MCell (ZLit 896240) 8 (ZLit 1)
  ; MCell (ZLit 896248) 8 (ZLit 0)
  ; MCell (ZLit 896256) 8 (ZLit 0)
  ; MCell (ZLit 896264) 8 (ZLit 0)
  ; MCell (ZLit 896272) 8 (ZLit 0)
  ; MCell (ZLit 896280) 8 (ZLit 0)
  ; MCell (ZLit 896288) 8 (ZLit 0)
  ; MCell (ZLit 896296) 8 (ZLit 0)
  ; MCell (ZLit 896304) 8 (ZLit 0)
  ; MCell (ZLit 896312) 4 (ZLit 0)
  ; MCell (ZLit 1424776) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 65536))
  ; MCell (ZLit 1424784) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20416))
  ; MCell (ZLit 1424792) 8 (ZLit 417664)
  ; MCell (ZLit 1424801) 1 (ZLit 1)
  ; MCell (ZLit 1480144) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-160)))
  ; MCell (ZLit 1480152) 4 (ZLit 0)
  ; MCell (ZLit 1480160) 8 (ZLit 4096)
  ; MCell (ZLit 1488480) 1 (ZLit 0)
  ; MZeroC (ZLit 1488481) 3
  ; MCell (ZLit 1488488) 8 (ZLit 1)
  ; MCell (ZLit 1488496) 8 (ZLit 0)
  ; MCell (ZLit 1488504) 8 (ZLit 0)
  ; MCell (ZLit 1488512) 8 (ZLit 82674)
  ; MCell (ZLit 1488520) 8 (ZLit 128849084416)
  ; MCell (ZLit 1488528) 8 (ZLit 0)
  ; MCell (ZLit 1488536) 8 (ZLit 0)
  ; MCell (ZLit 1488544) 8 (ZLit 0)
  ; MCell (ZLit 1488552) 8 (ZLit 0)
  ; MCell (ZLit 1488560) 8 (ZLit 1103823372545)
  ; MCell (ZLit 1488568) 8 (ZLit 4294967296)
  ; MCell (ZLit 1488576) 8 (ZLit 0)
  ; MCell (ZLit 1488584) 8 (ZLit 0)
  ; MCell (ZLit 1488592) 8 (ZLit 0)
  ; MCell (ZLit 1488600) 8 (ZLit 65537)
  ; MCell (ZLit 1488608) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 1488616) 8 (ZLit 72176)
  ; MCell (ZLit 1488624) 8 (ZLit 256)
  ; MCell (ZLit 1488632) 8 (ZLit 0)
  ; MCell (ZLit 1488640) 8 (ZLit 0)
  ; MCell (ZLit 1488648) 8 (ZLit 0)
  ; MCell (ZLit 1488656) 8 (ZLit 0)
  ; MCell (ZLit 1488664) 8 (ZLit 18446744069414584320)
  ; MCell (ZLit 1488672) 8 (ZLit 1)
  ; MCell (ZLit 1488680) 8 (ZLit 83534)
  ; MCell (ZLit 1488688) 8 (ZLit 82674)
  ; MCell (ZLit 1488696) 8 (ZLit 82674)
  ; MCell (ZLit 1488704) 8 (ZLit 1103823372544)
  ; MCell (ZLit 1488712) 8 (ZLit 0)
  ; MCell (ZLit 1488720) 8 (ZLit 126686)
  ; MCell (ZLit 1488728) 8 (ZLit 72339073309605888)
  ; MCell (ZLit 1488736) 8 (ZLit 72340172838076673)
  ; MCell (ZLit 1488744) 8 (ZLit 16843009)
  ; MCell (ZLit 1488752) 8 (ZLit 1103806595073)
  ; MCell (ZLit 1488760) 8 (ZLit 104707)
  ; MCell (ZLit 1488768) 8 (ZLit 281474976710912)
  ; MCell (ZLit 1488976) 8 (ZLit 396836)
  ; MCell (ZLit 1489016) 8 (ZLit 1)
  ; MCell (ZLit 1489040) 8 (ZLit 417524)
  ; MCell (ZLit 1489048) 8 (ZLit 417292)
  ; MCell (ZLit 1489056) 8 (ZLit 507656)
  ; MCell (ZLit 1489096) 1 (ZLit 1)
  ; MCell (ZLit 1489368) 1 (ZLit 0)
  ; MCell (ZLit 1751568) 8 (ZLit 8388608)
  ; MCell (ZLit 1751576) 8 (ZMul (ZLit 4096) (ZV 454))
  ; MCell (ZLit 1751588) 1 (ZLit 0)
  ; MZeroC (ZLit 1751589) 3
  ; MCell (ZLit 6011416) 4 (ZLit 1)
  ; MCell (ZLit 6011424) 1 (ZLit 0)
  ; MZeroC (ZLit 6011425) 3
  ; MCell (ZLit 6011432) 8 (ZMul (ZLit 4096) (ZV 453))
  ; MCell (ZLit 6274816) 1 (ZLit 0)
  ; MCell (ZLit 6274820) 4 (ZLit 0)
  ; MCell (ZLit 6274824) 8 (ZLit 72340172821233664)
  ; MCell (ZLit 6274832) 4 (ZLit 257)
  ; MCell (ZLit 6274836) 2 (ZLit 0)
  ; MCell (ZLit 6274838) 1 (ZLit 0)
  ; MCell (ZLit 6274840) 4 (ZLit 1)
  ; MCell (ZLit 6274848) 8 (ZLit 82674)
  ; MCell (ZLit 6274856) 4 (ZLit 1)
  ; MCell (ZLit 6275264) 8 (ZLit 6275328)
  ; MCell (ZLit 6275328) 8 (ZLit 874432)
  ; MCell (ZLit 6275336) 4 (ZLit 38)
  ; MCell (ZLit 6275344) 8 (ZLit 0)
  ; MCell (ZLit 6275352) 8 (ZLit 0)
  ; MCell (ZLit 6275360) 8 (ZLit 0)
  ; MZeroC (ZLit 6275368) 38
  ; MCell (ZLit 6275432) 1 (ZLit 1)
  ; MCell (ZLit 6275440) 1 (ZLit 0)
  ; MCell (ZLit 6275441) 1 (ZLit 1)
  ; MCell (ZLit 6275442) 2 (ZLit 0)
  ; MCell (ZLit 6275448) 2 (ZLit 0)
  ; MCell (ZLit 6275456) 8 (ZLit 82674)
  ; MCell (ZLit 6275464) 2 (ZLit 0)
  ; MCell (ZLit 6671400) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))) (ZLit 16))
  ; MCell (ZLit 6802704) 8 (ZLit 839376)
  ; MCell (ZLit 6671432) 8 (ZLit 0)
  ; MCell (ZLit 6802720) 8 (ZLit 24)
  ; MCell (ZLit 6802728) 8 (ZLit 8)
  ; MCell (ZLit 6802736) 8 (ZLit 0)
  ; MCell (ZLit 6671408) 8 (ZLit 6671408)
  ; MCell (ZLit 6671416) 8 (ZLit 6671408)
  ; MCell (ZLit 6671424) 8 (ZLit 6671408)
  ; MCell (ZLit 6671432) 8 (ZLit 0)
  ; MCell (ZLit 6671440) 4 (ZV 44)
  ; MCell (ZLit 6671448) 4 (ZLit 2)
  ; MCell (ZLit 6671458) 1 (ZLit 1)
  ; MCell (ZLit 6671520) 8 (ZLit 6807712)
  ; MCell (ZLit 6671528) 8 (ZLit 6671528)
  ; MCell (ZLit 6671560) 8 (ZLit 6803392)
  ; MCell (ZLit 6671592) 8 (ZV 45)
  ; MCell (ZLit 6671600) 8 (ZLit 6671640)
  ; MCell (ZLit 6671608) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MCell (ZLit 6671616) 8 (ZMul (ZLit 4096) (ZV 310))
  ; MCell (ZLit 6671640) 8 (ZLit 1)
  ; MCell (ZLit 6671648) 8 (ZLit 6673656)
  ; MRo (ZLit 6802744) 8 (ZV 45)
  ; MWr (ZLit 6802752) 8896
  ; MCell (ZLit 6802768) 4 (ZLit 1)
  ; MCell (ZLit 6802776) 8 (ZLit 6802784)
  ; MCell (ZLit 6802792) 8 (ZLit 777180)
  ; MCell (ZLit 6803048) 8 (ZLit 507656)
  ; MCell (ZLit 6672384) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))
  ; MCell (ZLit 6803336) 1 (ZLit 1)
  ; MCell (ZLit 6803344) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24))
  ; MCell (ZLit 6803352) 8 (ZLit 6802696)
  ; MCell (ZLit 6803360) 8 (ZLit 248)
  ; MCell (ZLit 6803368) 8 (ZLit 8)
  ; MCell (ZLit 6803376) 8 (ZLit 1)
  ; MCell (ZLit 6803384) 8 (ZLit 4096)
  ; MCell (ZLit 6803440) 8 (ZV 9)
  ; MCell (ZLit 6803472) 4 (ZLit 1)
  ; MCell (ZLit 6803476) 4 (ZLit 1)
  ; MCell (ZLit 6803496) 8 (ZLit 97)
  ; MCell (ZLit 6803504) 8 (ZLit 0)
  ; MCell (ZLit 6803944) 8 (ZLit 10)
  ; MCell (ZLit 6804048) 8 (ZLit 2)
  ; MCell (ZLit 6804080) 8 (ZLit 2)
  ; MCell (ZLit 6804112) 8 (ZLit 2)
  ; MCell (ZLit 6804376) 1 (ZLit 1)
  ; MCell (ZLit 6806624) 8 (ZLit 396320)
  ; MCell (ZLit 6807648) 4 (ZLit 0)
  ; MCell (ZLit 6807656) 4 (ZLit 0)
  ; MCell (ZLit 6807712) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MCell (ZLit 864808) 8 (ZLit 8)
  ; MCell (ZLit 864816) 8 (ZLit 138074)
  ; MCell (ZLit 864832) 4 (ZLit 2)
  ; MWr (ZLit 839680) 5963064
  ; MImg 877705 877784
  ; MImg 877808 877816
  ; MImg 877828 877832
  ; MImg 877841 877848
  ; MImg 877888 878464
  ; MImg 878468 878576
  ; MImg 878600 878664
  ; MImg 878666 881400
  ; MImg 881413 881464
  ; MImg 881485 881488
  ; MImg 881505 881508
  ; MImg 881525 881528
  ; MImg 881555 881556
  ; MImg 881561 881564
  ; MImg 881580 881584
  ; MImg 881585 881592
  ; MImg 881624 881648
  ; MImg 881656 881720
  ; MImg 886504 889720
  ; MImg 889723 889724
  ; MImg 889744 889752
  ; MImg 889757 889760
  ; MImg 889761 889764
  ; MImg 889768 891704
  ; MImg 891716 895000
  ; MImg 895004 895008
  ; MImg 895016 895032
  ; MImg 895033 895036
  ; MImg 895040 895152
  ; MImg 895168 895872
  ; MImg 895880 895936
  ; MImg 895948 895952
  ; MImg 895981 896040
  ; MImg 896041 896048
  ; MImg 896049 896056
  ; MImg 896080 896088
  ; MImg 896172 896176
  ; MImg 896316 1424776
  ; MImg 1424800 1424801
  ; MImg 1424802 1480144
  ; MImg 1480156 1480160
  ; MImg 1480168 1480192
  ; MImg 1484287 1484288
  ; MImg 1488383 1488480
  ; MImg 1488484 1488488
  ; MImg 1488776 1488976
  ; MImg 1488984 1489016
  ; MImg 1489024 1489040
  ; MImg 1489064 1489096
  ; MImg 1489097 1489368
  ; MImg 1489369 1751560
  ; MImg 6011420 6011424
  ; MImg 6011428 6011432
  ; MImg 6011440 6274816
  ; MImg 6274817 6274820
  ; MImg 6274839 6274840
  ; MImg 6274844 6274848
  ; MImg 6274860 6275264
  ; MImg 6275272 6275328
  ; MImg 6275340 6275344
  ; MImg 6275406 6275432
  ; MImg 6275433 6275440
  ; MImg 6275444 6275448
  ; MImg 6275450 6275456
  ; MImg 6275466 6671400
  ; MImg 6671408 6671424
  ; MImg 6671444 6671448
  ; MImg 6671452 6671458
  ; MImg 6671459 6671520
  ; MImg 6671536 6671560
  ; MImg 6671568 6671592
  ; MImg 6671624 6671640
  ; MImg 6671656 6802704
  ; MImg 6802752 6802768
  ; MImg 6802772 6802776
  ; MImg 6802784 6802792
  ; MImg 6802800 6803048
  ; MImg 6803056 6803320
  ; MImg 6803337 6803344
  ; MImg 6803392 6803440
  ; MImg 6803448 6803464
  ; MImg 6803480 6803488
  ; MImg 6803544 6803560
  ; MImg 6803568 6803664
  ; MImg 6803672 6803696
  ; MImg 6803704 6803728
  ; MImg 6803736 6803944
  ; MImg 6803952 6804048
  ; MImg 6804056 6804080
  ; MImg 6804088 6804112
  ; MImg 6804120 6804376
  ; MImg 6804377 6804384
  ; MImg 6804392 6806608
  ; MImg 6806616 6806624
  ; MImg 6806632 6807648
  ; MImg 6807652 6807656
  ; MImg 6807660 6807712
  ; MImg 6807720 6811648
  ; MImg 864824 864832
  ; MImg 864836 877696
  ; MImg 65536 864808
  ; MWr (ZLit 2147459072) 843264
  ; MZero (ZLit 2147459072) 9452
  ; MCell (ZLit 2147468524) 1 (ZLit 4)
  ; MFill (ZLit 2147468525) 3 249
  ; MZeroC (ZLit 2147468528) 28
  ; MCell (ZLit 2147468556) 1 (ZLit 6)
  ; MFill (ZLit 2147468557) 7 249
  ; MZeroC (ZLit 2147468564) 2
  ; MCell (ZLit 2147468566) 1 (ZLit 7)
  ; MFill (ZLit 2147468567) 5 249
  ; MZeroC (ZLit 2147468572) 3
  ; MCell (ZLit 2147468575) 1 (ZLit 3)
  ; MFill (ZLit 2147468576) 4 249
  ; MZeroC (ZLit 2147468580) 2
  ; MCell (ZLit 2147468582) 1 (ZLit 4)
  ; MFill (ZLit 2147468583) 5 249
  ; MZeroC (ZLit 2147468588) 3
  ; MCell (ZLit 2147468591) 1 (ZLit 1)
  ; MFill (ZLit 2147468592) 4 249
  ; MZeroC (ZLit 2147468596) 2
  ; MCell (ZLit 2147468598) 1 (ZLit 4)
  ; MFill (ZLit 2147468599) 5 249
  ; MZeroC (ZLit 2147468604) 2
  ; MCell (ZLit 2147468606) 1 (ZLit 3)
  ; MFill (ZLit 2147468607) 5 249
  ; MZeroC (ZLit 2147468612) 3
  ; MCell (ZLit 2147468615) 1 (ZLit 5)
  ; MFill (ZLit 2147468616) 4 249
  ; MZeroC (ZLit 2147468620) 4
  ; MCell (ZLit 2147468624) 1 (ZLit 4)
  ; MFill (ZLit 2147468625) 7 249
  ; MZeroC (ZLit 2147468632) 3
  ; MCell (ZLit 2147468635) 1 (ZLit 1)
  ; MFill (ZLit 2147468636) 4 249
  ; MZeroC (ZLit 2147468640) 3
  ; MCell (ZLit 2147468643) 1 (ZLit 2)
  ; MFill (ZLit 2147468644) 4 249
  ; MZeroC (ZLit 2147468648) 4
  ; MCell (ZLit 2147468652) 1 (ZLit 5)
  ; MFill (ZLit 2147468653) 7 249
  ; MZeroC (ZLit 2147468660) 3
  ; MCell (ZLit 2147468663) 1 (ZLit 4)
  ; MFill (ZLit 2147468664) 4 249
  ; MZeroC (ZLit 2147468668) 2
  ; MCell (ZLit 2147468670) 1 (ZLit 6)
  ; MFill (ZLit 2147468671) 5 249
  ; MZeroC (ZLit 2147468676) 3
  ; MCell (ZLit 2147468679) 1 (ZLit 4)
  ; MFill (ZLit 2147468680) 4 249
  ; MZeroC (ZLit 2147468684) 2
  ; MCell (ZLit 2147468686) 1 (ZLit 6)
  ; MFill (ZLit 2147468687) 5 249
  ; MZeroC (ZLit 2147468692) 3
  ; MCell (ZLit 2147468695) 1 (ZLit 6)
  ; MFill (ZLit 2147468696) 4 249
  ; MZeroC (ZLit 2147468700) 2
  ; MCell (ZLit 2147468702) 1 (ZLit 5)
  ; MFill (ZLit 2147468703) 5 249
  ; MZeroC (ZLit 2147468708) 2
  ; MCell (ZLit 2147468710) 1 (ZLit 7)
  ; MFill (ZLit 2147468711) 5 249
  ; MZeroC (ZLit 2147469580) 256
  ; MFill (ZLit 2147469836) 64 249
  ; MZeroC (ZLit 2147469900) 16
  ; MFill (ZLit 2147469916) 4 249
  ; MZeroC (ZLit 2147468716) 136
  ; MFill (ZLit 2147468852) 32 249
  ; MZero (ZLit 2147468884) 512
  ; MFill (ZLit 2147469396) 128 249
  ; MZeroC (ZLit 2147469524) 15
  ; MCell (ZLit 2147469539) 1 (ZLit 6)
  ; MFill (ZLit 2147469540) 4 249
  ; MZeroC (ZLit 2147469544) 7
  ; MCell (ZLit 2147469551) 1 (ZLit 6)
  ; MFill (ZLit 2147469552) 4 249
  ; MZeroC (ZLit 2147469556) 8
  ; MFill (ZLit 2147469564) 4 249
  ; MZeroC (ZLit 2147469568) 8
  ; MFill (ZLit 2147469576) 4 249
  ; MZeroC (ZLit 2147469920) 11
  ; MCell (ZLit 2147469931) 1 (ZLit 6)
  ; MFill (ZLit 2147469932) 4 249
  ; MZeroC (ZLit 2147469936) 2
  ; MCell (ZLit 2147469938) 1 (ZLit 6)
  ; MFill (ZLit 2147469939) 5 249
  ; MZeroC (ZLit 2147469944) 3
  ; MCell (ZLit 2147469947) 1 (ZLit 4)
  ; MFill (ZLit 2147469948) 4 249
  ; MZero (ZLit 2147469952) 90378
  ; MFill (ZLit 2147560330) 256 249
  ; MZero (ZLit 2147560586) 715694
  ; MFill (ZLit 2148276280) 8192 249
  ; MZero (ZLit 2148284472) 17864
  ; MWr (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 8388608
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-48))) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 8))
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-40))) 8 (ZLit 0)
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-32))) 8 (ZLit 0)
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-24))) 8 (ZLit 0)
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-16))) 8 (ZLit 0)
  ; MCell (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8))) 8 (ZLit 0)
  ; MRo (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) 8 (ZV 1)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 8)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit 16)) 8 (ZMul (ZLtu (ZLit 1) (ZV 1)) (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 3) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 185)))
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24)) 8 (ZLit 3)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 32)) 8 (ZLit 65600)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 40)) 8 (ZLit 4)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 48)) 8 (ZLit 56)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 56)) 8 (ZLit 5)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 64)) 8 (ZLit 11)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 72)) 8 (ZLit 16)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 80)) 8 (ZV 9)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 88)) 8 (ZLit 6)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 96)) 8 (ZLit 4096)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 104)) 8 (ZLit 11)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 112)) 8 (ZV 8)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 120)) 8 (ZLit 12)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 128)) 8 (ZV 8)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 136)) 8 (ZLit 23)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 144)) 8 (ZLit 0)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 152)) 8 (ZLit 25)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 160)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 8) (ZV 4)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 184))
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 168)) 8 (ZLit 0)
  ; MRo (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 176)) 8 (ZLit 0)
  ; MWrS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; MZeroS (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; MWr (ZMul (ZLit 4096) (ZV 78)) 65536
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19880)) 8 (ZMul (ZLit 4096) (ZV 471))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19888)) 8 (ZLit 4096)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19896)) 8 (ZLit 1)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904)) 8 (ZLit 875600)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19912)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920)) 8 (ZLit 875664)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19928)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936)) 8 (ZLit 875728)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19944)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952)) 8 (ZLit 875792)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19960)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968)) 8 (ZLit 875856)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19976)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984)) 8 (ZLit 875920)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19992)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000)) 8 (ZLit 875984)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20008)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016)) 8 (ZLit 876048)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20024)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032)) 8 (ZLit 876112)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20040)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048)) 8 (ZLit 876176)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20056)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064)) 8 (ZLit 876240)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20072)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080)) 8 (ZLit 876304)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20088)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096)) 8 (ZLit 876368)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20104)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20112)) 8 (ZLit 876432)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20120)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20128)) 8 (ZLit 876496)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20136)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20112))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20144)) 8 (ZLit 876560)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20152)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20128))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20160)) 8 (ZLit 876624)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20168)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20144))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20176)) 8 (ZLit 876688)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20184)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20160))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20192)) 8 (ZLit 876752)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20200)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20176))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20208)) 8 (ZLit 876816)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20216)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20192))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20224)) 8 (ZLit 876880)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20232)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20208))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20240)) 8 (ZLit 876944)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20248)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20224))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20256)) 8 (ZLit 877008)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20264)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20240))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20272)) 8 (ZLit 877072)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20280)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20256))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20288)) 8 (ZLit 877136)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20296)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20272))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20304)) 8 (ZLit 877200)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20312)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20288))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20320)) 8 (ZLit 877264)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20328)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20304))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20336)) 8 (ZLit 877328)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20344)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20320))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20352)) 8 (ZLit 877392)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20360)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20336))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20368)) 8 (ZLit 877456)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20376)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20352))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20384)) 8 (ZLit 877520)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20392)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20368))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20400)) 8 (ZLit 877584)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20408)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20384))
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192
  ; MWr (ZMul (ZLit 4096) (ZV 207)) 3727360
  ; MZero (ZMul (ZLit 4096) (ZV 207)) 3727360
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) 465920
  ; MWr (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096
  ; MZero (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008)) 4096
  ; MWr (ZAdd (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZMul (ZLit (-512)) (ZV 209))) (ZLit 19327328256)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 227)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 227)) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 8)) 8 (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344))))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 16)) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 4096) (ZV 344)))) (ZLit (-8388608)))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 24)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 32)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 40)) 1 (ZLit 0)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 41)) 7
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6673456)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6673676)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 64)) 8 (ZLit 6671616)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 72)) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3169)) 927
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 228)) 65536
  ; MCell (ZMul (ZLit 4096) (ZV 228)) 8 (ZLit 843664)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 8)) 4 (ZLit 0)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 12)) 4
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 16)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 24)) 4 (ZLit 0)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 28)) 4
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 32)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 40)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 48)) 1 (ZLit 0)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 49)) 63
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 112)) 4 (ZLit 2)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 116)) 1 (ZLit 1)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 117)) 3
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 120)) 4 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 124)) 4 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 128)) 4 (ZLit 0)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 132)) 4
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 136)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 144)) 4 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 148)) 2 (ZLit 1024)
  ; MZeroC (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 150)) 2
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 152)) 8 (ZMul (ZLit 4096) (ZV 227))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 160)) 65376
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192
  ; MFill (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 254
  ; MZeroC (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147459072)) 0
  ; MWr (ZMul (ZLit 4096) (ZV 245)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 245)) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 245)) (ZLit 8)) 4088
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 310)) 4096
  ; MZeroC (ZMul (ZLit 4096) (ZV 310)) 24
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6671608)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 32)) 8 (ZLit 0)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 40)) 4056
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; MZeroC (ZMul (ZLit 4096) (ZV 377)) 88
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 377)) (ZLit 88)) 8 (ZLit 20)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 377)) (ZLit 96)) 11571104
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400
  ; MWr (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; MZeroC (ZMul (ZLit 4096) (ZV 453)) 16
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 24)) 4 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 28)) 4 (ZLit 1)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 32)) 1048544
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 453)) (ZLit 2147450880)) 131072
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 453)) (ZLit 2147450880)) 131072
  ; MWr (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 8)) 8 (ZLit 304116)
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MWr (ZMul (ZLit 4096) (ZV 471)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 471)) 8 (ZLit 12297829379609722881)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 8)) 8 (ZLit 875600)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 16)) 8 (ZLit 877584)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 24)) 4072
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 471)) (ZLit 2147450880)) 512
].

Definition both_pure_facts_r30 : list pfact := [
  PVar 0 4294901760 4294967295
  ; PVar 1 1 1024
  ; PVar 2 0 256
  ; PVar 3 0 131071
  ; PVar 4 0 280000
  ; PVar 5 1631 525919
  ; PVar 6 0 255
  ; PVar 7 0 131071
  ; PVar 8 0 4294967294
  ; PVar 9 0 4194303
  ; PVar 10 0 7
  ; PVar 44 1 4194303
  ; PVar 78 1631 34359736304
  ; PVar 207 1631 34359735410
  ; PVar 208 4295491576 34326181871
  ; PVar 209 0 15
  ; PVar 226 1631 34359734272
  ; PVar 227 1 34359736319
  ; PVar 228 1631 34359736304
  ; PVar 245 1 34359736319
  ; PVar 310 1 34359736319
  ; PVar 311 1 34359736319
  ; PVar 344 0 1
  ; PVar 344 0 1
  ; PVar 377 1631 34359733495
  ; PVar 394 1631 524277
  ; PVar 394 1631 524277
  ; PVar 395 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 397 1 34359736319
  ; PVar 452 6680576 2154172416
  ; PVar 453 1631 34359736064
  ; PVar 454 1631 34359734272
  ; PVar 471 1 34359736319
  ; PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095
  ; PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095
  ; PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0
  ; PRange (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 8) (ZV 4)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 200)) 140735340871872 140737488355328
  ; PRange (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZAdd (ZV 1) (ZAdd (ZV 2) (ZAdd (ZV 4) (ZAdd (ZMul (ZLit 2) (ZV 6)) (ZMul (ZLit 512) (ZV 10))))))) 17591917608961 17592186044391
  ; PRange (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) 140735340871680 140737488355136
  ; PRange (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) 140735340871680 140737488351232
  ; PRange (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZAdd (ZMul (ZLit 2) (ZV 6)) (ZMul (ZLit 512) (ZV 10)))) 17591917608960 17592186044392
  ; PDisj (ZAdd (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZMul (ZLit (-512)) (ZV 209))) (ZLit 19327328256)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) 465920 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) 465920 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZLit 2147450880)) 17179877888 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 226)) (ZLit 2147450880)) 1048576 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 394)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 395)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 396)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 397)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826880
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 826880
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 208)) 137439023104
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 226)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 227)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 228)) 65536
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 226)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 227)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 228)) 65536
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 227)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 228)) 65536
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6615040
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 228)) 65536
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 65536) 6615040
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6615040
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZLit 65536) 6615040
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 394)) 8192 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 395)) 8192 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 395)) 8192 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 396)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 396)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 397)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZLit 65536) 6615040
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 207)) 3727360
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 208)) 137439023104
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 226)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 227)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 228)) 65536
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) (ZLit 465920) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZLit 2147450880)) (ZLit 17179877888) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 226)) (ZLit 2147450880)) (ZLit 1048576) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) (ZLit 8192) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) (ZLit 1446400) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 394)) (ZLit 2147450880)) (ZLit 1024) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 395)) (ZLit 2147450880)) (ZLit 1024) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 396)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 397)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) (ZLit 8192) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
].

(* #1390: both_pure_facts_r30 with each item just727 refuses on the #1390 hand-off states moved to the value those states hold (pl3_mf_cure_1390_g1.py); the r30 lemmas keep both_pure_facts_r30 *)
Definition both_pure_facts_r30_1390 : list pfact := [
  PVar 0 4294901760 4294967295
  ; PVar 1 1 1024
  ; PVar 2 0 256
  ; PVar 3 0 131071
  ; PVar 4 0 280000
  ; PVar 5 1663 525951
  ; PVar 6 0 255
  ; PVar 7 0 131071
  ; PVar 8 0 4294967294
  ; PVar 9 0 4194303
  ; PVar 10 0 7
  ; PVar 44 1 4194303
  ; PVar 78 1663 34359736304
  ; PVar 207 1663 34359735410
  ; PVar 208 4295491576 34326181871
  ; PVar 209 0 15
  ; PVar 226 1663 34359734272
  ; PVar 227 1 34359736319
  ; PVar 228 1663 34359736304
  ; PVar 245 1 34359736319
  ; PVar 310 1 34359736319
  ; PVar 311 1 34359736319
  ; PVar 344 0 1
  ; PVar 344 0 1
  ; PVar 377 1663 34359733495
  ; PVar 394 1663 524277
  ; PVar 394 1663 524277
  ; PVar 395 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 397 1 34359736319
  ; PVar 452 6811648 2154303488
  ; PVar 453 1663 34359736064
  ; PVar 454 1663 34359734272
  ; PVar 471 1 34359736319
  ; PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095
  ; PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4095
  ; PRange (ZAdd (ZMul (ZLit (-4096)) (ZV 209)) (ZAnd (ZMul (ZLit 4096) (ZV 208)) (ZLit 65535))) 0 0
  ; PRange (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 8) (ZV 4)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))))) (ZLit 200)) 140735340871872 140737488355328
  ; PRange (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZAdd (ZV 1) (ZAdd (ZV 2) (ZAdd (ZV 4) (ZAdd (ZMul (ZLit 2) (ZV 6)) (ZMul (ZLit 512) (ZV 10))))))) 17591917608961 17592186044391
  ; PRange (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) 140735340871680 140737488355136
  ; PRange (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) 140735340871680 140737488351232
  ; PRange (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZAdd (ZMul (ZLit 2) (ZV 6)) (ZMul (ZLit 512) (ZV 10)))) 17591917608960 17592186044392
  ; PDisj (ZAdd (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZMul (ZLit (-512)) (ZV 209))) (ZLit 19327328256)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) 465920 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) 465920 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZLit 2147450880)) 17179877888 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 226)) (ZLit 2147450880)) 1048576 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 394)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 395)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 396)) (ZLit 2147450880)) 512 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 397)) (ZLit 2147450880)) 512 (ZLit 2147459072) 843264
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 843264
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 208)) 137439023104
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 226)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 227)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 228)) 65536
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 207)) 3727360 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 226)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 227)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 228)) 65536
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 208)) 137439023104 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 227)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 228)) 65536
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 226)) 8388608 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6746112
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 228)) 65536
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 228)) 65536 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 65536) 6746112
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6746112
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZLit 65536) 6746112
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 377)) 11571200 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 394)) 8192 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 395)) 8192 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 395)) 8192 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 396)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 396)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 397)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 453)) 1048576 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 454)) 8388608 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZLit 65536) 6746112
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 207)) 3727360
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 208)) 137439023104
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 226)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 227)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 228)) 65536
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 245)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 78)) 65536 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) (ZLit 465920) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZLit 2147450880)) (ZLit 17179877888) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 226)) (ZLit 2147450880)) (ZLit 1048576) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) (ZLit 8192) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) (ZLit 1446400) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 394)) (ZLit 2147450880)) (ZLit 1024) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 395)) (ZLit 2147450880)) (ZLit 1024) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 396)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 397)) (ZLit 2147450880)) (ZLit 512) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
  ; PDisjS (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) (ZLit 8192) (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 0)) (ZMul (ZLit 512) (ZV 10))) (ZLit 2146402304)) (ZAdd (ZAdd (ZMul (ZLit (-4096)) (ZV 0)) (ZMul (ZLit (-512)) (ZV 10))) (ZLit 17592187092992))
].

Definition both_mem_facts_w1 : list mfact := [
  MCell (ZLit 1751560) 8 (ZLit 3)
  ; MCell (ZLit 1751584) 4 (ZLit 3)
  ; MCell (ZLit 3268520) 4 (ZLit 1)
  ; MImg 1751592 3268520
  ; MImg 3268524 6011416
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 10611996035665725796)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 2)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8 (ZLit 309060)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 24)) 8388584
].

(* #1390: both_mem_facts_w1 as it stood before the #1390 move, for the r30 lemmas *)
Definition both_mem_facts_w1_r30 : list mfact := [
  MCell (ZLit 1751560) 8 (ZLit 3)
  ; MCell (ZLit 1751584) 4 (ZLit 3)
  ; MCell (ZLit 5660844) 4 (ZLit 1)
  ; MImg 1751592 5660844
  ; MImg 5660848 6011416
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 1645447623097624997)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 2)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8 (ZLit 309076)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 24)) 8388584
].

Definition both_mem_facts_w2 : list mfact := [
  MCell (ZLit 1751560) 8 (ZLit 2)
  ; MCell (ZLit 1751584) 4 (ZLit 2)
  ; MCell (ZLit 2588352) 4 (ZLit 1)
  ; MImg 1751592 2588352
  ; MImg 2588356 6011416
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 13647248195054661930)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 1)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8388592
].

(* #1390: both_mem_facts_w2 as it stood before the #1390 move, for the r30 lemmas *)
Definition both_mem_facts_w2_r30 : list mfact := [
  MCell (ZLit 1751560) 8 (ZLit 2)
  ; MCell (ZLit 1751584) 4 (ZLit 2)
  ; MCell (ZLit 2646820) 4 (ZLit 1)
  ; MImg 1751592 2646820
  ; MImg 2646824 6011416
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 13153605090725276227)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 1)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8388592
].

Definition both_pure_facts_w1 : list pfact := [
  PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4030
].

Definition both_pure_facts_w2 : list pfact := [
  PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 4031 4095
].

Definition both_vis_app : list (zexp * zexp) := [
  (ZMul (ZLit 4096) (ZV 471), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 454), ZLit 8388608)
  ; (ZMul (ZLit 4096) (ZV 453), ZLit 1048576)
  ; (ZMul (ZLit 4096) (ZV 377), ZLit 11571200)
  ; (ZMul (ZLit 4096) (ZV 310), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 245), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 228), ZLit 65536)
  ; (ZMul (ZLit 4096) (ZV 227), ZLit 4096)
  ; (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 207), ZLit 3727360)
  ; (ZMul (ZLit 4096) (ZV 78), ZLit 65536)
  ; (ZLit 65536, ZLit 6746112)
  ; (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)), ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
].

(* #1390: both_vis_app as it stood before the #1390 move, for the r30 lemmas *)
Definition both_vis_app_r30 : list (zexp * zexp) := [
  (ZMul (ZLit 4096) (ZV 471), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 454), ZLit 8388608)
  ; (ZMul (ZLit 4096) (ZV 453), ZLit 1048576)
  ; (ZMul (ZLit 4096) (ZV 377), ZLit 11571200)
  ; (ZMul (ZLit 4096) (ZV 310), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 245), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 228), ZLit 65536)
  ; (ZMul (ZLit 4096) (ZV 227), ZLit 4096)
  ; (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 207), ZLit 3727360)
  ; (ZMul (ZLit 4096) (ZV 78), ZLit 65536)
  ; (ZLit 65536, ZLit 6615040)
  ; (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)), ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
].
Definition both_ghost : list (zexp * zexp) := [
  (ZMul (ZLit 4096) (ZV 311), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 394), ZLit 8192)
  ; (ZAdd (ZMul (ZLit 4096) (ZV 395)) (ZLit 4096), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 396), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 397), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 394), ZLit 8192)
  ; (ZMul (ZLit 4096) (ZV 397), ZLit 4096)
  ; (ZAdd (ZMul (ZLit 4096) (ZV 395)) (ZLit 4096), ZLit 4096)
  ; (ZMul (ZLit 4096) (ZV 396), ZLit 4096)
].
Definition both_vis : list (zexp * zexp) := both_vis_app ++ both_ghost.

Definition both_ledger : list lentry := [
  LMap (ZMul (ZLit 4096) (ZV 471)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 454)) 8388608 KRWLAZY
  ; LMap (ZMul (ZLit 4096) (ZV 453)) 1048576 KRW
  ; LFog 8192
  ; LFog 8192
  ; LMap (ZMul (ZLit 4096) (ZV 377)) 11571200 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 310)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 245)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 228)) 65536 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 227)) 4096 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 226)) 8388608 KNONELAZY
  ; LMap (ZMul (ZLit 4096) (ZV 208)) 137439023104 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 207)) 3727360 KRW
  ; LMap (ZMul (ZLit 4096) (ZV 78)) 65536 KRW
  ; LMap (ZLit 2201439137792) 15392894357504 KRWLAZY
  ; LMap (ZLit 2415882240) 2199023255552 KNONELAZY
  ; LMap (ZLit 2147446784) 268435456 KRWLAZY
].

Definition both_totsz_r30 : Z := 17729664974848.
Definition both_ylo_r30 : Z := 23387528589312.
Definition both_eager : Z := 16515072.
Definition both_abytes_r30 : Z := 2461207552.   (* #1390: the r30 value, for the r30 lemmas *)
Definition both_abytes : Z := 2461355008.   (* #1390: the #1390 states' a_abytes (was 2461207552) *)

Definition both_mem_hints_w1 : list N := [3; 2; 499; 498; 497; 494; 487; 493; 508; 486; 473; 476; 475; 474; 323; 324; 472; 471; 470; 469; 468; 464; 466; 465; 467; 618; 584; 583; 617; 612; 599; 611; 610; 609; 608; 616; 615; 614; 613; 606; 546; 607; 605; 604; 598; 603; 602; 601; 600; 619; 1; 6; 5; 126; 155; 0; 518; 532; 517; 519; 521; 520; 545; 544; 515; 513; 516; 535; 462; 463; 230; 670; 542; 630; 543; 489; 488; 231; 238; 237; 236; 235; 233; 232; 234; 419; 425; 418; 380; 392; 390; 422; 421; 420; 417; 416; 415; 424; 414; 423; 439; 438; 437; 266; 436; 435; 354; 358; 357; 270; 362; 361; 360; 430; 429; 428; 427; 426; 434; 433; 432; 431; 620; 9; 533; 509; 668; 585; 629; 536; 538; 547; 548; 549; 550; 551; 552; 553; 554; 555; 556; 557; 558; 559; 560; 561; 562; 563; 564; 565; 566; 567; 568; 569; 570; 571; 572; 573; 574; 575; 576; 577; 578; 579; 580; 581; 582; 539; 325; 540; 541; 456; 320; 461; 183; 164; 163; 184; 208; 187; 207; 188; 593; 592; 591; 590; 597; 596; 595; 594; 589; 241; 248; 247; 246; 245; 243; 242; 244; 239; 240; 249; 588; 587; 586; 704; 699; 698; 694; 697; 693; 687; 680; 679; 678; 683; 685; 349; 514; 681; 682; 676; 688; 271; 326; 689; 690; 677; 851; 457; 460; 459; 458; 700; 686; 703; 696; 692; 691; 695; 701; 702; 261; 254; 258; 259; 250; 251; 252; 253; 257; 511; 512; 510; 350; 534; 669; 537; 850; 750; 751; 752; 753; 754; 755; 756; 757; 758; 759; 760; 761; 762; 763; 764; 765; 766; 767; 768; 769; 770; 771; 772; 773; 774; 775; 776; 777; 778; 779; 780; 781; 782; 783; 784; 785; 786; 787; 788; 789; 790; 791; 792; 793; 794; 795; 796; 797; 798; 799; 800; 803; 804; 805; 806; 807; 808; 809; 810; 811; 812; 813; 814; 815; 816; 817; 818; 819; 820; 821; 822; 823; 824; 825; 826; 827; 828; 829; 830; 831; 832; 833; 834; 835; 836; 837; 838; 839; 840; 841; 842; 843; 844; 845; 846; 847; 848; 849; 748; 749; 747; 633; 634; 128; 129; 635; 123; 124; 636; 119; 120; 637; 115; 116; 638; 111; 112; 639; 107; 108; 640; 103; 104; 641; 99; 100; 642; 95; 96; 643; 91; 92; 644; 87; 88; 645; 83; 84; 646; 79; 80; 647; 75; 76; 648; 71; 72; 649; 67; 68; 650; 63; 64; 651; 59; 60; 652; 55; 56; 653; 51; 52; 660; 28; 661; 25; 654; 48; 655; 45; 656; 41; 42; 657; 37; 38; 658; 34; 659; 31; 662; 21; 22; 663; 17; 18; 664; 13; 14; 665; 4; 666; 10; 667; 722; 705; 671; 672; 673; 674; 675; 723; 724; 725; 726; 727; 728; 729; 730; 731; 732; 733; 734; 735; 736; 737; 738; 739; 740; 741; 742; 743; 744; 745; 631; 632; 624; 135; 134; 133; 127; 125; 122; 121; 118; 117; 114; 113; 110; 109; 106; 105; 102; 101; 98; 97; 94; 93; 90; 89; 86; 85; 82; 81; 78; 77; 74; 73; 70; 69; 66; 65; 62; 61; 58; 57; 54; 53; 50; 49; 47; 46; 44; 43; 40; 39; 36; 35; 33; 32; 30; 29; 27; 26; 24; 23; 20; 19; 16; 15; 12; 11; 8; 7; 623; 525; 526; 524; 491; 492; 490; 443; 351; 295; 294; 348; 347; 346; 444; 297; 296; 293; 272; 445; 209; 446; 442; 397; 381; 385; 398; 356; 384; 399; 269; 355; 386; 400; 268; 353; 401; 267; 389; 388; 402; 387; 383; 382; 403; 352; 404; 395; 391; 396; 367; 359; 368; 365; 366; 331; 332; 322; 321; 333; 329; 330; 278; 279; 273; 280; 276; 277; 191; 192; 157; 158; 193; 189; 190; 167; 160; 165; 166; 137; 130; 131; 132; 138; 136; 185; 159; 156; 801; 802; 186; 162; 161; 168]%N.
Lemma both_mem_facts_justified_w1 :
  forallb (mjustify (s_know (a_ss HS_both2_1)) (var_ranges (s_know (a_ss HS_both2_1))) 65536 6680576) (both_mem_facts_r30 ++ both_mem_facts_w1_r30) = true.
Proof. apply (mjust_hints_sound _ _ _ _ _ both_mem_hints_w1). vm_cast_no_check (@eq_refl bool true). Qed.
Definition both_pure_hints_w1 : list N := [706; 714; 715; 716; 720; 721; 707; 717; 718; 719; 708; 684; 626; 528; 503; 495; 480; 448; 406; 370; 335; 308; 211; 211; 282; 217; 217; 216; 215; 215; 214; 213; 195; 170; 140; 212; 212; 496; 709; 710; 711; 712; 713; 300; 299; 523; 501; 478; 301; 441; 302; 394; 303; 364; 304; 328; 306; 275; 222; 226; 228; 224; 298; 622; 527; 529; 530; 506; 484; 454; 412; 378; 344; 318; 291; 205; 181; 153; 502; 504; 505; 483; 453; 411; 377; 343; 317; 290; 204; 180; 152; 479; 481; 482; 452; 410; 376; 342; 316; 289; 203; 179; 151; 447; 449; 450; 451; 409; 375; 341; 315; 288; 202; 178; 150; 405; 407; 408; 374; 340; 314; 287; 201; 177; 149; 369; 371; 372; 373; 339; 313; 286; 200; 176; 148; 334; 336; 337; 338; 312; 285; 199; 175; 147; 307; 309; 310; 311; 281; 283; 284; 198; 174; 146; 221; 220; 220; 219; 219; 218; 194; 196; 197; 173; 145; 169; 171; 172; 144; 139; 141; 142; 143; 625; 627; 628; 531; 507; 485; 455; 413; 379; 345; 319; 292; 206; 182; 154; 522; 500; 477; 440; 393; 363; 327; 305; 274; 223; 227; 229; 225; 621; 210]%N.
Lemma both_pure_facts_justified_w1 :
  forallb (pjustify (s_know (a_ss HS_both2_1)) (var_ranges (s_know (a_ss HS_both2_1)))) (both_pure_facts_r30 ++ both_pure_facts_w1) = true.
Proof. apply (pjust_hints_sound _ _ _ both_pure_hints_w1). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_vis_justified_w1 :
  vis_match (var_ranges (s_know (a_ss HS_both2_1))) (a_vis HS_both2_1) both_vis_app_r30 = true /\ vis_match (var_ranges (s_know (a_ss HS_both2_1))) (a_ghost HS_both2_1) both_ghost = true.
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_ledger_justified_w1 :
  ledger_xmatch (var_ranges (s_know (a_ss HS_both2_1))) (a_maps HS_both2_1) both_ledger = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_consts_w1 : a_totsz HS_both2_1 = both_totsz_r30 /\ a_ylo HS_both2_1 = both_ylo_r30 /\ a_eager HS_both2_1 = both_eager /\ a_abytes HS_both2_1 = both_abytes_r30.
Proof. repeat split; reflexivity. Qed.
Definition both_mem_hints_w2 : list N := [3; 2; 498; 497; 496; 493; 486; 492; 507; 485; 472; 475; 474; 473; 322; 323; 471; 470; 469; 468; 467; 463; 465; 464; 466; 617; 583; 582; 616; 611; 598; 610; 609; 608; 607; 615; 614; 613; 612; 605; 545; 606; 604; 603; 597; 602; 601; 600; 599; 618; 1; 6; 5; 126; 155; 0; 517; 531; 516; 518; 520; 519; 544; 543; 514; 512; 515; 534; 461; 462; 229; 669; 541; 629; 542; 488; 487; 230; 237; 236; 235; 234; 232; 231; 233; 418; 424; 417; 379; 391; 389; 421; 420; 419; 416; 415; 414; 423; 413; 422; 438; 437; 436; 265; 435; 434; 353; 357; 356; 269; 361; 360; 359; 429; 428; 427; 426; 425; 433; 432; 431; 430; 619; 9; 532; 508; 667; 584; 628; 535; 537; 546; 547; 548; 549; 550; 551; 552; 553; 554; 555; 556; 557; 558; 559; 560; 561; 562; 563; 564; 565; 566; 567; 568; 569; 570; 571; 572; 573; 574; 575; 576; 577; 578; 579; 580; 581; 538; 324; 539; 540; 455; 319; 460; 182; 163; 162; 183; 207; 186; 206; 187; 592; 591; 590; 589; 596; 595; 594; 593; 588; 240; 247; 246; 245; 244; 242; 241; 243; 238; 239; 248; 587; 586; 585; 703; 698; 697; 693; 696; 692; 686; 679; 678; 677; 682; 684; 348; 513; 680; 681; 675; 687; 270; 325; 688; 689; 676; 850; 456; 459; 458; 457; 699; 685; 702; 695; 691; 690; 694; 700; 701; 260; 253; 257; 258; 249; 250; 251; 252; 256; 510; 511; 509; 349; 533; 668; 536; 849; 749; 750; 751; 752; 753; 754; 755; 756; 757; 758; 759; 760; 761; 762; 763; 764; 765; 766; 767; 768; 769; 770; 771; 772; 773; 774; 775; 776; 777; 778; 779; 780; 781; 782; 783; 784; 785; 786; 787; 788; 789; 790; 791; 792; 793; 794; 795; 796; 797; 798; 799; 802; 803; 804; 805; 806; 807; 808; 809; 810; 811; 812; 813; 814; 815; 816; 817; 818; 819; 820; 821; 822; 823; 824; 825; 826; 827; 828; 829; 830; 831; 832; 833; 834; 835; 836; 837; 838; 839; 840; 841; 842; 843; 844; 845; 846; 847; 848; 747; 748; 746; 632; 633; 128; 129; 634; 123; 124; 635; 119; 120; 636; 115; 116; 637; 111; 112; 638; 107; 108; 639; 103; 104; 640; 99; 100; 641; 95; 96; 642; 91; 92; 643; 87; 88; 644; 83; 84; 645; 79; 80; 646; 75; 76; 647; 71; 72; 648; 67; 68; 649; 63; 64; 650; 59; 60; 651; 55; 56; 652; 51; 52; 659; 28; 660; 25; 653; 48; 654; 45; 655; 41; 42; 656; 37; 38; 657; 34; 658; 31; 661; 21; 22; 662; 17; 18; 663; 13; 14; 664; 4; 665; 10; 666; 721; 704; 670; 671; 672; 673; 674; 722; 723; 724; 725; 726; 727; 728; 729; 730; 731; 732; 733; 734; 735; 736; 737; 738; 739; 740; 741; 742; 743; 744; 630; 631; 623; 135; 134; 133; 127; 125; 122; 121; 118; 117; 114; 113; 110; 109; 106; 105; 102; 101; 98; 97; 94; 93; 90; 89; 86; 85; 82; 81; 78; 77; 74; 73; 70; 69; 66; 65; 62; 61; 58; 57; 54; 53; 50; 49; 47; 46; 44; 43; 40; 39; 36; 35; 33; 32; 30; 29; 27; 26; 24; 23; 20; 19; 16; 15; 12; 11; 8; 7; 622; 524; 525; 523; 490; 491; 489; 442; 350; 294; 293; 347; 346; 345; 443; 296; 295; 292; 271; 444; 208; 445; 441; 396; 380; 384; 397; 355; 383; 398; 268; 354; 385; 399; 267; 352; 400; 266; 388; 387; 401; 386; 382; 381; 402; 351; 403; 394; 390; 395; 366; 358; 367; 364; 365; 330; 331; 321; 320; 332; 328; 329; 277; 278; 272; 279; 275; 276; 190; 191; 157; 158; 192; 188; 189; 166; 160; 164; 165; 137; 130; 131; 132; 138; 136; 184; 159; 156; 800; 801; 185; 161; 167]%N.
Lemma both_mem_facts_justified_w2 :
  forallb (mjustify (s_know (a_ss HS_both2_2)) (var_ranges (s_know (a_ss HS_both2_2))) 65536 6680576) (both_mem_facts_r30 ++ both_mem_facts_w2_r30) = true.
Proof. apply (mjust_hints_sound _ _ _ _ _ both_mem_hints_w2). vm_cast_no_check (@eq_refl bool true). Qed.
Definition both_pure_hints_w2 : list N := [705; 713; 714; 715; 719; 720; 706; 716; 717; 718; 707; 683; 625; 527; 502; 494; 479; 447; 405; 369; 334; 307; 210; 210; 281; 216; 216; 215; 214; 214; 213; 212; 194; 169; 140; 211; 211; 495; 708; 709; 710; 711; 712; 299; 298; 522; 500; 477; 300; 440; 301; 393; 302; 363; 303; 327; 305; 274; 221; 225; 227; 223; 297; 621; 526; 528; 529; 505; 483; 453; 411; 377; 343; 317; 290; 204; 180; 153; 501; 503; 504; 482; 452; 410; 376; 342; 316; 289; 203; 179; 152; 478; 480; 481; 451; 409; 375; 341; 315; 288; 202; 178; 151; 446; 448; 449; 450; 408; 374; 340; 314; 287; 201; 177; 150; 404; 406; 407; 373; 339; 313; 286; 200; 176; 149; 368; 370; 371; 372; 338; 312; 285; 199; 175; 148; 333; 335; 336; 337; 311; 284; 198; 174; 147; 306; 308; 309; 310; 280; 282; 283; 197; 173; 146; 220; 219; 219; 218; 218; 217; 193; 195; 196; 172; 145; 168; 170; 171; 144; 139; 141; 142; 143; 624; 626; 627; 530; 506; 484; 454; 412; 378; 344; 318; 291; 205; 181; 154; 521; 499; 476; 439; 392; 362; 326; 304; 273; 222; 226; 228; 224; 620; 209]%N.
Lemma both_pure_facts_justified_w2 :
  forallb (pjustify (s_know (a_ss HS_both2_2)) (var_ranges (s_know (a_ss HS_both2_2)))) (both_pure_facts_r30 ++ both_pure_facts_w2) = true.
Proof. apply (pjust_hints_sound _ _ _ both_pure_hints_w2). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_vis_justified_w2 :
  vis_match (var_ranges (s_know (a_ss HS_both2_2))) (a_vis HS_both2_2) both_vis_app_r30 = true /\ vis_match (var_ranges (s_know (a_ss HS_both2_2))) (a_ghost HS_both2_2) both_ghost = true.
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_ledger_justified_w2 :
  ledger_xmatch (var_ranges (s_know (a_ss HS_both2_2))) (a_maps HS_both2_2) both_ledger = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_consts_w2 : a_totsz HS_both2_2 = both_totsz_r30 /\ a_ylo HS_both2_2 = both_ylo_r30 /\ a_eager HS_both2_2 = both_eager /\ a_abytes HS_both2_2 = both_abytes_r30.
Proof. repeat split; reflexivity. Qed.

(* a worker (Both): this block is a worker's, its asan names renamed to both; the memory drop list at this binary's positions by content (rows 1-3's Both 233 :: 394 :: seq 402 22 = here 233 :: 453 :: seq 461 22); the pure drop list is the same; both_totsz / both_ylo: this binary's r30q2 values +/- 81920 *)
(* ===================================================================================================== *)
(* The main-entry exports at .
   - The start-up plans move every variable >= 15 by 4 (AsanRenum.rv 15 4). The lists keep the r30q2 numbering
     and are justified against the states AFTER the rename (rz / rmf / rpf / rvis / rle below).
   - 27 r30q2 facts describe the argument area of the r30q2 stack (a 10-pair auxv, argv at +184, 8 MB of stack below sp);
     they cannot hold at . 24 are unused by every reader and are left out; the stack fact is replaced by the
     one (6144513 bytes below sp); the argv[0] / argv[1] pointer facts move to both_argv_facts, by rseq. *)
(* ===================================================================================================== *)

Definition drop_ix {T : Type} (ixs : list nat) (l : list T) : list T :=
  map snd (filter (fun p => negb (existsb (Nat.eqb (fst p)) ixs)) (combine (seq 0 (length l)) l)).

Definition usp_z : zexp := ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))).
(* the stack known writable below sp at (stack_max_size less the largest argument block) *)
Definition ASTK : Z := 6144513.
Definition both_stack_fact : mfact := MWr (ZAdd usp_z (ZLit (- ASTK))) ASTK.

Definition both_mem_facts : list mfact := both_stack_fact :: drop_ix (324 :: 233 :: 453 :: seq 461 22)%nat both_mem_facts_r30_1390.
(* the list is stored COMPUTED (Eval vm_compute), not as the drop_ix expression: a kernel
   conversion between plist727 w and its unfolding otherwise evaluates drop_ix's unary-nat filter lazily and took over
   an hour at MainEntry's Qed (bisection: probes/p8, PJ434d slow vs PK434s 0.3 s). Same list, same elements. *)
Definition both_pure_facts : list pfact := Eval vm_compute in drop_ix [4; 38; 39]%nat both_pure_facts_r30_1390.
Lemma both_pure_facts_drop : both_pure_facts = drop_ix [4; 38; 39]%nat both_pure_facts_r30_1390.
Proof. vm_compute. reflexivity. Qed.

(* argv[0] / argv[1] at ; the auxv holds 27 + 2 r pairs (r = the kernel build's rseq bit) *)
Definition argv0_z (r : Z) : zexp :=
  ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 4)
    (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 8) (ZV 11)))))))) (ZLit (472 + 32 * r)).
Definition argv1_z (r : Z) : zexp :=
  ZMul (ZLtu (ZLit 1) (ZV 1))
    (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 3) (ZAdd (ZV 4)
      (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 8) (ZV 11))))))))) (ZLit (473 + 32 * r))).
Definition both_argv_facts (r : Z) : list mfact :=
  [MRo (ZAdd usp_z (ZLit 8)) 8 (argv0_z r); MRo (ZAdd usp_z (ZLit 16)) 8 (argv1_z r)].

Definition both_totsz : Z := 17729665187840.   (* #1390: the #1390 states' a_totsz (: 17729665056768) *)
Definition both_ylo : Z := 23387528507392.     (* r30q2 - 81920 *)

(* --- the rename --- *)
Fixpoint rz (e : zexp) : zexp :=
  match e with
  | ZLit z => ZLit z
  | ZV n => ZV (rv 15 4 n)
  | ZAdd a b => ZAdd (rz a) (rz b)
  | ZMul a b => ZMul (rz a) (rz b)
  | ZAnd a b => ZAnd (rz a) (rz b)
  | ZLtu a b => ZLtu (rz a) (rz b)
  end.
Definition rmf (f : mfact) : mfact :=
  match f with
  | MCell a w v => MCell (rz a) w (rz v)
  | MZeroC a n => MZeroC (rz a) n
  | MRo a w v => MRo (rz a) w (rz v)
  | MZero a n => MZero (rz a) n
  | MFill a n c => MFill (rz a) n c
  | MImg lo hi => MImg lo hi
  | MWr a n => MWr (rz a) n
  | MZeroS a n => MZeroS (rz a) (rz n)
  | MWrS a n => MWrS (rz a) (rz n)
  end.
Definition rpf (f : pfact) : pfact :=
  match f with
  | PVar n lo hi => PVar (rv 15 4 n) lo hi
  | PRange e lo hi => PRange (rz e) lo hi
  | PDisj a1 n1 a2 n2 => PDisj (rz a1) n1 (rz a2) n2
  | PDisjS a1 n1 a2 n2 => PDisjS (rz a1) (rz n1) (rz a2) (rz n2)
  end.
Definition rvis (l : list (zexp * zexp)) : list (zexp * zexp) := map (fun p => (rz (fst p), rz (snd p))) l.
Definition rle (e : lentry) : lentry := match e with LMap b n k => LMap (rz b) n k | LFog n => LFog n end.

(* --- the justification, one boolean per (hole, rseq) --- *)
Definition mlist727 (w : bool) (r : Z) : list mfact :=
  both_mem_facts ++ (if w then both_mem_facts_w1 else both_mem_facts_w2) ++ both_argv_facts r.
Definition plist727 (w : bool) : list pfact :=
  both_pure_facts ++ (if w then both_pure_facts_w1 else both_pure_facts_w2).
Definition hs727 (w : bool) (r : Z) : acs := if w then rsel r HS2_1_r0 HS2_1_r1 else rsel r HS2_2_r0 HS2_2_r1.
Definition just727 (w : bool) (r : Z) : bool :=
  let hs := hs727 w r in
  let kn := s_know (a_ss hs) in
  let vr := var_ranges kn in
  forallb (mjustify kn vr 65536 6811648) (map rmf (mlist727 w r))
  && forallb (pjustify kn vr) (map rpf (plist727 w))
  && vis_match vr (a_vis hs) (rvis both_vis_app) && vis_match vr (a_ghost hs) (rvis both_ghost)
  && ledger_xmatch vr (a_maps hs) (map rle both_ledger)
  && Z.eqb (a_totsz hs) both_totsz && Z.eqb (a_ylo hs) both_ylo
  && Z.eqb (a_eager hs) both_eager && Z.eqb (a_abytes hs) both_abytes.

Lemma just727_ok : forall w r, r = 0 \/ r = 1 -> just727 w r = true.
Proof. intros [|] r [-> | ->]; vm_cast_no_check (@eq_refl bool true). Qed.
