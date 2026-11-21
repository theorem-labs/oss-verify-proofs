(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import AxSymExec3 AsanPlan MainExport MainHint StartupHS2Asan.
(* the hand-off states and the plans' variable rename *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AS Require Import StartupHSAsan727 AsanRenum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* the r30q2 list, kept under this name; asan_mem_facts () is defined from it below *)
Definition asan_mem_facts_r30 : list mfact := [
  MCell (ZLit 872256) 8 (ZLit 1)
  ; MCell (ZLit 872264) 1 (ZLit 1)
  ; MCell (ZLit 872344) 8 (ZMul (ZLit 4096) (ZV 208))
  ; MCell (ZLit 872352) 8 (ZLit 137439023104)
  ; MCell (ZLit 872360) 8 (ZLit 95006)
  ; MCell (ZLit 872376) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))
  ; MCell (ZLit 872384) 4 (ZLit 18446744073709551615)
  ; MCell (ZLit 872392) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))
  ; MCell (ZLit 872400) 1 (ZLit 0)
  ; MCell (ZLit 872408) 8 (ZLit 4096)
  ; MCell (ZLit 872416) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 872424) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 872432) 8 (ZLit 8388608)
  ; MCell (ZLit 872440) 8 (ZLit 106643)
  ; MCell (ZLit 873024) 1 (ZLit 0)
  ; MZeroC (ZLit 873025) 3
  ; MCell (ZLit 873136) 8 (ZLit 268435456)
  ; MCell (ZLit 873144) 8 (ZLit 241591905)
  ; MCell (ZLit 873152) 8 (ZLit 1048576)
  ; MCell (ZLit 873224) 1 (ZLit 0)
  ; MCell (ZLit 873225) 1 (ZLit 0)
  ; MCell (ZLit 875960) 8 (ZLit 1099511627776)
  ; MCell (ZLit 875968) 2 (ZLit 16)
  ; MCell (ZLit 875970) 2 (ZLit 2048)
  ; MCell (ZLit 875972) 1 (ZLit 1)
  ; MCell (ZLit 876024) 4 (ZLit 4294967295)
  ; MCell (ZLit 876028) 4 (ZLit 256)
  ; MCell (ZLit 876032) 4 (ZLit 1024)
  ; MCell (ZLit 876036) 4 (ZLit 16)
  ; MCell (ZLit 876040) 4 (ZLit 2048)
  ; MCell (ZLit 876044) 1 (ZLit 0)
  ; MCell (ZLit 876048) 8 (ZLit 72340168526266369)
  ; MCell (ZLit 876056) 8 (ZLit 85899345936)
  ; MCell (ZLit 876064) 1 (ZLit 0)
  ; MCell (ZLit 876068) 4 (ZLit 4096)
  ; MCell (ZLit 876072) 8 (ZLit 816043786240)
  ; MCell (ZLit 876080) 4 (ZLit 85)
  ; MCell (ZLit 876084) 1 (ZLit 1)
  ; MCell (ZLit 876088) 8 (ZLit 0)
  ; MRo (ZLit 876096) 6 (ZLit 4294967296)
  ; MCell (ZLit 876102) 1 (ZLit 1)
  ; MCell (ZLit 876103) 1 (ZLit 0)
  ; MCell (ZLit 876104) 8 (ZLit 72340172838010881)
  ; MCell (ZLit 876112) 2 (ZLit 1)
  ; MCell (ZLit 876114) 1 (ZLit 0)
  ; MCell (ZLit 876116) 4 (ZLit 0)
  ; MCell (ZLit 876120) 1 (ZLit 1)
  ; MCell (ZLit 876124) 4 (ZLit 2)
  ; MCell (ZLit 876128) 8 (ZLit 82674)
  ; MCell (ZLit 876136) 4 (ZLit 65793)
  ; MCell (ZLit 876144) 1 (ZLit 1)
  ; MCell (ZLit 876152) 8 (ZLit 32)
  ; MCell (ZLit 876160) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20400))
  ; MCell (ZLit 876168) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZLit 876176) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19880))
  ; MCell (ZLit 876208) 8 (ZLit 0)
  ; MCell (ZLit 884280) 1 (ZLit 1)
  ; MCell (ZLit 884281) 1 (ZLit 1)
  ; MCell (ZLit 884282) 1 (ZLit 1)
  ; MCell (ZLit 884284) 4 (ZLit 299)
  ; MCell (ZLit 884288) 8 (ZLit 884296)
  ; MCell (ZLit 884296) 8 (ZMul (ZLit 4096) (ZV 207))
  ; MCell (ZLit 884312) 4 (ZLit 2)
  ; MCell (ZLit 884316) 1 (ZLit 1)
  ; MCell (ZLit 884320) 1 (ZLit 1)
  ; MCell (ZLit 884324) 4 (ZLit 0)
  ; MCell (ZLit 886264) 8 (ZLit 2147450880)
  ; MCell (ZLit 886272) 4 (ZLit 1)
  ; MCell (ZLit 889560) 1 (ZLit 1)
  ; MCell (ZLit 889561) 1 (ZLit 1)
  ; MCell (ZLit 889562) 1 (ZLit 0)
  ; MCell (ZLit 889563) 1 (ZLit 0)
  ; MCell (ZLit 889568) 8 (ZLit 140737488355327)
  ; MCell (ZLit 889592) 1 (ZLit 1)
  ; MCell (ZLit 889596) 4 (ZLit 30)
  ; MCell (ZLit 889712) 8 (ZLit 1)
  ; MCell (ZLit 889720) 8 (ZLit 4096)
  ; MCell (ZLit 890432) 8 (ZLit 890496)
  ; MCell (ZLit 890496) 8 (ZLit 859304)
  ; MCell (ZLit 890504) 4 (ZLit 5)
  ; MCell (ZLit 890512) 8 (ZLit 0)
  ; MCell (ZLit 890520) 8 (ZLit 0)
  ; MCell (ZLit 890528) 8 (ZLit 0)
  ; MZeroC (ZLit 890536) 5
  ; MCell (ZLit 890600) 1 (ZLit 1)
  ; MCell (ZLit 890608) 1 (ZLit 1)
  ; MCell (ZLit 890616) 8 (ZLit 890712)
  ; MCell (ZLit 890624) 8 (ZLit 890664)
  ; MCell (ZLit 890632) 8 (ZLit 0)
  ; MCell (ZLit 890648) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 65536))
  ; MCell (ZLit 890656) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 160))
  ; MCell (ZLit 890664) 8 (ZLit 0)
  ; MCell (ZLit 890672) 4 (ZLit 0)
  ; MCell (ZLit 890676) 4 (ZLit 0)
  ; MCell (ZLit 890680) 8 (ZLit 0)
  ; MCell (ZLit 890688) 8 (ZLit 0)
  ; MCell (ZLit 890696) 4 (ZLit 0)
  ; MCell (ZLit 890700) 4 (ZLit 0)
  ; MCell (ZLit 890704) 4 (ZLit 0)
  ; MCell (ZLit 890708) 4 (ZLit 0)
  ; MCell (ZLit 890712) 8 (ZLit 433684)
  ; MCell (ZLit 890720) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 890728) 4 (ZLit 0)
  ; MCell (ZLit 890736) 8 (ZLit 0)
  ; MCell (ZLit 890744) 4 (ZLit 0)
  ; MCell (ZLit 890748) 4 (ZLit 0)
  ; MCell (ZLit 890752) 8 (ZLit 1)
  ; MCell (ZLit 890760) 8 (ZLit 1)
  ; MCell (ZLit 890768) 8 (ZLit 1)
  ; MCell (ZLit 890776) 8 (ZLit 1)
  ; MCell (ZLit 890784) 8 (ZMul (ZLit 4096) (ZV 245))
  ; MCell (ZLit 890792) 8 (ZLit 4096)
  ; MCell (ZLit 890800) 8 (ZLit 1)
  ; MCell (ZLit 890808) 8 (ZLit 0)
  ; MCell (ZLit 890816) 8 (ZLit 0)
  ; MCell (ZLit 890824) 8 (ZLit 0)
  ; MCell (ZLit 890832) 8 (ZLit 0)
  ; MCell (ZLit 890840) 8 (ZLit 0)
  ; MCell (ZLit 890848) 8 (ZLit 0)
  ; MCell (ZLit 890856) 8 (ZLit 0)
  ; MCell (ZLit 890864) 8 (ZLit 0)
  ; MCell (ZLit 890872) 4 (ZLit 0)
  ; MCell (ZLit 1419336) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 65536))
  ; MCell (ZLit 1419344) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20416))
  ; MCell (ZLit 1419352) 8 (ZLit 417544)
  ; MCell (ZLit 1419361) 1 (ZLit 1)
  ; MCell (ZLit 1474704) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-160)))
  ; MCell (ZLit 1474712) 4 (ZLit 0)
  ; MCell (ZLit 1474720) 8 (ZLit 4096)
  ; MCell (ZLit 1483040) 1 (ZLit 0)
  ; MZeroC (ZLit 1483041) 3
  ; MCell (ZLit 1483048) 8 (ZLit 1)
  ; MCell (ZLit 1483056) 8 (ZLit 0)
  ; MCell (ZLit 1483064) 8 (ZLit 0)
  ; MCell (ZLit 1483072) 8 (ZLit 82674)
  ; MCell (ZLit 1483080) 8 (ZLit 128849084416)
  ; MCell (ZLit 1483088) 8 (ZLit 0)
  ; MCell (ZLit 1483096) 8 (ZLit 0)
  ; MCell (ZLit 1483104) 8 (ZLit 0)
  ; MCell (ZLit 1483112) 8 (ZLit 0)
  ; MCell (ZLit 1483120) 8 (ZLit 1103823372545)
  ; MCell (ZLit 1483128) 8 (ZLit 4294967296)
  ; MCell (ZLit 1483136) 8 (ZLit 0)
  ; MCell (ZLit 1483144) 8 (ZLit 0)
  ; MCell (ZLit 1483152) 8 (ZLit 0)
  ; MCell (ZLit 1483160) 8 (ZLit 65537)
  ; MCell (ZLit 1483168) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 1483176) 8 (ZLit 72176)
  ; MCell (ZLit 1483184) 8 (ZLit 256)
  ; MCell (ZLit 1483192) 8 (ZLit 0)
  ; MCell (ZLit 1483200) 8 (ZLit 0)
  ; MCell (ZLit 1483208) 8 (ZLit 0)
  ; MCell (ZLit 1483216) 8 (ZLit 0)
  ; MCell (ZLit 1483224) 8 (ZLit 18446744069414584320)
  ; MCell (ZLit 1483232) 8 (ZLit 1)
  ; MCell (ZLit 1483240) 8 (ZLit 83534)
  ; MCell (ZLit 1483248) 8 (ZLit 82674)
  ; MCell (ZLit 1483256) 8 (ZLit 82674)
  ; MCell (ZLit 1483264) 8 (ZLit 1103823372544)
  ; MCell (ZLit 1483272) 8 (ZLit 0)
  ; MCell (ZLit 1483280) 8 (ZLit 126686)
  ; MCell (ZLit 1483288) 8 (ZLit 72339073309605888)
  ; MCell (ZLit 1483296) 8 (ZLit 72340172838076673)
  ; MCell (ZLit 1483304) 8 (ZLit 16843009)
  ; MCell (ZLit 1483312) 8 (ZLit 1103806595073)
  ; MCell (ZLit 1483320) 8 (ZLit 104707)
  ; MCell (ZLit 1483328) 8 (ZLit 281474976710912)
  ; MCell (ZLit 1483536) 8 (ZLit 396716)
  ; MCell (ZLit 1483576) 8 (ZLit 1)
  ; MCell (ZLit 1483600) 8 (ZLit 417404)
  ; MCell (ZLit 1483608) 8 (ZLit 417172)
  ; MCell (ZLit 1483616) 8 (ZLit 507536)
  ; MCell (ZLit 1483656) 1 (ZLit 1)
  ; MCell (ZLit 1483928) 1 (ZLit 0)
  ; MCell (ZLit 1746128) 8 (ZLit 8388608)
  ; MCell (ZLit 1746136) 8 (ZMul (ZLit 4096) (ZV 454))
  ; MCell (ZLit 1746148) 1 (ZLit 0)
  ; MZeroC (ZLit 1746149) 3
  ; MCell (ZLit 6005976) 4 (ZLit 1)
  ; MCell (ZLit 6005984) 1 (ZLit 0)
  ; MZeroC (ZLit 6005985) 3
  ; MCell (ZLit 6005992) 8 (ZMul (ZLit 4096) (ZV 453))
  ; MCell (ZLit 6269376) 1 (ZLit 0)
  ; MCell (ZLit 6269380) 4 (ZLit 0)
  ; MCell (ZLit 6269384) 8 (ZLit 72340172821233664)
  ; MCell (ZLit 6269392) 4 (ZLit 257)
  ; MCell (ZLit 6269396) 2 (ZLit 0)
  ; MCell (ZLit 6269398) 1 (ZLit 0)
  ; MCell (ZLit 6269400) 4 (ZLit 1)
  ; MCell (ZLit 6269408) 8 (ZLit 82674)
  ; MCell (ZLit 6269416) 4 (ZLit 1)
  ; MCell (ZLit 6269824) 8 (ZLit 6269888)
  ; MCell (ZLit 6269888) 8 (ZLit 868984)
  ; MCell (ZLit 6269896) 4 (ZLit 38)
  ; MCell (ZLit 6269904) 8 (ZLit 0)
  ; MCell (ZLit 6269912) 8 (ZLit 0)
  ; MCell (ZLit 6269920) 8 (ZLit 0)
  ; MZeroC (ZLit 6269928) 38
  ; MCell (ZLit 6269992) 1 (ZLit 1)
  ; MCell (ZLit 6270000) 1 (ZLit 0)
  ; MCell (ZLit 6270001) 1 (ZLit 1)
  ; MCell (ZLit 6270002) 2 (ZLit 0)
  ; MCell (ZLit 6270008) 2 (ZLit 0)
  ; MCell (ZLit 6270016) 8 (ZLit 82674)
  ; MCell (ZLit 6270024) 2 (ZLit 0)
  ; MCell (ZLit 6665960) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))) (ZLit 16))
  ; MCell (ZLit 6665984) 8 (ZLit 833928)
  ; MCell (ZLit 6665992) 8 (ZLit 0)
  ; MCell (ZLit 6666000) 8 (ZLit 24)
  ; MCell (ZLit 6666008) 8 (ZLit 8)
  ; MCell (ZLit 6666016) 8 (ZLit 0)
  ; MCell (ZLit 6666024) 8 (ZLit 6666024)
  ; MCell (ZLit 6666032) 8 (ZLit 6666024)
  ; MCell (ZLit 6666040) 8 (ZLit 6666024)
  ; MCell (ZLit 6666048) 8 (ZLit 0)
  ; MCell (ZLit 6666056) 4 (ZV 44)
  ; MCell (ZLit 6666064) 4 (ZLit 2)
  ; MCell (ZLit 6666074) 1 (ZLit 1)
  ; MCell (ZLit 6666136) 8 (ZLit 6671328)
  ; MCell (ZLit 6666144) 8 (ZLit 6666144)
  ; MCell (ZLit 6666176) 8 (ZLit 6667008)
  ; MCell (ZLit 6666208) 8 (ZV 45)
  ; MCell (ZLit 6666216) 8 (ZLit 6666256)
  ; MCell (ZLit 6666224) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MCell (ZLit 6666232) 8 (ZMul (ZLit 4096) (ZV 310))
  ; MCell (ZLit 6666256) 8 (ZLit 1)
  ; MCell (ZLit 6666264) 8 (ZLit 6668272)
  ; MRo (ZLit 6666360) 8 (ZV 45)
  ; MWr (ZLit 6666368) 10112
  ; MCell (ZLit 6666384) 4 (ZLit 1)
  ; MCell (ZLit 6666392) 8 (ZLit 6666400)
  ; MCell (ZLit 6666408) 8 (ZLit 771736)
  ; MCell (ZLit 6666664) 8 (ZLit 507536)
  ; MCell (ZLit 6666944) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))
  ; MCell (ZLit 6666952) 1 (ZLit 1)
  ; MCell (ZLit 6666960) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24))
  ; MCell (ZLit 6666968) 8 (ZLit 6665976)
  ; MCell (ZLit 6666976) 8 (ZLit 248)
  ; MCell (ZLit 6666984) 8 (ZLit 8)
  ; MCell (ZLit 6666992) 8 (ZLit 1)
  ; MCell (ZLit 6667000) 8 (ZLit 4096)
  ; MCell (ZLit 6667056) 8 (ZV 9)
  ; MCell (ZLit 6667088) 4 (ZLit 1)
  ; MCell (ZLit 6667092) 4 (ZLit 1)
  ; MCell (ZLit 6667112) 8 (ZLit 97)
  ; MCell (ZLit 6667120) 8 (ZLit 0)
  ; MCell (ZLit 6667560) 8 (ZLit 10)
  ; MCell (ZLit 6667664) 8 (ZLit 2)
  ; MCell (ZLit 6667696) 8 (ZLit 2)
  ; MCell (ZLit 6667728) 8 (ZLit 2)
  ; MCell (ZLit 6667992) 1 (ZLit 1)
  ; MCell (ZLit 6670240) 8 (ZLit 396200)
  ; MCell (ZLit 6671264) 4 (ZLit 0)
  ; MCell (ZLit 6671272) 4 (ZLit 0)
  ; MCell (ZLit 6671328) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MCell (ZLit 859360) 8 (ZLit 8)
  ; MCell (ZLit 859368) 8 (ZLit 138074)
  ; MCell (ZLit 859384) 4 (ZLit 2)
  ; MWr (ZLit 835584) 5830776
  ; MImg 872265 872344
  ; MImg 872368 872376
  ; MImg 872388 872392
  ; MImg 872401 872408
  ; MImg 872448 873024
  ; MImg 873028 873136
  ; MImg 873160 873224
  ; MImg 873226 875960
  ; MImg 875973 876024
  ; MImg 876045 876048
  ; MImg 876065 876068
  ; MImg 876085 876088
  ; MImg 876115 876116
  ; MImg 876121 876124
  ; MImg 876140 876144
  ; MImg 876145 876152
  ; MImg 876184 876208
  ; MImg 876216 876280
  ; MImg 881064 884280
  ; MImg 884283 884284
  ; MImg 884304 884312
  ; MImg 884317 884320
  ; MImg 884321 884324
  ; MImg 884328 886264
  ; MImg 886276 889560
  ; MImg 889564 889568
  ; MImg 889576 889592
  ; MImg 889593 889596
  ; MImg 889600 889712
  ; MImg 889728 890432
  ; MImg 890440 890496
  ; MImg 890508 890512
  ; MImg 890541 890600
  ; MImg 890601 890608
  ; MImg 890609 890616
  ; MImg 890640 890648
  ; MImg 890732 890736
  ; MImg 890876 1419336
  ; MImg 1419360 1419361
  ; MImg 1419362 1474704
  ; MImg 1474716 1474720
  ; MImg 1474728 1474752
  ; MImg 1478847 1478848
  ; MImg 1482943 1483040
  ; MImg 1483044 1483048
  ; MImg 1483336 1483536
  ; MImg 1483544 1483576
  ; MImg 1483584 1483600
  ; MImg 1483624 1483656
  ; MImg 1483657 1483928
  ; MImg 1483929 1746120
  ; MImg 6005980 6005984
  ; MImg 6005988 6005992
  ; MImg 6006000 6269376
  ; MImg 6269377 6269380
  ; MImg 6269399 6269400
  ; MImg 6269404 6269408
  ; MImg 6269420 6269824
  ; MImg 6269832 6269888
  ; MImg 6269900 6269904
  ; MImg 6269966 6269992
  ; MImg 6269993 6270000
  ; MImg 6270004 6270008
  ; MImg 6270010 6270016
  ; MImg 6270026 6665960
  ; MImg 6665968 6665984
  ; MImg 6666060 6666064
  ; MImg 6666068 6666074
  ; MImg 6666075 6666136
  ; MImg 6666152 6666176
  ; MImg 6666184 6666208
  ; MImg 6666240 6666256
  ; MImg 6666272 6666360
  ; MImg 6666368 6666384
  ; MImg 6666388 6666392
  ; MImg 6666400 6666408
  ; MImg 6666416 6666664
  ; MImg 6666672 6666936
  ; MImg 6666953 6666960
  ; MImg 6667008 6667056
  ; MImg 6667064 6667080
  ; MImg 6667096 6667104
  ; MImg 6667160 6667176
  ; MImg 6667184 6667280
  ; MImg 6667288 6667312
  ; MImg 6667320 6667344
  ; MImg 6667352 6667560
  ; MImg 6667568 6667664
  ; MImg 6667672 6667696
  ; MImg 6667704 6667728
  ; MImg 6667736 6667992
  ; MImg 6667993 6668000
  ; MImg 6668008 6670224
  ; MImg 6670232 6670240
  ; MImg 6670248 6671264
  ; MImg 6671268 6671272
  ; MImg 6671276 6671328
  ; MImg 6671336 6676480
  ; MImg 859376 859384
  ; MImg 859388 872256
  ; MImg 65536 859360
  ; MWr (ZLit 2147459072) 826368
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
  ; MZero (ZLit 2147469952) 89698
  ; MFill (ZLit 2147559650) 256 249
  ; MZero (ZLit 2147559906) 715694
  ; MFill (ZLit 2148275600) 8192 249
  ; MZero (ZLit 2148283792) 1648
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904)) 8 (ZLit 870160)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19912)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920)) 8 (ZLit 870224)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19928)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936)) 8 (ZLit 870288)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19944)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952)) 8 (ZLit 870352)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19960)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968)) 8 (ZLit 870416)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19976)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984)) 8 (ZLit 870480)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19992)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000)) 8 (ZLit 870544)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20008)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016)) 8 (ZLit 870608)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20024)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032)) 8 (ZLit 870672)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20040)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048)) 8 (ZLit 870736)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20056)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064)) 8 (ZLit 870800)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20072)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080)) 8 (ZLit 870864)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20088)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096)) 8 (ZLit 870928)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20104)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20112)) 8 (ZLit 870992)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20120)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20128)) 8 (ZLit 871056)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20136)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20112))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20144)) 8 (ZLit 871120)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20152)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20128))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20160)) 8 (ZLit 871184)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20168)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20144))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20176)) 8 (ZLit 871248)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20184)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20160))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20192)) 8 (ZLit 871312)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20200)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20176))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20208)) 8 (ZLit 871376)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20216)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20192))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20224)) 8 (ZLit 871440)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20232)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20208))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20240)) 8 (ZLit 871504)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20248)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20224))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20256)) 8 (ZLit 871568)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20264)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20240))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20272)) 8 (ZLit 871632)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20280)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20256))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20288)) 8 (ZLit 871696)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20296)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20272))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20304)) 8 (ZLit 871760)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20312)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20288))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20320)) 8 (ZLit 871824)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20328)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20304))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20336)) 8 (ZLit 871888)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20344)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20320))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20352)) 8 (ZLit 871952)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20360)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20336))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20368)) 8 (ZLit 872016)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20376)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20352))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20384)) 8 (ZLit 872080)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20392)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20368))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20400)) 8 (ZLit 872144)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6668072)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6668292)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 64)) 8 (ZLit 6666232)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 72)) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3169)) 927
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 228)) 65536
  ; MCell (ZMul (ZLit 4096) (ZV 228)) 8 (ZLit 838216)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6666224)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 8)) 8 (ZLit 303996)
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MWr (ZMul (ZLit 4096) (ZV 471)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 471)) 8 (ZLit 12297829379609722881)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 8)) 8 (ZLit 870160)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 16)) 8 (ZLit 872144)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 24)) 4072
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 471)) (ZLit 2147450880)) 512
].

(* #1390: asan_mem_facts_r30 with each item just727 refuses on the #1390 hand-off states moved to the value those states hold (pl3_mf_cure_1390_g1.py); the r30 lemmas keep asan_mem_facts_r30 *)
Definition asan_mem_facts_r30_1390 : list mfact := [
  MCell (ZLit 872320) 8 (ZLit 1)
  ; MCell (ZLit 872328) 1 (ZLit 1)
  ; MCell (ZLit 872408) 8 (ZMul (ZLit 4096) (ZV 208))
  ; MCell (ZLit 872416) 8 (ZLit 137439023104)
  ; MCell (ZLit 872424) 8 (ZLit 95006)
  ; MCell (ZLit 872440) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))
  ; MCell (ZLit 872448) 4 (ZLit 18446744073709551615)
  ; MCell (ZLit 872456) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))
  ; MCell (ZLit 872464) 1 (ZLit 0)
  ; MCell (ZLit 872472) 8 (ZLit 4096)
  ; MCell (ZLit 872480) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 872488) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 872496) 8 (ZLit 8388608)
  ; MCell (ZLit 872504) 8 (ZLit 106643)
  ; MCell (ZLit 873088) 1 (ZLit 0)
  ; MZeroC (ZLit 873089) 3
  ; MCell (ZLit 873200) 8 (ZLit 268435456)
  ; MCell (ZLit 873208) 8 (ZLit 241591905)
  ; MCell (ZLit 873216) 8 (ZLit 1048576)
  ; MCell (ZLit 873288) 1 (ZLit 0)
  ; MCell (ZLit 873289) 1 (ZLit 0)
  ; MCell (ZLit 876024) 8 (ZLit 1099511627776)
  ; MCell (ZLit 876032) 2 (ZLit 16)
  ; MCell (ZLit 876034) 2 (ZLit 2048)
  ; MCell (ZLit 876036) 1 (ZLit 1)
  ; MCell (ZLit 876088) 4 (ZLit 4294967295)
  ; MCell (ZLit 876092) 4 (ZLit 256)
  ; MCell (ZLit 876096) 4 (ZLit 1024)
  ; MCell (ZLit 876100) 4 (ZLit 16)
  ; MCell (ZLit 876104) 4 (ZLit 2048)
  ; MCell (ZLit 876108) 1 (ZLit 0)
  ; MCell (ZLit 876112) 8 (ZLit 72340168526266369)
  ; MCell (ZLit 876120) 8 (ZLit 85899345936)
  ; MCell (ZLit 876128) 1 (ZLit 0)
  ; MCell (ZLit 876132) 4 (ZLit 4096)
  ; MCell (ZLit 876136) 8 (ZLit 816043786240)
  ; MCell (ZLit 876144) 4 (ZLit 85)
  ; MCell (ZLit 876148) 1 (ZLit 1)
  ; MCell (ZLit 876152) 8 (ZLit 0)
  ; MRo (ZLit 876160) 6 (ZLit 4294967296)
  ; MCell (ZLit 876166) 1 (ZLit 1)
  ; MCell (ZLit 876167) 1 (ZLit 0)
  ; MCell (ZLit 876168) 8 (ZLit 72340172838010881)
  ; MCell (ZLit 876176) 2 (ZLit 1)
  ; MCell (ZLit 876178) 1 (ZLit 0)
  ; MCell (ZLit 876180) 4 (ZLit 0)
  ; MCell (ZLit 876184) 1 (ZLit 1)
  ; MCell (ZLit 876188) 4 (ZLit 2)
  ; MCell (ZLit 876192) 8 (ZLit 82674)
  ; MCell (ZLit 876200) 4 (ZLit 65793)
  ; MCell (ZLit 876208) 1 (ZLit 1)
  ; MCell (ZLit 876216) 8 (ZLit 32)
  ; MCell (ZLit 876224) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20400))
  ; MCell (ZLit 876232) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZLit 876240) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19880))
  ; MCell (ZLit 876272) 8 (ZLit 0)
  ; MCell (ZLit 884344) 1 (ZLit 1)
  ; MCell (ZLit 884345) 1 (ZLit 1)
  ; MCell (ZLit 884346) 1 (ZLit 1)
  ; MCell (ZLit 884348) 4 (ZLit 299)
  ; MCell (ZLit 884352) 8 (ZLit 884360)
  ; MCell (ZLit 884360) 8 (ZMul (ZLit 4096) (ZV 207))
  ; MCell (ZLit 884376) 4 (ZLit 2)
  ; MCell (ZLit 884380) 1 (ZLit 1)
  ; MCell (ZLit 884384) 1 (ZLit 1)
  ; MCell (ZLit 884388) 4 (ZLit 0)
  ; MCell (ZLit 886328) 8 (ZLit 2147450880)
  ; MCell (ZLit 886336) 4 (ZLit 1)
  ; MCell (ZLit 889624) 1 (ZLit 1)
  ; MCell (ZLit 889625) 1 (ZLit 1)
  ; MCell (ZLit 889626) 1 (ZLit 0)
  ; MCell (ZLit 889627) 1 (ZLit 0)
  ; MCell (ZLit 889632) 8 (ZLit 140737488355327)
  ; MCell (ZLit 889656) 1 (ZLit 1)
  ; MCell (ZLit 889660) 4 (ZLit 30)
  ; MCell (ZLit 889776) 8 (ZLit 1)
  ; MCell (ZLit 889784) 8 (ZLit 4096)
  ; MCell (ZLit 890496) 8 (ZLit 890560)
  ; MCell (ZLit 890560) 8 (ZLit 859376)
  ; MCell (ZLit 890568) 4 (ZLit 5)
  ; MCell (ZLit 890576) 8 (ZLit 0)
  ; MCell (ZLit 890584) 8 (ZLit 0)
  ; MCell (ZLit 890592) 8 (ZLit 0)
  ; MZeroC (ZLit 890600) 5
  ; MCell (ZLit 890664) 1 (ZLit 1)
  ; MCell (ZLit 890672) 1 (ZLit 1)
  ; MCell (ZLit 890680) 8 (ZLit 890776)
  ; MCell (ZLit 890688) 8 (ZLit 890728)
  ; MCell (ZLit 890696) 8 (ZLit 0)
  ; MCell (ZLit 890712) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 65536))
  ; MCell (ZLit 890720) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 160))
  ; MCell (ZLit 890728) 8 (ZLit 0)
  ; MCell (ZLit 890736) 4 (ZLit 0)
  ; MCell (ZLit 890740) 4 (ZLit 0)
  ; MCell (ZLit 890744) 8 (ZLit 0)
  ; MCell (ZLit 890752) 8 (ZLit 0)
  ; MCell (ZLit 890760) 4 (ZLit 0)
  ; MCell (ZLit 890764) 4 (ZLit 0)
  ; MCell (ZLit 890768) 4 (ZLit 0)
  ; MCell (ZLit 890772) 4 (ZLit 0)
  ; MCell (ZLit 890776) 8 (ZLit 433764)
  ; MCell (ZLit 890784) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 890792) 4 (ZLit 0)
  ; MCell (ZLit 890800) 8 (ZLit 0)
  ; MCell (ZLit 890808) 4 (ZLit 0)
  ; MCell (ZLit 890812) 4 (ZLit 0)
  ; MCell (ZLit 890816) 8 (ZLit 1)
  ; MCell (ZLit 890824) 8 (ZLit 1)
  ; MCell (ZLit 890832) 8 (ZLit 1)
  ; MCell (ZLit 890840) 8 (ZLit 1)
  ; MCell (ZLit 890848) 8 (ZMul (ZLit 4096) (ZV 245))
  ; MCell (ZLit 890856) 8 (ZLit 4096)
  ; MCell (ZLit 890864) 8 (ZLit 1)
  ; MCell (ZLit 890872) 8 (ZLit 0)
  ; MCell (ZLit 890880) 8 (ZLit 0)
  ; MCell (ZLit 890888) 8 (ZLit 0)
  ; MCell (ZLit 890896) 8 (ZLit 0)
  ; MCell (ZLit 890904) 8 (ZLit 0)
  ; MCell (ZLit 890912) 8 (ZLit 0)
  ; MCell (ZLit 890920) 8 (ZLit 0)
  ; MCell (ZLit 890928) 8 (ZLit 0)
  ; MCell (ZLit 890936) 4 (ZLit 0)
  ; MCell (ZLit 1419400) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 65536))
  ; MCell (ZLit 1419408) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20416))
  ; MCell (ZLit 1419416) 8 (ZLit 417624)
  ; MCell (ZLit 1419425) 1 (ZLit 1)
  ; MCell (ZLit 1474768) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-160)))
  ; MCell (ZLit 1474776) 4 (ZLit 0)
  ; MCell (ZLit 1474784) 8 (ZLit 4096)
  ; MCell (ZLit 1483104) 1 (ZLit 0)
  ; MZeroC (ZLit 1483105) 3
  ; MCell (ZLit 1483112) 8 (ZLit 1)
  ; MCell (ZLit 1483120) 8 (ZLit 0)
  ; MCell (ZLit 1483128) 8 (ZLit 0)
  ; MCell (ZLit 1483136) 8 (ZLit 82674)
  ; MCell (ZLit 1483144) 8 (ZLit 128849084416)
  ; MCell (ZLit 1483152) 8 (ZLit 0)
  ; MCell (ZLit 1483160) 8 (ZLit 0)
  ; MCell (ZLit 1483168) 8 (ZLit 0)
  ; MCell (ZLit 1483176) 8 (ZLit 0)
  ; MCell (ZLit 1483184) 8 (ZLit 1103823372545)
  ; MCell (ZLit 1483192) 8 (ZLit 4294967296)
  ; MCell (ZLit 1483200) 8 (ZLit 0)
  ; MCell (ZLit 1483208) 8 (ZLit 0)
  ; MCell (ZLit 1483152) 8 (ZLit 0)
  ; MCell (ZLit 1483224) 8 (ZLit 65537)
  ; MCell (ZLit 1483232) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 1483240) 8 (ZLit 72176)
  ; MCell (ZLit 1483248) 8 (ZLit 256)
  ; MCell (ZLit 1483256) 8 (ZLit 0)
  ; MCell (ZLit 1483200) 8 (ZLit 0)
  ; MCell (ZLit 1483208) 8 (ZLit 0)
  ; MCell (ZLit 1483216) 8 (ZLit 0)
  ; MCell (ZLit 1483288) 8 (ZLit 18446744069414584320)
  ; MCell (ZLit 1483296) 8 (ZLit 1)
  ; MCell (ZLit 1483304) 8 (ZLit 83534)
  ; MCell (ZLit 1483312) 8 (ZLit 82674)
  ; MCell (ZLit 1483320) 8 (ZLit 82674)
  ; MCell (ZLit 1483328) 8 (ZLit 1103823372544)
  ; MCell (ZLit 1483272) 8 (ZLit 0)
  ; MCell (ZLit 1483344) 8 (ZLit 126686)
  ; MCell (ZLit 1483352) 8 (ZLit 72339073309605888)
  ; MCell (ZLit 1483360) 8 (ZLit 72340172838076673)
  ; MCell (ZLit 1483368) 8 (ZLit 16843009)
  ; MCell (ZLit 1483376) 8 (ZLit 1103806595073)
  ; MCell (ZLit 1483384) 8 (ZLit 104707)
  ; MCell (ZLit 1483392) 8 (ZLit 281474976710912)
  ; MCell (ZLit 1483600) 8 (ZLit 396796)
  ; MCell (ZLit 1483640) 8 (ZLit 1)
  ; MCell (ZLit 1483664) 8 (ZLit 417484)
  ; MCell (ZLit 1483672) 8 (ZLit 417252)
  ; MCell (ZLit 1483680) 8 (ZLit 507616)
  ; MCell (ZLit 1483720) 1 (ZLit 1)
  ; MCell (ZLit 1483992) 1 (ZLit 0)
  ; MCell (ZLit 1746192) 8 (ZLit 8388608)
  ; MCell (ZLit 1746200) 8 (ZMul (ZLit 4096) (ZV 454))
  ; MCell (ZLit 1746212) 1 (ZLit 0)
  ; MZeroC (ZLit 1746213) 3
  ; MCell (ZLit 6006040) 4 (ZLit 1)
  ; MCell (ZLit 6006048) 1 (ZLit 0)
  ; MZeroC (ZLit 6006049) 3
  ; MCell (ZLit 6006056) 8 (ZMul (ZLit 4096) (ZV 453))
  ; MCell (ZLit 6269440) 1 (ZLit 0)
  ; MCell (ZLit 6269444) 4 (ZLit 0)
  ; MCell (ZLit 6269448) 8 (ZLit 72340172821233664)
  ; MCell (ZLit 6269456) 4 (ZLit 257)
  ; MCell (ZLit 6269460) 2 (ZLit 0)
  ; MCell (ZLit 6269462) 1 (ZLit 0)
  ; MCell (ZLit 6269464) 4 (ZLit 1)
  ; MCell (ZLit 6269472) 8 (ZLit 82674)
  ; MCell (ZLit 6269480) 4 (ZLit 1)
  ; MCell (ZLit 6269888) 8 (ZLit 6269952)
  ; MCell (ZLit 6269952) 8 (ZLit 869056)
  ; MCell (ZLit 6269960) 4 (ZLit 38)
  ; MCell (ZLit 6269968) 8 (ZLit 0)
  ; MCell (ZLit 6269976) 8 (ZLit 0)
  ; MCell (ZLit 6269984) 8 (ZLit 0)
  ; MZeroC (ZLit 6269992) 38
  ; MCell (ZLit 6270056) 1 (ZLit 1)
  ; MCell (ZLit 6270064) 1 (ZLit 0)
  ; MCell (ZLit 6270065) 1 (ZLit 1)
  ; MCell (ZLit 6270066) 2 (ZLit 0)
  ; MCell (ZLit 6270072) 2 (ZLit 0)
  ; MCell (ZLit 6270080) 8 (ZLit 82674)
  ; MCell (ZLit 6270088) 2 (ZLit 0)
  ; MCell (ZLit 6666024) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))) (ZLit 16))
  ; MCell (ZLit 6797328) 8 (ZLit 834000)
  ; MCell (ZLit 6797336) 8 (ZLit 0)
  ; MCell (ZLit 6797344) 8 (ZLit 24)
  ; MCell (ZLit 6797352) 8 (ZLit 8)
  ; MCell (ZLit 6797360) 8 (ZLit 0)
  ; MCell (ZLit 6666032) 8 (ZLit 6666032)
  ; MCell (ZLit 6666040) 8 (ZLit 6666032)
  ; MCell (ZLit 6666048) 8 (ZLit 6666032)
  ; MCell (ZLit 6666056) 8 (ZLit 0)
  ; MCell (ZLit 6666064) 4 (ZV 44)
  ; MCell (ZLit 6666072) 4 (ZLit 2)
  ; MCell (ZLit 6666082) 1 (ZLit 1)
  ; MCell (ZLit 6666144) 8 (ZLit 6802336)
  ; MCell (ZLit 6666152) 8 (ZLit 6666152)
  ; MCell (ZLit 6666184) 8 (ZLit 6798016)
  ; MCell (ZLit 6666216) 8 (ZV 45)
  ; MCell (ZLit 6666224) 8 (ZLit 6666264)
  ; MCell (ZLit 6666232) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MCell (ZLit 6666240) 8 (ZMul (ZLit 4096) (ZV 310))
  ; MCell (ZLit 6666264) 8 (ZLit 1)
  ; MCell (ZLit 6666272) 8 (ZLit 6668280)
  ; MRo (ZLit 6797368) 8 (ZV 45)
  ; MWr (ZLit 6797376) 10176
  ; MCell (ZLit 6797392) 4 (ZLit 1)
  ; MCell (ZLit 6797400) 8 (ZLit 6797408)
  ; MCell (ZLit 6797416) 8 (ZLit 771804)
  ; MCell (ZLit 6797672) 8 (ZLit 507616)
  ; MCell (ZLit 6666944) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))
  ; MCell (ZLit 6797960) 1 (ZLit 1)
  ; MCell (ZLit 6797968) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24))
  ; MCell (ZLit 6797976) 8 (ZLit 6797320)
  ; MCell (ZLit 6797984) 8 (ZLit 248)
  ; MCell (ZLit 6797992) 8 (ZLit 8)
  ; MCell (ZLit 6798000) 8 (ZLit 1)
  ; MCell (ZLit 6798008) 8 (ZLit 4096)
  ; MCell (ZLit 6798064) 8 (ZV 9)
  ; MCell (ZLit 6798096) 4 (ZLit 1)
  ; MCell (ZLit 6798100) 4 (ZLit 1)
  ; MCell (ZLit 6798120) 8 (ZLit 97)
  ; MCell (ZLit 6798128) 8 (ZLit 0)
  ; MCell (ZLit 6798568) 8 (ZLit 10)
  ; MCell (ZLit 6798672) 8 (ZLit 2)
  ; MCell (ZLit 6798704) 8 (ZLit 2)
  ; MCell (ZLit 6798736) 8 (ZLit 2)
  ; MCell (ZLit 6799000) 1 (ZLit 1)
  ; MCell (ZLit 6801248) 8 (ZLit 396280)
  ; MCell (ZLit 6802272) 4 (ZLit 0)
  ; MCell (ZLit 6802280) 4 (ZLit 0)
  ; MCell (ZLit 6802336) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MCell (ZLit 859432) 8 (ZLit 8)
  ; MCell (ZLit 859440) 8 (ZLit 138074)
  ; MCell (ZLit 859456) 4 (ZLit 2)
  ; MWr (ZLit 835584) 5961784
  ; MImg 872329 872408
  ; MImg 872432 872440
  ; MImg 872452 872456
  ; MImg 872465 872472
  ; MImg 872512 873088
  ; MImg 873092 873200
  ; MImg 873224 873288
  ; MImg 873290 876024
  ; MImg 876037 876088
  ; MImg 876109 876112
  ; MImg 876129 876132
  ; MImg 876149 876152
  ; MImg 876179 876180
  ; MImg 876185 876188
  ; MImg 876204 876208
  ; MImg 876209 876216
  ; MImg 876248 876272
  ; MImg 876280 876344
  ; MImg 881128 884344
  ; MImg 884347 884348
  ; MImg 884368 884376
  ; MImg 884381 884384
  ; MImg 884385 884388
  ; MImg 884392 886328
  ; MImg 886340 889624
  ; MImg 889628 889632
  ; MImg 889640 889656
  ; MImg 889657 889660
  ; MImg 889664 889776
  ; MImg 889792 890496
  ; MImg 890504 890560
  ; MImg 890572 890576
  ; MImg 890605 890664
  ; MImg 890665 890672
  ; MImg 890673 890680
  ; MImg 890704 890712
  ; MImg 890796 890800
  ; MImg 890940 1419400
  ; MImg 1419424 1419425
  ; MImg 1419426 1474768
  ; MImg 1474780 1474784
  ; MImg 1474792 1474816
  ; MImg 1478911 1478912
  ; MImg 1483007 1483104
  ; MImg 1483108 1483112
  ; MImg 1483400 1483600
  ; MImg 1483608 1483640
  ; MImg 1483648 1483664
  ; MImg 1483688 1483720
  ; MImg 1483721 1483992
  ; MImg 1483993 1746184
  ; MImg 6006044 6006048
  ; MImg 6006052 6006056
  ; MImg 6006064 6269440
  ; MImg 6269441 6269444
  ; MImg 6269463 6269464
  ; MImg 6269468 6269472
  ; MImg 6269484 6269888
  ; MImg 6269896 6269952
  ; MImg 6269964 6269968
  ; MImg 6270030 6270056
  ; MImg 6270057 6270064
  ; MImg 6270068 6270072
  ; MImg 6270074 6270080
  ; MImg 6270090 6666024
  ; MImg 6665968 6665984
  ; MImg 6666068 6666072
  ; MImg 6666076 6666082
  ; MImg 6666083 6666144
  ; MImg 6666160 6666184
  ; MImg 6666192 6666216
  ; MImg 6666248 6666264
  ; MImg 6666280 6797328
  ; MImg 6797376 6797392
  ; MImg 6797396 6797400
  ; MImg 6797408 6797416
  ; MImg 6797424 6797672
  ; MImg 6797680 6797944
  ; MImg 6797961 6797968
  ; MImg 6798016 6798064
  ; MImg 6798072 6798088
  ; MImg 6798104 6798112
  ; MImg 6798168 6798184
  ; MImg 6798192 6798288
  ; MImg 6798296 6798320
  ; MImg 6798328 6798352
  ; MImg 6798360 6798568
  ; MImg 6798576 6798672
  ; MImg 6798680 6798704
  ; MImg 6798712 6798736
  ; MImg 6798744 6799000
  ; MImg 6799001 6799008
  ; MImg 6799016 6801232
  ; MImg 6801240 6801248
  ; MImg 6801256 6802272
  ; MImg 6802276 6802280
  ; MImg 6802284 6802336
  ; MImg 6802344 6807552
  ; MImg 859448 859456
  ; MImg 859460 872320
  ; MImg 65536 859432
  ; MWr (ZLit 2147459072) 842752
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
  ; MZero (ZLit 2147469952) 89706
  ; MFill (ZLit 2147559658) 256 249
  ; MZero (ZLit 2147559914) 715694
  ; MFill (ZLit 2148275608) 8192 249
  ; MZero (ZLit 2148283800) 18024
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904)) 8 (ZLit 870224)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19912)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920)) 8 (ZLit 870288)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19928)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936)) 8 (ZLit 870352)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19944)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952)) 8 (ZLit 870416)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19960)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968)) 8 (ZLit 870480)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19976)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984)) 8 (ZLit 870544)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19992)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000)) 8 (ZLit 870608)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20008)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016)) 8 (ZLit 870672)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20024)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032)) 8 (ZLit 870736)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20040)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048)) 8 (ZLit 870800)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20056)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064)) 8 (ZLit 870864)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20072)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080)) 8 (ZLit 870928)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20088)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096)) 8 (ZLit 870992)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20104)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20112)) 8 (ZLit 871056)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20120)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20128)) 8 (ZLit 871120)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20136)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20112))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20144)) 8 (ZLit 871184)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20152)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20128))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20160)) 8 (ZLit 871248)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20168)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20144))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20176)) 8 (ZLit 871312)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20184)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20160))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20192)) 8 (ZLit 871376)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20200)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20176))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20208)) 8 (ZLit 871440)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20216)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20192))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20224)) 8 (ZLit 871504)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20232)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20208))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20240)) 8 (ZLit 871568)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20248)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20224))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20256)) 8 (ZLit 871632)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20264)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20240))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20272)) 8 (ZLit 871696)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20280)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20256))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20288)) 8 (ZLit 871760)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20296)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20272))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20304)) 8 (ZLit 871824)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20312)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20288))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20320)) 8 (ZLit 871888)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20328)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20304))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20336)) 8 (ZLit 871952)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20344)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20320))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20352)) 8 (ZLit 872016)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20360)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20336))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20368)) 8 (ZLit 872080)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20376)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20352))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20384)) 8 (ZLit 872144)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20392)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20368))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20400)) 8 (ZLit 872208)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6668080)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6668300)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 64)) 8 (ZLit 6666240)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 72)) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3169)) 927
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 228)) 65536
  ; MCell (ZMul (ZLit 4096) (ZV 228)) 8 (ZLit 838288)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6666232)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 8)) 8 (ZLit 304076)
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MWr (ZMul (ZLit 4096) (ZV 471)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 471)) 8 (ZLit 12297829379609722881)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 8)) 8 (ZLit 870224)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 16)) 8 (ZLit 872208)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 24)) 4072
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 471)) (ZLit 2147450880)) 512
].

Definition asan_pure_facts_r30 : list pfact := [
  PVar 0 4294901760 4294967295
  ; PVar 1 1 1024
  ; PVar 2 0 256
  ; PVar 3 0 131071
  ; PVar 4 0 280000
  ; PVar 5 1630 525918
  ; PVar 6 0 255
  ; PVar 7 0 131071
  ; PVar 8 0 4294967294
  ; PVar 9 0 4194303
  ; PVar 10 0 7
  ; PVar 44 1 4194303
  ; PVar 78 1630 34359736304
  ; PVar 207 1630 34359735410
  ; PVar 208 4295491576 34326181871
  ; PVar 209 0 15
  ; PVar 226 1630 34359734272
  ; PVar 227 1 34359736319
  ; PVar 228 1630 34359736304
  ; PVar 245 1 34359736319
  ; PVar 310 1 34359736319
  ; PVar 311 1 34359736319
  ; PVar 344 0 1
  ; PVar 344 0 1
  ; PVar 377 1630 34359733495
  ; PVar 394 1630 524277
  ; PVar 394 1630 524277
  ; PVar 395 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 397 1 34359736319
  ; PVar 452 6676480 2154164224
  ; PVar 453 1630 34359736064
  ; PVar 454 1630 34359734272
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
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) 465920 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZLit 2147450880)) 17179877888 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 226)) (ZLit 2147450880)) 1048576 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 394)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 395)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 396)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 397)) (ZLit 2147450880)) 512 (ZLit 2147459072) 826368
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 826368
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
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6610944
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
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 65536) 6610944
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6610944
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZLit 65536) 6610944
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
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZLit 65536) 6610944
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

(* #1390: asan_pure_facts_r30 with each item just727 refuses on the #1390 hand-off states moved to the value those states hold (pl3_mf_cure_1390_g1.py); the r30 lemmas keep asan_pure_facts_r30 *)
Definition asan_pure_facts_r30_1390 : list pfact := [
  PVar 0 4294901760 4294967295
  ; PVar 1 1 1024
  ; PVar 2 0 256
  ; PVar 3 0 131071
  ; PVar 4 0 280000
  ; PVar 5 1662 525950
  ; PVar 6 0 255
  ; PVar 7 0 131071
  ; PVar 8 0 4294967294
  ; PVar 9 0 4194303
  ; PVar 10 0 7
  ; PVar 44 1 4194303
  ; PVar 78 1662 34359736304
  ; PVar 207 1662 34359735410
  ; PVar 208 4295491576 34326181871
  ; PVar 209 0 15
  ; PVar 226 1662 34359734272
  ; PVar 227 1 34359736319
  ; PVar 228 1662 34359736304
  ; PVar 245 1 34359736319
  ; PVar 310 1 34359736319
  ; PVar 311 1 34359736319
  ; PVar 344 0 1
  ; PVar 344 0 1
  ; PVar 377 1662 34359733495
  ; PVar 394 1662 524277
  ; PVar 394 1662 524277
  ; PVar 395 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 397 1 34359736319
  ; PVar 452 6807552 2154295296
  ; PVar 453 1662 34359736064
  ; PVar 454 1662 34359734272
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
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) 465920 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZLit 2147450880)) 17179877888 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 226)) (ZLit 2147450880)) 1048576 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 394)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 395)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 396)) (ZLit 2147450880)) 512 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 397)) (ZLit 2147450880)) 512 (ZLit 2147459072) 842752
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 842752
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
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6742016
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
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 65536) 6742016
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6742016
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZLit 65536) 6742016
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
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZLit 65536) 6742016
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

Definition asan_mem_facts_w1 : list mfact := [
  MCell (ZLit 1746184) 8 (ZLit 3)
  ; MCell (ZLit 1746208) 4 (ZLit 3)
  ; MCell (ZLit 5889652) 4 (ZLit 1)
  ; MImg 1746216 5889652
  ; MImg 5889656 6006040
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 9868317396083641943)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 2)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8 (ZLit 309020)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 24)) 8388584
].

(* #1390: asan_mem_facts_w1 as it stood before the #1390 move, for the r30 lemmas *)
Definition asan_mem_facts_w1_r30 : list mfact := [
  MCell (ZLit 1746120) 8 (ZLit 3)
  ; MCell (ZLit 1746144) 4 (ZLit 3)
  ; MCell (ZLit 3961004) 4 (ZLit 1)
  ; MImg 1746152 3961004
  ; MImg 3961008 6005976
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 7810276467364344565)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 2)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8 (ZLit 308940)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 24)) 8388584
].

Definition asan_mem_facts_w2 : list mfact := [
  MCell (ZLit 1746184) 8 (ZLit 2)
  ; MCell (ZLit 1746208) 4 (ZLit 2)
  ; MCell (ZLit 2468332) 4 (ZLit 1)
  ; MImg 1746216 2468332
  ; MImg 2468336 6006040
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 4917725556788855093)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 1)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8388592
].

(* #1390: asan_mem_facts_w2 as it stood before the #1390 move, for the r30 lemmas *)
Definition asan_mem_facts_w2_r30 : list mfact := [
  MCell (ZLit 1746120) 8 (ZLit 2)
  ; MCell (ZLit 1746144) 4 (ZLit 2)
  ; MCell (ZLit 4058652) 4 (ZLit 1)
  ; MImg 1746152 4058652
  ; MImg 4058656 6005976
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 15308442630245356113)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 1)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8388592
].

Definition asan_pure_facts_w1 : list pfact := [
  PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4030
].

Definition asan_pure_facts_w2 : list pfact := [
  PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 4031 4095
].

Definition asan_vis_app : list (zexp * zexp) := [
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
  ; (ZLit 65536, ZLit 6742016)
  ; (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)), ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
].

(* #1390: asan_vis_app as it stood before the #1390 move, for the r30 lemmas *)
Definition asan_vis_app_r30 : list (zexp * zexp) := [
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
  ; (ZLit 65536, ZLit 6610944)
  ; (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)), ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
].
Definition asan_ghost : list (zexp * zexp) := [
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
Definition asan_vis : list (zexp * zexp) := asan_vis_app ++ asan_ghost.

Definition asan_ledger : list lentry := [
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

Definition asan_totsz_r30 : Z := 17729664970752.
Definition asan_ylo_r30 : Z := 23387528589312.
Definition asan_eager : Z := 16515072.
Definition asan_abytes_r30 : Z := 2461202944.   (* #1390: the r30 value, for the r30 lemmas *)
Definition asan_abytes : Z := 2461350400.   (* #1390: the #1390 states' a_abytes (was 2461202944) *)

Definition asan_mem_hints_w1 : list N := [3; 2; 499; 498; 497; 494; 487; 493; 508; 486; 473; 476; 475; 474; 323; 324; 472; 471; 470; 469; 468; 464; 466; 465; 467; 618; 584; 583; 617; 612; 599; 611; 610; 609; 608; 616; 615; 614; 613; 606; 546; 607; 605; 604; 598; 603; 602; 601; 600; 619; 1; 6; 5; 126; 155; 0; 518; 532; 517; 519; 521; 520; 545; 544; 515; 513; 516; 535; 462; 463; 230; 670; 542; 630; 543; 489; 488; 231; 238; 237; 236; 235; 233; 232; 234; 419; 425; 418; 380; 392; 390; 422; 421; 420; 417; 416; 415; 424; 414; 423; 439; 438; 437; 266; 436; 435; 354; 358; 357; 270; 362; 361; 360; 430; 429; 428; 427; 426; 434; 433; 432; 431; 620; 9; 533; 509; 668; 585; 629; 536; 538; 547; 548; 549; 550; 551; 552; 553; 554; 555; 556; 557; 558; 559; 560; 561; 562; 563; 564; 565; 566; 567; 568; 569; 570; 571; 572; 573; 574; 575; 576; 577; 578; 579; 580; 581; 582; 539; 325; 540; 541; 456; 320; 461; 183; 164; 163; 184; 208; 187; 207; 188; 593; 592; 591; 590; 597; 596; 595; 594; 589; 241; 248; 247; 246; 245; 243; 242; 244; 239; 240; 249; 588; 587; 586; 704; 699; 698; 694; 697; 693; 687; 680; 679; 678; 683; 685; 349; 514; 681; 682; 676; 688; 271; 326; 689; 690; 677; 851; 457; 460; 459; 458; 700; 686; 703; 696; 692; 691; 695; 701; 702; 261; 254; 258; 259; 250; 251; 252; 253; 257; 511; 512; 510; 350; 534; 669; 537; 850; 750; 751; 752; 753; 754; 755; 756; 757; 758; 759; 760; 761; 762; 763; 764; 765; 766; 767; 768; 769; 770; 771; 772; 773; 774; 775; 776; 777; 778; 779; 780; 781; 782; 783; 784; 785; 786; 787; 788; 789; 790; 791; 792; 793; 794; 795; 796; 797; 798; 799; 800; 803; 804; 805; 806; 807; 808; 809; 810; 811; 812; 813; 814; 815; 816; 817; 818; 819; 820; 821; 822; 823; 824; 825; 826; 827; 828; 829; 830; 831; 832; 833; 834; 835; 836; 837; 838; 839; 840; 841; 842; 843; 844; 845; 846; 847; 848; 849; 748; 749; 747; 633; 634; 128; 129; 635; 123; 124; 636; 119; 120; 637; 115; 116; 638; 111; 112; 639; 107; 108; 640; 103; 104; 641; 99; 100; 642; 95; 96; 643; 91; 92; 644; 87; 88; 645; 83; 84; 646; 79; 80; 647; 75; 76; 648; 71; 72; 649; 67; 68; 650; 63; 64; 651; 59; 60; 652; 55; 56; 653; 51; 52; 660; 28; 661; 25; 654; 48; 655; 45; 656; 41; 42; 657; 37; 38; 658; 34; 659; 31; 662; 21; 22; 663; 17; 18; 664; 13; 14; 665; 4; 666; 10; 667; 722; 705; 671; 672; 673; 674; 675; 723; 724; 725; 726; 727; 728; 729; 730; 731; 732; 733; 734; 735; 736; 737; 738; 739; 740; 741; 742; 743; 744; 745; 631; 632; 624; 135; 134; 133; 127; 125; 122; 121; 118; 117; 114; 113; 110; 109; 106; 105; 102; 101; 98; 97; 94; 93; 90; 89; 86; 85; 82; 81; 78; 77; 74; 73; 70; 69; 66; 65; 62; 61; 58; 57; 54; 53; 50; 49; 47; 46; 44; 43; 40; 39; 36; 35; 33; 32; 30; 29; 27; 26; 24; 23; 20; 19; 16; 15; 12; 11; 8; 7; 623; 525; 526; 524; 491; 492; 490; 443; 351; 295; 294; 348; 347; 346; 444; 297; 296; 293; 272; 445; 209; 446; 442; 397; 381; 385; 398; 356; 384; 399; 269; 355; 386; 400; 268; 353; 401; 267; 389; 388; 402; 387; 383; 382; 403; 352; 404; 395; 391; 396; 367; 359; 368; 365; 366; 331; 332; 322; 321; 333; 329; 330; 278; 279; 273; 280; 276; 277; 191; 192; 157; 158; 193; 189; 190; 167; 160; 165; 166; 137; 130; 131; 132; 138; 136; 185; 159; 156; 801; 802; 186; 162; 161; 168]%N.
Lemma asan_mem_facts_justified_w1 :
  forallb (mjustify (s_know (a_ss HS_asan2_1)) (var_ranges (s_know (a_ss HS_asan2_1))) 65536 6676480) (asan_mem_facts_r30 ++ asan_mem_facts_w1_r30) = true.
Proof. apply (mjust_hints_sound _ _ _ _ _ asan_mem_hints_w1). vm_cast_no_check (@eq_refl bool true). Qed.
Definition asan_pure_hints_w1 : list N := [706; 714; 715; 716; 720; 721; 707; 717; 718; 719; 708; 684; 626; 528; 503; 495; 480; 448; 406; 370; 335; 308; 211; 211; 282; 217; 217; 216; 215; 215; 214; 213; 195; 170; 140; 212; 212; 496; 709; 710; 711; 712; 713; 300; 299; 523; 501; 478; 301; 441; 302; 394; 303; 364; 304; 328; 306; 275; 222; 226; 228; 224; 298; 622; 527; 529; 530; 506; 484; 454; 412; 378; 344; 318; 291; 205; 181; 153; 502; 504; 505; 483; 453; 411; 377; 343; 317; 290; 204; 180; 152; 479; 481; 482; 452; 410; 376; 342; 316; 289; 203; 179; 151; 447; 449; 450; 451; 409; 375; 341; 315; 288; 202; 178; 150; 405; 407; 408; 374; 340; 314; 287; 201; 177; 149; 369; 371; 372; 373; 339; 313; 286; 200; 176; 148; 334; 336; 337; 338; 312; 285; 199; 175; 147; 307; 309; 310; 311; 281; 283; 284; 198; 174; 146; 221; 220; 220; 219; 219; 218; 194; 196; 197; 173; 145; 169; 171; 172; 144; 139; 141; 142; 143; 625; 627; 628; 531; 507; 485; 455; 413; 379; 345; 319; 292; 206; 182; 154; 522; 500; 477; 440; 393; 363; 327; 305; 274; 223; 227; 229; 225; 621; 210]%N.
Lemma asan_pure_facts_justified_w1 :
  forallb (pjustify (s_know (a_ss HS_asan2_1)) (var_ranges (s_know (a_ss HS_asan2_1)))) (asan_pure_facts_r30 ++ asan_pure_facts_w1) = true.
Proof. apply (pjust_hints_sound _ _ _ asan_pure_hints_w1). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_vis_justified_w1 :
  vis_match (var_ranges (s_know (a_ss HS_asan2_1))) (a_vis HS_asan2_1) asan_vis_app_r30 = true /\ vis_match (var_ranges (s_know (a_ss HS_asan2_1))) (a_ghost HS_asan2_1) asan_ghost = true.
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_ledger_justified_w1 :
  ledger_xmatch (var_ranges (s_know (a_ss HS_asan2_1))) (a_maps HS_asan2_1) asan_ledger = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_consts_w1 : a_totsz HS_asan2_1 = asan_totsz_r30 /\ a_ylo HS_asan2_1 = asan_ylo_r30 /\ a_eager HS_asan2_1 = asan_eager /\ a_abytes HS_asan2_1 = asan_abytes_r30.
Proof. repeat split; reflexivity. Qed.
Definition asan_mem_hints_w2 : list N := [3; 2; 498; 497; 496; 493; 486; 492; 507; 485; 472; 475; 474; 473; 322; 323; 471; 470; 469; 468; 467; 463; 465; 464; 466; 617; 583; 582; 616; 611; 598; 610; 609; 608; 607; 615; 614; 613; 612; 605; 545; 606; 604; 603; 597; 602; 601; 600; 599; 618; 1; 6; 5; 126; 155; 0; 517; 531; 516; 518; 520; 519; 544; 543; 514; 512; 515; 534; 461; 462; 229; 669; 541; 629; 542; 488; 487; 230; 237; 236; 235; 234; 232; 231; 233; 418; 424; 417; 379; 391; 389; 421; 420; 419; 416; 415; 414; 423; 413; 422; 438; 437; 436; 265; 435; 434; 353; 357; 356; 269; 361; 360; 359; 429; 428; 427; 426; 425; 433; 432; 431; 430; 619; 9; 532; 508; 667; 584; 628; 535; 537; 546; 547; 548; 549; 550; 551; 552; 553; 554; 555; 556; 557; 558; 559; 560; 561; 562; 563; 564; 565; 566; 567; 568; 569; 570; 571; 572; 573; 574; 575; 576; 577; 578; 579; 580; 581; 538; 324; 539; 540; 455; 319; 460; 182; 163; 162; 183; 207; 186; 206; 187; 592; 591; 590; 589; 596; 595; 594; 593; 588; 240; 247; 246; 245; 244; 242; 241; 243; 238; 239; 248; 587; 586; 585; 703; 698; 697; 693; 696; 692; 686; 679; 678; 677; 682; 684; 348; 513; 680; 681; 675; 687; 270; 325; 688; 689; 676; 850; 456; 459; 458; 457; 699; 685; 702; 695; 691; 690; 694; 700; 701; 260; 253; 257; 258; 249; 250; 251; 252; 256; 510; 511; 509; 349; 533; 668; 536; 849; 749; 750; 751; 752; 753; 754; 755; 756; 757; 758; 759; 760; 761; 762; 763; 764; 765; 766; 767; 768; 769; 770; 771; 772; 773; 774; 775; 776; 777; 778; 779; 780; 781; 782; 783; 784; 785; 786; 787; 788; 789; 790; 791; 792; 793; 794; 795; 796; 797; 798; 799; 802; 803; 804; 805; 806; 807; 808; 809; 810; 811; 812; 813; 814; 815; 816; 817; 818; 819; 820; 821; 822; 823; 824; 825; 826; 827; 828; 829; 830; 831; 832; 833; 834; 835; 836; 837; 838; 839; 840; 841; 842; 843; 844; 845; 846; 847; 848; 747; 748; 746; 632; 633; 128; 129; 634; 123; 124; 635; 119; 120; 636; 115; 116; 637; 111; 112; 638; 107; 108; 639; 103; 104; 640; 99; 100; 641; 95; 96; 642; 91; 92; 643; 87; 88; 644; 83; 84; 645; 79; 80; 646; 75; 76; 647; 71; 72; 648; 67; 68; 649; 63; 64; 650; 59; 60; 651; 55; 56; 652; 51; 52; 659; 28; 660; 25; 653; 48; 654; 45; 655; 41; 42; 656; 37; 38; 657; 34; 658; 31; 661; 21; 22; 662; 17; 18; 663; 13; 14; 664; 4; 665; 10; 666; 721; 704; 670; 671; 672; 673; 674; 722; 723; 724; 725; 726; 727; 728; 729; 730; 731; 732; 733; 734; 735; 736; 737; 738; 739; 740; 741; 742; 743; 744; 630; 631; 623; 135; 134; 133; 127; 125; 122; 121; 118; 117; 114; 113; 110; 109; 106; 105; 102; 101; 98; 97; 94; 93; 90; 89; 86; 85; 82; 81; 78; 77; 74; 73; 70; 69; 66; 65; 62; 61; 58; 57; 54; 53; 50; 49; 47; 46; 44; 43; 40; 39; 36; 35; 33; 32; 30; 29; 27; 26; 24; 23; 20; 19; 16; 15; 12; 11; 8; 7; 622; 524; 525; 523; 490; 491; 489; 442; 350; 294; 293; 347; 346; 345; 443; 296; 295; 292; 271; 444; 208; 445; 441; 396; 380; 384; 397; 355; 383; 398; 268; 354; 385; 399; 267; 352; 400; 266; 388; 387; 401; 386; 382; 381; 402; 351; 403; 394; 390; 395; 366; 358; 367; 364; 365; 330; 331; 321; 320; 332; 328; 329; 277; 278; 272; 279; 275; 276; 190; 191; 157; 158; 192; 188; 189; 166; 160; 164; 165; 137; 130; 131; 132; 138; 136; 184; 159; 156; 800; 801; 185; 161; 167]%N.
Lemma asan_mem_facts_justified_w2 :
  forallb (mjustify (s_know (a_ss HS_asan2_2)) (var_ranges (s_know (a_ss HS_asan2_2))) 65536 6676480) (asan_mem_facts_r30 ++ asan_mem_facts_w2_r30) = true.
Proof. apply (mjust_hints_sound _ _ _ _ _ asan_mem_hints_w2). vm_cast_no_check (@eq_refl bool true). Qed.
Definition asan_pure_hints_w2 : list N := [705; 713; 714; 715; 719; 720; 706; 716; 717; 718; 707; 683; 625; 527; 502; 494; 479; 447; 405; 369; 334; 307; 210; 210; 281; 216; 216; 215; 214; 214; 213; 212; 194; 169; 140; 211; 211; 495; 708; 709; 710; 711; 712; 299; 298; 522; 500; 477; 300; 440; 301; 393; 302; 363; 303; 327; 305; 274; 221; 225; 227; 223; 297; 621; 526; 528; 529; 505; 483; 453; 411; 377; 343; 317; 290; 204; 180; 153; 501; 503; 504; 482; 452; 410; 376; 342; 316; 289; 203; 179; 152; 478; 480; 481; 451; 409; 375; 341; 315; 288; 202; 178; 151; 446; 448; 449; 450; 408; 374; 340; 314; 287; 201; 177; 150; 404; 406; 407; 373; 339; 313; 286; 200; 176; 149; 368; 370; 371; 372; 338; 312; 285; 199; 175; 148; 333; 335; 336; 337; 311; 284; 198; 174; 147; 306; 308; 309; 310; 280; 282; 283; 197; 173; 146; 220; 219; 219; 218; 218; 217; 193; 195; 196; 172; 145; 168; 170; 171; 144; 139; 141; 142; 143; 624; 626; 627; 530; 506; 484; 454; 412; 378; 344; 318; 291; 205; 181; 154; 521; 499; 476; 439; 392; 362; 326; 304; 273; 222; 226; 228; 224; 620; 209]%N.
Lemma asan_pure_facts_justified_w2 :
  forallb (pjustify (s_know (a_ss HS_asan2_2)) (var_ranges (s_know (a_ss HS_asan2_2)))) (asan_pure_facts_r30 ++ asan_pure_facts_w2) = true.
Proof. apply (pjust_hints_sound _ _ _ asan_pure_hints_w2). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_vis_justified_w2 :
  vis_match (var_ranges (s_know (a_ss HS_asan2_2))) (a_vis HS_asan2_2) asan_vis_app_r30 = true /\ vis_match (var_ranges (s_know (a_ss HS_asan2_2))) (a_ghost HS_asan2_2) asan_ghost = true.
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_ledger_justified_w2 :
  ledger_xmatch (var_ranges (s_know (a_ss HS_asan2_2))) (a_maps HS_asan2_2) asan_ledger = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_consts_w2 : a_totsz HS_asan2_2 = asan_totsz_r30 /\ a_ylo HS_asan2_2 = asan_ylo_r30 /\ a_eager HS_asan2_2 = asan_eager /\ a_abytes HS_asan2_2 = asan_abytes_r30.
Proof. repeat split; reflexivity. Qed.

(* ===================================================================================================== *)
(* The main-entry exports at .
   - The start-up plans move every variable >= 15 by 4 (AsanRenum.rv 15 4). The lists keep the r30q2 numbering
     and are justified against the states AFTER the rename (rz / rmf / rpf / rvis / rle below).
   - 27 r30q2 facts describe the argument area of the r30q2 stack (a 10-pair auxv, argv at +184, 8 MB of stack below sp);
     they cannot hold at . 24 are unused by every reader and are left out; the stack fact is replaced by the
     one (6144513 bytes below sp); the argv[0] / argv[1] pointer facts move to asan_argv_facts, by rseq. *)
(* ===================================================================================================== *)

Definition drop_ix {T : Type} (ixs : list nat) (l : list T) : list T :=
  map snd (filter (fun p => negb (existsb (Nat.eqb (fst p)) ixs)) (combine (seq 0 (length l)) l)).

Definition usp_z : zexp := ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))).
(* the stack known writable below sp at (stack_max_size less the largest argument block) *)
Definition ASTK : Z := 6144513.
Definition asan_stack_fact : mfact := MWr (ZAdd usp_z (ZLit (- ASTK))) ASTK.

Definition asan_mem_facts : list mfact := asan_stack_fact :: drop_ix (324 :: 233 :: 453 :: seq 461 22)%nat asan_mem_facts_r30_1390.
(* row 27 (): row 27's r30 facts that fail at , read by vm_compute on its four states
   (probe MF27Diag): 233 (the GOT cell holding argv), 453 (the r30 8 MB stack), 461 / 462 (argv[0] / argv[1]'s
   pointers) and 463-482 (the 10 r30 auxv pairs); rows 1-3's PORTED drops 233 :: 397 :: seq 405 22 (the carry's literal map had moved that 22 to 23). *)
(* the list is stored COMPUTED (Eval vm_compute), not as the drop_ix expression: a kernel
   conversion between plist727 w and its unfolding otherwise evaluates drop_ix's unary-nat filter lazily and took over
   an hour at MainEntry's Qed (bisection: probes/p8, PJ434d slow vs PK434s 0.3 s). Same list, same elements. *)
Definition asan_pure_facts : list pfact := Eval vm_compute in drop_ix [4; 38; 39]%nat asan_pure_facts_r30_1390.
Lemma asan_pure_facts_drop : asan_pure_facts = drop_ix [4; 38; 39]%nat asan_pure_facts_r30_1390.
Proof. vm_compute. reflexivity. Qed.

(* argv[0] / argv[1] at ; the auxv holds 27 + 2 r pairs (r = the kernel build's rseq bit) *)
Definition argv0_z (r : Z) : zexp :=
  ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 4)
    (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 8) (ZV 11)))))))) (ZLit (472 + 32 * r)).   (* row 27: 472 + 32 r, read off row 27's 727 states at usp + 8 (probe MF27Diag3); the same 472 as rows 1-3's PORTED (the carry's literal map had moved it to 578) *)
Definition argv1_z (r : Z) : zexp :=
  ZMul (ZLtu (ZLit 1) (ZV 1))
    (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 3) (ZAdd (ZV 4)
      (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 8) (ZV 11))))))))) (ZLit (473 + 32 * r))).   (* row 27: 473 + 32 r at usp + 16 (MF27Diag3); the same 473 as rows 1-3's PORTED (the carry's literal map had moved it to 579) *)
Definition asan_argv_facts (r : Z) : list mfact :=
  [MRo (ZAdd usp_z (ZLit 8)) 8 (argv0_z r); MRo (ZAdd usp_z (ZLit 16)) 8 (argv1_z r)].

Definition asan_totsz : Z := 17729665183744.   (* #1390: the #1390 states' a_totsz (: 17729665052672) *)
Definition asan_ylo : Z := 23387528507392.     (* r30q2 - 81920 *)

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
  asan_mem_facts ++ (if w then asan_mem_facts_w1 else asan_mem_facts_w2) ++ asan_argv_facts r.
Definition plist727 (w : bool) : list pfact :=
  asan_pure_facts ++ (if w then asan_pure_facts_w1 else asan_pure_facts_w2).
Definition hs727 (w : bool) (r : Z) : acs := if w then rsel r HS2_1_r0 HS2_1_r1 else rsel r HS2_2_r0 HS2_2_r1.
Definition just727 (w : bool) (r : Z) : bool :=
  let hs := hs727 w r in
  let kn := s_know (a_ss hs) in
  let vr := var_ranges kn in
  forallb (mjustify kn vr 65536 6807552) (map rmf (mlist727 w r))
  && forallb (pjustify kn vr) (map rpf (plist727 w))
  && vis_match vr (a_vis hs) (rvis asan_vis_app) && vis_match vr (a_ghost hs) (rvis asan_ghost)
  && ledger_xmatch vr (a_maps hs) (map rle asan_ledger)
  && Z.eqb (a_totsz hs) asan_totsz && Z.eqb (a_ylo hs) asan_ylo
  && Z.eqb (a_eager hs) asan_eager && Z.eqb (a_abytes hs) asan_abytes.

Lemma just727_ok : forall w r, r = 0 \/ r = 1 -> just727 w r = true.
Proof. intros [|] r [-> | ->]; vm_cast_no_check (@eq_refl bool true). Qed.
