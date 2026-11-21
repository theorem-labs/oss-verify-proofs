(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* s7: the lists and constants of AS/MainFactsBoth.v AS GRADED, under names with the suffix _g30: read only by that text's 10 lemmas against the earlier-form states; made by a tool from the graded bytes; no number of this text is ever relocated *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import AxSymExec3 AsanPlan MainExport MainHint StartupHS2Both.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.AS Require Import StartupHSBoth727 AsanRenum.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

Definition both_mem_facts_r30_g30 : list mfact := [
  MCell (ZLit 648256) 8 (ZLit 1)
  ; MCell (ZLit 648264) 1 (ZLit 1)
  ; MCell (ZLit 648344) 8 (ZMul (ZLit 4096) (ZV 208))
  ; MCell (ZLit 648352) 8 (ZLit 137439023104)
  ; MCell (ZLit 648360) 8 (ZLit 92843)
  ; MCell (ZLit 648376) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))
  ; MCell (ZLit 648384) 4 (ZLit 18446744073709551615)
  ; MCell (ZLit 648392) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))
  ; MCell (ZLit 648400) 1 (ZLit 0)
  ; MCell (ZLit 648408) 8 (ZLit 4096)
  ; MCell (ZLit 648416) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 648424) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 648432) 8 (ZLit 8388608)
  ; MCell (ZLit 648440) 8 (ZLit 102847)
  ; MCell (ZLit 649024) 1 (ZLit 0)
  ; MZeroC (ZLit 649025) 3
  ; MCell (ZLit 649136) 8 (ZLit 268435456)
  ; MCell (ZLit 649144) 8 (ZLit 241591905)
  ; MCell (ZLit 649152) 8 (ZLit 1048576)
  ; MCell (ZLit 649224) 1 (ZLit 0)
  ; MCell (ZLit 649225) 1 (ZLit 0)
  ; MCell (ZLit 651960) 8 (ZLit 1099511627776)
  ; MCell (ZLit 651968) 2 (ZLit 16)
  ; MCell (ZLit 651970) 2 (ZLit 2048)
  ; MCell (ZLit 651972) 1 (ZLit 1)
  ; MCell (ZLit 652024) 4 (ZLit 4294967295)
  ; MCell (ZLit 652028) 4 (ZLit 256)
  ; MCell (ZLit 652032) 4 (ZLit 1024)
  ; MCell (ZLit 652036) 4 (ZLit 16)
  ; MCell (ZLit 652040) 4 (ZLit 2048)
  ; MCell (ZLit 652044) 1 (ZLit 0)
  ; MCell (ZLit 652048) 8 (ZLit 72340168526266369)
  ; MCell (ZLit 652056) 8 (ZLit 85899345936)
  ; MCell (ZLit 652064) 1 (ZLit 0)
  ; MCell (ZLit 652068) 4 (ZLit 4096)
  ; MCell (ZLit 652072) 8 (ZLit 816043786240)
  ; MCell (ZLit 652080) 4 (ZLit 85)
  ; MCell (ZLit 652084) 1 (ZLit 1)
  ; MCell (ZLit 652088) 8 (ZLit 0)
  ; MRo (ZLit 652096) 6 (ZLit 4294967296)
  ; MCell (ZLit 652102) 1 (ZLit 1)
  ; MCell (ZLit 652103) 1 (ZLit 0)
  ; MCell (ZLit 652104) 8 (ZLit 72340172838010881)
  ; MCell (ZLit 652112) 2 (ZLit 1)
  ; MCell (ZLit 652114) 1 (ZLit 0)
  ; MCell (ZLit 652116) 4 (ZLit 0)
  ; MCell (ZLit 652120) 1 (ZLit 1)
  ; MCell (ZLit 652124) 4 (ZLit 2)
  ; MCell (ZLit 652128) 8 (ZLit 81510)
  ; MCell (ZLit 652136) 4 (ZLit 65793)
  ; MCell (ZLit 652144) 1 (ZLit 1)
  ; MCell (ZLit 652152) 8 (ZLit 11)
  ; MCell (ZLit 652160) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064))
  ; MCell (ZLit 652168) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZLit 652176) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19880))
  ; MCell (ZLit 652208) 8 (ZLit 0)
  ; MCell (ZLit 660280) 1 (ZLit 1)
  ; MCell (ZLit 660281) 1 (ZLit 1)
  ; MCell (ZLit 660282) 1 (ZLit 1)
  ; MCell (ZLit 660284) 4 (ZLit 299)
  ; MCell (ZLit 660288) 8 (ZLit 660296)
  ; MCell (ZLit 660296) 8 (ZMul (ZLit 4096) (ZV 207))
  ; MCell (ZLit 660312) 4 (ZLit 2)
  ; MCell (ZLit 660316) 1 (ZLit 1)
  ; MCell (ZLit 660320) 1 (ZLit 1)
  ; MCell (ZLit 660324) 4 (ZLit 0)
  ; MCell (ZLit 662264) 8 (ZLit 2147450880)
  ; MCell (ZLit 662272) 4 (ZLit 1)
  ; MCell (ZLit 665560) 1 (ZLit 1)
  ; MCell (ZLit 665561) 1 (ZLit 1)
  ; MCell (ZLit 665562) 1 (ZLit 0)
  ; MCell (ZLit 665563) 1 (ZLit 0)
  ; MCell (ZLit 665568) 8 (ZLit 140737488355327)
  ; MCell (ZLit 665592) 1 (ZLit 1)
  ; MCell (ZLit 665596) 4 (ZLit 30)
  ; MCell (ZLit 665712) 8 (ZLit 1)
  ; MCell (ZLit 665720) 8 (ZLit 4096)
  ; MCell (ZLit 666432) 8 (ZLit 666496)
  ; MCell (ZLit 666496) 8 (ZLit 636680)
  ; MCell (ZLit 666504) 4 (ZLit 5)
  ; MCell (ZLit 666512) 8 (ZLit 0)
  ; MCell (ZLit 666520) 8 (ZLit 0)
  ; MCell (ZLit 666528) 8 (ZLit 0)
  ; MZeroC (ZLit 666536) 5
  ; MCell (ZLit 666600) 1 (ZLit 1)
  ; MCell (ZLit 666608) 1 (ZLit 1)
  ; MCell (ZLit 666616) 8 (ZLit 666712)
  ; MCell (ZLit 666624) 8 (ZLit 666664)
  ; MCell (ZLit 666632) 8 (ZLit 0)
  ; MCell (ZLit 666648) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 65536))
  ; MCell (ZLit 666656) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 160))
  ; MCell (ZLit 666664) 8 (ZLit 0)
  ; MCell (ZLit 666672) 4 (ZLit 0)
  ; MCell (ZLit 666676) 4 (ZLit 0)
  ; MCell (ZLit 666680) 8 (ZLit 0)
  ; MCell (ZLit 666688) 8 (ZLit 0)
  ; MCell (ZLit 666696) 4 (ZLit 0)
  ; MCell (ZLit 666700) 4 (ZLit 0)
  ; MCell (ZLit 666704) 4 (ZLit 0)
  ; MCell (ZLit 666708) 4 (ZLit 0)
  ; MCell (ZLit 666712) 8 (ZLit 383384)
  ; MCell (ZLit 666720) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 666728) 4 (ZLit 0)
  ; MCell (ZLit 666736) 8 (ZLit 0)
  ; MCell (ZLit 666744) 4 (ZLit 0)
  ; MCell (ZLit 666748) 4 (ZLit 0)
  ; MCell (ZLit 666752) 8 (ZLit 1)
  ; MCell (ZLit 666760) 8 (ZLit 1)
  ; MCell (ZLit 666768) 8 (ZLit 1)
  ; MCell (ZLit 666776) 8 (ZLit 1)
  ; MCell (ZLit 666784) 8 (ZMul (ZLit 4096) (ZV 245))
  ; MCell (ZLit 666792) 8 (ZLit 4096)
  ; MCell (ZLit 666800) 8 (ZLit 1)
  ; MCell (ZLit 666808) 8 (ZLit 0)
  ; MCell (ZLit 666816) 8 (ZLit 0)
  ; MCell (ZLit 666824) 8 (ZLit 0)
  ; MCell (ZLit 666832) 8 (ZLit 0)
  ; MCell (ZLit 666840) 8 (ZLit 0)
  ; MCell (ZLit 666848) 8 (ZLit 0)
  ; MCell (ZLit 666856) 8 (ZLit 0)
  ; MCell (ZLit 666864) 8 (ZLit 0)
  ; MCell (ZLit 666872) 4 (ZLit 0)
  ; MCell (ZLit 1195336) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 65536))
  ; MCell (ZLit 1195344) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080))
  ; MCell (ZLit 1195352) 8 (ZLit 367244)
  ; MCell (ZLit 1195361) 1 (ZLit 1)
  ; MCell (ZLit 1250704) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-160)))
  ; MCell (ZLit 1250712) 4 (ZLit 0)
  ; MCell (ZLit 1250720) 8 (ZLit 4096)
  ; MCell (ZLit 1259040) 1 (ZLit 0)
  ; MZeroC (ZLit 1259041) 3
  ; MCell (ZLit 1259048) 8 (ZLit 1)
  ; MCell (ZLit 1259056) 8 (ZLit 0)
  ; MCell (ZLit 1259064) 8 (ZLit 0)
  ; MCell (ZLit 1259072) 8 (ZLit 81510)
  ; MCell (ZLit 1259080) 8 (ZLit 128849084416)
  ; MCell (ZLit 1259088) 8 (ZLit 0)
  ; MCell (ZLit 1259096) 8 (ZLit 0)
  ; MCell (ZLit 1259104) 8 (ZLit 0)
  ; MCell (ZLit 1259112) 8 (ZLit 0)
  ; MCell (ZLit 1259120) 8 (ZLit 1103823372545)
  ; MCell (ZLit 1259128) 8 (ZLit 4294967296)
  ; MCell (ZLit 1259136) 8 (ZLit 0)
  ; MCell (ZLit 1259144) 8 (ZLit 0)
  ; MCell (ZLit 1259152) 8 (ZLit 0)
  ; MCell (ZLit 1259160) 8 (ZLit 65537)
  ; MCell (ZLit 1259168) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 1259176) 8 (ZLit 71687)
  ; MCell (ZLit 1259184) 8 (ZLit 256)
  ; MCell (ZLit 1259192) 8 (ZLit 0)
  ; MCell (ZLit 1259200) 8 (ZLit 0)
  ; MCell (ZLit 1259208) 8 (ZLit 0)
  ; MCell (ZLit 1259216) 8 (ZLit 0)
  ; MCell (ZLit 1259224) 8 (ZLit 18446744069414584320)
  ; MCell (ZLit 1259232) 8 (ZLit 1)
  ; MCell (ZLit 1259240) 8 (ZLit 82370)
  ; MCell (ZLit 1259248) 8 (ZLit 81510)
  ; MCell (ZLit 1259256) 8 (ZLit 81510)
  ; MCell (ZLit 1259264) 8 (ZLit 1103823372544)
  ; MCell (ZLit 1259272) 8 (ZLit 0)
  ; MCell (ZLit 1259280) 8 (ZLit 121192)
  ; MCell (ZLit 1259288) 8 (ZLit 72339073309605888)
  ; MCell (ZLit 1259296) 8 (ZLit 72340172838076673)
  ; MCell (ZLit 1259304) 8 (ZLit 16843009)
  ; MCell (ZLit 1259312) 8 (ZLit 1103806595073)
  ; MCell (ZLit 1259320) 8 (ZLit 101176)
  ; MCell (ZLit 1259328) 8 (ZLit 281474976710912)
  ; MCell (ZLit 1259536) 8 (ZLit 347008)
  ; MCell (ZLit 1259576) 8 (ZLit 1)
  ; MCell (ZLit 1259600) 8 (ZLit 367104)
  ; MCell (ZLit 1259608) 8 (ZLit 366872)
  ; MCell (ZLit 1259616) 8 (ZLit 457236)
  ; MCell (ZLit 1259656) 1 (ZLit 1)
  ; MCell (ZLit 1259928) 1 (ZLit 0)
  ; MCell (ZLit 1522128) 8 (ZLit 8388608)
  ; MCell (ZLit 1522136) 8 (ZMul (ZLit 4096) (ZV 454))
  ; MCell (ZLit 1522148) 1 (ZLit 0)
  ; MZeroC (ZLit 1522149) 3
  ; MCell (ZLit 5781976) 4 (ZLit 1)
  ; MCell (ZLit 5781984) 1 (ZLit 0)
  ; MZeroC (ZLit 5781985) 3
  ; MCell (ZLit 5781992) 8 (ZMul (ZLit 4096) (ZV 453))
  ; MCell (ZLit 6045376) 1 (ZLit 0)
  ; MCell (ZLit 6045380) 4 (ZLit 0)
  ; MCell (ZLit 6045384) 8 (ZLit 72340172821233664)
  ; MCell (ZLit 6045392) 4 (ZLit 257)
  ; MCell (ZLit 6045396) 2 (ZLit 0)
  ; MCell (ZLit 6045398) 1 (ZLit 0)
  ; MCell (ZLit 6045400) 4 (ZLit 1)
  ; MCell (ZLit 6045408) 8 (ZLit 81510)
  ; MCell (ZLit 6045416) 4 (ZLit 1)
  ; MCell (ZLit 6045824) 8 (ZLit 6045888)
  ; MCell (ZLit 6045888) 8 (ZLit 646360)
  ; MCell (ZLit 6045896) 4 (ZLit 38)
  ; MCell (ZLit 6045904) 8 (ZLit 0)
  ; MCell (ZLit 6045912) 8 (ZLit 0)
  ; MCell (ZLit 6045920) 8 (ZLit 0)
  ; MZeroC (ZLit 6045928) 38
  ; MCell (ZLit 6045992) 1 (ZLit 1)
  ; MCell (ZLit 6046000) 1 (ZLit 0)
  ; MCell (ZLit 6046001) 1 (ZLit 1)
  ; MCell (ZLit 6046002) 2 (ZLit 0)
  ; MCell (ZLit 6046008) 2 (ZLit 0)
  ; MCell (ZLit 6046016) 8 (ZLit 81510)
  ; MCell (ZLit 6046024) 2 (ZLit 0)
  ; MCell (ZLit 6113728) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))) (ZLit 16))
  ; MCell (ZLit 6113752) 8 (ZLit 623368)
  ; MCell (ZLit 6113760) 8 (ZLit 0)
  ; MCell (ZLit 6113768) 8 (ZLit 24)
  ; MCell (ZLit 6113776) 8 (ZLit 8)
  ; MCell (ZLit 6113784) 8 (ZLit 0)
  ; MCell (ZLit 6113792) 8 (ZLit 6113792)
  ; MCell (ZLit 6113800) 8 (ZLit 6113792)
  ; MCell (ZLit 6113808) 8 (ZLit 6113792)
  ; MCell (ZLit 6113816) 8 (ZLit 0)
  ; MCell (ZLit 6113824) 4 (ZV 44)
  ; MCell (ZLit 6113832) 4 (ZLit 2)
  ; MCell (ZLit 6113842) 1 (ZLit 1)
  ; MCell (ZLit 6113904) 8 (ZLit 6119096)
  ; MCell (ZLit 6113912) 8 (ZLit 6113912)
  ; MCell (ZLit 6113944) 8 (ZLit 6114776)
  ; MCell (ZLit 6113976) 8 (ZV 45)
  ; MCell (ZLit 6113984) 8 (ZLit 6114024)
  ; MCell (ZLit 6113992) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MCell (ZLit 6114000) 8 (ZMul (ZLit 4096) (ZV 310))
  ; MCell (ZLit 6114024) 8 (ZLit 1)
  ; MCell (ZLit 6114032) 8 (ZLit 6116040)
  ; MRo (ZLit 6114128) 8 (ZV 45)
  ; MWr (ZLit 6114136) 9384
  ; MCell (ZLit 6114152) 4 (ZLit 1)
  ; MCell (ZLit 6114160) 8 (ZLit 6114168)
  ; MCell (ZLit 6114176) 8 (ZLit 562020)
  ; MCell (ZLit 6114432) 8 (ZLit 457236)
  ; MCell (ZLit 6114712) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))
  ; MCell (ZLit 6114720) 1 (ZLit 1)
  ; MCell (ZLit 6114728) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24))
  ; MCell (ZLit 6114736) 8 (ZLit 6113744)
  ; MCell (ZLit 6114744) 8 (ZLit 248)
  ; MCell (ZLit 6114752) 8 (ZLit 8)
  ; MCell (ZLit 6114760) 8 (ZLit 1)
  ; MCell (ZLit 6114768) 8 (ZLit 4096)
  ; MCell (ZLit 6114824) 8 (ZV 9)
  ; MCell (ZLit 6114856) 4 (ZLit 1)
  ; MCell (ZLit 6114860) 4 (ZLit 1)
  ; MCell (ZLit 6114880) 8 (ZLit 97)
  ; MCell (ZLit 6114888) 8 (ZLit 0)
  ; MCell (ZLit 6115328) 8 (ZLit 10)
  ; MCell (ZLit 6115432) 8 (ZLit 2)
  ; MCell (ZLit 6115464) 8 (ZLit 2)
  ; MCell (ZLit 6115496) 8 (ZLit 2)
  ; MCell (ZLit 6115760) 1 (ZLit 1)
  ; MCell (ZLit 6118008) 8 (ZLit 346492)
  ; MCell (ZLit 6119032) 4 (ZLit 0)
  ; MCell (ZLit 6119040) 4 (ZLit 0)
  ; MCell (ZLit 6119096) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MCell (ZLit 636736) 8 (ZLit 8)
  ; MCell (ZLit 636744) 8 (ZLit 131571)
  ; MCell (ZLit 636760) 4 (ZLit 2)
  ; MWr (ZLit 626688) 5487440
  ; MImg 648265 648344
  ; MImg 648368 648376
  ; MImg 648388 648392
  ; MImg 648401 648408
  ; MImg 648448 649024
  ; MImg 649028 649136
  ; MImg 649160 649224
  ; MImg 649226 651960
  ; MImg 651973 652024
  ; MImg 652045 652048
  ; MImg 652065 652068
  ; MImg 652085 652088
  ; MImg 652115 652116
  ; MImg 652121 652124
  ; MImg 652140 652144
  ; MImg 652145 652152
  ; MImg 652184 652208
  ; MImg 652216 652280
  ; MImg 657064 660280
  ; MImg 660283 660284
  ; MImg 660304 660312
  ; MImg 660317 660320
  ; MImg 660321 660324
  ; MImg 660328 662264
  ; MImg 662276 665560
  ; MImg 665564 665568
  ; MImg 665576 665592
  ; MImg 665593 665596
  ; MImg 665600 665712
  ; MImg 665728 666432
  ; MImg 666440 666496
  ; MImg 666508 666512
  ; MImg 666541 666600
  ; MImg 666601 666608
  ; MImg 666609 666616
  ; MImg 666640 666648
  ; MImg 666732 666736
  ; MImg 666876 1195336
  ; MImg 1195360 1195361
  ; MImg 1195362 1250704
  ; MImg 1250716 1250720
  ; MImg 1250728 1250752
  ; MImg 1254847 1254848
  ; MImg 1258943 1259040
  ; MImg 1259044 1259048
  ; MImg 1259336 1259536
  ; MImg 1259544 1259576
  ; MImg 1259584 1259600
  ; MImg 1259624 1259656
  ; MImg 1259657 1259928
  ; MImg 1259929 1522120
  ; MImg 5781980 5781984
  ; MImg 5781988 5781992
  ; MImg 5782000 6045376
  ; MImg 6045377 6045380
  ; MImg 6045399 6045400
  ; MImg 6045404 6045408
  ; MImg 6045420 6045824
  ; MImg 6045832 6045888
  ; MImg 6045900 6045904
  ; MImg 6045966 6045992
  ; MImg 6045993 6046000
  ; MImg 6046004 6046008
  ; MImg 6046010 6046016
  ; MImg 6046026 6113728
  ; MImg 6113736 6113752
  ; MImg 6113828 6113832
  ; MImg 6113836 6113842
  ; MImg 6113843 6113904
  ; MImg 6113920 6113944
  ; MImg 6113952 6113976
  ; MImg 6114008 6114024
  ; MImg 6114040 6114128
  ; MImg 6114136 6114152
  ; MImg 6114156 6114160
  ; MImg 6114168 6114176
  ; MImg 6114184 6114432
  ; MImg 6114440 6114704
  ; MImg 6114721 6114728
  ; MImg 6114776 6114824
  ; MImg 6114832 6114848
  ; MImg 6114864 6114872
  ; MImg 6114928 6114944
  ; MImg 6114952 6115048
  ; MImg 6115056 6115080
  ; MImg 6115088 6115112
  ; MImg 6115120 6115328
  ; MImg 6115336 6115432
  ; MImg 6115440 6115464
  ; MImg 6115472 6115496
  ; MImg 6115504 6115760
  ; MImg 6115761 6115768
  ; MImg 6115776 6117992
  ; MImg 6118000 6118008
  ; MImg 6118016 6119032
  ; MImg 6119036 6119040
  ; MImg 6119044 6119096
  ; MImg 6119104 6123520
  ; MImg 636752 636760
  ; MImg 636764 648256
  ; MImg 65536 636736
  ; MWr (ZLit 2147459072) 757248
  ; MZero (ZLit 2147459072) 8613
  ; MCell (ZLit 2147467685) 1 (ZLit 5)
  ; MFill (ZLit 2147467686) 2 249
  ; MZeroC (ZLit 2147467688) 2
  ; MCell (ZLit 2147467690) 1 (ZLit 7)
  ; MFill (ZLit 2147467691) 5 249
  ; MZeroC (ZLit 2147467696) 1
  ; MCell (ZLit 2147467697) 1 (ZLit 5)
  ; MFill (ZLit 2147467698) 2 249
  ; MZeroC (ZLit 2147467700) 9
  ; MCell (ZLit 2147467709) 1 (ZLit 1)
  ; MFill (ZLit 2147467710) 6 249
  ; MZeroC (ZLit 2147467716) 8
  ; MCell (ZLit 2147467724) 1 (ZLit 5)
  ; MFill (ZLit 2147467725) 7 249
  ; MZeroC (ZLit 2147467732) 8
  ; MCell (ZLit 2147467740) 1 (ZLit 7)
  ; MFill (ZLit 2147467741) 7 249
  ; MZeroC (ZLit 2147467748) 2
  ; MCell (ZLit 2147467750) 1 (ZLit 1)
  ; MFill (ZLit 2147467751) 5 249
  ; MZeroC (ZLit 2147467756) 10
  ; MCell (ZLit 2147467766) 1 (ZLit 5)
  ; MFill (ZLit 2147467767) 5 249
  ; MZeroC (ZLit 2147467772) 128
  ; MFill (ZLit 2147467900) 32 249
  ; MZero (ZLit 2147467932) 512
  ; MFill (ZLit 2147468444) 128 249
  ; MZeroC (ZLit 2147468572) 16
  ; MFill (ZLit 2147468588) 4 249
  ; MZero (ZLit 2147468592) 63226
  ; MFill (ZLit 2147531818) 88 249
  ; MZero (ZLit 2147531906) 684414
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904)) 8 (ZLit 647504)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19912)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920)) 8 (ZLit 647568)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19928)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936)) 8 (ZLit 647632)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19944)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952)) 8 (ZLit 647696)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19960)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968)) 8 (ZLit 647760)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19976)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984)) 8 (ZLit 647824)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19992)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000)) 8 (ZLit 647888)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20008)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016)) 8 (ZLit 647952)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20024)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032)) 8 (ZLit 648016)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20040)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048)) 8 (ZLit 648080)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20056)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064)) 8 (ZLit 648144)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20072)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048))
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6115840)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6116060)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 64)) 8 (ZLit 6114000)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 72)) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3169)) 927
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 228)) 65536
  ; MCell (ZMul (ZLit 4096) (ZV 228)) 8 (ZLit 627656)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6113992)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 8)) 8 (ZLit 258708)
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MWr (ZMul (ZLit 4096) (ZV 471)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 471)) 8 (ZLit 12297829379609722881)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 8)) 8 (ZLit 647504)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 16)) 8 (ZLit 648144)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 24)) 4072
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 471)) (ZLit 2147450880)) 512
].

Definition both_pure_facts_r30_g30 : list pfact := [
  PVar 0 4294901760 4294967295
  ; PVar 1 1 1024
  ; PVar 2 0 256
  ; PVar 3 0 131071
  ; PVar 4 0 280000
  ; PVar 5 1495 525783
  ; PVar 6 0 255
  ; PVar 7 0 131071
  ; PVar 8 0 4294967294
  ; PVar 9 0 4194303
  ; PVar 10 0 7
  ; PVar 44 1 4194303
  ; PVar 78 1495 34359736304
  ; PVar 207 1495 34359735410
  ; PVar 208 4295491576 34326181871
  ; PVar 209 0 15
  ; PVar 226 1495 34359734272
  ; PVar 227 1 34359736319
  ; PVar 228 1495 34359736304
  ; PVar 245 1 34359736319
  ; PVar 310 1 34359736319
  ; PVar 311 1 34359736319
  ; PVar 344 0 1
  ; PVar 344 0 1
  ; PVar 377 1495 34359733495
  ; PVar 394 1495 524277
  ; PVar 394 1495 524277
  ; PVar 395 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 397 1 34359736319
  ; PVar 452 6123520 2153615360
  ; PVar 453 1495 34359736064
  ; PVar 454 1495 34359734272
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
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) 465920 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZLit 2147450880)) 17179877888 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 226)) (ZLit 2147450880)) 1048576 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 394)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 395)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 396)) (ZLit 2147450880)) 512 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 397)) (ZLit 2147450880)) 512 (ZLit 2147459072) 757248
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 757248
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
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6057984
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
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 65536) 6057984
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6057984
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZLit 65536) 6057984
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
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZLit 65536) 6057984
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

Definition both_mem_facts_w1_g30 : list mfact := [
  MCell (ZLit 1522120) 8 (ZLit 3)
  ; MCell (ZLit 1522144) 4 (ZLit 3)
  ; MCell (ZLit 3199784) 4 (ZLit 1)
  ; MImg 1522152 3199784
  ; MImg 3199788 5781976
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 10081486681788524116)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 2)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8 (ZLit 263652)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 24)) 8388584
].

Definition both_mem_facts_w2_g30 : list mfact := [
  MCell (ZLit 1522120) 8 (ZLit 2)
  ; MCell (ZLit 1522144) 4 (ZLit 2)
  ; MCell (ZLit 1815272) 4 (ZLit 1)
  ; MImg 1522152 1815272
  ; MImg 1815276 5781976
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 4041888335072910916)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 1)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8388592
].

Definition both_pure_facts_w1_g30 : list pfact := [
  PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 0 4030
].

Definition both_pure_facts_w2_g30 : list pfact := [
  PRange (ZAdd (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit (-4096)) (ZV 344))) (ZLit 3935)) 4031 4095
].

Definition both_vis_app_g30 : list (zexp * zexp) := [
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
  ; (ZLit 65536, ZLit 6057984)
  ; (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608)), ZAdd (ZAdd (ZMul (ZLit (-32768)) (ZV 0)) (ZMul (ZLit (-4096)) (ZV 10))) (ZLit 140737496743936))
].
Definition both_ghost_g30 : list (zexp * zexp) := [
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
Definition both_vis_g30 : list (zexp * zexp) := both_vis_app_g30 ++ both_ghost_g30.

Definition both_ledger_g30 : list lentry := [
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

Definition both_totsz_r30_g30 : Z := 17729664417792.
Definition both_ylo_r30_g30 : Z := 23387528589312.
Definition both_eager_g30 : Z := 16515072.
Definition both_abytes_g30 : Z := 2460580864.

