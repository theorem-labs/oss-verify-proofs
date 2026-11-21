(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* AS/MainFactsBoth at = AS/MainFactsAsan port ( -> ) carried by hand onto Both (the carry tool refused one conflict) *)
(* the r30q2 lists kept as *_r30; the lists (Both's drop positions found by content), the rename and their justification appended at the end *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.AS Require Import AxSymExec3 AsanPlan MainExport MainHint StartupHS2Both.
(* the hand-off states and the plans' variable rename *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.AS Require Import StartupHSBoth727 AsanRenum.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.AS Require Import MainFactsBothR30Lists.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* port727: the r30q2 list, kept under this name; both_mem_facts () is defined from it below *)
Definition both_mem_facts_r30 : list mfact := [
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
  ; MCell (ZLit 666496) 8 (ZLit 636736)
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
  ; MCell (ZLit 666712) 8 (ZLit 383456)
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
  ; MCell (ZLit 1195352) 8 (ZLit 367316)
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
  ; MCell (ZLit 1259536) 8 (ZLit 347080)
  ; MCell (ZLit 1259576) 8 (ZLit 1)
  ; MCell (ZLit 1259600) 8 (ZLit 367176)
  ; MCell (ZLit 1259608) 8 (ZLit 366944)
  ; MCell (ZLit 1259616) 8 (ZLit 457308)
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
  ; MCell (ZLit 6045888) 8 (ZLit 646416)
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
  ; MCell (ZLit 6245032) 8 (ZLit 623424)
  ; MCell (ZLit 6245040) 8 (ZLit 0)
  ; MCell (ZLit 6245048) 8 (ZLit 24)
  ; MCell (ZLit 6245056) 8 (ZLit 8)
  ; MCell (ZLit 6245064) 8 (ZLit 0)
  ; MCell (ZLit 6113736) 8 (ZLit 6113736)
  ; MCell (ZLit 6113744) 8 (ZLit 6113736)
  ; MCell (ZLit 6113752) 8 (ZLit 6113736)
  ; MCell (ZLit 6113760) 8 (ZLit 0)
  ; MCell (ZLit 6113768) 4 (ZV 44)
  ; MCell (ZLit 6113776) 4 (ZLit 2)
  ; MCell (ZLit 6113786) 1 (ZLit 1)
  ; MCell (ZLit 6113848) 8 (ZLit 6250040)
  ; MCell (ZLit 6113856) 8 (ZLit 6113856)
  ; MCell (ZLit 6113888) 8 (ZLit 6245720)
  ; MCell (ZLit 6113920) 8 (ZV 45)
  ; MCell (ZLit 6113928) 8 (ZLit 6113968)
  ; MCell (ZLit 6113936) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MCell (ZLit 6113944) 8 (ZMul (ZLit 4096) (ZV 310))
  ; MCell (ZLit 6113968) 8 (ZLit 1)
  ; MCell (ZLit 6113976) 8 (ZLit 6115984)
  ; MRo (ZLit 6245072) 8 (ZV 45)
  ; MWr (ZLit 6245080) 9512
  ; MCell (ZLit 6245096) 4 (ZLit 1)
  ; MCell (ZLit 6245104) 8 (ZLit 6245112)
  ; MCell (ZLit 6245120) 8 (ZLit 562080)
  ; MCell (ZLit 6245376) 8 (ZLit 457308)
  ; MCell (ZLit 6245656) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))
  ; MCell (ZLit 6245664) 1 (ZLit 1)
  ; MCell (ZLit 6245672) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24))
  ; MCell (ZLit 6245680) 8 (ZLit 6245024)
  ; MCell (ZLit 6245688) 8 (ZLit 248)
  ; MCell (ZLit 6245696) 8 (ZLit 8)
  ; MCell (ZLit 6245704) 8 (ZLit 1)
  ; MCell (ZLit 6245712) 8 (ZLit 4096)
  ; MCell (ZLit 6245768) 8 (ZV 9)
  ; MCell (ZLit 6245800) 4 (ZLit 1)
  ; MCell (ZLit 6245804) 4 (ZLit 1)
  ; MCell (ZLit 6245824) 8 (ZLit 97)
  ; MCell (ZLit 6245832) 8 (ZLit 0)
  ; MCell (ZLit 6246272) 8 (ZLit 10)
  ; MCell (ZLit 6246376) 8 (ZLit 2)
  ; MCell (ZLit 6246408) 8 (ZLit 2)
  ; MCell (ZLit 6246440) 8 (ZLit 2)
  ; MCell (ZLit 6246704) 1 (ZLit 1)
  ; MCell (ZLit 6248952) 8 (ZLit 346564)
  ; MCell (ZLit 6249976) 4 (ZLit 0)
  ; MCell (ZLit 6249984) 4 (ZLit 0)
  ; MCell (ZLit 6250040) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MCell (ZLit 636792) 8 (ZLit 8)
  ; MCell (ZLit 636800) 8 (ZLit 131571)
  ; MCell (ZLit 636816) 4 (ZLit 2)
  ; MWr (ZLit 626688) 5618384
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
  ; MImg 6113772 6113776
  ; MImg 6113780 6113786
  ; MImg 6113787 6113848
  ; MImg 6113864 6113888
  ; MImg 6113896 6113920
  ; MImg 6113952 6113968
  ; MImg 6113984 6245032
  ; MImg 6245080 6245096
  ; MImg 6245100 6245104
  ; MImg 6245112 6245120
  ; MImg 6245128 6245376
  ; MImg 6245384 6245648
  ; MImg 6245665 6245672
  ; MImg 6245720 6245768
  ; MImg 6245776 6245792
  ; MImg 6245808 6245816
  ; MImg 6245872 6245888
  ; MImg 6245896 6245992
  ; MImg 6246000 6246024
  ; MImg 6246032 6246056
  ; MImg 6246064 6246272
  ; MImg 6246280 6246376
  ; MImg 6246384 6246408
  ; MImg 6246416 6246440
  ; MImg 6246448 6246704
  ; MImg 6246705 6246712
  ; MImg 6246720 6248936
  ; MImg 6248944 6248952
  ; MImg 6248960 6249976
  ; MImg 6249980 6249984
  ; MImg 6249988 6250040
  ; MImg 6250048 6254592
  ; MImg 636808 636816
  ; MImg 636820 648256
  ; MImg 65536 636792
  ; MWr (ZLit 2147459072) 773632
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
  ; MZero (ZLit 2147468592) 63232
  ; MFill (ZLit 2147531824) 88 249
  ; MZero (ZLit 2147531912) 700792
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904)) 8 (ZLit 647552)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19912)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920)) 8 (ZLit 647616)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19928)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936)) 8 (ZLit 647680)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19944)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952)) 8 (ZLit 647744)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19960)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968)) 8 (ZLit 647808)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19976)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984)) 8 (ZLit 647872)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19992)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000)) 8 (ZLit 647936)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20008)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016)) 8 (ZLit 648000)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20024)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032)) 8 (ZLit 648064)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20040)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048)) 8 (ZLit 648128)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20056)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064)) 8 (ZLit 648192)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6115784)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6116004)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 64)) 8 (ZLit 6113944)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 72)) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3169)) 927
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 228)) 65536
  ; MCell (ZMul (ZLit 4096) (ZV 228)) 8 (ZLit 627712)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6113936)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 8)) 8 (ZLit 258780)
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MWr (ZMul (ZLit 4096) (ZV 471)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 471)) 8 (ZLit 12297829379609722881)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 8)) 8 (ZLit 647552)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 16)) 8 (ZLit 648192)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 24)) 4072
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 471)) (ZLit 2147450880)) 512
].

Definition both_pure_facts_r30 : list pfact := [
  PVar 0 4294901760 4294967295
  ; PVar 1 1 1024
  ; PVar 2 0 256
  ; PVar 3 0 131071
  ; PVar 4 0 280000
  ; PVar 5 1527 525815
  ; PVar 6 0 255
  ; PVar 7 0 131071
  ; PVar 8 0 4294967294
  ; PVar 9 0 4194303
  ; PVar 10 0 7
  ; PVar 44 1 4194303
  ; PVar 78 1527 34359736304
  ; PVar 207 1527 34359735410
  ; PVar 208 4295491576 34326181871
  ; PVar 209 0 15
  ; PVar 226 1527 34359734272
  ; PVar 227 1 34359736319
  ; PVar 228 1527 34359736304
  ; PVar 245 1 34359736319
  ; PVar 310 1 34359736319
  ; PVar 311 1 34359736319
  ; PVar 344 0 1
  ; PVar 344 0 1
  ; PVar 377 1527 34359733495
  ; PVar 394 1527 524277
  ; PVar 394 1527 524277
  ; PVar 395 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 396 1 34359736319
  ; PVar 397 1 34359736319
  ; PVar 452 6254592 2153746432
  ; PVar 453 1527 34359736064
  ; PVar 454 1527 34359734272
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
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 207)) (ZLit 2147450880)) 465920 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 208)) (ZLit 2147450880)) 17179877888 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 226)) (ZLit 2147450880)) 1048576 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 228)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 245)) (ZLit 2147450880)) 512 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 310)) (ZLit 2147450880)) 512 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 377)) (ZLit 2147450880)) 1446400 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 394)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 395)) (ZLit 2147450880)) 1024 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 396)) (ZLit 2147450880)) 512 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 397)) (ZLit 2147450880)) 512 (ZLit 2147459072) 773632
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZAdd (ZMul (ZLit 512) (ZV 311)) (ZLit 2147450880)) 512
  ; PDisj (ZAdd (ZMul (ZLit 512) (ZV 78)) (ZLit 2147450880)) 8192 (ZLit 2147459072) 773632
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
  ; PDisj (ZMul (ZLit 4096) (ZV 227)) 4096 (ZLit 65536) 6189056
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
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 65536) 6189056
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 310)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 245)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 65536) 6189056
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZLit 2147446784) 17592186048512
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 311)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 377)) 11571200
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 453)) 1048576
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 454)) 8388608
  ; PDisj (ZMul (ZLit 4096) (ZV 310)) 4096 (ZMul (ZLit 4096) (ZV 471)) 4096
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-8388608))) 12582912
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZMul (ZLit 4096) (ZV 10))) (ZLit (-8388608))) 140737496743936
  ; PDisj (ZMul (ZLit 4096) (ZV 311)) 4096 (ZLit 65536) 6189056
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
  ; PDisj (ZMul (ZLit 4096) (ZV 471)) 4096 (ZLit 65536) 6189056
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
  MCell (ZLit 1522120) 8 (ZLit 3)
  ; MCell (ZLit 1522144) 4 (ZLit 3)
  ; MCell (ZLit 2624268) 4 (ZLit 1)
  ; MImg 1522152 2624268
  ; MImg 2624272 5781976
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 7109469326694151245)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 2)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8 (ZLit 263724)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 24)) 8388584
].

Definition both_mem_facts_w2 : list mfact := [
  MCell (ZLit 1522120) 8 (ZLit 2)
  ; MCell (ZLit 1522144) 4 (ZLit 2)
  ; MCell (ZLit 3772992) 4 (ZLit 1)
  ; MImg 1522152 3772992
  ; MImg 3772996 5781976
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 6996210148568487450)
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
  ; (ZLit 65536, ZLit 6189056)
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

Definition both_totsz_r30 : Z := 17729664417792.
Definition both_ylo_r30 : Z := 23387528589312.
Definition both_eager : Z := 16515072.
Definition both_abytes : Z := 2460728320.

Definition both_mem_hints_w1 : list N := [3; 2; 419; 418; 417; 414; 407; 413; 428; 406; 393; 396; 395; 394; 243; 244; 392; 391; 390; 389; 388; 384; 386; 385; 387; 538; 504; 503; 537; 532; 519; 531; 530; 529; 528; 536; 535; 534; 533; 526; 466; 527; 525; 524; 518; 523; 522; 521; 520; 539; 1; 6; 5; 46; 75; 0; 438; 452; 437; 439; 441; 440; 465; 464; 435; 433; 436; 455; 382; 383; 150; 569; 462; 550; 463; 409; 408; 151; 158; 157; 156; 155; 153; 152; 154; 339; 345; 338; 300; 312; 310; 342; 341; 340; 337; 336; 335; 344; 334; 343; 359; 358; 357; 186; 356; 355; 274; 278; 277; 190; 282; 281; 280; 350; 349; 348; 347; 346; 354; 353; 352; 351; 540; 9; 453; 429; 567; 505; 549; 456; 458; 467; 468; 469; 470; 471; 472; 473; 474; 475; 476; 477; 478; 479; 480; 481; 482; 483; 484; 485; 486; 487; 488; 489; 490; 491; 492; 493; 494; 495; 496; 497; 498; 499; 500; 501; 502; 459; 245; 460; 461; 376; 240; 381; 103; 84; 83; 104; 128; 107; 127; 108; 513; 512; 511; 510; 517; 516; 515; 514; 509; 161; 168; 167; 166; 165; 163; 162; 164; 159; 160; 169; 508; 507; 506; 603; 598; 597; 593; 596; 592; 586; 579; 578; 577; 582; 584; 269; 434; 580; 581; 575; 587; 191; 246; 588; 589; 576; 750; 377; 380; 379; 378; 599; 585; 602; 595; 591; 590; 594; 600; 601; 181; 174; 178; 179; 170; 171; 172; 173; 177; 431; 432; 430; 270; 454; 568; 457; 749; 649; 650; 651; 652; 653; 654; 655; 656; 657; 658; 659; 660; 661; 662; 663; 664; 665; 666; 667; 668; 669; 670; 671; 672; 673; 674; 675; 676; 677; 678; 679; 680; 681; 682; 683; 684; 685; 686; 687; 688; 689; 690; 691; 692; 693; 694; 695; 696; 697; 698; 699; 702; 703; 704; 705; 706; 707; 708; 709; 710; 711; 712; 713; 714; 715; 716; 717; 718; 719; 720; 721; 722; 723; 724; 725; 726; 727; 728; 729; 730; 731; 732; 733; 734; 735; 736; 737; 738; 739; 740; 741; 742; 743; 744; 745; 746; 747; 748; 647; 648; 646; 553; 554; 48; 49; 555; 43; 44; 556; 39; 40; 557; 35; 36; 558; 31; 32; 559; 27; 28; 560; 23; 24; 561; 19; 20; 562; 16; 563; 13; 564; 10; 565; 4; 566; 621; 604; 570; 571; 572; 573; 574; 622; 623; 624; 625; 626; 627; 628; 629; 630; 631; 632; 633; 634; 635; 636; 637; 638; 639; 640; 641; 642; 643; 644; 551; 552; 544; 55; 54; 53; 47; 45; 42; 41; 38; 37; 34; 33; 30; 29; 26; 25; 22; 21; 18; 17; 15; 14; 12; 11; 8; 7; 543; 445; 446; 444; 411; 412; 410; 363; 271; 215; 214; 268; 267; 266; 364; 217; 216; 213; 192; 365; 129; 366; 362; 317; 301; 305; 318; 276; 304; 319; 189; 275; 306; 320; 188; 273; 321; 187; 309; 308; 322; 307; 303; 302; 323; 272; 324; 315; 311; 316; 287; 279; 288; 285; 286; 251; 252; 242; 241; 253; 249; 250; 198; 199; 193; 200; 196; 197; 111; 112; 77; 78; 113; 109; 110; 87; 80; 85; 86; 57; 50; 51; 52; 58; 56; 105; 79; 76; 700; 701; 106; 82; 81; 88]%N.
Lemma both_mem_facts_justified_w1 :
  forallb (mjustify (s_know (a_ss HS_both2_1)) (var_ranges (s_know (a_ss HS_both2_1))) 65536 6123520) (both_mem_facts_r30_g30 ++ both_mem_facts_w1_g30) = true.
Proof. apply (mjust_hints_sound _ _ _ _ _ both_mem_hints_w1). vm_cast_no_check (@eq_refl bool true). Qed.
Definition both_pure_hints_w1 : list N := [605; 613; 614; 615; 619; 620; 606; 616; 617; 618; 607; 583; 546; 448; 423; 415; 400; 368; 326; 290; 255; 228; 131; 131; 202; 137; 137; 136; 135; 135; 134; 133; 115; 90; 60; 132; 132; 416; 608; 609; 610; 611; 612; 220; 219; 443; 421; 398; 221; 361; 222; 314; 223; 284; 224; 248; 226; 195; 142; 146; 148; 144; 218; 542; 447; 449; 450; 426; 404; 374; 332; 298; 264; 238; 211; 125; 101; 73; 422; 424; 425; 403; 373; 331; 297; 263; 237; 210; 124; 100; 72; 399; 401; 402; 372; 330; 296; 262; 236; 209; 123; 99; 71; 367; 369; 370; 371; 329; 295; 261; 235; 208; 122; 98; 70; 325; 327; 328; 294; 260; 234; 207; 121; 97; 69; 289; 291; 292; 293; 259; 233; 206; 120; 96; 68; 254; 256; 257; 258; 232; 205; 119; 95; 67; 227; 229; 230; 231; 201; 203; 204; 118; 94; 66; 141; 140; 140; 139; 139; 138; 114; 116; 117; 93; 65; 89; 91; 92; 64; 59; 61; 62; 63; 545; 547; 548; 451; 427; 405; 375; 333; 299; 265; 239; 212; 126; 102; 74; 442; 420; 397; 360; 313; 283; 247; 225; 194; 143; 147; 149; 145; 541; 130]%N.
Lemma both_pure_facts_justified_w1 :
  forallb (pjustify (s_know (a_ss HS_both2_1)) (var_ranges (s_know (a_ss HS_both2_1)))) (both_pure_facts_r30_g30 ++ both_pure_facts_w1_g30) = true.
Proof. apply (pjust_hints_sound _ _ _ both_pure_hints_w1). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_vis_justified_w1 :
  vis_match (var_ranges (s_know (a_ss HS_both2_1))) (a_vis HS_both2_1) both_vis_app_g30 = true /\ vis_match (var_ranges (s_know (a_ss HS_both2_1))) (a_ghost HS_both2_1) both_ghost_g30 = true.
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_ledger_justified_w1 :
  ledger_xmatch (var_ranges (s_know (a_ss HS_both2_1))) (a_maps HS_both2_1) both_ledger_g30 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_consts_w1 : a_totsz HS_both2_1 = both_totsz_r30_g30 /\ a_ylo HS_both2_1 = both_ylo_r30_g30 /\ a_eager HS_both2_1 = both_eager_g30 /\ a_abytes HS_both2_1 = both_abytes_g30.
Proof. repeat split; reflexivity. Qed.
Definition both_mem_hints_w2 : list N := [3; 2; 418; 417; 416; 413; 406; 412; 427; 405; 392; 395; 394; 393; 242; 243; 391; 390; 389; 388; 387; 383; 385; 384; 386; 537; 503; 502; 536; 531; 518; 530; 529; 528; 527; 535; 534; 533; 532; 525; 465; 526; 524; 523; 517; 522; 521; 520; 519; 538; 1; 6; 5; 46; 75; 0; 437; 451; 436; 438; 440; 439; 464; 463; 434; 432; 435; 454; 381; 382; 149; 568; 461; 549; 462; 408; 407; 150; 157; 156; 155; 154; 152; 151; 153; 338; 344; 337; 299; 311; 309; 341; 340; 339; 336; 335; 334; 343; 333; 342; 358; 357; 356; 185; 355; 354; 273; 277; 276; 189; 281; 280; 279; 349; 348; 347; 346; 345; 353; 352; 351; 350; 539; 9; 452; 428; 566; 504; 548; 455; 457; 466; 467; 468; 469; 470; 471; 472; 473; 474; 475; 476; 477; 478; 479; 480; 481; 482; 483; 484; 485; 486; 487; 488; 489; 490; 491; 492; 493; 494; 495; 496; 497; 498; 499; 500; 501; 458; 244; 459; 460; 375; 239; 380; 102; 83; 82; 103; 127; 106; 126; 107; 512; 511; 510; 509; 516; 515; 514; 513; 508; 160; 167; 166; 165; 164; 162; 161; 163; 158; 159; 168; 507; 506; 505; 602; 597; 596; 592; 595; 591; 585; 578; 577; 576; 581; 583; 268; 433; 579; 580; 574; 586; 190; 245; 587; 588; 575; 749; 376; 379; 378; 377; 598; 584; 601; 594; 590; 589; 593; 599; 600; 180; 173; 177; 178; 169; 170; 171; 172; 176; 430; 431; 429; 269; 453; 567; 456; 748; 648; 649; 650; 651; 652; 653; 654; 655; 656; 657; 658; 659; 660; 661; 662; 663; 664; 665; 666; 667; 668; 669; 670; 671; 672; 673; 674; 675; 676; 677; 678; 679; 680; 681; 682; 683; 684; 685; 686; 687; 688; 689; 690; 691; 692; 693; 694; 695; 696; 697; 698; 701; 702; 703; 704; 705; 706; 707; 708; 709; 710; 711; 712; 713; 714; 715; 716; 717; 718; 719; 720; 721; 722; 723; 724; 725; 726; 727; 728; 729; 730; 731; 732; 733; 734; 735; 736; 737; 738; 739; 740; 741; 742; 743; 744; 745; 746; 747; 646; 647; 645; 552; 553; 48; 49; 554; 43; 44; 555; 39; 40; 556; 35; 36; 557; 31; 32; 558; 27; 28; 559; 23; 24; 560; 19; 20; 561; 16; 562; 13; 563; 10; 564; 4; 565; 620; 603; 569; 570; 571; 572; 573; 621; 622; 623; 624; 625; 626; 627; 628; 629; 630; 631; 632; 633; 634; 635; 636; 637; 638; 639; 640; 641; 642; 643; 550; 551; 543; 55; 54; 53; 47; 45; 42; 41; 38; 37; 34; 33; 30; 29; 26; 25; 22; 21; 18; 17; 15; 14; 12; 11; 8; 7; 542; 444; 445; 443; 410; 411; 409; 362; 270; 214; 213; 267; 266; 265; 363; 216; 215; 212; 191; 364; 128; 365; 361; 316; 300; 304; 317; 275; 303; 318; 188; 274; 305; 319; 187; 272; 320; 186; 308; 307; 321; 306; 302; 301; 322; 271; 323; 314; 310; 315; 286; 278; 287; 284; 285; 250; 251; 241; 240; 252; 248; 249; 197; 198; 192; 199; 195; 196; 110; 111; 77; 78; 112; 108; 109; 86; 80; 84; 85; 57; 50; 51; 52; 58; 56; 104; 79; 76; 699; 700; 105; 81; 87]%N.
Lemma both_mem_facts_justified_w2 :
  forallb (mjustify (s_know (a_ss HS_both2_2)) (var_ranges (s_know (a_ss HS_both2_2))) 65536 6123520) (both_mem_facts_r30_g30 ++ both_mem_facts_w2_g30) = true.
Proof. apply (mjust_hints_sound _ _ _ _ _ both_mem_hints_w2). vm_cast_no_check (@eq_refl bool true). Qed.
Definition both_pure_hints_w2 : list N := [604; 612; 613; 614; 618; 619; 605; 615; 616; 617; 606; 582; 545; 447; 422; 414; 399; 367; 325; 289; 254; 227; 130; 130; 201; 136; 136; 135; 134; 134; 133; 132; 114; 89; 60; 131; 131; 415; 607; 608; 609; 610; 611; 219; 218; 442; 420; 397; 220; 360; 221; 313; 222; 283; 223; 247; 225; 194; 141; 145; 147; 143; 217; 541; 446; 448; 449; 425; 403; 373; 331; 297; 263; 237; 210; 124; 100; 73; 421; 423; 424; 402; 372; 330; 296; 262; 236; 209; 123; 99; 72; 398; 400; 401; 371; 329; 295; 261; 235; 208; 122; 98; 71; 366; 368; 369; 370; 328; 294; 260; 234; 207; 121; 97; 70; 324; 326; 327; 293; 259; 233; 206; 120; 96; 69; 288; 290; 291; 292; 258; 232; 205; 119; 95; 68; 253; 255; 256; 257; 231; 204; 118; 94; 67; 226; 228; 229; 230; 200; 202; 203; 117; 93; 66; 140; 139; 139; 138; 138; 137; 113; 115; 116; 92; 65; 88; 90; 91; 64; 59; 61; 62; 63; 544; 546; 547; 450; 426; 404; 374; 332; 298; 264; 238; 211; 125; 101; 74; 441; 419; 396; 359; 312; 282; 246; 224; 193; 142; 146; 148; 144; 540; 129]%N.
Lemma both_pure_facts_justified_w2 :
  forallb (pjustify (s_know (a_ss HS_both2_2)) (var_ranges (s_know (a_ss HS_both2_2)))) (both_pure_facts_r30_g30 ++ both_pure_facts_w2_g30) = true.
Proof. apply (pjust_hints_sound _ _ _ both_pure_hints_w2). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_vis_justified_w2 :
  vis_match (var_ranges (s_know (a_ss HS_both2_2))) (a_vis HS_both2_2) both_vis_app_g30 = true /\ vis_match (var_ranges (s_know (a_ss HS_both2_2))) (a_ghost HS_both2_2) both_ghost_g30 = true.
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_ledger_justified_w2 :
  ledger_xmatch (var_ranges (s_know (a_ss HS_both2_2))) (a_maps HS_both2_2) both_ledger_g30 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_consts_w2 : a_totsz HS_both2_2 = both_totsz_r30_g30 /\ a_ylo HS_both2_2 = both_ylo_r30_g30 /\ a_eager HS_both2_2 = both_eager_g30 /\ a_abytes HS_both2_2 = both_abytes_g30.
Proof. repeat split; reflexivity. Qed.

(* (Both): this block is its asan names renamed to both; the memory drop list at Both's positions by content (ASan 233 :: 397 :: seq 405 22 = Both 233 :: 394 :: seq 402 22); the pure drop list is the same; both_totsz / both_ylo: Both's r30q2 values equal ASan's, so +/- 81920 gives the same values *)
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

Definition both_mem_facts : list mfact := both_stack_fact :: drop_ix (233 :: 393 :: seq 401 22)%nat both_mem_facts_r30.
(* the list is stored COMPUTED (Eval vm_compute), not as the drop_ix expression: a kernel
   conversion between plist727 w and its unfolding otherwise evaluates drop_ix's unary-nat filter lazily and took over
   an hour at MainEntry's Qed (bisection: probes/p8, PJ434d slow vs PK434s 0.3 s). Same list, same elements. *)
Definition both_pure_facts : list pfact := Eval vm_compute in drop_ix [4; 38; 39]%nat both_pure_facts_r30.
Lemma both_pure_facts_drop : both_pure_facts = drop_ix [4; 38; 39]%nat both_pure_facts_r30.
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

Definition both_totsz : Z := 17729664630784.   (* r30q2 + 81920: the vDSO pair's 20-page reservation bound *)
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
  forallb (mjustify kn vr 65536 6254592) (map rmf (mlist727 w r))
  && forallb (pjustify kn vr) (map rpf (plist727 w))
  && vis_match vr (a_vis hs) (rvis both_vis_app) && vis_match vr (a_ghost hs) (rvis both_ghost)
  && ledger_xmatch vr (a_maps hs) (map rle both_ledger)
  && Z.eqb (a_totsz hs) both_totsz && Z.eqb (a_ylo hs) both_ylo
  && Z.eqb (a_eager hs) both_eager && Z.eqb (a_abytes hs) both_abytes.

Lemma just727_ok : forall w r, r = 0 \/ r = 1 -> just727 w r = true.
Proof. intros [|] r [-> | ->]; vm_cast_no_check (@eq_refl bool true). Qed.
