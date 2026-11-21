(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* AS/MainFactsAsan = our text + 's own edits to theories/Common/MainFactsAsan.v, 3-way merged (proposal md5 ); the old text is kept aside *)
(* AS/MainFactsAsan at : the r30q2 lists kept as *_r30; the lists, the rename and their justification appended at the end *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.AS Require Import AxSymExec3 AsanPlan MainExport MainHint StartupHS2Asan.
(* the hand-off states and the plans' variable rename *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.AS Require Import StartupHSAsan727 AsanRenum.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.AS Require Import MainFactsAsanR30Lists.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.

(* the r30q2 list, kept under this name; asan_mem_facts () is defined from it below *)
Definition asan_mem_facts_r30 : list mfact := [
  MCell (ZLit 648000) 8 (ZLit 1)
  ; MCell (ZLit 648008) 1 (ZLit 1)
  ; MCell (ZLit 648088) 8 (ZMul (ZLit 4096) (ZV 208))
  ; MCell (ZLit 648096) 8 (ZLit 137439023104)
  ; MCell (ZLit 648104) 8 (ZLit 92843)
  ; MCell (ZLit 648120) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))
  ; MCell (ZLit 648128) 4 (ZLit 18446744073709551615)
  ; MCell (ZLit 648136) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))
  ; MCell (ZLit 648144) 1 (ZLit 0)
  ; MCell (ZLit 648152) 8 (ZLit 4096)
  ; MCell (ZLit 648160) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 648168) 8 (ZMul (ZLit 4096) (ZV 226))
  ; MCell (ZLit 648176) 8 (ZLit 8388608)
  ; MCell (ZLit 648184) 8 (ZLit 102847)
  ; MCell (ZLit 648768) 1 (ZLit 0)
  ; MZeroC (ZLit 648769) 3
  ; MCell (ZLit 648880) 8 (ZLit 268435456)
  ; MCell (ZLit 648888) 8 (ZLit 241591905)
  ; MCell (ZLit 648896) 8 (ZLit 1048576)
  ; MCell (ZLit 648968) 1 (ZLit 0)
  ; MCell (ZLit 648969) 1 (ZLit 0)
  ; MCell (ZLit 651704) 8 (ZLit 1099511627776)
  ; MCell (ZLit 651712) 2 (ZLit 16)
  ; MCell (ZLit 651714) 2 (ZLit 2048)
  ; MCell (ZLit 651716) 1 (ZLit 1)
  ; MCell (ZLit 651768) 4 (ZLit 4294967295)
  ; MCell (ZLit 651772) 4 (ZLit 256)
  ; MCell (ZLit 651776) 4 (ZLit 1024)
  ; MCell (ZLit 651780) 4 (ZLit 16)
  ; MCell (ZLit 651784) 4 (ZLit 2048)
  ; MCell (ZLit 651788) 1 (ZLit 0)
  ; MCell (ZLit 651792) 8 (ZLit 72340168526266369)
  ; MCell (ZLit 651800) 8 (ZLit 85899345936)
  ; MCell (ZLit 651808) 1 (ZLit 0)
  ; MCell (ZLit 651812) 4 (ZLit 4096)
  ; MCell (ZLit 651816) 8 (ZLit 816043786240)
  ; MCell (ZLit 651824) 4 (ZLit 85)
  ; MCell (ZLit 651828) 1 (ZLit 1)
  ; MCell (ZLit 651832) 8 (ZLit 0)
  ; MRo (ZLit 651840) 6 (ZLit 4294967296)
  ; MCell (ZLit 651846) 1 (ZLit 1)
  ; MCell (ZLit 651847) 1 (ZLit 0)
  ; MCell (ZLit 651848) 8 (ZLit 72340172838010881)
  ; MCell (ZLit 651856) 2 (ZLit 1)
  ; MCell (ZLit 651858) 1 (ZLit 0)
  ; MCell (ZLit 651860) 4 (ZLit 0)
  ; MCell (ZLit 651864) 1 (ZLit 1)
  ; MCell (ZLit 651868) 4 (ZLit 2)
  ; MCell (ZLit 651872) 8 (ZLit 81510)
  ; MCell (ZLit 651880) 4 (ZLit 65793)
  ; MCell (ZLit 651888) 1 (ZLit 1)
  ; MCell (ZLit 651896) 8 (ZLit 12)
  ; MCell (ZLit 651904) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080))
  ; MCell (ZLit 651912) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZLit 651920) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19880))
  ; MCell (ZLit 651952) 8 (ZLit 0)
  ; MCell (ZLit 660024) 1 (ZLit 1)
  ; MCell (ZLit 660025) 1 (ZLit 1)
  ; MCell (ZLit 660026) 1 (ZLit 1)
  ; MCell (ZLit 660028) 4 (ZLit 299)
  ; MCell (ZLit 660032) 8 (ZLit 660040)
  ; MCell (ZLit 660040) 8 (ZMul (ZLit 4096) (ZV 207))
  ; MCell (ZLit 660056) 4 (ZLit 2)
  ; MCell (ZLit 660060) 1 (ZLit 1)
  ; MCell (ZLit 660064) 1 (ZLit 1)
  ; MCell (ZLit 660068) 4 (ZLit 0)
  ; MCell (ZLit 662008) 8 (ZLit 2147450880)
  ; MCell (ZLit 662016) 4 (ZLit 1)
  ; MCell (ZLit 665304) 1 (ZLit 1)
  ; MCell (ZLit 665305) 1 (ZLit 1)
  ; MCell (ZLit 665306) 1 (ZLit 0)
  ; MCell (ZLit 665307) 1 (ZLit 0)
  ; MCell (ZLit 665312) 8 (ZLit 140737488355327)
  ; MCell (ZLit 665336) 1 (ZLit 1)
  ; MCell (ZLit 665340) 4 (ZLit 30)
  ; MCell (ZLit 665456) 8 (ZLit 1)
  ; MCell (ZLit 665464) 8 (ZLit 4096)
  ; MCell (ZLit 666176) 8 (ZLit 666240)
  ; MCell (ZLit 666240) 8 (ZLit 636400)
  ; MCell (ZLit 666248) 4 (ZLit 5)
  ; MCell (ZLit 666256) 8 (ZLit 0)
  ; MCell (ZLit 666264) 8 (ZLit 0)
  ; MCell (ZLit 666272) 8 (ZLit 0)
  ; MZeroC (ZLit 666280) 5
  ; MCell (ZLit 666344) 1 (ZLit 1)
  ; MCell (ZLit 666352) 1 (ZLit 1)
  ; MCell (ZLit 666360) 8 (ZLit 666456)
  ; MCell (ZLit 666368) 8 (ZLit 666408)
  ; MCell (ZLit 666376) 8 (ZLit 0)
  ; MCell (ZLit 666392) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 65536))
  ; MCell (ZLit 666400) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 160))
  ; MCell (ZLit 666408) 8 (ZLit 0)
  ; MCell (ZLit 666416) 4 (ZLit 0)
  ; MCell (ZLit 666420) 4 (ZLit 0)
  ; MCell (ZLit 666424) 8 (ZLit 0)
  ; MCell (ZLit 666432) 8 (ZLit 0)
  ; MCell (ZLit 666440) 4 (ZLit 0)
  ; MCell (ZLit 666444) 4 (ZLit 0)
  ; MCell (ZLit 666448) 4 (ZLit 0)
  ; MCell (ZLit 666452) 4 (ZLit 0)
  ; MCell (ZLit 666456) 8 (ZLit 383576)
  ; MCell (ZLit 666464) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 666472) 4 (ZLit 0)
  ; MCell (ZLit 666480) 8 (ZLit 0)
  ; MCell (ZLit 666488) 4 (ZLit 0)
  ; MCell (ZLit 666492) 4 (ZLit 0)
  ; MCell (ZLit 666496) 8 (ZLit 1)
  ; MCell (ZLit 666504) 8 (ZLit 1)
  ; MCell (ZLit 666512) 8 (ZLit 1)
  ; MCell (ZLit 666520) 8 (ZLit 1)
  ; MCell (ZLit 666528) 8 (ZMul (ZLit 4096) (ZV 245))
  ; MCell (ZLit 666536) 8 (ZLit 4096)
  ; MCell (ZLit 666544) 8 (ZLit 1)
  ; MCell (ZLit 666552) 8 (ZLit 0)
  ; MCell (ZLit 666560) 8 (ZLit 0)
  ; MCell (ZLit 666568) 8 (ZLit 0)
  ; MCell (ZLit 666576) 8 (ZLit 0)
  ; MCell (ZLit 666584) 8 (ZLit 0)
  ; MCell (ZLit 666592) 8 (ZLit 0)
  ; MCell (ZLit 666600) 8 (ZLit 0)
  ; MCell (ZLit 666608) 8 (ZLit 0)
  ; MCell (ZLit 666616) 4 (ZLit 0)
  ; MCell (ZLit 1195080) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 65536))
  ; MCell (ZLit 1195088) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096))
  ; MCell (ZLit 1195096) 8 (ZLit 367436)
  ; MCell (ZLit 1195105) 1 (ZLit 1)
  ; MCell (ZLit 1250448) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-160)))
  ; MCell (ZLit 1250456) 4 (ZLit 0)
  ; MCell (ZLit 1250464) 8 (ZLit 4096)
  ; MCell (ZLit 1258784) 1 (ZLit 0)
  ; MZeroC (ZLit 1258785) 3
  ; MCell (ZLit 1258792) 8 (ZLit 1)
  ; MCell (ZLit 1258800) 8 (ZLit 0)
  ; MCell (ZLit 1258808) 8 (ZLit 0)
  ; MCell (ZLit 1258816) 8 (ZLit 81510)
  ; MCell (ZLit 1258824) 8 (ZLit 128849084416)
  ; MCell (ZLit 1258832) 8 (ZLit 0)
  ; MCell (ZLit 1258840) 8 (ZLit 0)
  ; MCell (ZLit 1258848) 8 (ZLit 0)
  ; MCell (ZLit 1258856) 8 (ZLit 0)
  ; MCell (ZLit 1258864) 8 (ZLit 1103823372545)
  ; MCell (ZLit 1258872) 8 (ZLit 4294967296)
  ; MCell (ZLit 1258880) 8 (ZLit 0)
  ; MCell (ZLit 1258888) 8 (ZLit 0)
  ; MCell (ZLit 1258896) 8 (ZLit 0)
  ; MCell (ZLit 1258904) 8 (ZLit 65537)
  ; MCell (ZLit 1258912) 8 (ZLit 18446744073709551615)
  ; MCell (ZLit 1258920) 8 (ZLit 71687)
  ; MCell (ZLit 1258928) 8 (ZLit 256)
  ; MCell (ZLit 1258936) 8 (ZLit 0)
  ; MCell (ZLit 1258944) 8 (ZLit 0)
  ; MCell (ZLit 1258952) 8 (ZLit 0)
  ; MCell (ZLit 1258960) 8 (ZLit 0)
  ; MCell (ZLit 1258968) 8 (ZLit 18446744069414584320)
  ; MCell (ZLit 1258976) 8 (ZLit 1)
  ; MCell (ZLit 1258984) 8 (ZLit 82370)
  ; MCell (ZLit 1258992) 8 (ZLit 81510)
  ; MCell (ZLit 1259000) 8 (ZLit 81510)
  ; MCell (ZLit 1259008) 8 (ZLit 1103823372544)
  ; MCell (ZLit 1259016) 8 (ZLit 0)
  ; MCell (ZLit 1259024) 8 (ZLit 121199)
  ; MCell (ZLit 1259032) 8 (ZLit 72339073309605888)
  ; MCell (ZLit 1259040) 8 (ZLit 72340172838076673)
  ; MCell (ZLit 1259048) 8 (ZLit 16843009)
  ; MCell (ZLit 1259056) 8 (ZLit 1103806595073)
  ; MCell (ZLit 1259064) 8 (ZLit 101176)
  ; MCell (ZLit 1259072) 8 (ZLit 281474976710912)
  ; MCell (ZLit 1259280) 8 (ZLit 347200)
  ; MCell (ZLit 1259320) 8 (ZLit 1)
  ; MCell (ZLit 1259344) 8 (ZLit 367296)
  ; MCell (ZLit 1259352) 8 (ZLit 367064)
  ; MCell (ZLit 1259360) 8 (ZLit 457428)
  ; MCell (ZLit 1259400) 1 (ZLit 1)
  ; MCell (ZLit 1259672) 1 (ZLit 0)
  ; MCell (ZLit 1521872) 8 (ZLit 8388608)
  ; MCell (ZLit 1521880) 8 (ZMul (ZLit 4096) (ZV 454))
  ; MCell (ZLit 1521892) 1 (ZLit 0)
  ; MZeroC (ZLit 1521893) 3
  ; MCell (ZLit 5781720) 4 (ZLit 1)
  ; MCell (ZLit 5781728) 1 (ZLit 0)
  ; MZeroC (ZLit 5781729) 3
  ; MCell (ZLit 5781736) 8 (ZMul (ZLit 4096) (ZV 453))
  ; MCell (ZLit 6045120) 1 (ZLit 0)
  ; MCell (ZLit 6045124) 4 (ZLit 0)
  ; MCell (ZLit 6045128) 8 (ZLit 72340172821233664)
  ; MCell (ZLit 6045136) 4 (ZLit 257)
  ; MCell (ZLit 6045140) 2 (ZLit 0)
  ; MCell (ZLit 6045142) 1 (ZLit 0)
  ; MCell (ZLit 6045144) 4 (ZLit 1)
  ; MCell (ZLit 6045152) 8 (ZLit 81510)
  ; MCell (ZLit 6045160) 4 (ZLit 1)
  ; MCell (ZLit 6045568) 8 (ZLit 6045632)
  ; MCell (ZLit 6045632) 8 (ZLit 646080)
  ; MCell (ZLit 6045640) 4 (ZLit 38)
  ; MCell (ZLit 6045648) 8 (ZLit 0)
  ; MCell (ZLit 6045656) 8 (ZLit 0)
  ; MCell (ZLit 6045664) 8 (ZLit 0)
  ; MZeroC (ZLit 6045672) 38
  ; MCell (ZLit 6045736) 1 (ZLit 1)
  ; MCell (ZLit 6045744) 1 (ZLit 0)
  ; MCell (ZLit 6045745) 1 (ZLit 1)
  ; MCell (ZLit 6045746) 2 (ZLit 0)
  ; MCell (ZLit 6045752) 2 (ZLit 0)
  ; MCell (ZLit 6045760) 8 (ZLit 81510)
  ; MCell (ZLit 6045768) 2 (ZLit 0)
  ; MCell (ZLit 6113472) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))) (ZLit 16))
  ; MCell (ZLit 6244776) 8 (ZLit 623088)
  ; MCell (ZLit 6244784) 8 (ZLit 0)
  ; MCell (ZLit 6244792) 8 (ZLit 24)
  ; MCell (ZLit 6244800) 8 (ZLit 8)
  ; MCell (ZLit 6244808) 8 (ZLit 0)
  ; MCell (ZLit 6113480) 8 (ZLit 6113480)
  ; MCell (ZLit 6113488) 8 (ZLit 6113480)
  ; MCell (ZLit 6113496) 8 (ZLit 6113480)
  ; MCell (ZLit 6113504) 8 (ZLit 0)
  ; MCell (ZLit 6113512) 4 (ZV 44)
  ; MCell (ZLit 6113520) 4 (ZLit 2)
  ; MCell (ZLit 6113530) 1 (ZLit 1)
  ; MCell (ZLit 6113592) 8 (ZLit 6249784)
  ; MCell (ZLit 6113600) 8 (ZLit 6113600)
  ; MCell (ZLit 6113632) 8 (ZLit 6245464)
  ; MCell (ZLit 6113664) 8 (ZV 45)
  ; MCell (ZLit 6113672) 8 (ZLit 6113712)
  ; MCell (ZLit 6113680) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MCell (ZLit 6113688) 8 (ZMul (ZLit 4096) (ZV 310))
  ; MCell (ZLit 6113712) 8 (ZLit 1)
  ; MCell (ZLit 6113720) 8 (ZLit 6115728)
  ; MRo (ZLit 6244816) 8 (ZV 45)
  ; MWr (ZLit 6244824) 9768
  ; MCell (ZLit 6244840) 4 (ZLit 1)
  ; MCell (ZLit 6244848) 8 (ZLit 6244856)
  ; MCell (ZLit 6244864) 8 (ZLit 561744)
  ; MCell (ZLit 6245120) 8 (ZLit 457428)
  ; MCell (ZLit 6245400) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))
  ; MCell (ZLit 6245408) 1 (ZLit 1)
  ; MCell (ZLit 6245416) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24))
  ; MCell (ZLit 6245424) 8 (ZLit 6244768)
  ; MCell (ZLit 6245432) 8 (ZLit 248)
  ; MCell (ZLit 6245440) 8 (ZLit 8)
  ; MCell (ZLit 6245448) 8 (ZLit 1)
  ; MCell (ZLit 6245456) 8 (ZLit 4096)
  ; MCell (ZLit 6245512) 8 (ZV 9)
  ; MCell (ZLit 6245544) 4 (ZLit 1)
  ; MCell (ZLit 6245548) 4 (ZLit 1)
  ; MCell (ZLit 6245568) 8 (ZLit 97)
  ; MCell (ZLit 6245576) 8 (ZLit 0)
  ; MCell (ZLit 6246016) 8 (ZLit 10)
  ; MCell (ZLit 6246120) 8 (ZLit 2)
  ; MCell (ZLit 6246152) 8 (ZLit 2)
  ; MCell (ZLit 6246184) 8 (ZLit 2)
  ; MCell (ZLit 6246448) 1 (ZLit 1)
  ; MCell (ZLit 6248696) 8 (ZLit 346684)
  ; MCell (ZLit 6249720) 4 (ZLit 0)
  ; MCell (ZLit 6249728) 4 (ZLit 0)
  ; MCell (ZLit 6249784) 8 (ZMul (ZLit 4096) (ZV 228))
  ; MCell (ZLit 636456) 8 (ZLit 8)
  ; MCell (ZLit 636464) 8 (ZLit 131578)
  ; MCell (ZLit 636480) 4 (ZLit 2)
  ; MWr (ZLit 626688) 5618128
  ; MImg 648009 648088
  ; MImg 648112 648120
  ; MImg 648132 648136
  ; MImg 648145 648152
  ; MImg 648192 648768
  ; MImg 648772 648880
  ; MImg 648904 648968
  ; MImg 648970 651704
  ; MImg 651717 651768
  ; MImg 651789 651792
  ; MImg 651809 651812
  ; MImg 651829 651832
  ; MImg 651859 651860
  ; MImg 651865 651868
  ; MImg 651884 651888
  ; MImg 651889 651896
  ; MImg 651928 651952
  ; MImg 651960 652024
  ; MImg 656808 660024
  ; MImg 660027 660028
  ; MImg 660048 660056
  ; MImg 660061 660064
  ; MImg 660065 660068
  ; MImg 660072 662008
  ; MImg 662020 665304
  ; MImg 665308 665312
  ; MImg 665320 665336
  ; MImg 665337 665340
  ; MImg 665344 665456
  ; MImg 665472 666176
  ; MImg 666184 666240
  ; MImg 666252 666256
  ; MImg 666285 666344
  ; MImg 666345 666352
  ; MImg 666353 666360
  ; MImg 666384 666392
  ; MImg 666476 666480
  ; MImg 666620 1195080
  ; MImg 1195104 1195105
  ; MImg 1195106 1250448
  ; MImg 1250460 1250464
  ; MImg 1250472 1250496
  ; MImg 1254591 1254592
  ; MImg 1258687 1258784
  ; MImg 1258788 1258792
  ; MImg 1259080 1259280
  ; MImg 1259288 1259320
  ; MImg 1259328 1259344
  ; MImg 1259368 1259400
  ; MImg 1259401 1259672
  ; MImg 1259673 1521864
  ; MImg 5781724 5781728
  ; MImg 5781732 5781736
  ; MImg 5781744 6045120
  ; MImg 6045121 6045124
  ; MImg 6045143 6045144
  ; MImg 6045148 6045152
  ; MImg 6045164 6045568
  ; MImg 6045576 6045632
  ; MImg 6045644 6045648
  ; MImg 6045710 6045736
  ; MImg 6045737 6045744
  ; MImg 6045748 6045752
  ; MImg 6045754 6045760
  ; MImg 6045770 6113472
  ; MImg 6113516 6113520
  ; MImg 6113524 6113530
  ; MImg 6113531 6113592
  ; MImg 6113608 6113632
  ; MImg 6113640 6113664
  ; MImg 6113696 6113712
  ; MImg 6113728 6244776
  ; MImg 6244824 6244840
  ; MImg 6244844 6244848
  ; MImg 6244856 6244864
  ; MImg 6244872 6245120
  ; MImg 6245128 6245392
  ; MImg 6245409 6245416
  ; MImg 6245464 6245512
  ; MImg 6245520 6245536
  ; MImg 6245552 6245560
  ; MImg 6245616 6245632
  ; MImg 6245640 6245736
  ; MImg 6245744 6245768
  ; MImg 6245776 6245800
  ; MImg 6245808 6246016
  ; MImg 6246024 6246120
  ; MImg 6246128 6246152
  ; MImg 6246160 6246184
  ; MImg 6246192 6246448
  ; MImg 6246449 6246456
  ; MImg 6246464 6248680
  ; MImg 6248688 6248696
  ; MImg 6248704 6249720
  ; MImg 6249724 6249728
  ; MImg 6249732 6249784
  ; MImg 6249792 6254592
  ; MImg 636472 636480
  ; MImg 636484 648000
  ; MImg 65536 636456
  ; MWr (ZLit 2147459072) 773632
  ; MZero (ZLit 2147459072) 8609
  ; MCell (ZLit 2147467681) 1 (ZLit 5)
  ; MFill (ZLit 2147467682) 2 249
  ; MZeroC (ZLit 2147467684) 6
  ; MCell (ZLit 2147467690) 1 (ZLit 4)
  ; MFill (ZLit 2147467691) 5 249
  ; MZeroC (ZLit 2147467696) 2
  ; MCell (ZLit 2147467698) 1 (ZLit 7)
  ; MFill (ZLit 2147467699) 5 249
  ; MZeroC (ZLit 2147467704) 1
  ; MCell (ZLit 2147467705) 1 (ZLit 5)
  ; MFill (ZLit 2147467706) 2 249
  ; MZeroC (ZLit 2147467708) 9
  ; MCell (ZLit 2147467717) 1 (ZLit 1)
  ; MFill (ZLit 2147467718) 6 249
  ; MZeroC (ZLit 2147467724) 8
  ; MCell (ZLit 2147467732) 1 (ZLit 5)
  ; MFill (ZLit 2147467733) 7 249
  ; MZeroC (ZLit 2147467740) 8
  ; MCell (ZLit 2147467748) 1 (ZLit 7)
  ; MFill (ZLit 2147467749) 7 249
  ; MZeroC (ZLit 2147467756) 2
  ; MCell (ZLit 2147467758) 1 (ZLit 1)
  ; MFill (ZLit 2147467759) 5 249
  ; MZeroC (ZLit 2147467764) 10
  ; MCell (ZLit 2147467774) 1 (ZLit 5)
  ; MFill (ZLit 2147467775) 5 249
  ; MZeroC (ZLit 2147467780) 136
  ; MFill (ZLit 2147467916) 32 249
  ; MZero (ZLit 2147467948) 512
  ; MFill (ZLit 2147468460) 128 249
  ; MZeroC (ZLit 2147468588) 16
  ; MFill (ZLit 2147468604) 4 249
  ; MZero (ZLit 2147468608) 63174
  ; MFill (ZLit 2147531782) 96 249
  ; MZero (ZLit 2147531878) 700826
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904)) 8 (ZLit 647216)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19912)) 8 (ZLit 0)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920)) 8 (ZLit 647280)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19928)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936)) 8 (ZLit 647344)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19944)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952)) 8 (ZLit 647408)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19960)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968)) 8 (ZLit 647472)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19976)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984)) 8 (ZLit 647536)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19992)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000)) 8 (ZLit 647600)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20008)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016)) 8 (ZLit 647664)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20024)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032)) 8 (ZLit 647728)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20040)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048)) 8 (ZLit 647792)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20056)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064)) 8 (ZLit 647856)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20072)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048))
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080)) 8 (ZLit 647920)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20088)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064))
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6115528)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6115748)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 64)) 8 (ZLit 6113688)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 72)) 8 (ZMul (ZLit 4096) (ZV 377))
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3169)) 927
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512
  ; MWr (ZMul (ZLit 4096) (ZV 228)) 65536
  ; MCell (ZMul (ZLit 4096) (ZV 228)) 8 (ZLit 627376)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6113680)
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
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 8)) 8 (ZLit 258900)
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MZero (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
  ; MWr (ZMul (ZLit 4096) (ZV 471)) 4096
  ; MCell (ZMul (ZLit 4096) (ZV 471)) 8 (ZLit 12297829379609722881)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 8)) 8 (ZLit 647216)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 16)) 8 (ZLit 647920)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 24)) 4072
  ; MWr (ZAdd (ZMul (ZLit 512) (ZV 471)) (ZLit 2147450880)) 512
].

Definition asan_pure_facts_r30 : list pfact := [
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

Definition asan_mem_facts_w1 : list mfact := [
  MCell (ZLit 1521864) 8 (ZLit 3)
  ; MCell (ZLit 1521888) 4 (ZLit 3)
  ; MCell (ZLit 4634560) 4 (ZLit 1)
  ; MImg 1521896 4634560
  ; MImg 4634564 5781720
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 1368218649204858810)
  ; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 2)
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8 (ZLit 263844)
  ; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 24)) 8388584
].

Definition asan_mem_facts_w2 : list mfact := [
  MCell (ZLit 1521864) 8 (ZLit 2)
  ; MCell (ZLit 1521888) 4 (ZLit 2)
  ; MCell (ZLit 5410488) 4 (ZLit 1)
  ; MImg 1521896 5410488
  ; MImg 5410492 5781720
  ; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 11531633707311863160)
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
  ; (ZLit 65536, ZLit 6189056)
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

Definition asan_totsz_r30 : Z := 17729664417792.
Definition asan_ylo_r30 : Z := 23387528589312.
Definition asan_eager : Z := 16515072.
Definition asan_abytes : Z := 2460728320.

Definition asan_mem_hints_w1 : list N := [3; 2; 423; 422; 421; 418; 411; 417; 432; 410; 397; 400; 399; 398; 247; 248; 396; 395; 394; 393; 392; 388; 390; 389; 391; 542; 508; 507; 541; 536; 523; 535; 534; 533; 532; 540; 539; 538; 537; 530; 470; 531; 529; 528; 522; 527; 526; 525; 524; 543; 1; 6; 5; 50; 79; 0; 442; 456; 441; 443; 445; 444; 469; 468; 439; 437; 440; 459; 386; 387; 154; 574; 466; 554; 467; 413; 412; 155; 162; 161; 160; 159; 157; 156; 158; 343; 349; 342; 304; 316; 314; 346; 345; 344; 341; 340; 339; 348; 338; 347; 363; 362; 361; 190; 360; 359; 278; 282; 281; 194; 286; 285; 284; 354; 353; 352; 351; 350; 358; 357; 356; 355; 544; 9; 457; 433; 572; 509; 553; 460; 462; 471; 472; 473; 474; 475; 476; 477; 478; 479; 480; 481; 482; 483; 484; 485; 486; 487; 488; 489; 490; 491; 492; 493; 494; 495; 496; 497; 498; 499; 500; 501; 502; 503; 504; 505; 506; 463; 249; 464; 465; 380; 244; 385; 107; 88; 87; 108; 132; 111; 131; 112; 517; 516; 515; 514; 521; 520; 519; 518; 513; 165; 172; 171; 170; 169; 167; 166; 168; 163; 164; 173; 512; 511; 510; 608; 603; 602; 598; 601; 597; 591; 584; 583; 582; 587; 589; 273; 438; 585; 586; 580; 592; 195; 250; 593; 594; 581; 755; 381; 384; 383; 382; 604; 590; 607; 600; 596; 595; 599; 605; 606; 185; 178; 182; 183; 174; 175; 176; 177; 181; 435; 436; 434; 274; 458; 573; 461; 754; 654; 655; 656; 657; 658; 659; 660; 661; 662; 663; 664; 665; 666; 667; 668; 669; 670; 671; 672; 673; 674; 675; 676; 677; 678; 679; 680; 681; 682; 683; 684; 685; 686; 687; 688; 689; 690; 691; 692; 693; 694; 695; 696; 697; 698; 699; 700; 701; 702; 703; 704; 707; 708; 709; 710; 711; 712; 713; 714; 715; 716; 717; 718; 719; 720; 721; 722; 723; 724; 725; 726; 727; 728; 729; 730; 731; 732; 733; 734; 735; 736; 737; 738; 739; 740; 741; 742; 743; 744; 745; 746; 747; 748; 749; 750; 751; 752; 753; 652; 653; 651; 557; 558; 52; 53; 559; 47; 48; 560; 43; 44; 561; 39; 40; 562; 35; 36; 563; 31; 32; 564; 27; 28; 565; 23; 24; 566; 19; 20; 567; 16; 568; 13; 569; 10; 570; 4; 571; 626; 609; 575; 576; 577; 578; 579; 627; 628; 629; 630; 631; 632; 633; 634; 635; 636; 637; 638; 639; 640; 641; 642; 643; 644; 645; 646; 647; 648; 649; 555; 556; 548; 59; 58; 57; 51; 49; 46; 45; 42; 41; 38; 37; 34; 33; 30; 29; 26; 25; 22; 21; 18; 17; 15; 14; 12; 11; 8; 7; 547; 449; 450; 448; 415; 416; 414; 367; 275; 219; 218; 272; 271; 270; 368; 221; 220; 217; 196; 369; 133; 370; 366; 321; 305; 309; 322; 280; 308; 323; 193; 279; 310; 324; 192; 277; 325; 191; 313; 312; 326; 311; 307; 306; 327; 276; 328; 319; 315; 320; 291; 283; 292; 289; 290; 255; 256; 246; 245; 257; 253; 254; 202; 203; 197; 204; 200; 201; 115; 116; 81; 82; 117; 113; 114; 91; 84; 89; 90; 61; 54; 55; 56; 62; 60; 109; 83; 80; 705; 706; 110; 86; 85; 92]%N.
Lemma asan_mem_facts_justified_w1 :
  forallb (mjustify (s_know (a_ss HS_asan2_1)) (var_ranges (s_know (a_ss HS_asan2_1))) 65536 6123520) (asan_mem_facts_r30_g30 ++ asan_mem_facts_w1_g30) = true.
Proof. apply (mjust_hints_sound _ _ _ _ _ asan_mem_hints_w1). vm_cast_no_check (@eq_refl bool true). Qed.
Definition asan_pure_hints_w1 : list N := [610; 618; 619; 620; 624; 625; 611; 621; 622; 623; 612; 588; 550; 452; 427; 419; 404; 372; 330; 294; 259; 232; 135; 135; 206; 141; 141; 140; 139; 139; 138; 137; 119; 94; 64; 136; 136; 420; 613; 614; 615; 616; 617; 224; 223; 447; 425; 402; 225; 365; 226; 318; 227; 288; 228; 252; 230; 199; 146; 150; 152; 148; 222; 546; 451; 453; 454; 430; 408; 378; 336; 302; 268; 242; 215; 129; 105; 77; 426; 428; 429; 407; 377; 335; 301; 267; 241; 214; 128; 104; 76; 403; 405; 406; 376; 334; 300; 266; 240; 213; 127; 103; 75; 371; 373; 374; 375; 333; 299; 265; 239; 212; 126; 102; 74; 329; 331; 332; 298; 264; 238; 211; 125; 101; 73; 293; 295; 296; 297; 263; 237; 210; 124; 100; 72; 258; 260; 261; 262; 236; 209; 123; 99; 71; 231; 233; 234; 235; 205; 207; 208; 122; 98; 70; 145; 144; 144; 143; 143; 142; 118; 120; 121; 97; 69; 93; 95; 96; 68; 63; 65; 66; 67; 549; 551; 552; 455; 431; 409; 379; 337; 303; 269; 243; 216; 130; 106; 78; 446; 424; 401; 364; 317; 287; 251; 229; 198; 147; 151; 153; 149; 545; 134]%N.
Lemma asan_pure_facts_justified_w1 :
  forallb (pjustify (s_know (a_ss HS_asan2_1)) (var_ranges (s_know (a_ss HS_asan2_1)))) (asan_pure_facts_r30_g30 ++ asan_pure_facts_w1_g30) = true.
Proof. apply (pjust_hints_sound _ _ _ asan_pure_hints_w1). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_vis_justified_w1 :
  vis_match (var_ranges (s_know (a_ss HS_asan2_1))) (a_vis HS_asan2_1) asan_vis_app_g30 = true /\ vis_match (var_ranges (s_know (a_ss HS_asan2_1))) (a_ghost HS_asan2_1) asan_ghost_g30 = true.
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_ledger_justified_w1 :
  ledger_xmatch (var_ranges (s_know (a_ss HS_asan2_1))) (a_maps HS_asan2_1) asan_ledger_g30 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_consts_w1 : a_totsz HS_asan2_1 = asan_totsz_r30_g30 /\ a_ylo HS_asan2_1 = asan_ylo_r30_g30 /\ a_eager HS_asan2_1 = asan_eager_g30 /\ a_abytes HS_asan2_1 = asan_abytes_g30.
Proof. repeat split; reflexivity. Qed.
Definition asan_mem_hints_w2 : list N := [3; 2; 422; 421; 420; 417; 410; 416; 431; 409; 396; 399; 398; 397; 246; 247; 395; 394; 393; 392; 391; 387; 389; 388; 390; 541; 507; 506; 540; 535; 522; 534; 533; 532; 531; 539; 538; 537; 536; 529; 469; 530; 528; 527; 521; 526; 525; 524; 523; 542; 1; 6; 5; 50; 79; 0; 441; 455; 440; 442; 444; 443; 468; 467; 438; 436; 439; 458; 385; 386; 153; 573; 465; 553; 466; 412; 411; 154; 161; 160; 159; 158; 156; 155; 157; 342; 348; 341; 303; 315; 313; 345; 344; 343; 340; 339; 338; 347; 337; 346; 362; 361; 360; 189; 359; 358; 277; 281; 280; 193; 285; 284; 283; 353; 352; 351; 350; 349; 357; 356; 355; 354; 543; 9; 456; 432; 571; 508; 552; 459; 461; 470; 471; 472; 473; 474; 475; 476; 477; 478; 479; 480; 481; 482; 483; 484; 485; 486; 487; 488; 489; 490; 491; 492; 493; 494; 495; 496; 497; 498; 499; 500; 501; 502; 503; 504; 505; 462; 248; 463; 464; 379; 243; 384; 106; 87; 86; 107; 131; 110; 130; 111; 516; 515; 514; 513; 520; 519; 518; 517; 512; 164; 171; 170; 169; 168; 166; 165; 167; 162; 163; 172; 511; 510; 509; 607; 602; 601; 597; 600; 596; 590; 583; 582; 581; 586; 588; 272; 437; 584; 585; 579; 591; 194; 249; 592; 593; 580; 754; 380; 383; 382; 381; 603; 589; 606; 599; 595; 594; 598; 604; 605; 184; 177; 181; 182; 173; 174; 175; 176; 180; 434; 435; 433; 273; 457; 572; 460; 753; 653; 654; 655; 656; 657; 658; 659; 660; 661; 662; 663; 664; 665; 666; 667; 668; 669; 670; 671; 672; 673; 674; 675; 676; 677; 678; 679; 680; 681; 682; 683; 684; 685; 686; 687; 688; 689; 690; 691; 692; 693; 694; 695; 696; 697; 698; 699; 700; 701; 702; 703; 706; 707; 708; 709; 710; 711; 712; 713; 714; 715; 716; 717; 718; 719; 720; 721; 722; 723; 724; 725; 726; 727; 728; 729; 730; 731; 732; 733; 734; 735; 736; 737; 738; 739; 740; 741; 742; 743; 744; 745; 746; 747; 748; 749; 750; 751; 752; 651; 652; 650; 556; 557; 52; 53; 558; 47; 48; 559; 43; 44; 560; 39; 40; 561; 35; 36; 562; 31; 32; 563; 27; 28; 564; 23; 24; 565; 19; 20; 566; 16; 567; 13; 568; 10; 569; 4; 570; 625; 608; 574; 575; 576; 577; 578; 626; 627; 628; 629; 630; 631; 632; 633; 634; 635; 636; 637; 638; 639; 640; 641; 642; 643; 644; 645; 646; 647; 648; 554; 555; 547; 59; 58; 57; 51; 49; 46; 45; 42; 41; 38; 37; 34; 33; 30; 29; 26; 25; 22; 21; 18; 17; 15; 14; 12; 11; 8; 7; 546; 448; 449; 447; 414; 415; 413; 366; 274; 218; 217; 271; 270; 269; 367; 220; 219; 216; 195; 368; 132; 369; 365; 320; 304; 308; 321; 279; 307; 322; 192; 278; 309; 323; 191; 276; 324; 190; 312; 311; 325; 310; 306; 305; 326; 275; 327; 318; 314; 319; 290; 282; 291; 288; 289; 254; 255; 245; 244; 256; 252; 253; 201; 202; 196; 203; 199; 200; 114; 115; 81; 82; 116; 112; 113; 90; 84; 88; 89; 61; 54; 55; 56; 62; 60; 108; 83; 80; 704; 705; 109; 85; 91]%N.
Lemma asan_mem_facts_justified_w2 :
  forallb (mjustify (s_know (a_ss HS_asan2_2)) (var_ranges (s_know (a_ss HS_asan2_2))) 65536 6123520) (asan_mem_facts_r30_g30 ++ asan_mem_facts_w2_g30) = true.
Proof. apply (mjust_hints_sound _ _ _ _ _ asan_mem_hints_w2). vm_cast_no_check (@eq_refl bool true). Qed.
Definition asan_pure_hints_w2 : list N := [609; 617; 618; 619; 623; 624; 610; 620; 621; 622; 611; 587; 549; 451; 426; 418; 403; 371; 329; 293; 258; 231; 134; 134; 205; 140; 140; 139; 138; 138; 137; 136; 118; 93; 64; 135; 135; 419; 612; 613; 614; 615; 616; 223; 222; 446; 424; 401; 224; 364; 225; 317; 226; 287; 227; 251; 229; 198; 145; 149; 151; 147; 221; 545; 450; 452; 453; 429; 407; 377; 335; 301; 267; 241; 214; 128; 104; 77; 425; 427; 428; 406; 376; 334; 300; 266; 240; 213; 127; 103; 76; 402; 404; 405; 375; 333; 299; 265; 239; 212; 126; 102; 75; 370; 372; 373; 374; 332; 298; 264; 238; 211; 125; 101; 74; 328; 330; 331; 297; 263; 237; 210; 124; 100; 73; 292; 294; 295; 296; 262; 236; 209; 123; 99; 72; 257; 259; 260; 261; 235; 208; 122; 98; 71; 230; 232; 233; 234; 204; 206; 207; 121; 97; 70; 144; 143; 143; 142; 142; 141; 117; 119; 120; 96; 69; 92; 94; 95; 68; 63; 65; 66; 67; 548; 550; 551; 454; 430; 408; 378; 336; 302; 268; 242; 215; 129; 105; 78; 445; 423; 400; 363; 316; 286; 250; 228; 197; 146; 150; 152; 148; 544; 133]%N.
Lemma asan_pure_facts_justified_w2 :
  forallb (pjustify (s_know (a_ss HS_asan2_2)) (var_ranges (s_know (a_ss HS_asan2_2)))) (asan_pure_facts_r30_g30 ++ asan_pure_facts_w2_g30) = true.
Proof. apply (pjust_hints_sound _ _ _ asan_pure_hints_w2). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_vis_justified_w2 :
  vis_match (var_ranges (s_know (a_ss HS_asan2_2))) (a_vis HS_asan2_2) asan_vis_app_g30 = true /\ vis_match (var_ranges (s_know (a_ss HS_asan2_2))) (a_ghost HS_asan2_2) asan_ghost_g30 = true.
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_ledger_justified_w2 :
  ledger_xmatch (var_ranges (s_know (a_ss HS_asan2_2))) (a_maps HS_asan2_2) asan_ledger_g30 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_consts_w2 : a_totsz HS_asan2_2 = asan_totsz_r30_g30 /\ a_ylo HS_asan2_2 = asan_ylo_r30_g30 /\ a_eager HS_asan2_2 = asan_eager_g30 /\ a_abytes HS_asan2_2 = asan_abytes_g30.
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

Definition asan_mem_facts : list mfact := asan_stack_fact :: drop_ix (233 :: 396 :: seq 404 22)%nat asan_mem_facts_r30.
(* the list is stored COMPUTED (Eval vm_compute), not as the drop_ix expression: a kernel
   conversion between plist727 w and its unfolding otherwise evaluates drop_ix's unary-nat filter lazily and took over
   an hour at MainEntry's Qed (bisection: probes/p8, PJ434d slow vs PK434s 0.3 s). Same list, same elements. *)
Definition asan_pure_facts : list pfact := Eval vm_compute in drop_ix [4; 38; 39]%nat asan_pure_facts_r30.
Lemma asan_pure_facts_drop : asan_pure_facts = drop_ix [4; 38; 39]%nat asan_pure_facts_r30.
Proof. vm_compute. reflexivity. Qed.

(* argv[0] / argv[1] at ; the auxv holds 27 + 2 r pairs (r = the kernel build's rseq bit) *)
Definition argv0_z (r : Z) : zexp :=
  ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 4)
    (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 8) (ZV 11)))))))) (ZLit (472 + 32 * r)).
Definition argv1_z (r : Z) : zexp :=
  ZMul (ZLtu (ZLit 1) (ZV 1))
    (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZV 3) (ZAdd (ZV 4)
      (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZAdd (ZMul (ZLit 4096) (ZV 10)) (ZMul (ZLit 8) (ZV 11))))))))) (ZLit (473 + 32 * r))).
Definition asan_argv_facts (r : Z) : list mfact :=
  [MRo (ZAdd usp_z (ZLit 8)) 8 (argv0_z r); MRo (ZAdd usp_z (ZLit 16)) 8 (argv1_z r)].

Definition asan_totsz : Z := 17729664630784.   (* r30q2 + 81920: the vDSO pair's 20-page reservation bound *)
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
  forallb (mjustify kn vr 65536 6254592) (map rmf (mlist727 w r))
  && forallb (pjustify kn vr) (map rpf (plist727 w))
  && vis_match vr (a_vis hs) (rvis asan_vis_app) && vis_match vr (a_ghost hs) (rvis asan_ghost)
  && ledger_xmatch vr (a_maps hs) (map rle asan_ledger)
  && Z.eqb (a_totsz hs) asan_totsz && Z.eqb (a_ylo hs) asan_ylo
  && Z.eqb (a_eager hs) asan_eager && Z.eqb (a_abytes hs) asan_abytes.

Lemma just727_ok : forall w r, r = 0 \/ r = 1 -> just727 w r = true.
Proof. intros [|] r [-> | ->]; vm_cast_no_check (@eq_refl bool true). Qed.
