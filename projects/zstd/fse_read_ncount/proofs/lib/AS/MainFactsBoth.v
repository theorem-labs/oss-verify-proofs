(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import AxSymExec3 AsanPlan MainExport MainHint StartupHS2Both.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Definition both_mem_facts : list mfact := [
MCell (ZLit 650880) 8 (ZLit 1)
; MCell (ZLit 650888) 1 (ZLit 1)
; MCell (ZLit 650968) 8 (ZMul (ZLit 4096) (ZV 208))
; MCell (ZLit 650976) 8 (ZLit 137439023104)
; MCell (ZLit 650984) 8 (ZLit 93074)
; MCell (ZLit 651000) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 65536))
; MCell (ZLit 651008) 4 (ZLit 18446744073709551615)
; MCell (ZLit 651016) 8 (ZAdd (ZAdd (ZMul (ZLit 4096) (ZV 208)) (ZMul (ZLit (-4096)) (ZV 209))) (ZLit 137439019008))
; MCell (ZLit 651024) 1 (ZLit 0)
; MCell (ZLit 651032) 8 (ZLit 4096)
; MCell (ZLit 651040) 8 (ZMul (ZLit 4096) (ZV 226))
; MCell (ZLit 651048) 8 (ZMul (ZLit 4096) (ZV 226))
; MCell (ZLit 651056) 8 (ZLit 8388608)
; MCell (ZLit 651064) 8 (ZLit 103102)
; MCell (ZLit 651648) 1 (ZLit 0)
; MZeroC (ZLit 651649) 3
; MCell (ZLit 651760) 8 (ZLit 268435456)
; MCell (ZLit 651768) 8 (ZLit 241591905)
; MCell (ZLit 651776) 8 (ZLit 1048576)
; MCell (ZLit 651848) 1 (ZLit 0)
; MCell (ZLit 651849) 1 (ZLit 0)
; MCell (ZLit 654584) 8 (ZLit 1099511627776)
; MCell (ZLit 654592) 2 (ZLit 16)
; MCell (ZLit 654594) 2 (ZLit 2048)
; MCell (ZLit 654596) 1 (ZLit 1)
; MCell (ZLit 654648) 4 (ZLit 4294967295)
; MCell (ZLit 654652) 4 (ZLit 256)
; MCell (ZLit 654656) 4 (ZLit 1024)
; MCell (ZLit 654660) 4 (ZLit 16)
; MCell (ZLit 654664) 4 (ZLit 2048)
; MCell (ZLit 654668) 1 (ZLit 0)
; MCell (ZLit 654672) 8 (ZLit 72340168526266369)
; MCell (ZLit 654680) 8 (ZLit 85899345936)
; MCell (ZLit 654688) 1 (ZLit 0)
; MCell (ZLit 654692) 4 (ZLit 4096)
; MCell (ZLit 654696) 8 (ZLit 816043786240)
; MCell (ZLit 654704) 4 (ZLit 85)
; MCell (ZLit 654708) 1 (ZLit 1)
; MCell (ZLit 654712) 8 (ZLit 0)
; MRo (ZLit 654720) 6 (ZLit 4294967296)
; MCell (ZLit 654726) 1 (ZLit 1)
; MCell (ZLit 654727) 1 (ZLit 0)
; MCell (ZLit 654728) 8 (ZLit 72340172838010881)
; MCell (ZLit 654736) 2 (ZLit 1)
; MCell (ZLit 654738) 1 (ZLit 0)
; MCell (ZLit 654740) 4 (ZLit 0)
; MCell (ZLit 654744) 1 (ZLit 1)
; MCell (ZLit 654748) 4 (ZLit 2)
; MCell (ZLit 654752) 8 (ZLit 81629)
; MCell (ZLit 654760) 4 (ZLit 65793)
; MCell (ZLit 654768) 1 (ZLit 1)
; MCell (ZLit 654776) 8 (ZLit 51)
; MCell (ZLit 654784) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20704))
; MCell (ZLit 654792) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
; MCell (ZLit 654800) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19880))
; MCell (ZLit 654832) 8 (ZLit 0)
; MCell (ZLit 662904) 1 (ZLit 1)
; MCell (ZLit 662905) 1 (ZLit 1)
; MCell (ZLit 662906) 1 (ZLit 1)
; MCell (ZLit 662908) 4 (ZLit 299)
; MCell (ZLit 662912) 8 (ZLit 662920)
; MCell (ZLit 662920) 8 (ZMul (ZLit 4096) (ZV 207))
; MCell (ZLit 662936) 4 (ZLit 2)
; MCell (ZLit 662940) 1 (ZLit 1)
; MCell (ZLit 662944) 1 (ZLit 1)
; MCell (ZLit 662948) 4 (ZLit 0)
; MCell (ZLit 664888) 8 (ZLit 2147450880)
; MCell (ZLit 664896) 4 (ZLit 1)
; MCell (ZLit 668184) 1 (ZLit 1)
; MCell (ZLit 668185) 1 (ZLit 1)
; MCell (ZLit 668186) 1 (ZLit 0)
; MCell (ZLit 668187) 1 (ZLit 0)
; MCell (ZLit 668192) 8 (ZLit 140737488355327)
; MCell (ZLit 668216) 1 (ZLit 1)
; MCell (ZLit 668220) 4 (ZLit 30)
; MCell (ZLit 668336) 8 (ZLit 1)
; MCell (ZLit 668344) 8 (ZLit 4096)
; MCell (ZLit 669056) 8 (ZLit 669120)
; MCell (ZLit 669120) 8 (ZLit 636800)
; MCell (ZLit 669128) 4 (ZLit 5)
; MCell (ZLit 669136) 8 (ZLit 0)
; MCell (ZLit 669144) 8 (ZLit 0)
; MCell (ZLit 669152) 8 (ZLit 0)
; MZeroC (ZLit 669160) 5
; MCell (ZLit 669224) 1 (ZLit 1)
; MCell (ZLit 669232) 1 (ZLit 1)
; MCell (ZLit 669240) 8 (ZLit 669336)
; MCell (ZLit 669248) 8 (ZLit 669288)
; MCell (ZLit 669256) 8 (ZLit 0)
; MCell (ZLit 669272) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 65536))
; MCell (ZLit 669280) 8 (ZAdd (ZMul (ZLit 4096) (ZV 228)) (ZLit 160))
; MCell (ZLit 669288) 8 (ZLit 0)
; MCell (ZLit 669296) 4 (ZLit 0)
; MCell (ZLit 669300) 4 (ZLit 0)
; MCell (ZLit 669304) 8 (ZLit 0)
; MCell (ZLit 669312) 8 (ZLit 0)
; MCell (ZLit 669320) 4 (ZLit 0)
; MCell (ZLit 669324) 4 (ZLit 0)
; MCell (ZLit 669328) 4 (ZLit 0)
; MCell (ZLit 669332) 4 (ZLit 0)
; MCell (ZLit 669336) 8 (ZLit 385636)
; MCell (ZLit 669344) 8 (ZLit 18446744073709551615)
; MCell (ZLit 669352) 4 (ZLit 0)
; MCell (ZLit 669360) 8 (ZLit 0)
; MCell (ZLit 669368) 4 (ZLit 0)
; MCell (ZLit 669372) 4 (ZLit 0)
; MCell (ZLit 669376) 8 (ZLit 1)
; MCell (ZLit 669384) 8 (ZLit 1)
; MCell (ZLit 669392) 8 (ZLit 1)
; MCell (ZLit 669400) 8 (ZLit 1)
; MCell (ZLit 669408) 8 (ZMul (ZLit 4096) (ZV 245))
; MCell (ZLit 669416) 8 (ZLit 4096)
; MCell (ZLit 669424) 8 (ZLit 1)
; MCell (ZLit 669432) 8 (ZLit 0)
; MCell (ZLit 669440) 8 (ZLit 0)
; MCell (ZLit 669448) 8 (ZLit 0)
; MCell (ZLit 669456) 8 (ZLit 0)
; MCell (ZLit 669464) 8 (ZLit 0)
; MCell (ZLit 669472) 8 (ZLit 0)
; MCell (ZLit 669480) 8 (ZLit 0)
; MCell (ZLit 669488) 8 (ZLit 0)
; MCell (ZLit 669496) 4 (ZLit 0)
; MCell (ZLit 1197960) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 65536))
; MCell (ZLit 1197968) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20720))
; MCell (ZLit 1197976) 8 (ZLit 369496)
; MCell (ZLit 1197985) 1 (ZLit 1)
; MCell (ZLit 1253328) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))) (ZLit (-160)))
; MCell (ZLit 1253336) 4 (ZLit 0)
; MCell (ZLit 1253344) 8 (ZLit 4096)
; MCell (ZLit 1261664) 1 (ZLit 0)
; MZeroC (ZLit 1261665) 3
; MCell (ZLit 1261672) 8 (ZLit 1)
; MCell (ZLit 1261680) 8 (ZLit 0)
; MCell (ZLit 1261688) 8 (ZLit 0)
; MCell (ZLit 1261696) 8 (ZLit 81629)
; MCell (ZLit 1261704) 8 (ZLit 128849084416)
; MCell (ZLit 1261712) 8 (ZLit 0)
; MCell (ZLit 1261720) 8 (ZLit 0)
; MCell (ZLit 1261728) 8 (ZLit 0)
; MCell (ZLit 1261736) 8 (ZLit 0)
; MCell (ZLit 1261744) 8 (ZLit 1103823372545)
; MCell (ZLit 1261752) 8 (ZLit 4294967296)
; MCell (ZLit 1261760) 8 (ZLit 0)
; MCell (ZLit 1261768) 8 (ZLit 0)
; MCell (ZLit 1261776) 8 (ZLit 0)
; MCell (ZLit 1261784) 8 (ZLit 65537)
; MCell (ZLit 1261792) 8 (ZLit 18446744073709551615)
; MCell (ZLit 1261800) 8 (ZLit 71726)
; MCell (ZLit 1261808) 8 (ZLit 256)
; MCell (ZLit 1261816) 8 (ZLit 0)
; MCell (ZLit 1261824) 8 (ZLit 0)
; MCell (ZLit 1261832) 8 (ZLit 0)
; MCell (ZLit 1261840) 8 (ZLit 0)
; MCell (ZLit 1261848) 8 (ZLit 18446744069414584320)
; MCell (ZLit 1261856) 8 (ZLit 1)
; MCell (ZLit 1261864) 8 (ZLit 82489)
; MCell (ZLit 1261872) 8 (ZLit 81629)
; MCell (ZLit 1261880) 8 (ZLit 81629)
; MCell (ZLit 1261888) 8 (ZLit 1103823372544)
; MCell (ZLit 1261896) 8 (ZLit 0)
; MCell (ZLit 1261904) 8 (ZLit 121494)
; MCell (ZLit 1261912) 8 (ZLit 72339073309605888)
; MCell (ZLit 1261920) 8 (ZLit 72340172838076673)
; MCell (ZLit 1261928) 8 (ZLit 16843009)
; MCell (ZLit 1261936) 8 (ZLit 1103806595073)
; MCell (ZLit 1261944) 8 (ZLit 101431)
; MCell (ZLit 1261952) 8 (ZLit 281474976710912)
; MCell (ZLit 1262160) 8 (ZLit 349260)
; MCell (ZLit 1262200) 8 (ZLit 1)
; MCell (ZLit 1262224) 8 (ZLit 369356)
; MCell (ZLit 1262232) 8 (ZLit 369124)
; MCell (ZLit 1262240) 8 (ZLit 459488)
; MCell (ZLit 1262280) 1 (ZLit 1)
; MCell (ZLit 1262552) 1 (ZLit 0)
; MCell (ZLit 1524752) 8 (ZLit 8388608)
; MCell (ZLit 1524760) 8 (ZMul (ZLit 4096) (ZV 454))
; MCell (ZLit 1524772) 1 (ZLit 0)
; MZeroC (ZLit 1524773) 3
; MCell (ZLit 5784600) 4 (ZLit 1)
; MCell (ZLit 5784608) 1 (ZLit 0)
; MZeroC (ZLit 5784609) 3
; MCell (ZLit 5784616) 8 (ZMul (ZLit 4096) (ZV 453))
; MCell (ZLit 6048000) 1 (ZLit 0)
; MCell (ZLit 6048004) 4 (ZLit 0)
; MCell (ZLit 6048008) 8 (ZLit 72340172821233664)
; MCell (ZLit 6048016) 4 (ZLit 257)
; MCell (ZLit 6048020) 2 (ZLit 0)
; MCell (ZLit 6048022) 1 (ZLit 0)
; MCell (ZLit 6048024) 4 (ZLit 1)
; MCell (ZLit 6048032) 8 (ZLit 81629)
; MCell (ZLit 6048040) 4 (ZLit 1)
; MCell (ZLit 6048448) 8 (ZLit 6048512)
; MCell (ZLit 6048512) 8 (ZLit 646480)
; MCell (ZLit 6048520) 4 (ZLit 38)
; MCell (ZLit 6048528) 8 (ZLit 0)
; MCell (ZLit 6048536) 8 (ZLit 0)
; MCell (ZLit 6048544) 8 (ZLit 0)
; MZeroC (ZLit 6048552) 38
; MCell (ZLit 6048616) 1 (ZLit 1)
; MCell (ZLit 6048624) 1 (ZLit 0)
; MCell (ZLit 6048625) 1 (ZLit 1)
; MCell (ZLit 6048626) 2 (ZLit 0)
; MCell (ZLit 6048632) 2 (ZLit 0)
; MCell (ZLit 6048640) 8 (ZLit 81629)
; MCell (ZLit 6048648) 2 (ZLit 0)
; MCell (ZLit 6116352) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10))))) (ZLit 16))
; MCell (ZLit 6247656) 8 (ZLit 623480)
; MCell (ZLit 6247664) 8 (ZLit 0)
; MCell (ZLit 6247672) 8 (ZLit 24)
; MCell (ZLit 6247680) 8 (ZLit 8)
; MCell (ZLit 6247688) 8 (ZLit 0)
; MCell (ZLit 6116360) 8 (ZLit 6116360)
; MCell (ZLit 6116368) 8 (ZLit 6116360)
; MCell (ZLit 6116376) 8 (ZLit 6116360)
; MCell (ZLit 6116384) 8 (ZLit 0)
; MCell (ZLit 6116392) 4 (ZV 44)
; MCell (ZLit 6116400) 4 (ZLit 2)
; MCell (ZLit 6116410) 1 (ZLit 1)
; MCell (ZLit 6116472) 8 (ZLit 6252664)
; MCell (ZLit 6116480) 8 (ZLit 6116480)
; MCell (ZLit 6116512) 8 (ZLit 6248344)
; MCell (ZLit 6116544) 8 (ZV 45)
; MCell (ZLit 6116552) 8 (ZLit 6116592)
; MCell (ZLit 6116560) 8 (ZMul (ZLit 4096) (ZV 377))
; MCell (ZLit 6116568) 8 (ZMul (ZLit 4096) (ZV 310))
; MCell (ZLit 6116592) 8 (ZLit 1)
; MCell (ZLit 6116600) 8 (ZLit 6118608)
; MRo (ZLit 6247696) 8 (ZV 45)
; MWr (ZLit 6247704) 6888
; MCell (ZLit 6247720) 4 (ZLit 1)
; MCell (ZLit 6247728) 8 (ZLit 6247736)
; MCell (ZLit 6247744) 8 (ZLit 562136)
; MCell (ZLit 6248000) 8 (ZLit 459488)
; MCell (ZLit 6248280) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 184))
; MCell (ZLit 6248288) 1 (ZLit 1)
; MCell (ZLit 6248296) 8 (ZAdd (ZAdd (ZMul (ZLit 32768) (ZV 0)) (ZAdd (ZMul (ZLit 8) (ZV 1)) (ZAdd (ZMul (ZLit 8) (ZV 2)) (ZAdd (ZMul (ZLit 16) (ZV 6)) (ZMul (ZLit 4096) (ZV 10)))))) (ZLit 24))
; MCell (ZLit 6248304) 8 (ZLit 6247648)
; MCell (ZLit 6248312) 8 (ZLit 248)
; MCell (ZLit 6248320) 8 (ZLit 8)
; MCell (ZLit 6248328) 8 (ZLit 1)
; MCell (ZLit 6248336) 8 (ZLit 4096)
; MCell (ZLit 6248392) 8 (ZV 9)
; MCell (ZLit 6248424) 4 (ZLit 1)
; MCell (ZLit 6248428) 4 (ZLit 1)
; MCell (ZLit 6248448) 8 (ZLit 97)
; MCell (ZLit 6248456) 8 (ZLit 0)
; MCell (ZLit 6248896) 8 (ZLit 10)
; MCell (ZLit 6249000) 8 (ZLit 2)
; MCell (ZLit 6249032) 8 (ZLit 2)
; MCell (ZLit 6249064) 8 (ZLit 2)
; MCell (ZLit 6249328) 1 (ZLit 1)
; MCell (ZLit 6251576) 8 (ZLit 348744)
; MCell (ZLit 6252600) 4 (ZLit 0)
; MCell (ZLit 6252608) 4 (ZLit 0)
; MCell (ZLit 6252664) 8 (ZMul (ZLit 4096) (ZV 228))
; MCell (ZLit 636856) 8 (ZLit 8)
; MCell (ZLit 636864) 8 (ZLit 131873)
; MCell (ZLit 636880) 4 (ZLit 2)
; MWr (ZLit 626688) 5621008
; MImg 650889 650968
; MImg 650992 651000
; MImg 651012 651016
; MImg 651025 651032
; MImg 651072 651648
; MImg 651652 651760
; MImg 651784 651848
; MImg 651850 654584
; MImg 654597 654648
; MImg 654669 654672
; MImg 654689 654692
; MImg 654709 654712
; MImg 654739 654740
; MImg 654745 654748
; MImg 654764 654768
; MImg 654769 654776
; MImg 654808 654832
; MImg 654840 654904
; MImg 659688 662904
; MImg 662907 662908
; MImg 662928 662936
; MImg 662941 662944
; MImg 662945 662948
; MImg 662952 664888
; MImg 664900 668184
; MImg 668188 668192
; MImg 668200 668216
; MImg 668217 668220
; MImg 668224 668336
; MImg 668352 669056
; MImg 669064 669120
; MImg 669132 669136
; MImg 669165 669224
; MImg 669225 669232
; MImg 669233 669240
; MImg 669264 669272
; MImg 669356 669360
; MImg 669500 1197960
; MImg 1197984 1197985
; MImg 1197986 1253328
; MImg 1253340 1253344
; MImg 1253352 1253376
; MImg 1257471 1257472
; MImg 1261567 1261664
; MImg 1261668 1261672
; MImg 1261960 1262160
; MImg 1262168 1262200
; MImg 1262208 1262224
; MImg 1262248 1262280
; MImg 1262281 1262552
; MImg 1262553 1524744
; MImg 5784604 5784608
; MImg 5784612 5784616
; MImg 5784624 6048000
; MImg 6048001 6048004
; MImg 6048023 6048024
; MImg 6048028 6048032
; MImg 6048044 6048448
; MImg 6048456 6048512
; MImg 6048524 6048528
; MImg 6048590 6048616
; MImg 6048617 6048624
; MImg 6048628 6048632
; MImg 6048634 6048640
; MImg 6048650 6116352
; MImg 6116396 6116400
; MImg 6116404 6116410
; MImg 6116411 6116472
; MImg 6116488 6116512
; MImg 6116520 6116544
; MImg 6116576 6116592
; MImg 6116608 6247656
; MImg 6247704 6247720
; MImg 6247724 6247728
; MImg 6247736 6247744
; MImg 6247752 6248000
; MImg 6248008 6248272
; MImg 6248289 6248296
; MImg 6248344 6248392
; MImg 6248400 6248416
; MImg 6248432 6248440
; MImg 6248496 6248512
; MImg 6248520 6248616
; MImg 6248624 6248648
; MImg 6248656 6248680
; MImg 6248688 6248896
; MImg 6248904 6249000
; MImg 6249008 6249032
; MImg 6249040 6249064
; MImg 6249072 6249328
; MImg 6249329 6249336
; MImg 6249344 6251560
; MImg 6251568 6251576
; MImg 6251584 6252600
; MImg 6252604 6252608
; MImg 6252612 6252664
; MImg 6252672 6254592
; MImg 636872 636880
; MImg 636884 650880
; MImg 65536 636856
; MWr (ZLit 2147459072) 773632
; MZero (ZLit 2147459072) 8656
; MCell (ZLit 2147467728) 1 (ZLit 4)
; MFill (ZLit 2147467729) 7 249
; MZeroC (ZLit 2147467736) 8
; MCell (ZLit 2147467744) 1 (ZLit 1)
; MFill (ZLit 2147467745) 7 249
; MZeroC (ZLit 2147467756) 3
; MCell (ZLit 2147467752) 1 (ZLit 1)
; MFill (ZLit 2147467753) 3 249
; MFill (ZLit 2147467759) 5 249
; MZeroC (ZLit 2147467764) 3
; MZeroC (ZLit 2147467772) 3
; MCell (ZLit 2147467767) 1 (ZLit 2)
; MFill (ZLit 2147467768) 4 249
; MZeroC (ZLit 2147467780) 4
; MCell (ZLit 2147467775) 1 (ZLit 1)
; MFill (ZLit 2147467776) 4 249
; MZeroC (ZLit 2147467792) 3
; MCell (ZLit 2147467784) 1 (ZLit 5)
; MFill (ZLit 2147467785) 7 249
; MZeroC (ZLit 2147467800) 3
; MCell (ZLit 2147467795) 1 (ZLit 1)
; MFill (ZLit 2147467796) 4 249
; MZeroC (ZLit 2147467808) 58
; MCell (ZLit 2147467803) 1 (ZLit 3)
; MFill (ZLit 2147467804) 4 249
; MZeroC (ZLit 2147467872) 2
; MCell (ZLit 2147467866) 1 (ZLit 7)
; MFill (ZLit 2147467867) 5 249
; MZeroC (ZLit 2147467880) 2
; MCell (ZLit 2147467874) 1 (ZLit 2)
; MFill (ZLit 2147467875) 5 249
; MZeroC (ZLit 2147467884) 3
; MFill (ZLit 2147467882) 2 249
; MZeroC (ZLit 2147467892) 2
; MCell (ZLit 2147467887) 1 (ZLit 1)
; MFill (ZLit 2147467888) 4 249
; MZeroC (ZLit 2147467900) 3
; MCell (ZLit 2147467894) 1 (ZLit 6)
; MFill (ZLit 2147467895) 5 249
; MZeroC (ZLit 2147467908) 5
; MCell (ZLit 2147467903) 1 (ZLit 4)
; MFill (ZLit 2147467904) 4 249
; MZeroC (ZLit 2147467920) 3
; MCell (ZLit 2147467913) 1 (ZLit 4)
; MFill (ZLit 2147467914) 6 249
; MZeroC (ZLit 2147467928) 4
; MCell (ZLit 2147467923) 1 (ZLit 1)
; MFill (ZLit 2147467924) 4 249
; MZeroC (ZLit 2147467940) 7
; MCell (ZLit 2147467932) 1 (ZLit 5)
; MFill (ZLit 2147467933) 7 249
; MZeroC (ZLit 2147467952) 2
; MCell (ZLit 2147467947) 1 (ZLit 7)
; MFill (ZLit 2147467948) 4 249
; MZeroC (ZLit 2147467960) 4
; MCell (ZLit 2147467954) 1 (ZLit 6)
; MFill (ZLit 2147467955) 5 249
; MZeroC (ZLit 2147467972) 3
; MCell (ZLit 2147467964) 1 (ZLit 6)
; MFill (ZLit 2147467965) 7 249
; MZeroC (ZLit 2147467980) 3
; MCell (ZLit 2147467975) 1 (ZLit 2)
; MFill (ZLit 2147467976) 4 249
; MZeroC (ZLit 2147467988) 4
; MCell (ZLit 2147467983) 1 (ZLit 5)
; MFill (ZLit 2147467984) 4 249
; MZeroC (ZLit 2147468000) 4
; MCell (ZLit 2147467992) 1 (ZLit 5)
; MFill (ZLit 2147467993) 7 249
; MZeroC (ZLit 2147468012) 6
; MCell (ZLit 2147468004) 1 (ZLit 5)
; MFill (ZLit 2147468005) 7 249
; MZeroC (ZLit 2147468024) 6
; MCell (ZLit 2147468018) 1 (ZLit 5)
; MFill (ZLit 2147468019) 5 249
; MZeroC (ZLit 2147468036) 5
; MFill (ZLit 2147468030) 6 249
; MZeroC (ZLit 2147468048) 4
; MCell (ZLit 2147468041) 1 (ZLit 1)
; MFill (ZLit 2147468042) 6 249
; MZeroC (ZLit 2147468060) 6
; MCell (ZLit 2147468052) 1 (ZLit 6)
; MFill (ZLit 2147468053) 7 249
; MZeroC (ZLit 2147468072) 6
; MFill (ZLit 2147468066) 6 249
; MZeroC (ZLit 2147468084) 3
; MCell (ZLit 2147468078) 1 (ZLit 4)
; MFill (ZLit 2147468079) 5 249
; MZeroC (ZLit 2147468092) 2
; MFill (ZLit 2147468087) 5 249
; MZeroC (ZLit 2147468100) 5
; MCell (ZLit 2147468094) 1 (ZLit 4)
; MFill (ZLit 2147468095) 5 249
; MZeroC (ZLit 2147468112) 4
; MCell (ZLit 2147468105) 1 (ZLit 7)
; MFill (ZLit 2147468106) 6 249
; MZeroC (ZLit 2147468120) 2
; MFill (ZLit 2147468116) 4 249
; MZeroC (ZLit 2147468128) 4
; MCell (ZLit 2147468122) 1 (ZLit 6)
; MFill (ZLit 2147468123) 5 249
; MZeroC (ZLit 2147468140) 10
; MCell (ZLit 2147468132) 1 (ZLit 5)
; MFill (ZLit 2147468133) 7 249
; MZeroC (ZLit 2147468156) 9
; MFill (ZLit 2147468150) 6 249
; MZeroC (ZLit 2147468172) 3
; MCell (ZLit 2147468165) 1 (ZLit 1)
; MFill (ZLit 2147468166) 6 249
; MZeroC (ZLit 2147468180) 5
; MCell (ZLit 2147468175) 1 (ZLit 1)
; MFill (ZLit 2147468176) 4 249
; MZeroC (ZLit 2147468192) 3
; MCell (ZLit 2147468185) 1 (ZLit 3)
; MFill (ZLit 2147468186) 6 249
; MZeroC (ZLit 2147468200) 2
; MCell (ZLit 2147468195) 1 (ZLit 4)
; MFill (ZLit 2147468196) 4 249
; MZeroC (ZLit 2147468208) 7
; MCell (ZLit 2147468202) 1 (ZLit 7)
; MFill (ZLit 2147468203) 5 249
; MZeroC (ZLit 2147468220) 4
; MCell (ZLit 2147468215) 1 (ZLit 6)
; MFill (ZLit 2147468216) 4 249
; MZeroC (ZLit 2147468232) 24
; MCell (ZLit 2147468224) 1 (ZLit 1)
; MFill (ZLit 2147468225) 7 249
; MZeroC (ZLit 2147468264) 1
; MCell (ZLit 2147468256) 1 (ZLit 4)
; MFill (ZLit 2147468257) 7 249
; MZeroC (ZLit 2147468272) 4
; MCell (ZLit 2147468265) 1 (ZLit 5)
; MFill (ZLit 2147468266) 2 249
; MZeroC (ZLit 2147468284) 8
; MCell (ZLit 2147468268) 1 (ZLit 1)
; MFill (ZLit 2147468269) 3 249
; MCell (ZLit 2147468276) 1 (ZLit 4)
; MFill (ZLit 2147468277) 7 249
; MZeroC (ZLit 2147468300) 63532
; MCell (ZLit 2147468292) 1 (ZLit 6)
; MFill (ZLit 2147468293) 3 249
; MZeroC (ZLit 2147532240) 700464
; MCell (ZLit 2147468296) 1 (ZLit 1)
; MFill (ZLit 2147468297) 3 249
; MFill (ZLit 2147531832) 408 249
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
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904)) 8 (ZLit 647616)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19912)) 8 (ZLit 0)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920)) 8 (ZLit 647680)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19928)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19904))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936)) 8 (ZLit 647744)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19944)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19920))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952)) 8 (ZLit 647808)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19960)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19936))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968)) 8 (ZLit 647872)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19976)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19952))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984)) 8 (ZLit 647936)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19992)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19968))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000)) 8 (ZLit 648000)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20008)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 19984))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016)) 8 (ZLit 648064)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20024)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20000))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032)) 8 (ZLit 648128)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20040)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20016))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048)) 8 (ZLit 648192)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20056)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20032))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064)) 8 (ZLit 648256)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20072)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20048))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080)) 8 (ZLit 648320)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20088)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20064))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096)) 8 (ZLit 648384)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20104)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20080))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20112)) 8 (ZLit 648448)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20120)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20096))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20128)) 8 (ZLit 648512)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20136)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20112))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20144)) 8 (ZLit 648576)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20152)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20128))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20160)) 8 (ZLit 648640)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20168)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20144))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20176)) 8 (ZLit 648704)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20184)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20160))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20192)) 8 (ZLit 648768)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20200)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20176))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20208)) 8 (ZLit 648832)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20216)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20192))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20224)) 8 (ZLit 648896)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20232)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20208))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20240)) 8 (ZLit 648960)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20248)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20224))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20256)) 8 (ZLit 649024)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20264)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20240))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20272)) 8 (ZLit 649088)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20280)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20256))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20288)) 8 (ZLit 649152)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20296)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20272))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20304)) 8 (ZLit 649216)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20312)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20288))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20320)) 8 (ZLit 649280)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20328)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20304))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20336)) 8 (ZLit 649344)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20344)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20320))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20352)) 8 (ZLit 649408)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20360)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20336))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20368)) 8 (ZLit 649472)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20376)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20352))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20384)) 8 (ZLit 649536)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20392)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20368))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20400)) 8 (ZLit 649600)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20408)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20384))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20416)) 8 (ZLit 649664)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20424)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20400))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20432)) 8 (ZLit 649728)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20440)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20416))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20448)) 8 (ZLit 649792)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20456)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20432))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20464)) 8 (ZLit 649856)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20472)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20448))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20480)) 8 (ZLit 649920)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20488)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20464))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20496)) 8 (ZLit 649984)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20504)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20480))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20512)) 8 (ZLit 650048)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20520)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20496))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20528)) 8 (ZLit 650112)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20536)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20512))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20544)) 8 (ZLit 650176)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20552)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20528))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20560)) 8 (ZLit 650240)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20568)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20544))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20576)) 8 (ZLit 650304)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20584)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20560))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20592)) 8 (ZLit 650368)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20600)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20576))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20608)) 8 (ZLit 650432)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20616)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20592))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20624)) 8 (ZLit 650496)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20632)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20608))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20640)) 8 (ZLit 650560)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20648)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20624))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20656)) 8 (ZLit 650624)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20664)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20640))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20672)) 8 (ZLit 650688)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20680)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20656))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20688)) 8 (ZLit 650752)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20696)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20672))
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20704)) 8 (ZLit 650816)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20712)) 8 (ZAdd (ZMul (ZLit 4096) (ZV 78)) (ZLit 20688))
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
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 48)) 8 (ZLit 6118408)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 56)) 8 (ZLit 6118628)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 64)) 8 (ZLit 6116568)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 72)) 8 (ZMul (ZLit 4096) (ZV 377))
; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 80)) 3088
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3168)) 1 (ZLit 0)
; MZero (ZAdd (ZMul (ZLit 4096) (ZV 227)) (ZLit 3169)) 927
; MWr (ZAdd (ZMul (ZLit 512) (ZV 227)) (ZLit 2147450880)) 512
; MWr (ZMul (ZLit 4096) (ZV 228)) 65536
; MCell (ZMul (ZLit 4096) (ZV 228)) 8 (ZLit 627768)
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
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 310)) (ZLit 24)) 8 (ZLit 6116560)
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
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 8)) 8 (ZLit 259204)
; MWr (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
; MZero (ZAdd (ZMul (ZLit 512) (ZV 454)) (ZLit 2147450880)) 1048576
; MWr (ZMul (ZLit 4096) (ZV 471)) 4096
; MCell (ZMul (ZLit 4096) (ZV 471)) 8 (ZLit 12297829379609722881)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 8)) 8 (ZLit 647616)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 16)) 8 (ZLit 650816)
; MZero (ZAdd (ZMul (ZLit 4096) (ZV 471)) (ZLit 24)) 4072
; MWr (ZAdd (ZMul (ZLit 512) (ZV 471)) (ZLit 2147450880)) 512
].
Definition both_pure_facts : list pfact := [
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
MCell (ZLit 1524744) 8 (ZLit 3)
; MCell (ZLit 1524768) 4 (ZLit 3)
; MCell (ZLit 3840988) 4 (ZLit 1)
; MImg 1524776 3840988
; MImg 3840992 5784600
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 18194018707084711409)
; MCell (ZMul (ZLit 4096) (ZV 454)) 8 (ZLit 2)
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 16)) 8 (ZLit 264148)
; MZero (ZAdd (ZMul (ZLit 4096) (ZV 454)) (ZLit 24)) 8388584
].
Definition both_mem_facts_w2 : list mfact := [
MCell (ZLit 1524744) 8 (ZLit 2)
; MCell (ZLit 1524768) 4 (ZLit 2)
; MCell (ZLit 5398088) 4 (ZLit 1)
; MImg 1524776 5398088
; MImg 5398092 5784600
; MCell (ZAdd (ZMul (ZLit 4096) (ZV 453)) (ZLit 16)) 8 (ZLit 4602097575695124108)
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
Definition both_totsz : Z := 17729664548864.
Definition both_ylo : Z := 23387528589312.
Definition both_eager : Z := 16515072.
Definition both_abytes : Z := 2460728320.
Definition both_mem_hints_w1 : list N := [3; 2; 575; 574; 573; 570; 563; 569; 584; 562; 549; 552; 551; 550; 399; 400; 548; 547; 546; 545; 544; 540; 542; 541; 543; 694; 660; 659; 693; 688; 675; 687; 686; 685; 684; 692; 691; 690; 689; 682; 622; 683; 681; 680; 674; 679; 678; 677; 676; 695; 1; 6; 5; 202; 231; 0; 594; 608; 593; 595; 597; 596; 621; 620; 591; 589; 592; 611; 538; 539; 306; 762; 618; 706; 619; 565; 564; 307; 314; 313; 312; 311; 309; 308; 310; 495; 501; 494; 456; 468; 466; 498; 497; 496; 493; 492; 491; 500; 490; 499; 515; 514; 513; 342; 512; 511; 430; 434; 433; 346; 438; 437; 436; 506; 505; 504; 503; 502; 510; 509; 508; 507; 696; 9; 609; 585; 760; 661; 705; 612; 614; 623; 624; 625; 626; 627; 628; 629; 630; 631; 632; 633; 634; 635; 636; 637; 638; 639; 640; 641; 642; 643; 644; 645; 646; 647; 648; 649; 650; 651; 652; 653; 654; 655; 656; 657; 658; 615; 401; 616; 617; 532; 396; 537; 259; 240; 239; 260; 284; 263; 283; 264; 669; 668; 667; 666; 673; 672; 671; 670; 665; 317; 324; 323; 322; 321; 319; 318; 320; 315; 316; 325; 664; 663; 662; 796; 791; 790; 786; 789; 785; 779; 772; 771; 770; 775; 777; 425; 590; 773; 774; 768; 780; 347; 402; 781; 782; 769; 942; 533; 536; 535; 534; 792; 778; 795; 788; 784; 783; 787; 793; 794; 337; 330; 334; 335; 326; 327; 328; 329; 333; 587; 588; 586; 426; 610; 761; 613; 941; 842; 843; 844; 845; 846; 847; 848; 849; 850; 851; 852; 853; 854; 855; 856; 857; 858; 859; 860; 861; 862; 863; 864; 865; 866; 867; 868; 869; 870; 871; 872; 873; 874; 875; 876; 877; 878; 879; 880; 881; 882; 883; 884; 885; 886; 887; 888; 889; 890; 891; 892; 895; 896; 897; 898; 899; 900; 901; 902; 903; 904; 905; 906; 907; 908; 909; 910; 911; 912; 913; 914; 915; 916; 917; 918; 919; 920; 921; 922; 923; 924; 925; 926; 927; 928; 929; 930; 931; 932; 933; 934; 935; 936; 937; 938; 939; 940; 840; 841; 839; 709; 710; 204; 205; 711; 199; 200; 712; 195; 196; 192; 713; 714; 188; 189; 715; 184; 185; 716; 180; 181; 717; 176; 177; 718; 172; 173; 719; 168; 169; 720; 164; 165; 721; 161; 722; 157; 158; 723; 153; 154; 724; 149; 150; 725; 145; 146; 726; 141; 142; 727; 137; 138; 728; 133; 134; 729; 129; 130; 730; 125; 126; 731; 121; 122; 732; 117; 118; 733; 113; 114; 734; 109; 110; 735; 105; 106; 736; 102; 737; 98; 99; 738; 94; 95; 739; 91; 740; 87; 88; 741; 84; 742; 80; 81; 743; 76; 77; 744; 73; 745; 69; 70; 746; 65; 66; 747; 62; 748; 58; 59; 749; 54; 55; 750; 50; 51; 751; 46; 47; 752; 42; 43; 753; 38; 39; 754; 34; 35; 755; 30; 31; 756; 26; 27; 757; 22; 23; 18; 19; 758; 14; 15; 759; 10; 11; 4; 814; 797; 763; 764; 765; 766; 767; 815; 816; 817; 818; 819; 820; 821; 822; 823; 824; 825; 826; 827; 828; 829; 830; 831; 832; 833; 834; 835; 836; 837; 707; 708; 700; 211; 210; 209; 203; 201; 198; 197; 194; 193; 191; 190; 187; 186; 183; 182; 179; 178; 175; 174; 171; 170; 167; 166; 163; 162; 160; 159; 156; 155; 152; 151; 148; 147; 144; 143; 140; 139; 136; 135; 132; 131; 128; 127; 124; 123; 120; 119; 116; 115; 112; 111; 108; 107; 104; 103; 101; 100; 97; 96; 93; 92; 90; 89; 86; 85; 83; 82; 79; 78; 75; 74; 72; 71; 68; 67; 64; 63; 61; 60; 57; 56; 53; 52; 49; 48; 45; 44; 41; 40; 37; 36; 33; 32; 29; 28; 25; 24; 21; 20; 17; 16; 13; 12; 8; 7; 699; 601; 602; 600; 567; 568; 566; 519; 427; 371; 370; 424; 423; 422; 520; 373; 372; 369; 348; 521; 285; 522; 518; 473; 457; 461; 474; 432; 460; 475; 345; 431; 462; 476; 344; 429; 477; 343; 465; 464; 478; 463; 459; 458; 479; 428; 480; 471; 467; 472; 443; 435; 444; 441; 442; 407; 408; 398; 397; 409; 405; 406; 354; 355; 349; 356; 352; 353; 267; 268; 233; 234; 269; 265; 266; 243; 236; 241; 242; 213; 206; 207; 208; 214; 212; 261; 235; 232; 893; 894; 262; 238; 237; 244]%N.
Lemma both_mem_facts_justified_w1 :
forallb (mjustify (s_know (a_ss HS_both2_1)) (var_ranges (s_know (a_ss HS_both2_1))) 65536 6254592) (both_mem_facts ++ both_mem_facts_w1) = true.
Proof. apply (mjust_hints_sound _ _ _ _ _ both_mem_hints_w1). vm_cast_no_check (@eq_refl bool true). Qed.
Definition both_pure_hints_w1 : list N := [798; 806; 807; 808; 812; 813; 799; 809; 810; 811; 800; 776; 702; 604; 579; 571; 556; 524; 482; 446; 411; 384; 287; 287; 358; 293; 293; 292; 291; 291; 290; 289; 271; 246; 216; 288; 288; 572; 801; 802; 803; 804; 805; 376; 375; 599; 577; 554; 377; 517; 378; 470; 379; 440; 380; 404; 382; 351; 298; 302; 304; 300; 374; 698; 603; 605; 606; 582; 560; 530; 488; 454; 420; 394; 367; 281; 257; 229; 578; 580; 581; 559; 529; 487; 453; 419; 393; 366; 280; 256; 228; 555; 557; 558; 528; 486; 452; 418; 392; 365; 279; 255; 227; 523; 525; 526; 527; 485; 451; 417; 391; 364; 278; 254; 226; 481; 483; 484; 450; 416; 390; 363; 277; 253; 225; 445; 447; 448; 449; 415; 389; 362; 276; 252; 224; 410; 412; 413; 414; 388; 361; 275; 251; 223; 383; 385; 386; 387; 357; 359; 360; 274; 250; 222; 297; 296; 296; 295; 295; 294; 270; 272; 273; 249; 221; 245; 247; 248; 220; 215; 217; 218; 219; 701; 703; 704; 607; 583; 561; 531; 489; 455; 421; 395; 368; 282; 258; 230; 598; 576; 553; 516; 469; 439; 403; 381; 350; 299; 303; 305; 301; 697; 286]%N.
Lemma both_pure_facts_justified_w1 :
forallb (pjustify (s_know (a_ss HS_both2_1)) (var_ranges (s_know (a_ss HS_both2_1)))) (both_pure_facts ++ both_pure_facts_w1) = true.
Proof. apply (pjust_hints_sound _ _ _ both_pure_hints_w1). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_vis_justified_w1 :
vis_match (var_ranges (s_know (a_ss HS_both2_1))) (a_vis HS_both2_1) both_vis_app = true /\ vis_match (var_ranges (s_know (a_ss HS_both2_1))) (a_ghost HS_both2_1) both_ghost = true.
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_ledger_justified_w1 :
ledger_xmatch (var_ranges (s_know (a_ss HS_both2_1))) (a_maps HS_both2_1) both_ledger = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_consts_w1 : a_totsz HS_both2_1 = both_totsz /\ a_ylo HS_both2_1 = both_ylo /\ a_eager HS_both2_1 = both_eager /\ a_abytes HS_both2_1 = both_abytes.
Proof. repeat split; reflexivity. Qed.
Definition both_mem_hints_w2 : list N := [3; 2; 574; 573; 572; 569; 562; 568; 583; 561; 548; 551; 550; 549; 398; 399; 547; 546; 545; 544; 543; 539; 541; 540; 542; 693; 659; 658; 692; 687; 674; 686; 685; 684; 683; 691; 690; 689; 688; 681; 621; 682; 680; 679; 673; 678; 677; 676; 675; 694; 1; 6; 5; 202; 231; 0; 593; 607; 592; 594; 596; 595; 620; 619; 590; 588; 591; 610; 537; 538; 305; 761; 617; 705; 618; 564; 563; 306; 313; 312; 311; 310; 308; 307; 309; 494; 500; 493; 455; 467; 465; 497; 496; 495; 492; 491; 490; 499; 489; 498; 514; 513; 512; 341; 511; 510; 429; 433; 432; 345; 437; 436; 435; 505; 504; 503; 502; 501; 509; 508; 507; 506; 695; 9; 608; 584; 759; 660; 704; 611; 613; 622; 623; 624; 625; 626; 627; 628; 629; 630; 631; 632; 633; 634; 635; 636; 637; 638; 639; 640; 641; 642; 643; 644; 645; 646; 647; 648; 649; 650; 651; 652; 653; 654; 655; 656; 657; 614; 400; 615; 616; 531; 395; 536; 258; 239; 238; 259; 283; 262; 282; 263; 668; 667; 666; 665; 672; 671; 670; 669; 664; 316; 323; 322; 321; 320; 318; 317; 319; 314; 315; 324; 663; 662; 661; 795; 790; 789; 785; 788; 784; 778; 771; 770; 769; 774; 776; 424; 589; 772; 773; 767; 779; 346; 401; 780; 781; 768; 941; 532; 535; 534; 533; 791; 777; 794; 787; 783; 782; 786; 792; 793; 336; 329; 333; 334; 325; 326; 327; 328; 332; 586; 587; 585; 425; 609; 760; 612; 940; 841; 842; 843; 844; 845; 846; 847; 848; 849; 850; 851; 852; 853; 854; 855; 856; 857; 858; 859; 860; 861; 862; 863; 864; 865; 866; 867; 868; 869; 870; 871; 872; 873; 874; 875; 876; 877; 878; 879; 880; 881; 882; 883; 884; 885; 886; 887; 888; 889; 890; 891; 894; 895; 896; 897; 898; 899; 900; 901; 902; 903; 904; 905; 906; 907; 908; 909; 910; 911; 912; 913; 914; 915; 916; 917; 918; 919; 920; 921; 922; 923; 924; 925; 926; 927; 928; 929; 930; 931; 932; 933; 934; 935; 936; 937; 938; 939; 839; 840; 838; 708; 709; 204; 205; 710; 199; 200; 711; 195; 196; 192; 712; 713; 188; 189; 714; 184; 185; 715; 180; 181; 716; 176; 177; 717; 172; 173; 718; 168; 169; 719; 164; 165; 720; 161; 721; 157; 158; 722; 153; 154; 723; 149; 150; 724; 145; 146; 725; 141; 142; 726; 137; 138; 727; 133; 134; 728; 129; 130; 729; 125; 126; 730; 121; 122; 731; 117; 118; 732; 113; 114; 733; 109; 110; 734; 105; 106; 735; 102; 736; 98; 99; 737; 94; 95; 738; 91; 739; 87; 88; 740; 84; 741; 80; 81; 742; 76; 77; 743; 73; 744; 69; 70; 745; 65; 66; 746; 62; 747; 58; 59; 748; 54; 55; 749; 50; 51; 750; 46; 47; 751; 42; 43; 752; 38; 39; 753; 34; 35; 754; 30; 31; 755; 26; 27; 756; 22; 23; 18; 19; 757; 14; 15; 758; 10; 11; 4; 813; 796; 762; 763; 764; 765; 766; 814; 815; 816; 817; 818; 819; 820; 821; 822; 823; 824; 825; 826; 827; 828; 829; 830; 831; 832; 833; 834; 835; 836; 706; 707; 699; 211; 210; 209; 203; 201; 198; 197; 194; 193; 191; 190; 187; 186; 183; 182; 179; 178; 175; 174; 171; 170; 167; 166; 163; 162; 160; 159; 156; 155; 152; 151; 148; 147; 144; 143; 140; 139; 136; 135; 132; 131; 128; 127; 124; 123; 120; 119; 116; 115; 112; 111; 108; 107; 104; 103; 101; 100; 97; 96; 93; 92; 90; 89; 86; 85; 83; 82; 79; 78; 75; 74; 72; 71; 68; 67; 64; 63; 61; 60; 57; 56; 53; 52; 49; 48; 45; 44; 41; 40; 37; 36; 33; 32; 29; 28; 25; 24; 21; 20; 17; 16; 13; 12; 8; 7; 698; 600; 601; 599; 566; 567; 565; 518; 426; 370; 369; 423; 422; 421; 519; 372; 371; 368; 347; 520; 284; 521; 517; 472; 456; 460; 473; 431; 459; 474; 344; 430; 461; 475; 343; 428; 476; 342; 464; 463; 477; 462; 458; 457; 478; 427; 479; 470; 466; 471; 442; 434; 443; 440; 441; 406; 407; 397; 396; 408; 404; 405; 353; 354; 348; 355; 351; 352; 266; 267; 233; 234; 268; 264; 265; 242; 236; 240; 241; 213; 206; 207; 208; 214; 212; 260; 235; 232; 892; 893; 261; 237; 243]%N.
Lemma both_mem_facts_justified_w2 :
forallb (mjustify (s_know (a_ss HS_both2_2)) (var_ranges (s_know (a_ss HS_both2_2))) 65536 6254592) (both_mem_facts ++ both_mem_facts_w2) = true.
Proof. apply (mjust_hints_sound _ _ _ _ _ both_mem_hints_w2). vm_cast_no_check (@eq_refl bool true). Qed.
Definition both_pure_hints_w2 : list N := [797; 805; 806; 807; 811; 812; 798; 808; 809; 810; 799; 775; 701; 603; 578; 570; 555; 523; 481; 445; 410; 383; 286; 286; 357; 292; 292; 291; 290; 290; 289; 288; 270; 245; 216; 287; 287; 571; 800; 801; 802; 803; 804; 375; 374; 598; 576; 553; 376; 516; 377; 469; 378; 439; 379; 403; 381; 350; 297; 301; 303; 299; 373; 697; 602; 604; 605; 581; 559; 529; 487; 453; 419; 393; 366; 280; 256; 229; 577; 579; 580; 558; 528; 486; 452; 418; 392; 365; 279; 255; 228; 554; 556; 557; 527; 485; 451; 417; 391; 364; 278; 254; 227; 522; 524; 525; 526; 484; 450; 416; 390; 363; 277; 253; 226; 480; 482; 483; 449; 415; 389; 362; 276; 252; 225; 444; 446; 447; 448; 414; 388; 361; 275; 251; 224; 409; 411; 412; 413; 387; 360; 274; 250; 223; 382; 384; 385; 386; 356; 358; 359; 273; 249; 222; 296; 295; 295; 294; 294; 293; 269; 271; 272; 248; 221; 244; 246; 247; 220; 215; 217; 218; 219; 700; 702; 703; 606; 582; 560; 530; 488; 454; 420; 394; 367; 281; 257; 230; 597; 575; 552; 515; 468; 438; 402; 380; 349; 298; 302; 304; 300; 696; 285]%N.
Lemma both_pure_facts_justified_w2 :
forallb (pjustify (s_know (a_ss HS_both2_2)) (var_ranges (s_know (a_ss HS_both2_2)))) (both_pure_facts ++ both_pure_facts_w2) = true.
Proof. apply (pjust_hints_sound _ _ _ both_pure_hints_w2). vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_vis_justified_w2 :
vis_match (var_ranges (s_know (a_ss HS_both2_2))) (a_vis HS_both2_2) both_vis_app = true /\ vis_match (var_ranges (s_know (a_ss HS_both2_2))) (a_ghost HS_both2_2) both_ghost = true.
Proof. split; vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_ledger_justified_w2 :
ledger_xmatch (var_ranges (s_know (a_ss HS_both2_2))) (a_maps HS_both2_2) both_ledger = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma both_consts_w2 : a_totsz HS_both2_2 = both_totsz /\ a_ylo HS_both2_2 = both_ylo /\ a_eager HS_both2_2 = both_eager /\ a_abytes HS_both2_2 = both_abytes.
Proof. repeat split; reflexivity. Qed.
