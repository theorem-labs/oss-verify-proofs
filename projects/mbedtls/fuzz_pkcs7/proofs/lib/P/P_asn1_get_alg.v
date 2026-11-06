(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk AStep CellsX Asn1Aux X509Aux X509AuxB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import PImg.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_asn1_get_tag P_platform_zeroize P_asn1_get_alg_A P_asn1_get_alg_B P_asn1_get_alg_C.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac.
Import OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P00c60cc38c13302b 0 3 0 1 1 1 28 1P01f11dfbb42657c6 0 4 0 1 24 1 34 1 35 1P02d88cd7cfde274d 2 20 0 5 0 1 2 1 21 1 29 1 30 1 0 4 0 1 1 1 29 1 30 1P04c6050a3d1e09de 0 4 0 1 21 1 29 1 30 1P053e9e151a882bf5 2 19 0 5 0 1 3 1 22 1 30 1 31 1 0 4 0 1 2 1 30 1 31 1P069f70987b6ba26b 0 2 0 1 24 1P0caa3c873a144832 0 3 0 1 1 1 23 1P0ec0cd1ae097d5ae 0 5 0 1 26 1 27 1 28 1 29 1P0f3f382b46dddf74 0 2 0 1 2 1P100127b20babe6ee 2 26 0 5 0 1 1 1 25 1 33 1 34 1 0 4 0 1 2 1 33 1 34 1P10a617d3a2dd28ce 0 5 0 1 25 1 26 1 27 1 28 1P13f5c01da4b60035 0 4 0 1 19 1 27 1 28 1P15fdbe953820cf28 0 2 0 1 35 1P1917631f3cc39dce 0 2 0 1 31 1P19cfa7951bfeba6e 2 28 0 5 0 1 1 1 27 1 39 1 40 1 0 4 0 1 2 1 39 1 40 1P1c2c899f06e63fce 2 21 0 5 0 1 2 1 21 1 29 1 30 1 0 4 0 1 1 1 29 1 30 1P1f713b8b5c3783bb 0 5 0 1 20 1 21 1 22 1 23 1P21895078adeeab34 0 3 0 1 4 1 27 1P25a15ccb05650714 0 2 0 1 1 1P26c14aa7490df875 0 2 0 1 28 1P2d7b6e6d2bb1c492 0 4 0 1 24 1 32 1 33 1P2f2dfc360f7f74e7 0 2 0 1 5 1P30753e19f235315f 0 2 0 1 29 1P3181d8d66a05f358 0 4 0 1 25 1 37 1 38 1P338c88dda9895fa5 0 2 0 1 2 1P339de1f00d8f510d 0 2 0 1 1 1P366b180376a761ec 0 2 0 1 2 1P38e82665ebec7220 0 2 0 1 34 1P3a125753b8268ef1 0 2 0 1 13 1P3b021fe9bdd3f536 0 2 0 1 5 1P3d449d482c792a61 0 2 0 1 1 1P3d774a5822995f76 2 22 0 5 0 1 2 1 21 1 29 1 30 1 0 4 0 1 1 1 29 1 30 1P3df4065e053d6ead 2 26 0 5 0 1 1 1 25 1 33 1 34 1 0 4 0 1 2 1 33 1 34 1N0038546bfc4a357bN0041918196cd3febN004f07d8195066d9N0052e0ee449a7e65N006ef3829447d2e2N009d74c9fcce76f8N00cfdd3bdf7dae49N00d4eb5d5e426793N0107e0cbf8ceffe4N014b2e54078e396dN01653e23bd3c0a52N0186ef477af30e2bN02af14d542128743N033ceb39eafeb447N036c478a1cfefed3N0376e1a3a3698013N0394eb20887e15f9N03e0ae6cbc875783N04249a1d211803aaN04496f55c7dd72cfN044d09494be2c85cN0482bbbdb1a3110bN049212fb2ba46105N04b0740202426c35N04c0d1e9feb78c5cN0534b97c1247725aN05cedfdd4f7ba4d5N05dfbcdea330226aN0606ae3944deb5a6N068e29e6e8f7b548N069a3366900eb410N06a2ae1f1cf43443N06c25f4953266f95N06ec6f5a143cfdf1N071f8c8e05ab483eN072f6fcba4ff805bN0762ad83d5132471N07beb9944a54c022N0812c770862aefabN0825f49c99f629b4N0826e87b51e68dcbN08a82e745c81b557N08fb9b54fdf2978bN092d025f679fdafcN0964529b1fe47bbbN098fd95b28d34ba6N099e01dd8e259f4fN09f7e32e6ed83be0N0a004753d76c2dceN0a4188a111a2eeaaN0a4971b9a665ee1aN0a9222b747cb3df1N0a965175bfbc6585N0a9b03f1cfa57a9fN0aaaad252eefba56N0acc454809e492d8N0ad93d98716919a9N0b424f069081566dN0be93c6844318b0bN0c324c4e7dae7eccN0c431df234d9051fN0cd518938b63ddd6N0cd985dfd5d8e57bN0d352c41b5e627a3N0d53ae6c9f890deaN0d61ad44b96388c4N0d72df43c9fb6c5cN0da8128dec1d335bN0dae9b8f0a3ca179N0de0f6af678d23c2N0e019242324ca302N0e084b8b3247a158N0e45d5d69d709644N0e70b4d1923e1d00N0e7102f1d94fb498N0e74a52de08d65dbN0ea8d2cb67293de8N0eb09e888f5661c5N0ec705c37925b48bN0ed88660493e63f6N0f99cb5ac65c949aN0fed81099d5e087dN0feefc85cd88c2ffN10fdcc8aac0a73f2N115a02c0218444b1N118821e359648c87N119a318b3a4e6806N11a5abc689670da0N11f987aec58f6f1cN12049105798b91beN120c35533d88fa0fN1213c6f35f23e759N122b7d5dcaa28c10N125e0569715e9073N1275a3b19d6dc0eaN1281d3c71fb065faN12998862b2f436f7N12ad73e2ad9b0c75N12ceece91f29a15bN130aba7197a3fec4N136e11e02e81f638N142ff6dd30a31492N147bb17b4dbb4a2fN1485e5b1b0b429cbN149f76d4569769beN14f7b044cb99b3e5N152487854ea9e97fN1528cfa8b577325aN152c00c8955a9de7N16ab3f38ceb760e2N1721c6f2bb54d8f8N1738535b743ff824N173b2f6733cc5952N1744f1ec6cf23081N17637311dc393b47N182cb9719d98bfedN18436c553b723e10N184c85b7bd50bf9bN1885267d95812724N188e945fead1206fN18c98f80b0dcdc76N18d42ff45cfbf388N18d628c1277dab35N18d892fb1f0cd54eN193d23530dda5e5dN1963d81b4c10e0b6N198b27abd40c414cN19b9aec6833504c6N19cdd8518cfdfa32N1a32881aec76e24fN1a6d6c629304b576N1ab7c49b8a218928N1ac1a2b567b7731aN1ad0f2765392abaaN1af8c2dc0721f198N1b1352162fa7d8eeN1b681d602ae6ac59N1ba22530f1f6156dN1be2ecca6132a0deN1be8b44e3a300226N1bf5e9f391e54e46N1bf7ba930390c0cbN1c406d19798877d8N1c65cf8ca05ecb2aN1cb62f82a497d081N1cc6b2dacd5a36d2N1cd0f0e037a59290N1cd15d61499ec177N1cead9355b96f964N1d0dde5dffbb6121N1d4595e60bf5ac79N1d4bddf84d8a6f46N1d95d37a5b4e6ea6N1d9ee62121893aafN1ddb2f814134a88bN1de535efcf50d6e9N1e3bd9b1759f499eN1ed52bde0672605cN1edbfe0e29b7a657N1ef9517411d1a160N1f1ea99721f91805N1f3a15ae50f9eb8aN1f61bb2ead8b0335N1f798ec385c7f65dN1fa439e34601263eN1fd0798e6440cd36N1fd1723b2de61142N1fe9ad78f460f7d7N2025a15a2e46a15bN202ccdbeb68ba5daN206970d52f7627f7N20925831ea902d91N20a472943c68d72eN20b82a55a305e3b9N2136cdd53c5cc3f8N219e4f83ec3b8c1dN2213db9adc320ef7N22e7d0fcfa45dc44N230320f685f7286eN2303ba2e7d25e42cN23077ab9a474f91fN23188482a2c08289N2367f1ed94664e5fN238fbfa529637332N239f67c1947fb4a4N23c03b38d0868b0dN23c06a108d111a44N23c0717eb0e61b53N23f30df6a0a4c2e3N2428a4fc0dc78dffN248d6e3133d9e4fdN249d9d342d1a9383N24edfb414b84ff39N24f775dcb1e9e879N2533f1f4de32c716N254dce6097fcad53N2553369b955fd079N25771b19dcf39055N259db1b478d2ab07N25b5d7946e1e1684N25de2ffe2153e7ceN25e70137bca40edbN25ec61b36653fd96N25f8e5614d438627N260694053adfab54N260d4a3e5a766430N26aacae0a6852ffaN26b7b298bd5863fdN27111ad81c16a24bN272b18e805f2dfdfN273b6c75441bf73eN278caa6592049a29N27b21a084faf2d02N27d97557053bac2eN27f283e3d01c2e75N27f49da57a05204bN28519dfd110f2dd8N285da9ae667d8837N287d20aabb769432N2941fc4501f9d60dN296ad4e915b6f646N296ce494b91a2f1bN297ba123465f23ddN29903f6797b9f9dcN29f9be98a91e14e9N2a000863d4495f8bN2a810e90b85966ffN2b193213de4d8580N2b3c128561f27ef0N2b674ac1708b57d7N2b9797f4be0e0d72N2bc724703b2afeb6N2be9a67bfd93a766N2c0a53db09effa16N2c182c51b7f868f3N2c3bb3a95e57f0a9N2c4f5a100621a576N2c4f8564b5853a90N2d320eaa8a7d3182N2d70b8eefe427113N2dd55e1c694a4d97N2df2bbe9d096e807N2e2cc022c84d28abN2e361fdaed26072dN2e6faa728e58e390N2e715d8c0c6b1242N2e8919bfe35e6ccbN2f3f4cbc064443b6N2fb03ac346c471a8N2fded97ffe5cc2dcN301b9ee9301b1013N305ac300b2318cf6N309a00a1df17464fN30c47badfeaecce3N30e2ec9638671f77N30ff939a3b49fed6N3105a0aee57d57c4N315642a7f7f7e24dN318a3d58cca22b1cN31c252e77042c37dN31e4afbafe4bd802N3217dcdeb598ffb8N321f9a14f877a7fbN32259dfd771c3b08N32399c335b86b981N324c8f92a2daa3d3N3253e43ba495b7efN326de289f6548a61N329f54b207b26669N32a5e97ab4b6314dN32d1431a10a7480eN32ff3b9654822d41N33059335c2ecfd3fN3347a9b33d25e6c6N33686bef9a69db5dN33939666dff6379eN33abfcbe6d7c7758N33e2d386bdd3c2d1N34639af21d004973N347a0f57e012b185N3490b5be31fcde7fN34f9214d77207b21N351b2758793b6865N3524deb1e6076735N35e5b560c812da12N35f077c37679aacfN360f62e2ecfc3963N36476216fb98f135N36cdebc0167a3161N36f260434949dfedN36f6f32aed5911e0N370c1928b7d4f929N37587fe380804d9aN37cf9a59710df4a6N37cfcd4bb9612d3aN37eb08f06b5c63c1N380774c403d402e9N38078355aea52336N380c1be8c33c97bcN3835b53b11a8bd8bN385c7574fe43b6d9N387f68e5e1e350f6N388e855c336def99N38b56c4a08b25795N392365c7f2cb689eN39264f529834d305N394ded1f92c95696N39793a7e4f80a44cN3984c3c518b96e69N39b602c45721f364N39f5a46e5bfc0850N3a199a2c5b9a4fd2N3aa4f9b27243ac0cN3aee23ed368e94eeN3b74ebc205c3a583N3bb1b4b405cb055bN3bbacd8f163e6b99N3c673203892a259aN3cb0001a1e73be5fN3ce548571c46215cN3d118069a0016d94N3d392713dde72717N3d6e30da5e637db3N3dbb1a94109a6b4cN3dd90e8c96d9e78cN3df1726506782476N3e81f809e26b3d1eN3ed6ea70ba420c83N3ed9d99cf68cececN3ee025d3a1fcc2a9N3efda6a7fcfeccf7N3f2e1ef9c6e21d9bN3f557a38614c68bcN3fc57bc1dcd054e8N3fd4769030b0fa27"%lxh.
Import ListNotations.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac lia_nodisj ::= orc_dlia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Walk.
  Variable L : heap_layout.
  Hypothesis HZ : platform_zeroize_stmt psegs L P_PLATFORM_ZEROIZE P_MEMSET_FUNC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (PP ALG PAR P END BUF lo : Z) (bs : list byte).
  Hypothesis B1 : BUF <= P.
  Hypothesis B3 : END <= BUF + Z.of_nat (length bs).
  Hypothesis B4 : BUF + Z.of_nat (length bs) < 2^63.
  Hypothesis D1 : PP + 8 <= ALG \/ ALG + 24 <= PP.
  Hypothesis D1b : PP + 8 <= PAR \/ PAR + 24 <= PP.
  Hypothesis D1c : ALG + 24 <= PAR \/ PAR + 24 <= ALG.
  Hypothesis D2 : PP + 8 <= BUF \/ BUF + Z.of_nat (length bs) <= PP.
  Hypothesis D3 : ALG + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= ALG.
  Hypothesis D3b : PAR + 24 <= BUF \/ BUF + Z.of_nat (length bs) <= PAR.
  Hypothesis PPB : 0 <= PP /\ PP + 8 <= 2^64.
  Hypothesis ALGB : 0 <= ALG /\ ALG + 24 <= 2^64.
  Hypothesis PARB : 0 <= PAR /\ PAR + 24 <= 2^64.
  Hypothesis BUF0 : 0 <= BUF.
  Hypothesis NZ3 : 0 < PAR.
  Hypothesis SLO : lo <= bv_unsigned sp - 64.
  Hypothesis ACL : alloc_ceiling <= lo.
  Hypothesis ACP : 4096 < alloc_ceiling.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis DS1 : PP + 8 <= lo \/ bv_unsigned sp <= PP.
  Hypothesis DS2 : ALG + 24 <= lo \/ bv_unsigned sp <= ALG.
  Hypothesis DS3 : PAR + 24 <= lo \/ bv_unsigned sp <= PAR.
  Hypothesis DS4 : BUF + Z.of_nat (length bs) <= lo \/ bv_unsigned sp <= BUF.
  Hypothesis CA : const_at L P_MEMSET_FUNC 8.
  Hypothesis DHI : hl_data_hi L <= alloc_ceiling.
  Hypothesis OD1 : PP + 8 <= hl_data_lo L \/ hl_data_hi L <= PP.
  Hypothesis OD2 : ALG + 24 <= hl_data_lo L \/ hl_data_hi L <= ALG.
  Hypothesis OD3 : PAR + 24 <= hl_data_lo L \/ hl_data_hi L <= PAR.
  Hypothesis SPB : bv_unsigned sp < 2^64.

  Notation W := [(PP, PP + 8); (ALG, ALG + 24); (PAR, PAR + 24); (bv_unsigned sp - ASN1_GET_ALG_STACK, bv_unsigned sp)].
  Notation POST := (asn1_get_alg_post psegs L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc PP ALG PAR P END BUF lo m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00U0?L20433961190.92L24780512698.84L25636474627.99L25636484149.92L29736098495.91L29736100233.98L38892891850.91L39385962213.92L39385968083.99L39457292955.83L39457293209.87L39457293209.90L39457293334.78L39459391378.92L42148661401.2 L42812834613.88L42814931121.74L42814932798.83L43061775753.90L47832315070.86L48148060671.91L49921689324.83L49921689324.86L49923785447.88L52753416298.79L52753417959.74L53792479276.4 L58974787136.88L58974793078.95L60929871484.79L64819221669.99L64819228563.92L68316749683.95L68316750917.88L8806420828.28 L8806420828.29 L8806420828.30 00000700U01701V02602Y03:03[04?05105c06U07G08908@08U08j09?09M09b0:?0:]0;;0;Y0<70<U0<a0==0=\0>10>T0?40?W0@70A80B90C:S2sp2bsS2sp1P3END2bs1j2j03LXJ4LXJ02H7S2sp2PP3BUF2bs2D21j2j03LXJ4LXJ02nnS2sp2PP3BUF2bs2D21j2j03LXJ4LXJ0S2sp3BUF2lo2bs3DS41j2j03LXJ4LXJ0S2sp3BUF2lo2bs3DS41j2j03LXJ4LXJ02nnS2sp1P3END2bs1j2j03LXJ4LXJ02nn2H5S2sp3PAR3BUF2bs3D3b1j2j03LXJ4LXJ0S2sp3PAR3BUF2bs3D3b1j2j03LXJ4LXJ02nnS2sp1P3BUF2bs4alen3apw4ptag4plen3ppw1j2j03LXJ4LXJ0S2sp1P3BUF2bs4alen3apw4ptag4plen3ppw1j2j03LXJ4LXJ0S2sp1P3BUF2bs4alen3apw4ptag4plen3ppw1j2j03LXJ4LXJ0S2sp1P3BUF2bs4alen3apw4ptag4plen3ppw1j2j03LXJ4LXJ0S2sp1P3BUF2bs4alen3apw4ptag4plen3ppw1j2j03LXJ4LXJ0S2nn2HNS2sp2bs1j2j03LXJ4LXJ0S2sp2bs1j2j03LXJ4LXJ0S2sp2bs1j2j03LXJ4LXJ0S2sp2lo2bs3SLOS2sp2bs1j2j03LXJ4LXJ0S2sp1P2bs1j2j03LXJ4LXJ02nn2HNS2sp1P3END2bs1j2j03LXJ4LXJ02H9S2sp1P3END2bs1j2j03LXJ4LXJ02H8S2sp1P3END2bs1j2j03LXJ4LXJ02H9S2sp1P3END2bs2B21j2j03LXJ4LXJ0S2sp1P3END2bs2B21j2j03LXJ4LXJ0S4lxv02nn2H6S2sp3BUF2bs2B41j2j03LXJ4LXJ0S2sp3BUF2bs2B41j2j03LXJ4LXJ02nnS2sp2bs1j2j03LXJ4LXJ0S2sp3ALG3BUF2bs2D31j2j03LXJ4LXJ02nnS2sp3ALG3BUF2bs2D31j2j03LXJ4LXJ0S2sp3END3BUF2bs2B31j2j03LXJ4LXJ02nnS2sp3END3BUF2bs2B31j2j03LXJ4LXJ0S1L2sp2PP3ALG3PAR2lo2bs3SLO3ACL3DS13DS23DS33DHI3OD13OD23OD32aa2HaS1L2sp2PP3ALG3PAR2lo2bs3SLO3ACL3DS13DS23DS33DHI3OD13OD23OD32aa2HaS1L2sp2PP3ALG3PAR2lo2bs3SLO3ACL3DS13DS23DS33DHI3OD13OD23OD32aa2Ha". (* [comment removed for export] *)
  Lemma main_walk : forall (atag apad alen apw ptag ppad plen ppw x5 x6 x7 x14 x15 x16 x17 : word),
    P <= END ->
    rw_cells psegs m PP [C8 (Z_to_bv 64 P)] ->
    rw_cells psegs m ALG [C4 atag; C4 apad; C8 alen; C8 apw] ->
    rw_cells psegs m PAR [C4 ptag; C4 ppad; C8 plen; C8 ppw] ->
    bytes_at psegs m BUF bs -> stk psegs m lo (bv_unsigned sp) -> statics_ok psegs L m -> mem_inv psegs m ->
    evt psegs POST
      (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 PP) (Z_to_bv 64 END) (Z_to_bv 64 ALG) (Z_to_bv 64 PAR) x14
              x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1e7b4) fc None m (seg_rom psegs)).
  Proof.
  intros atag apad alen apw ptag ppad plen ppw x5 x6 x7 x14 x15 x16 x17 B2 HPP HALG HPAR HBUF ST SOK MI.
  pose proof (munch_refl W m) as MU.
  pose proof (wmono_refl psegs m) as WM.
  pose proof (proj1 ST) as LO0.
  carve_frame 16%nat ST.
  lxp_split_frame [8;8]%nat. lxp_seps 16.
  lxp_run (PLAN [0x1e7fc; 0x1e848; 0x1e898; 0x1e910; 0x1e968; 0x1e9dc; 0x242bc] [] 171%N).
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    lxp_longform nn.
    lxp_apply loop1_walk.  (* [comment removed for export] *)
  }
  { (* [comment removed for export] *)
    lxp_ret.
  }
  { (* [comment removed for export] *)
    first [ solve [ lxp_apply j1_walk ] | solve [ eapply j1_walk with (p1 := P + 2); lxp_apply_post ] | lxp_apply j1_walk ].  (* [comment removed for export] *)
  }
Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Lemma P_asn1_get_alg_spec : forall L, platform_zeroize_stmt psegs L P_PLATFORM_ZEROIZE P_MEMSET_FUNC ->
  asn1_get_alg_stmt psegs L P_ASN1_GET_ALG P_MEMSET_FUNC.
Proof.
  intros L HZ. unfold asn1_get_alg_stmt, P_ASN1_GET_ALG.
  intros until ppw. intros HPP HALG HPAR HBUF B1 B2 B3 B4 D1 D1b D1c D2 D3 D3b AL1 AL2 AL3 NZ1 NZ2 NZ3 NZ4 ST SLO ACL SPA DS1 DS2 DS3 DS4
         SOK CA DHI OD1 OD2 OD3 MI -> -> -> ->.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB. pose proof (rw_cells_bound _ _ _ _ HALG) as ALGB. pose proof (rw_cells_bound _ _ _ _ HPAR) as PARB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add] in PPB, ALGB, PARB.
  pose proof (proj1 HBUF) as BUF0. pose proof alloc_ceiling_pos as ACP.
  pose proof (bv_unsigned_in_range 64 sp) as SPB. unfold bv_modulus in SPB. cbn in SPB.
  eapply main_walk; try eassumption; try nia.
Qed.
