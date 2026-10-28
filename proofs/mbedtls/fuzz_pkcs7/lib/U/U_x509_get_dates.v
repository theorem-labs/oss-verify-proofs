(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk Asn1Aux X509Aux AStep CellsX Cells Mem.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep RepCrt CrtStmts CrtParseStmts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_asn1_get_tag U_x509_get_time.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPTac. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXU Require Import LxU_Sums3.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxP_Flat.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Ltac is_arith_goal :=
  lazymatch goal with
  | |- @eq Z _ _ => idtac | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
  | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac | |- _ <> _ => idtac | |- False => idtac | |- True => idtac
  | |- @eq nat _ _ => idtac | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac | |- Z.divide _ _ => idtac
  end.
(* [comment removed for export] *)
Local Ltac addr_diff E A ::=
  let k := lazymatch E with
  | Z.add ?X ?c1 =>
      lazymatch A with
      | Z.add X ?c2 => let c1 := zlit c1 in let c2 := zlit c2 in eval vm_compute in (c1 - c2)%Z
      | X => zlit c1
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  | _ =>
      lazymatch A with
      | Z.add E ?c2 => let c2 := zlit c2 in eval vm_compute in (- c2)%Z
      | E => constr:(0%Z)
      | _ => let e := zlit E in let a := zlit A in eval vm_compute in (e - a)%Z
      end
  end in
  lazymatch eval vm_compute in (Z.leb 0 k) with true => k end.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P002d83ebce33413a 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P003f1cba55b52bc7 0 4 0 1 2 1 41 1 42 1P00dc2ae8929fc789 1 1 8 3 1 1 56 1 59 1 4 2 2 57 2 58 2 60 16P017643c55df05286 0 4 0 1 44 1 54 1 55 1P01b79d8a50f5fca2 1 1 16 2 0 1 54 1 3 35 1 55 1 56 16P01ff65c8e226518d 0 4 1 1 2 1 56 1 57 1P023b70b3d8d2b7d0 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P02435211f2dfc5cb 1 1 8 3 0 1 57 1 58 1 5 2 2 46 2 56 2 59 2 60 16P030b14df53acf819 2 16 0 5 0 1 3 1 21 1 31 1 32 1 0 4 0 1 2 1 31 1 32 1P03265d851ed8ae88 0 4 0 1 2 1 39 1 40 1P03a217ecc1a41f48 1 1 8 3 1 1 40 1 41 1 5 2 2 29 2 39 2 42 2 43 16P049cd3fb5263a488 1 1 8 3 1 1 56 1 59 1 4 2 2 57 2 58 2 60 16P049e42a78c5ad2fc 1 1 8 2 21 1 29 1 3 0 1 28 1 30 8P05182b46d1eb8ed5 0 2 0 1 48 1P056907b1cbd72122 0 2 0 1 19 1P05bcf816a37714ed 1 1 16 2 19 1 37 1 3 0 1 38 1 39 16P06357fa73b772530 0 2 0 1 43 1P06745eb4cbbc60d6 0 4 0 1 44 1 54 1 55 1P069fe6c125f3d3a6 0 4 0 1 27 1 37 1 38 1P06b6893e92687fc3 0 5 1 1 2 1 20 1 30 1 31 1P071a2f79ed83b18b 2 18 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P07506c3419af683b 0 2 0 1 6 1P07cc5be996b24946 0 2 0 1 14 1P07ccb5a7de3581c7 1 1 8 3 1 1 39 1 42 1 4 2 2 40 2 41 2 43 16P0912c3ba5295b6da 0 2 0 1 15 1P092685833882e009 0 4 0 1 2 1 58 1 59 1P09387bf32b9fca39 0 2 0 1 5 1P093fa9680ed72fd5 0 2 0 1 15 1P09dc3280f3c38eb1 1 1 8 3 1 1 56 1 59 1 4 2 1 57 1 58 1 60 8P0a2de8ef3d154356 0 2 0 1 28 1P0a327bdd2502ac6f 1 1 8 3 0 1 57 1 58 1 5 2 2 46 2 56 2 59 2 60 16P0a8c036b56f3c328 1 1 8 2 30 1 38 1 3 0 1 37 1 39 8P0ac0a55ef264bb75 0 4 0 1 2 1 58 1 59 1P0b3a0fda89e9f67f 1 1 8 2 47 1 55 1 3 0 1 54 1 56 8P0b3a4de5fc5a81cd 0 4 1 1 2 1 39 1 40 1P0b48e01b311b4209 0 2 0 1 22 1P0c86d786fb690c3f 0 2 0 1 15 1P0cf6ccbb61da8482 2 16 0 5 0 1 3 1 21 1 31 1 32 1 0 4 0 1 2 1 31 1 32 1P0d897838cea522f6 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P0de1265be3e792ce 0 4 0 1 61 1 71 1 72 1P0e04d358edf5e732 1 1 8 3 1 1 30 1 33 1 4 2 2 31 2 32 2 34 16P0e4338450f7bc5bd 1 1 8 3 0 1 39 1 42 1 4 2 2 40 2 41 2 43 16P0e5fd9cd0b50a63d 2 18 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P0e939415fb046f63 0 4 0 1 3 1 31 1 32 1P0eed5dbac880bb5b 1 1 8 3 0 1 30 1 33 1 4 2 2 31 2 32 2 34 16P0fa3a3a4e9dc919e 0 2 0 1 5 1P0ffd4e2ab9ece978 0 2 0 1 16 1P100230f104502f43 1 1 8 3 1 1 31 1 32 1 4 2 2 30 2 33 2 34 16P1158c7cdf67432c3 1 1 8 2 29 1 38 1 3 0 1 37 1 39 8P116ee32f4a56a209 1 1 8 3 1 1 56 1 59 1 4 2 2 57 2 58 2 60 16P117d89fd629c14b2 0 1 1 1P11968fda7194bd7b 1 1 8 3 0 1 40 1 41 1 4 2 1 39 1 42 1 43 8P121ecf0374989f00 1 1 8 3 0 1 40 1 41 1 5 2 2 29 2 39 2 42 2 43 16P1274c413a89869b4 2 18 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P129220d875fc174a 1 1 8 3 1 1 40 1 41 1 4 2 2 39 2 42 2 43 16P12b7236c20a24d16 0 4 0 1 2 1 56 1 57 1P13830a2c1d3a149b 0 4 0 1 27 1 37 1 38 1P1487c9ef65dde169 0 2 0 1 7 1P14ed083d077a7856 0 2 0 1 16 1P1627aa9e479701b8 2 16 0 5 0 1 3 1 21 1 31 1 32 1 0 4 0 1 2 1 31 1 32 1P166c223ade419bf9 0 4 0 1 44 1 54 1 55 1P169c4ebbb885aec1 1 1 8 3 1 1 57 1 58 1 4 2 2 56 2 59 2 60 16P17d3cce3bfb63e86 0 4 0 1 2 1 32 1 33 1P17f139c0028fdf39 0 2 0 1 1 1P19ecfc5c72d39eab 0 4 0 1 44 1 54 1 55 1P1a08b86d258aa459 0 4 0 1 2 1 41 1 42 1P1ac02917e6266213 1 1 8 3 0 1 57 1 58 1 4 2 1 56 1 59 1 60 8P1ae3b876d7b0ba43 2 18 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P1b09e6a7137a12d9 1 1 8 3 0 1 57 1 58 1 5 2 2 46 2 56 2 59 2 60 16P1b7a12ae78344c65 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P1c1bb976ac3cef60 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P1c3a7671ea112264 0 2 0 1 25 1P1ddc386a1ad21ae5 0 4 0 8 41 8 54 8 55 8P1de8dc65be38afad 0 2 0 1 24 1P1efc2cfd90356293 0 4 0 1 25 1 35 1 36 1P1f47b8b535f7415b 0 3 0 1 21 1 49 1P1fd525ea108b16c8 0 2 0 1 1 1P1fec02d8ff97ec45 2 16 0 5 0 1 3 1 21 1 31 1 32 1 0 4 0 1 2 1 31 1 32 1P201bdb030e7ec914 0 2 0 1 2 1P2025880194fd0169 1 1 8 3 1 1 39 1 42 1 4 2 1 40 1 41 1 43 8P23ef3e5adf585818 1 1 8 3 0 1 30 1 33 1 4 2 2 31 2 32 2 34 16P252db7256fe3b129 0 3 0 1 5 1 34 1P253d1c22824a624f 1 1 8 3 0 1 40 1 41 1 5 2 2 29 2 39 2 42 2 43 16P25af51091785094e 0 2 0 1 15 1P2630039b382d5cb8 0 5 1 1 3 1 47 1 57 1 58 1P26d336bebd6ad49d 1 1 8 3 0 1 40 1 41 1 5 2 2 29 2 39 2 42 2 43 16P270f51177bf9111c 1 1 8 3 1 1 31 1 32 1 5 2 2 20 2 30 2 33 2 34 16P2729b5c7ab6ebf5c 0 4 0 1 3 1 57 1 58 1P275e4dc70d969f99 1 1 8 3 1 1 31 1 32 1 5 2 2 20 2 30 2 33 2 34 16P2842589ae2e4b819 0 2 0 1 31 1P28649cba54d88f64 0 4 0 1 61 1 71 1 72 1P2a0eccf3861cfa4e 0 4 0 1 3 1 40 1 41 1P2a10b6d741fd5376 0 2 0 1 45 1P2a3dd92078de0b7a 1 1 8 3 1 1 30 1 33 1 4 2 2 31 2 32 2 34 16P2a71536df77fb454 1 1 8 3 0 1 40 1 41 1 5 2 2 29 2 39 2 42 2 43 16P2bdd40d41503f787 0 4 0 1 2 1 30 1 31 1P2be0117eade9e57f 0 2 0 1 5 1P2bff7502ea5859a3 0 5 1 1 3 1 21 1 31 1 32 1P2c939c3b26545dcb 1 1 8 3 1 1 40 1 41 1 4 2 2 39 2 42 2 43 16P2cf4fad3b935ff1d 0 4 0 1 25 1 35 1 36 1P2d0b755c8833c92f 1 1 8 3 0 1 56 1 59 1 4 2 2 57 2 58 2 60 16P2d665a79148c08df 1 1 8 3 0 1 31 1 32 1 5 2 2 20 2 30 2 33 2 34 16P2daa7dbd2c9e67de 0 2 0 1 15 1P2e3b79b6568a8b47 0 4 0 1 61 1 71 1 72 1P2e46a13d21029205 0 4 0 1 15 1 22 1 51 1P2ea1dde058157ff9 0 2 0 1 26 1P2ee2f6728d58ca33 0 4 0 1 61 1 71 1 72 1P30a750cfd3df6334 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P3325627d287b892c 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P338c380f7979136b 1 1 8 3 1 1 39 1 42 1 4 2 2 40 2 41 2 43 16P339e5de8d1c29a67 0 2 0 1 23 1P33ca942fb639c201 1 1 8 3 1 1 57 1 58 1 5 2 2 46 2 56 2 59 2 60 16P33d4486c6783760f 0 4 1 1 2 1 39 1 40 1P33e860fca2fd59c0 1 1 8 3 1 1 39 1 42 1 4 2 2 40 2 41 2 43 16P34ed2ebe64da0125 0 2 0 1 15 1P355938972819ac18 0 4 1 1 2 1 56 1 57 1P37a9f29f69d5aa7d 1 1 8 3 0 1 31 1 32 1 5 2 2 20 2 30 2 33 2 34 16P385fb96f59a79599 0 5 1 1 3 1 30 1 40 1 41 1P38624f6f5186e698 2 18 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P3959ed4107150f3e 1 1 8 3 0 1 57 1 58 1 5 2 2 46 2 56 2 59 2 60 16P399423a654b1df49 1 1 16 2 36 1 54 1 3 0 1 55 1 56 16P3aa2586b2f62fd63 0 5 0 16 7 16 18 16 28 16 29 16P3aec1ec5015f54a9 0 2 0 1 2 1P3b3fdbe192b460d1 1 1 8 3 1 1 57 1 58 1 4 2 2 56 2 59 2 60 16P3ba44f40ea0cc30d 0 2 0 1 3 1P3bb4bca133162b93 2 16 0 5 0 1 3 1 21 1 31 1 32 1 0 4 0 1 2 1 31 1 32 1P3c21fa7e797cf962 1 1 16 2 0 1 37 1 3 18 1 38 1 39 16P3c578c117a79ec21 2 17 1 1 8 3 2 1 31 1 32 1 5 0 2 20 2 30 2 33 2 34 16 1 1 8 3 1 1 30 1 33 1 4 0 2 31 2 32 2 34 16P3d74c3f708a62024 1 1 8 3 1 1 39 1 42 1 4 2 2 40 2 41 2 43 16P3fd44fbbf120f311 1 1 8 3 1 1 56 1 59 1 4 2 2 57 2 58 2 60 16P3fe86710cf9160e5 0 3 0 1 4 1 32 1N006c281353e2ff02N00793b1aa9ea0f24N00ed7a8e53e6efa0N0123d4ca977ffc9dN02be956b5cb42e90N0300d6bee18e5f62N03332b58894cd7ccN03665b334b01821cN03737df8980fe527N047ccce9c66b5230N04c5387296544181N05dec112c43d2d22N064e65c0f73b4eecN06f4692a5300ebaaN0721d9b8146a17b6N07293db40507160dN079d47592a2e0f50N081c1e0f42d355f0N0866016756ecee6eN088947aead2f50a7N0982327c67a2425aN09cc919892c680fdN09e5179279133f94N0a2c55961edb4affN0a535a5c2e1b9fbeN0acaf0816f1c65cbN0b38cd4478a25da4N0b4d033418bf0de7N0bab1ac5d2980d87N0bd06847f66b9061N0c02d258cb3722d7N0c7193894e38c099N0c9ac89903da02a7N0cd3f31289db1f0fN0cf55323db448bdaN0d5b4403d39d66eaN0dd6dd01081c333bN0e62bb65de61ee9eN0f52f93ca37c9f78N0f97bfe085f2596bN0fd978ddca2a0d35N0fe469e00ad59859N1009f77a9ce5a52fN102390fd083b0be5N10ba5ff4f05430d7N114052030392087dN11a9644fab2c5cd1N11f312048ae3f3deN1208225dbff39694N1238167b56036f7fN124ce49ddd969333N1286e981eee795dbN1320853aaf2d5a8bN13dbcc0f7ab8b85fN1473a71a23f0ded6N14a82bd3e897b836N14b9fb83d4a7a015N14f1be0a4dafc3ffN15b89a926e2b9628N16219834d47a9b70N17c33ab26a713811N180f2ee208e25787N1845455bbb52ec9cN18b0a19d25f43409N197d5eefcfe0266dN19b2e7cf147cf807N1a02c1ca1484d365N1a09a257134bdd57N1a4774810264bab2N1a8cbfe928a79f31N1aa7125df0e23874N1b24862602c32867N1ba0ed29bdcd78f5N1bb3a4aedc660bc3N1c04aedf83c571e4N1c3d77f9cb47ee32N1d33e1e900a2ecf3N1d825558064ba987N1d8c8ef3e6e5d901N1dd591d0ce55a953N1e0e7c79db646d1dN1eb2037640c28a19N1f24266ab0fe1ad9N1fa0b78bcb896faaN1fd3c7f296813cd5N1ffdbf660ec622a0N2017105d6faebc97N205492a1677a2ea9N2069f260c0f9595aN2077ac2594156ddfN213c9ffbcce557f1N222a69131ec36c0eN2264b3b48980b261N22d1099a2b4a5612N22ffe6b378698f3eN23076ff1a9c97c78N23278f3506635d87N237d43c7adcad003N23a972eef9d6f3a2N23b8c076315ffe79N242fee3fb47fc021N244d58b343e0d323N251808a28d98bcafN25cc010ad07a0b7aN2611d1b1e6d1a900N2622710676e4a76eN26ba0638a3ba04f9N286be71f7386d5d7N28b806f012b11526N2945b115e538a9c1N297ba1bd3ea2d820N2a0c8d1348dc027aN2a16f24cc40eecd3N2a2c8935f9d5a414N2a822b256aa4673eN2ad241d3ab5ba209N2ba1022aa07205adN2bf629416ec797dfN2c837e31377d5b6fN2cadaa5a75024befN2d195cf7e80e14bdN2d1e0cb56a6245cbN2d4b93c2489ee446N2da341004a619022N2dcba7bf9988a781N2de7144de13c5e83N2ed3e687437e5027N305ee4cca3df95b5N3270d8ed8045bd8fN32bdc4c3cfc294faN32efa4915662d7e4N32f6f943d0e74748N342c70d9883f15e1N348a4a357b01b373N3506bf3ae8d0b197N354c34f7df3d0af3N35c0d0ff586e8a70N36b583e9d5342d89N36bc4f7ebceeb638N36f04deeae69433eN374c010dbcd25dd3N37f0d170166ed4a0N38604ecc24dce876N3899611c0ac09328N392dcfb4a9dba390N39483d211a0d7c15N398e55fd68df5efcN39f4e6af4ba1847dN3a3f1b3174852641N3a63a42d285db588N3afe48722abb7038N3b7420add2801f1dN3b91fc988360ba44N3bf9168d3f48498bN3c00b4dcd635c8b4N3c03dd7f988f8e1cN3c342059c5a39233N3c8dd92633bef06aN3d0cf0212884d900N3db9e388b1d76bb0N3e55353354e3a86cN3e90cef510ea53e3N3ea8ea08ede83a03N3fa02c9c479dd078N3fad296ff3def627N3fd4ba1406f82384N3feae231c85d142e"%lxh.
Ltac2 gd_tbl_P_x509_get_dates () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.U.U_x509_get_time.time_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_bytes"; "Corelib.Init.Datatypes.app"].


Definition U_X509_GET_DATES : Z := 0x26b0c.

Lemma land64_zero : forall r, -2^63 <= r < 2^63 -> Z.land r 18446744073709551615 = 0 -> r = 0.
Proof.
  intros r Hr H. change 18446744073709551615 with (Z.ones 64) in H. rewrite Z.land_ones in H by lia.
  destruct (Z.lt_ge_cases r 0); [| rewrite Z.mod_small in H by lia; exact H].
  rewrite <- (Z.mod_add r 1 (2^64)) in H by lia. rewrite Z.mod_small in H by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma le4_le_bytes_to_word : forall bs, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite Mem.Z_to_le_bytes_mod by (cbn; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Definition w4 (bs : list byte) (k : nat) : word := le_bytes_to_word (firstn 4 (skipn (4 * k) bs)).

Lemma time_of_blob : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_dates ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Ptb,(0.(2.&8.))P,(5.R4.R3.R2.(6.$7.(8.#18.R1.)(9.$7.)))(:.(2.&40.)Ly,(2.&40.)(:.(2.&40.)Lmo,(2.&40.)(:.(2.&40.)Ld,(2.&40.)(:.(2.&40.)Lh,(2.&40.)(:.(2.&40.)Lmi,(2.&40.)(:.(2.&40.)Ls,(2.&40.)(5.R;.R:.R9.(;.R6.R5.R4.R3.R2.R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros segs m A tb H. flat constr:(H) 2%nat. intros (WF & _) _. cbn in WF. flat constr:(WF) 2%nat. flclear WF. intros LEN _.
  exists (w4 tb 0), (w4 tb 1), (w4 tb 2), (w4 tb 3), (w4 tb 4), (w4 tb 5).
  eapply rw_cells_reshape; [exact H| cbn; tauto|].
  unfold time_cells, w4. cbn [cells_bytes cbytes app Nat.mul].
  do 6 (destruct tb as [|? tb]; [cbn in LEN; lia|]). do 6 (destruct tb as [|? tb]; [cbn in LEN; lia|]).
  do 6 (destruct tb as [|? tb]; [cbn in LEN; lia|]). do 6 (destruct tb as [|? tb]; [cbn in LEN; lia|]).
  destruct tb; [| cbn in LEN; lia].
  cbn [firstn skipn]. rewrite !le4_le_bytes_to_word by reflexivity. reflexivity.
Qed.

Lemma blob_of_time : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_dates ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Py,(2.&40.)Pmo,(2.&40.)Pd,(2.&40.)Ph,(2.&40.)Pmi,(2.&40.)Ps,(2.&40.)P,(5.R9.R8.R7.(;.R6.R5.R4.R3.R2.R1.))(5.R:.R9.R8.(6.$7.(8.#18.(<.(;.R7.R6.R5.R4.R3.R2.)))(9.$7.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A y mo d h mi s H. eapply rw_cells_reshape; [exact H| | cbn [cells_bytes cbytes app]; rewrite app_nil_r; reflexivity].
  cbn [cells_wf cell_wf]. split; [| exact I]. rewrite cells_bytes_length by (cbn; tauto). reflexivity.
Qed.

Lemma blob48_join : ltac2:(CDefT.buildp (gd_tbl_P_x509_get_dates ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pb1,(0.(2.&8.))Pb2,(0.(2.&8.))P,(5.R5.R4.R3.(6.$7.(8.#18.R2.)(6.$7.(8.#18.R1.)(9.$7.))))(5.R6.R5.R4.(6.$7.(8.#30.(=.(2.&8.)R3.R2.))(9.$7.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A b1 b2 H. flat constr:(H) 2%nat. intros (WF & _) _. cbn in WF. flat constr:(WF) 3%nat. flclear WF. intros L1 L2 _.
  eapply rw_cells_reshape; [exact H| | cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity].
  cbn [cells_wf cell_wf]. split; [| exact I]. rewrite length_app. lia.
Qed.

(* [comment removed for export] *)
Ltac joinr H1 H2 :=
  lazymatch type of H1 with rw_cells ?sg ?mm ?A1 ?cs1 =>
  lazymatch type of H2 with rw_cells _ _ ?A2 ?cs2 =>
    replace A2 with (A1 + Z.of_nat (cells_size cs1)) in H2 by (cbn; lia);
    let Hj := fresh "J" in
    pose proof (proj2 (rw_cells_app sg mm A1 cs1 cs2) (conj H1 H2)) as Hj; clear H1 H2; rename Hj into H1;
    cbn [app] in H1
  end end.
Ltac zofnat H := cbn [cells_size csize Nat.add length] in H;
  repeat match type of H with context [Z.of_nat (Datatypes.S ?k)] => let v := eval vm_compute in (Z.of_nat (Datatypes.S k)) in change (Z.of_nat (Datatypes.S k)) with v in H end;
  repeat match type of H with context [Z.add (Z.add ?a ?b) ?c] => is_Zlit b; is_Zlit c; let v := eval vm_compute in (Z.add b c) in replace (Z.add (Z.add a b) c) with (Z.add a v) in H by lia end.
(* [comment removed for export] *)
Ltac spine_firstn k cs :=
  let k := eval cbv in k in
  lazymatch k with
  | Datatypes.O => eval lazy beta iota delta [firstn] in (firstn Datatypes.O cs)
  | Datatypes.S ?k' => lazymatch cs with
             | ?c :: ?cs' => let r := spine_firstn k' cs' in constr:(c :: r)
             | _ => eval cbv beta iota delta [firstn] in (firstn k cs)
             end
  end.
Ltac spine_skipn k cs :=
  let k := eval cbv in k in
  lazymatch k with
  | Datatypes.O => cs
  | Datatypes.S ?k' => lazymatch cs with
             | _ :: ?cs' => spine_skipn k' cs'
             | _ => eval cbv beta iota delta [skipn] in (skipn k cs)
             end
  end.
Ltac splitat H k H2 :=
  lazymatch type of H with rw_cells ?sg ?mm ?A0 ?cs =>
    let l1 := spine_firstn k cs in
    let l2 := spine_skipn k cs in
    change (rw_cells sg mm A0 (l1 ++ l2)) in H;
    let H1 := fresh "SP" in
    (flat constr:((proj1 (rw_cells_app sg mm A0 l1 l2) H)) 2%nat; intros H1 H2); clear H; rename H1 into H; zofnat H2
  end.

Lemma U_x509_get_dates_spec {L : heap_layout} : x509_get_dates_stmt usegs L U_X509_GET_DATES.
Proof.
  unfold x509_get_dates_stmt, U_X509_GET_DATES.
  intros until tb0.
  intros HPP HTM HBUF B1 B2 B3 B4 D1 D2 D3 AL1 AL2 NZ1 NZ2 NZ3 ST SLO ACL SPA DS1 DS2 DS3 MI -> -> -> ->.
  pose proof alloc_ceiling_pos as ACP.
  unfold X509_GET_DATES_STACK in SLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR.
  unfold bv_modulus in SPR.
  cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HPP) as PPB.
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in PPB.
  change (Z.of_nat 8) with 8 in PPB.
  pose proof (rw_cells_bound _ _ _ _ HTM) as TMB.
  cbn [cells_size csize Nat.add] in TMB.
  change (Z.of_nat 48) with 48 in TMB.
  pose proof (munch_refl [(PP, PP + 8); (TM, TM + 48); (bv_unsigned sp - 96, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  (* [comment removed for export] *)
    flat constr:(HTM) 2%nat. intros (WF48 & _) _.
  cbn in WF48.
  flat constr:(WF48) 2%nat. flclear WF48. intros LEN48 _.
  apply (rw_cells_reshape usegs m TM _ [CB 24 (firstn 24 tb0); CB 24 (skipn 24 tb0)]) in HTM;
    [| cbn; rewrite firstn_length, skipn_length; (flsplit; repeat split); lia | cbn [cells_bytes cbytes app]; rewrite !app_nil_r, firstn_skipn; reflexivity].
  splitat HTM 1%nat HTM2.
  apply time_of_blob in HTM.
  flat constr:(HTM) 7%nat. flclear HTM. intros ya yb yc yd ye yf HTM.
  apply time_of_blob in HTM2.
  flat constr:(HTM2) 7%nat. flclear HTM2. intros za zb zc zd ze zf HTM2.
  unfold time_cells in HTM, HTM2.
  carve_frame 48%nat ST.
  lxp_split_frame [8;8;8;8;8;8]%nat. lxp_seps 48.
  (* [comment removed for export] *)
  pose proof (@sums3_ok _) as LXSUMS.
  lxp_run (PLANS [] [] 64%N SUMS3).
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
Qed.
