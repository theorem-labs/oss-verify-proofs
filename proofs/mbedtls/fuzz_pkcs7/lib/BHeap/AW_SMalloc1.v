(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Dealloc AW_SFree5 AW_FakeDefs AW_SMalloc.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXAW Require Import LxFlat.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P0004cd132951f63c 1 1 8 4 2 1 44 1 67 1 70 1 4 39 1 68 1 69 1 71 8P003b22ba19c96f7f 0 2 0 1 19 1P00d565eb77107ced 1 1 1016 7 0 128 50 1 64 1 65 128 66 1 67 1 68 128 6 35 128 50 1 64 1 66 1 67 1 69 8P013a60d406943a11 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P01d501d01da2e1bb 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P02659923812a6200 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P0377cae104b3160f 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P03fe7fb187f3ce8c 0 4 1 1 20 1 21 1 22 1P049d1b0fc9dae371 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P05ab3c31bc88b449 0 2 1 1 40 1P05b87153dff10a5f 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P064ecb3b4a6f7dce 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P06c6d5de2f930a66 0 4 0 8 4 8 65 8 66 8P06ca748db624c4d3 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P06f7225ee472f247 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P070d7a337675ba93 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P0732f3a5b6f5f00f 0 2 0 1 54 1P082a7815e7084fdc 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P0882c97aaaa27d84 0 2 1 1 40 1P08bdc3097da81126 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P09bffea6ca8eac2c 0 2 0 1 54 1P09da0bf5c784101e 0 2 0 1 19 1P09efbd217166892d 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P0a6773fc0d6e7c51 0 2 1 1 40 1P0ad9d71cef3f0c81 0 2 1 1 40 1P0b2dfbfa9d0b65ef 0 2 1 1 40 1P0b9fbe01fa2ba561 0 4 1 1 20 1 21 1 22 1P0ca4d804bcfbd623 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P0d1a0cf64ba1dd3d 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P0d40d380cb747654 0 6 0 8 36 8 65 8 66 8 67 8 68 8P0d683bda299c4627 1 1 1016 7 0 128 50 1 64 1 65 128 66 1 67 1 68 128 6 35 128 50 1 64 1 66 1 67 1 69 8P0e2c3a884277461e 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P0e314342a528afac 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P0e82f08b092c2be0 0 6 0 1 51 1 52 1 57 1 62 1 63 1P0ed33f6a2708d9fa 1 1 1016 7 0 128 50 1 64 1 65 128 66 1 67 1 68 128 6 35 128 50 1 64 1 66 1 67 1 69 8P0f6695974f6161cc 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P10a3f7e48e9f121c 0 4 1 1 18 1 20 1 21 1P111b9e3bedc2d9d1 0 2 1 1 40 1P11b2be0f0881c7b2 0 6 0 8 36 8 65 8 66 8 67 8 68 8P11b85132df509971 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P11d81a3f6ba15823 0 4 1 1 20 1 21 1 22 1P127844fbeab1e75c 0 4 1 1 20 1 21 1 22 1P1395d20dca80a1c1 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P13cf6bb1aed3baa4 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P15043308f8f93db9 1 1 8 2 0 1 65 1 3 5 1 66 1 67 8P155ee2a4087f6bb9 1 1 8 4 2 1 44 1 67 1 70 1 4 39 1 68 1 69 1 71 8P15e80f4c64482535 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P17410e890d3c8574 0 2 1 1 40 1P1839a16f0dee7384 0 2 1 1 40 1P186da47cffdb7ab5 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P18cab74e7f019e8e 0 2 0 1 19 1P19817e3b5522f484 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P1b3a79662ca99fab 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1b5d9170bb87cfc8 0 2 0 1 54 1P1bcf0b56e7345f4b 0 2 1 1 40 1P1c01175997fd6bd4 0 5 0 8 36 8 45 8 65 8 66 8P1c2beaa30ddbb2e0 1 1 3670016 7 0 1024 35 15360 50 128 64 128 66 128 67 128 68 1024 3 45 1 67 1 69 4096P1d55ca0f6d4ac593 0 4 0 8 4 8 65 8 66 8P1d7d51905d640181 0 6 0 8 36 8 65 8 66 8 67 8 68 8P1e4f10ec2a6f819a 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1e97e3861b5196c8 1 1 8 3 0 1 63 1 64 1 4 38 1 62 1 65 1 66 8P1f0b567068147a73 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P1f7076c8c830f949 1 1 8 2 0 1 65 1 4 37 1 45 1 66 1 67 8P20838c94fce3e767 0 2 1 1 40 1P20db24a77d71b563 0 2 0 1 19 1P21223cb1a5c5c504 1 1 8 4 2 1 44 1 67 1 70 1 4 39 1 68 1 69 1 71 8P214c658101ba8f72 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P217508b7d3481644 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P217e39914fb484d9 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P227c028eaa2c33bd 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P231326defe245708 0 2 0 1 54 1P233c41f741fbd36d 0 2 1 1 40 1P23eaa5c80049f104 0 2 0 1 42 1P243540a0b30914a5 0 2 0 1 7 1P2480cae62cb483e3 0 4 1 1 18 1 20 1 21 1P2490a1bac17c3674 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P24c823f04cb29d6a 0 1 1 1P24f5d2297a7453d8 0 2 0 1 13 1P25c612df08ccac5c 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P260b94bdf6c9b639 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P262b150fb2903be9 1 1 8 3 0 1 61 1 64 1 4 36 1 62 1 63 1 65 8P26bda64f91e21830 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P26cb2cc95df74f5d 0 2 0 1 19 1P26f9d7a34db671b1 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P2709418689e9a5ac 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P27301ee8849516e2 0 2 0 1 19 1P27fe9e1f8f8d415a 0 4 1 1 20 1 21 1 22 1P2821c7dda2fb4267 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P28404eaa7768d1a4 0 2 0 1 54 1P28d916412e5d9cde 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P28db5308438cabe1 0 2 0 1 13 1P28eb6ec577d28984 0 4 1 1 20 1 21 1 22 1P28eff254e3defc00 0 8 0 8 34 1024 40 8 49 8 60 8 63 8 65 8 66 8P295d39e9d226eaeb 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P298270ab626383fd 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P2bd0cea2ed4d14da 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P2cedb22b181e2cf9 0 4 0 1 14 1 15 1 16 1P2d518922f9de0216 0 4 1 1 20 1 21 1 22 1P2de75af48575d6af 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P2e3891853ce43d92 0 4 1 1 18 1 20 1 21 1P2e4230705546e8cf 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P2ea8a63b1fcc29a3 0 6 0 8 36 8 65 8 66 8 67 8 68 8P2f5a505d518e6faa 0 2 0 1 42 1P30b84222b13a64ab 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P30bd13fcd1c55dd1 1 1 8 2 0 1 65 1 4 37 1 45 1 66 1 67 8P30d3a6a99b528de5 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P30e52210cf89c0d1 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P3169b4f62cfe9e51 0 2 0 1 54 1P318c583697119f18 0 2 1 1 40 1P31921cac09a1e7aa 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P31bc871af858ee1d 0 2 1 1 40 1P32257960f84c8daf 1 1 3670016 7 0 1024 35 15360 50 128 64 128 66 128 67 128 68 1024 3 45 1 67 1 69 4096P329037bc924e95d1 0 2 1 1 40 1P32baf3e9aff62db5 0 4 1 1 18 1 20 1 21 1P32cbc01f55365e81 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P32deb76915bcc5b1 0 2 0 1 54 1P32f735f23cb8f125 0 4 1 1 20 1 21 1 22 1P335a506b8a3d2fa5 0 2 0 1 19 1P33df5f9fa85b5b6d 0 2 0 1 54 1P33f3396200034f10 0 2 0 1 19 1P345cf3660541dfef 1 1 1016 7 0 128 50 1 64 1 65 128 66 1 67 1 68 128 6 35 128 50 1 64 1 66 1 67 1 69 8P34fd63d3014b212d 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P362183b78c3ff7b0 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P36a34cf02a47c61b 0 2 0 1 15 1P36d25c37a9932bc4 0 2 0 1 54 1P36f9c36363237e5f 0 2 0 1 19 1P37552b5792a52699 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P383244e77461d2cf 0 2 0 1 13 1P383712f6d3a6bed5 1 1 8 2 0 1 65 1 3 5 1 66 1 67 8P38553e8a980d5b3c 0 2 1 1 40 1P389fcc202bcb21ae 0 2 0 1 19 1P3915c2d0bdbf9cce 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P3938d50cc26ac5f3 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P393ff8a9e41276b9 1 1 8 3 0 1 62 1 63 1 4 37 1 61 1 64 1 65 8P39487921ebb88dbb 0 2 0 1 19 1P39654c730de3559e 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P39c7e64ab88d5211 0 2 0 1 19 1P3a05cf7c874c016a 0 2 1 1 40 1P3a771feb66f05ffa 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P3bc6059be2641901 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P3c2910ddf67036f5 0 2 0 1 13 1P3c58dd752deeb79c 1 1 8 4 2 1 44 1 67 1 70 1 4 39 1 68 1 69 1 71 8P3c7b3b5ae6cd2e3a 0 2 0 1 54 1P3dd2b361a01caf8c 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P3e56fe9ddc4a0370 0 2 0 1 13 1P3fa4b3adf5277735 0 2 0 1 15 1N0012cce9d6c0b737N003d024c0786c746N00afc859f6adf9f1N00bf3e4617840ffeN00ea86006ccca4b8N011c0dd61ddc7313N01edde9400622537N01f070e74ad51c85N020328fd231e2f4fN02b8a687aaca12efN02fabafe48843131N0306eb974527adefN032afa5c5685df49N035625dd576ae70fN03c24572fd41bc4cN040da71ea2e16a29N0411f149610ba096N044e9cb106900b9fN049d470d8951bf3aN04b435899bbf6d41N04ba091abe3f83d0N04e68e8a320f8f19N050facd8e70f4df9N0533829a95a20a64N05445d0305d1acfdN05b616c1eae544c9N0659410f1a63c7caN07267b4876634daeN0729b5c45bcb0d73N0749739869c15898N07adca52d1c22260N07c6a7fe02fe8c6eN08ee76eee880f8f3N09091c18599474d1N092a2b79f1ec6dd8N0975f6ab7a12dfcfN099560d31e1ddb9fN09be00778260cc09N09c46ceeaea64448N09ccf984b688a6a3N0a004e0dc4f05eecN0ac589b6c8d92a39N0ae7b613f22e794aN0b73b336bde0fe13N0b8654774d25ce6cN0bd1f0099740aab6N0bf5cfb207fbf2c4N0c00ce1b1ee51202N0c330124207f7159N0c59eb624244e0cfN0c6949417b9acd56N0c8597d5b722069fN0ccc6f059ea3e5bfN0d04000f59021643N0d1fa6985036e34eN0d211f5259fdbe07N0d72a272500fc93fN0d9e965f4d8e9a51N0dde120114a97f05N0e0f1a3289505dfdN0e36770b40ef1f34N0f672b92c066f62bN101c1dc3733a189bN102033a671dffc05N1078457ee977de1bN1092ef688d85920cN11fca09e5a722a3cN12d909d44487882bN133d156be583a4bbN13474cb7c0a6cadfN135972c5b766de8fN13c08a2ccdbd0a6cN13c8060c91397836N140874d03f0e594bN1441e3c1cff2e522N147e6563416fb940N14cfd190e7986ed7N1508fbeb3d085146N1520eed420fa9bf2N152b97e6853a0c60N15388332979e7550N1568dcafafb3c5dcN15922fc340428779N15a54725e4e1dd13N15d583155a180a3cN15d932291df80afaN15e17cfa13fa2be8N15f04c5450a3e7c6N1621a10e80343729N1637d7fd45cf52bbN1682c488be529045N16bd04f59c525a56N1738b805af8eb1bbN17a060d0b5c2dcdfN17c1faa248a473acN17c4bc9c20e4f1e7N17e8568a781251dbN18668f356f48ce53N186a54d36fc53764N188440a5d2f56d10N18f2a081f0f08824N190c50a393b8ded7N19d646b7e2e4356cN1a3d08a35b497dafN1ae01ce173f7264aN1bdc383634257ca3N1c2adefec0e7fd23N1c345e714ac983cdN1cc521a00b526476N1cdaf6f55f589004N1d09646cf5714da4N1d3fb581a38a4855N1d8b194464454f91N1e40b5eb96caacfbN1e80668236d6568dN1eb241c5c8fa46fbN1ed7d4b3fac8f361N1f152ecf7cb5a99bN1fa776a4353bb215N1fdd07a731d16fa5N2011e3905f9840faN2021070339a07e6cN208017cdacb77cfdN208e83a0693bafc4N20d03f4fa87b1ec2N20f75fe24d744e87N20fc9056917936e5N21528e2afdb7a18aN216eaa0011ec77fcN220c56eae855ea37N221817972e55324eN22c70a4f319ece58N231b92f18a9eb5feN2358307bfb4fe20dN23b301dd910de8eeN244ef38a33bb3a49N2459956ccba3d28bN247eb8fa2797a0a2N24ba5f9a867d1bd4N25da9538b5b867faN25df266773478045N26d0d0a2e98b9bc4N274c85d960b93396N2756162ecfef91a3N2790d2885df77261N279e04e2fbe7756cN27a72404f35bddc2N281252d770499474N283997ab4733bd4aN2863ed5bc79695c3N28a00eb9b054f241N28cc50158b4b0666N28cf84a6fcce643cN299290cec23610adN299a9c5f851836bbN29c4700d9a36fd25N2a7f55c532ddc777N2b21807da8d88a5fN2b3264bd0dbd4665N2b61549ba93f81e3N2baa82c72866f677N2bd316af88156ff0N2bddd86ebeffd2afN2be292620fbdd4e6N2c6c8e95980c81b1N2c8f54536852e5e8N2c904a65d772c26dN2c963b87ac574fccN2d1375414de699d3N2d7480f330206aeaN2d78d2f45b17c6a7N2da92c5532aaf0aeN2dd14ede77677374N2df4baa9da5bb56eN2e04592383dba102N2e1abdae9b893993N2e265397113bafdfN2f29ae2dce64e523N2f642675d63335d8N2f68647aa18760e3N2f705ace4164404aN2f8824814a68ec41N2f8c0aad574814f9N3074d6f7e218f086N3080b3120720b6eaN3088b41f2ee76208N30a5d74609cb1295N3166e59da68e102aN3185560d82f2e098N32cd57a61f79da38N32dda436558188a8N32dfdd933aa25deeN32ece5e91598830dN32fd29bf5e310b7cN3421083ca54cb300N348fffe7932857a4N34bb1bf6cd9f8bbaN34bca40f66caf96aN34c558cbf50b87a6N34cd2aac57f3c2baN359d6967640b6d68N35c89f8f82662faeN35d03a2468be0acfN3683b6845cea912aN3687c5743038565aN36984ac3930de8ecN36fc22aff189c344N372a6dfea89d7cd6N375d28b49c4ff38dN37d88f132142503cN383630cbdcc1d071N38b940a5da551b56N38c509b4941668b3N390dd8088e81ae27N393610e03eca40f4N39a550fd0f8e2835N3a2feaa1e0f7fc0bN3a41f9bd968f4082N3a8aa7e72e3eccb3N3adaed6207a3321cN3b6ddffbe8a80318N3b9005dfc30e025fN3bda4fcd8d1d47cbN3bfc677d71c09e10N3c1f6406f95eb62fN3c542ebe5ee353f6N3c819947718c440cN3ca389dd539f9e5aN3cab52f53919eabcN3d074f30d68c899aN3d7033557aa7f2e4N3d76c3de2260f44bN3db8b45ba0b7aa27N3e1312599d89483fN3e1c084f9b3aaa0fN3e2deb7689017472N3e728f47e92c3e5cN3e8ea1cecbbb412dN3e8f30fc0d47d922N3ef4b6e60a1300acN3fd6c8c71fa27631"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_SMalloc1 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.A_SM1_RA"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.SMalloc1.sm1_regs"; "ARUN_1.A_SM1_FOUND"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.not"; "ARUN_1.A_SM1_NONE"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.SMalloc1.scan1_post"; "ARUN_1.A_SM1_LOOP"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SMalloc.smalloc_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.sub"; "ARUN_1.SMalloc1.sm1_A_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SMalloc.A_SMALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fsk_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.shd"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "ARUN_1.SMalloc1.sm1_found_post"; "ARUN_1.SMalloc1.smalloc1_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_SM1_RA : Z := 0x53090.      (* [comment removed for export] *)
Definition A_SM1_LOOP : Z := 0x53100.    (* [comment removed for export] *)
Definition A_SM1_NONE : Z := 0x5311c.    (* [comment removed for export] *)
Definition A_SM1_FOUND : Z := 0x53178.   (* [comment removed for export] *)

Section SMalloc1.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.   (* [comment removed for export] *)

  Ltac facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.

  (* [comment removed for export] *)
  Definition sm1_regs (SP FS : Z) (gp x5 t1 t2 a0 a2 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc1 ()) "(0.(1.&40.$2.)(1.&40.(3.O18.-20.))O16.(1.&40.$4.)O15.O14.O13.(1.&40.O18.)(1.&40.O17.)O12.(1.&40.(3.O17.+1000.))O11.(1.&40.(3.O17.+5000.))(1.&40.+1???.)O10.O?.O>.(1.&40.+14.)O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition scan1_post (SP FS : Z) (gp t1 t2 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (fl : list byte) (m : mem) (r cur : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc1 ()) "Lms',$5.(6.(7.$8.Lr',$8.(7.$8.Lc,$8.(7.$8.Lpos,$8.(7.(9.&8.)Lb,(9.&8.)(:.(:.(;.=R3.)(<.R3.(=.+2.+40.)))(:.(>.$8.R2.(?.R3.+2000.))(:.(>.(10.(9.&8.))(11.(9.&8.)O4.(12.R2.))(13.(9.&8.)R1.))(:.(>.$8.(14.&8.R1.)=)(>.$5.R5.(15.(16.O19.O18.O17.(1.&40.=)O16.O15.(1.&40.R4.)(1.&40.R3.)(1.&40.(3.(3.O18.+5000.)R2.))O14.(1.&40.R2.)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.(1.&40.$17.)O5.(18.(9.&40.))O3.(19.$1:.)))))))))))(:.Pj,$8.P,(:.(;.=R1.)(<.R1.O2.))(7.(9.&8.)Lb,(9.&8.)(:.(>.(10.(9.&8.))(11.(9.&8.)O4.(12.(?.(3.O1.R3.)+2000.)))(13.(9.&8.)R1.))(1;.(>.$8.(14.&8.R1.)=))))(7.(9.&40.)Lx5,(9.&40.)(7.(9.&40.)Lx12,(9.&40.)(7.(9.&40.)Lx15,(9.&40.)(7.(9.&40.)Lx17,(9.&40.)(>.$5.R5.(15.(16.O19.O18.O17.R4.O16.O15.(1.&40.=)R3.R2.O14.R1.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.(1.&40.$1<.)O5.(18.(9.&40.))O3.(19.$1:.)))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L11608399893.9L3579524304.1200000100?SS3cur1j1q2rr1D". (* [comment removed for export] *)
  Lemma scan1_shift : forall cur j, (((cur + 1) mod 2^64) + (j - 1)) mod 8192 = (cur + j) mod 8192.
  Proof.
    intros cur j. pose proof (Z.div_mod (cur + 1) (2^64) ltac:(lia)) as D.
    set (q := (cur + 1) / 2^64) in *. set (rr := (cur + 1) mod 2^64) in *.
    replace (cur + j) with ((rr + (j - 1)) + (q * (2^64 / 8192)) * 8192) by (change (2^64 / 8192) with 2251799813685248; lia).
    rewrite Z_mod_plus_full. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L12529075241.4 L13278302029.2 L16980495076.53L18941427511.49L23970772284.56L2625671488.7  L28925203287.44L29008555810.55L3396492593.5  L36364150030.53L59310648043.5 L60519880076.2 L6343387025.5  L64930759789.5 L8929160544.6  00000;00C00]00m01D01U03<03S03b04<04O04U04^04m05:S1r1j2Hj2NES3cur2PBS3hAR2nn1r3cur2FS2fl2Hn2PBS3hAR2nn1r2fl2HnS3hAR2nn1r3cur2fl2Hn2HrS2nn1r2Hn2Kr1j2HjS3hAR2AL2CS1r3cur2gp2x52t12t22a63x153x172s32s42s52s62s72s82s93s103s112t32t42t52t62SP2FS2fl1F2fc1m2Hn2HrS3hAR2nn1r3cur2fl2Hn2HrS2nn1r2Hn2Hr2KrS3hAR2nn1r3cur2FS2fl2Hn2PBS3cur2fl3FLL2PB3NTHS1r2HrS2nn1r2HnS2nn1r2Hn2Hr2KrS2nn1r3cur2Hn". (* [comment removed for export] *)
  Lemma scan1_loop : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc1 ()) "Pnn,$1=.Pr,$8.Pcur,$8.Pgp,(9.&40.)Px5,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa6,(9.&40.)Px15,(9.&40.)Px17,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.Pfl,(1>.(9.&8.))PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(10.(9.&8.))P,(>.$8.(20.R1=.)R1<.)P,(:.(;.+1.R1=.)(;.R1=.+2000.))P,(:.(;.=R1=.)(<.R1=.(=.+2.+40.)))P,(21.$1:.R4.(3.R8.+5000.)R7.)P,(>.$8.(20.(22.(9.&8.)R8.))+2000.)P,(23.VCS,(3.R:.+5000.)+2000.)P,(;.+65?000.R;.)P,(;.(3.R<.+;09000.)(24.VhAR,))P,(25.$1:.R9.)(26.$1:.VAL,VCS,(27.R?.R>.R23.R21.R20.R1?.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R<.R;.R=.R:.R25.R24.)(15.(16.R?.R>.R23.R22.R21.R20.(1.&40.R25.)(1.&40.R24.)R1>.R1?.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R<.(1.&40.$28.)R;.(18.(9.&40.))R:.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    induction nn as [|nn IH]; intros r cur gp x5 t1 t2 a6 x15 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS fl F fc m
      Hn Hr Hc FLA FLL FLCS FS0 FS1 MI; [lia|].
    facts. unfold sm1_regs, A_SM1_LOOP, A_SM1_RA, A_TP in *.
    pose proof (Z.mod_pos_bound cur 8192 ltac:(lia)) as PB.
    destruct (nth_error fl (Z.to_nat (cur mod 8192))) as [b|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear -NTH PB FLL; lia].
    pose proof (u8arr_read asegs m (FS + 20480) fl (cur mod 8192) b _ FLA NTH ltac:(clear -PB; lia) eq_refl) as RD.
    (* [comment removed for export] *)
    zstep. first [rewrite (land_8191 cur) | rewrite Z.land_comm, (land_8191 cur)].
    zstep. zstep. clear RD.
    zstep. if_cases Kb; zify_cond Kb.
    - cbv beta. pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
      rewrite ?Z.mod_small in Kb by (clear -BR; lia).
      replace (Z_to_bv 64 (bv_unsigned b)) with (Z_to_bv 64 0) by (rewrite Kb; reflexivity).
      apply evtA_done. left. exists r, cur, (cur mod 8192), b.
      split; [exact Hc|]. split; [reflexivity|]. split; [exact NTH|]. split; [exact Kb| reflexivity].
    - (* [comment removed for export] *)
      cbv beta in Kb. pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
      rewrite ?Z.mod_small in Kb by (clear -BR; lia).
      assert (NZ0 : exists b0 : byte, nth_error fl (Z.to_nat ((cur + 0) mod 8192)) = Some b0 /\ bv_unsigned b0 <> 0).
      { exists b. rewrite Z.add_0_r. split; [exact NTH| exact Kb]. }
      (* [comment removed for export] *)
      zstep. rewrite (swrap32_small (r + -1)) by (clear -Hr; lia).
      zstep.
      zstep. if_cases Kr; zify_cond Kr.
      + rewrite <- (zbv_mod64 (cur + 1)).
        eapply evtA_mono.
        * eapply (IH (r + -1) ((cur + 1) mod 2^64)); try eassumption; try (clear -Hn Hr Kr; lia).
          all: pose proof (Z.mod_pos_bound (cur + 1) (2^64) ltac:(clear; lia)) as MPB; clear -MPB; lia.
        * cbv beta. intros ms' [P | [ALL P]]; [left; exact P| right]. split; [| exact P].
          intros j Hj. destruct (Z.eq_dec j 0) as [->|NE]; [exact NZ0|].
          destruct (ALL (j - 1) ltac:(clear -Hj NE; lia)) as (b1 & N1 & Z1). exists b1. rewrite <- (scan1_shift cur j). split; [exact N1| exact Z1].
      + apply evtA_done. right. split.
        * intros j Hj. replace j with 0 by (clear -Kr Hr Hn Hj; lia). exact NZ0.
        * unfold A_SM1_NONE. replace (r + -1) with 0 by (clear -Kr Hr Hn; lia). do 4 eexists. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition sm1_A_post (SP FS lo hint : Z) (ra gp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc1 ()) "Lms',$5.(7.P,(9.&40.)(10.(9.&8.))Lm1,P,(9.&40.)(10.(9.&8.))(:.(>.$5.R2.(15.(16.O1=.O1<.O18.O17.O16.O15.(1.&40.+2000.)(1.&40.O1:.)(1.&40.(3.O1:.+1???.))(1.&40.(3.O1:.+2000.))O12.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)O3.(1.&40.$28.)O2.(18.(9.&40.))R1.(19.$1:.)))(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.O1;.O1=.)(2=.(2;.$8.$8.)))O1.R1.)(:.(2>.$1:.O1.R1.)(:.(25.$1:.R1.)(:.(2?.$1:.R1.(3.O1=.-20.)(2:.$30.(31.O11.)(2:.$30.(31.O13.)(2:.$30.(31.O14.)(2:.$30.(31.O19.)(2=.$30.))))))(32.$1:.R1.O1;.(3.O1=.-20.))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11330676608.7 L11923395103.4 L16143243576.5 L21436398648.5 L21870408481.0 L26238223716.5 L26680464573.65L27846297964.3 L29753927507.3 L38235734261.1 L3958017386.4  L3958017390.4  L41599022925.2 L9448615682.3  L9448615686.2  L9678154644.12 00000F00T00i01>01?01O01_01f02102502602702>02?02G02oS3hAR2SP1T2lo2TH5LOIMGS3hAR2lo5LOIMGS3hAR2FS2lo3FSH5LOIMGS3hAR2FS2lo3FSH5LOIMGSS2SP2lo2A'2n'2H'S3hAR2SP2lo1y2HyS2SP2loS2SP2lo3SPLS2loFFS2SP2loFS2SP3SPHS3hAR2SP3BLK3CTX2lo2BH2CH5LOIMG2A'2n'2H'". (* [comment removed for export] *)
  Lemma sm1_A : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc1 ()) "Pra,(9.&40.)Pgp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.PBLK,$8.PT,$8.PCTX,$8.Plo,$8.Phint,$8.PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(10.(9.&8.))P,(:.(;.+1000.R8.)(6.(;.(3.R8.+1000.)+10000.)(;.+65?000.R8.)))P,(;.(3.R9.+1000.)(24.VhAR,))P,(;.+65?000.R8.)P,(;.(3.R9.+10000.)(24.VhAR,))P,(:.(;.+1000.R;.)(6.(;.(3.R;.+1000.)+10000.)(;.+65?000.R;.)))P,(;.(3.R<.+1000.)(24.VhAR,))P,(:.(;.+65?000.R?.)(6.(;.(3.R?.$33.)+7???7000.)(;.+10007???8000.R?.)))P,(;.(3.R10.$33.)(24.VhAR,))P,(:.(;.=R<.)(<.R<.(=.+2.+40.)))P,(34.R:.R12.R11.R10.R?.)P,(23.VCS,R12.+1000.)P,(23.VCS,R11.+10000.)P,(23.VCS,R13.+1000.)P,(7.(9.&40.)Ltb,(9.&40.)(7.(9.&40.)Lte,(9.&40.)(35.$1:.R10.(3.R16.+30.)(2:.$30.(31.R2.)(2:.$30.(31.R1.)(2=.$30.))))))P,(35.$1:.R?.(3.R17.+58.)(2:.$30.(31.(1.&40.+14.))(2:.$30.(36.(1.&8.=))(2=.$30.))))P,(2?.$1:.R10.(3.R18.+8.)(2:.$30.(31.(1.&40.R13.))(2=.$30.)))P,(23.VCS,R19.+1000.)P,(32.$1:.R12.R16.R1;.)P,(;.(24.VhAR,)R17.)P,(;.R18.(37.R1=.+=0.))P,(;.R1>.(=.+2.+3>.))P,(23.VCS,R1:.(37.R1?.R1:.))P,(25.$1:.R17.)(26.$1:.VAL,VCS,(38.R21.R20.R1<.R1;.R3>.R3=.R3<.R3;.R3:.R39.R38.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1:.R19.R18.)(15.(0.R3>.(1.&40.R21.)R3=.(1.&40.$4.)R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R1:.(1.&40.(39.+1.))R19.(18.(9.&40.))R18.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint F fc m
      BL BH CL CH TL TH FSL FSH HNT SS BCS CCS TCS TT HDR HC FCS ST LOIMG SPL SPH SCS MI.
    unfold kHighMemBeg, kFakeBytes in *. cbn [A_SMALLOC].
    flat constr:(SS) 6%nat. intros _ _ _ _ TPFS _. unfold A_TP in TPFS.
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    lx_hide SS. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x5d06c] [] 20%N). lx_unhide.
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, STl : stk _ _ lo (SP + -32) |- _ =>
      eapply evtA_cut; [eapply (tga_spec AL IMG ALWF CS CSOK) with (SP := SP + -32) (FS := FS) (BLK := BLK) (T := T) (CTX := CTX) (lo := lo) (m := mx);
        first [exact BL | exact BH | exact CL | exact CH | exact TL | exact TH | exact BCS | exact CCS | exact TCS | exact LOIMG | assumption
              | eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MUl); intros A' n' H'; cbn; clear -H' LOIMG SPL CH BH; lia
              | (flat constr:(TT) 3%nat; flclear TT; intros tb te TT'); exists tb, te; eapply ro_cells_transport; [exact TT'| exact MUl| cbn; clear -LOIMG SPL TH; lia]
              | clear -SPL; lia | clear -SPH; lia
              | eapply crange_sub; [exact SCS| clear; lia| clear -SPL; lia] ] |] end.
    cbv beta; intros ms1 (mA & x11 & x12 & x13 & MU1 & WM1 & MI1 & ST1 & ->).
    unfold A_TP in *; replace (ret_pc (Z_to_bv 64 0x53090)) with (Z_to_bv 64 0x53090) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    assert (LO1 : forall A' n', A' + n' <= lo -> disjoint_from [(lo, SP + -32)] A' n') by (intros A' n' H'; cbn; clear -H'; lia).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, FRl : rw_cells _ _ (SP + -32) _, TPl : ro_cells _ _ 6539920 _,
                        HDRl : ro_cells _ ?mx' (FS + 88) _, HCl : rw_cells _ ?mx'' (FS + 8) _ |- _ =>
      assert (FR1 : rw_cells asegs mA (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply rw_cells_transport; [exact FRl| exact MU1| exact WM1| cbn; clear; lia]);
      assert (TPFS' : ro_cells asegs mA 6539920 [C8 (Z_to_bv 64 FS)])
        by (eapply ro_cells_transport; [exact TPl| exact MU1| apply LO1; cbn; clear -LOIMG H; lia]);
      assert (HDR1 : ro_cells asegs mA (FS + 88) [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)])
        by (eapply ro_cells_transport; [exact HDRl| exact MU1| apply LO1; cbn; clear -LOIMG FSH; lia]);
      assert (HC1 : rw_cells asegs mA (FS + 8) [C8 (Z_to_bv 64 hint)])
        by (eapply rw_cells_transport; [exact HCl| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH; lia]);
      assert (MU2 : munch [(lo, SP)] m mA) by (lx_munch MUl MU1);
      pose proof (wmono_trans asegs _ _ _ WMl WM1) as WM2;
      clear MU1 WM1 ST MI TPFS HDR HC SS TT; lx_clear_mem mx; rename MU2 into MU; rename WM2 into WM; rename MI1 into MI; rename ST1 into ST
    end.
    (* [comment removed for export] *)
    lx_run (PLAN [0x53100] [] 40%N).
    apply evtA_done. unfold sm1_A_post, sm1_regs, A_SM1_LOOP, A_SM1_RA, A_TP. exists lxm.
    lx_ands; [ lx_mseq | assumption | assumption | assumption | assumption | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma sm1_none : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc1 ()) "Pra,(9.&40.)Pgp,(9.&40.)Px5,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Px12,(9.&40.)Px15,(9.&40.)Px17,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.Plo,$8.Phint,$8.PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(10.(9.&8.))Pm,P,(9.&40.)(10.(9.&8.))P,(:.(;.+65?000.R7.)(6.(;.(3.R7.$33.)+7???7000.)(;.+10007???8000.R7.)))P,(;.(3.R8.$33.)(24.VhAR,))P,(2?.$1:.R3.(3.R9.+8.)(2:.$30.(31.(1.&40.R7.))(2=.$30.)))P,(23.VCS,R:.+1000.)P,(2?.$1:.R5.(3.R<.-20.)(2:.$30.(31.R1:.)(2:.$30.(31.R1>.)(2:.$30.(31.R1?.)(2:.$30.(31.R24.)(2=.$30.))))))P,(32.$1:.R6.R;.(3.R=.-20.))P,(;.(24.VhAR,)R<.)P,(;.R=.(37.R?.+20.))P,(;.R10.(=.+2.+3>.))P,(23.VCS,R?.(37.R11.R?.))P,(29.(2:.(2;.$8.$8.)(2<.$8.$8.R10.R12.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.R11.+8.)(3.R11.+10.))(2=.(2;.$8.$8.))))R<.R;.)P,(2>.$1:.R=.R<.)P,(25.$1:.R=.)(26.$1:.VAL,VCS,Lms',$5.(7.P,(9.&40.)(10.(9.&8.))Lm',P,(9.&40.)(10.(9.&8.))(:.(>.$5.R2.(15.(0.R2?.(1.&40.R17.)R2>.(1.&40.$4.)R2=.R2<.R2;.R2:.R29.(1.&40.=)(1.&40.(3.R16.+1000.))R28.(1.&40.(3.R16.+5000.))(1.&40.+1???.)R27.(1.&40.(3.R14.+2000.))R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R13.(3:.R2?.)R12.(18.(9.&40.))R1.(19.$1:.)))(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.R15.R17.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.R16.+8.)(3.R16.+10.))(2=.(2;.$8.$8.))))R11.R1.)(:.(2>.$1:.R11.R1.)(:.(25.$1:.R1.)(:.(2?.$1:.R1.(3.R16.+8.)(2:.$30.(31.(1.&40.(3.R14.+2000.)))(2=.$30.)))(32.$1:.R1.R15.R17.)))))))(15.(16.R15.R14.R2<.R2;.R2:.R29.(1.&40.=)R26.R25.(1.&40.(3.R12.+2000.))R24.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R11.(1.&40.$1<.)R10.(18.(9.&40.))R>.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp x5 t1 t2 s0 s1 x12 x15 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo hint F fc m0 m
      FSL FSH HC FCS FR ST LOIMG SPL SPH SCS MU WM MI.
    unfold kHighMemBeg, kFakeBytes, sm1_regs, A_SM1_NONE, A_SM1_RA, A_TP in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_post.
  Qed.

  Definition sm1_found_post (SP FS lo pos c : Z) (ra gp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (fl : list byte) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc1 ()) "Lms',$5.(7.(9.&40.)Lx5,(9.&40.)(7.(9.&40.)Lx11,(9.&40.)(7.(9.&40.)Lx12,(9.&40.)(7.(9.&40.)Lx13,(9.&40.)(7.(9.&40.)Lx14,(9.&40.)(7.(9.&40.)Lx15,(9.&40.)(7.(9.&40.)Lx16,(9.&40.)(7.(9.&40.)Lx17,(9.&40.)(7.P,(9.&40.)(10.(9.&8.))Lm',P,(9.&40.)(10.(9.&8.))(7.(1>.(9.&8.))Lj1,(1>.(9.&8.))(7.(1>.(9.&8.))Lj2,(1>.(9.&8.))ZFB,$8.(3;.O1<.+1.O1:.)(:.(>.$5.R=.(15.(0.O18.(1.&40.O1=.)O17.(1.&40.$4.)R<.O16.O15.O14.O13.(1.&40.R1.)R;.R:.R9.R8.R7.R6.R5.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)O4.(3:.O18.)O3.(18.(9.&40.))R4.(19.$1:.)))(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.O1;.O1=.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.O1<.+8.)(3.O1<.+10.))(2:.(2;.$8.$8.)(2<.$8.$8.(3.(3.O1<.+5000.)O1:.)(3.(3.(3.O1<.+5000.)O1:.)+1.))(2:.(2;.$8.$8.)(2<.$8.$8.R1.(3.R1.+80.))(2:.(2;.$8.$8.)(2<.$8.$8.(3<.R1.)(3.(3<.R1.)+10.))(2=.(2;.$8.$8.)))))))O1.R4.)(:.(2>.$1:.O1.R4.)(:.(25.$1:.R4.)(:.(2?.$1:.R4.(3.O1<.+8.)(2:.$30.(31.(1.&40.(3.O19.+1.)))(2=.$30.)))(:.(21.$1:.R4.(3.O1<.+5000.)(3=.(9.&8.)O2.(12.O1:.)(1.&8.+1.)))(:.(2?.$1:.R4.R1.(2:.$30.(3>.#18.R3.)(2:.$30.(31.(1.&40.O1=.))(2:.$30.(3>.#58.R2.)(2:.$30.(31.(1.&40.(3.(3.O1<.+5000.)O1:.)))(2=.$30.))))))(:.(2?.$1:.R4.(3<.R1.)(2:.$30.(3>.#10.(3?.(9.&8.)(1.&8.=)#10.))(2=.$30.)))(:.(40.R4.)(32.$1:.R4.O1;.O1=.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00S0@L10187340561.104L12381266366.102L13335596837.101L13335596837.102L15938068669.2  L1641455751.101 L17120848823.0  L21943567510.16 L24642758929.104L24973756177.104L25456994354.101L25458997615.103L27048764373.97 L29729355235.104L29984749841.104L3129187939.104 L35807947067.2  L35842253073.104L38364278545.104L39188636933.0  L43442085943.9  L44706278166.104L45867630865.104L51489812398.73 L53830988561.104L54152160195.3  L54587168821.2  L54961663500.97 L55204150092.1  L55588686165.0  L57794683085.104L62746513610.104L65271643703.0  L66172036696.3  L8618464589.2   00000T00h01L02002102K02L03?03c04G04o05W05i06@06d06e06m07Q08508608Y09T0:80:W0;;0;G0;O0;a0;e0;f0<Q0=P0=Q0=\0=dS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FBS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0FS3hAR2SP2FS2lo3pos1c2fl2FBSS3hAR2SP2FS2lo3pos2FB5LOIMG2PB3FBR2SR4FSL02A'2n'2H'S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB3FSH2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB3FSH2Hc3HFB3FBR4FSL0S3hAR2FS3pos2fl2PBS3hAR2FS3pos1c2fl2FB2PBS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0FS2FS3posS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0SS3hAR2FS3pos2FB3FSL3FSH3HFB3DFS3FBRS3hAR2FS3pos1c2fl2FB3FSA2Hc2HP3HFB3DFS3FBR2SR3FBA4FSL04FSL1S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2SP2FS2lo3pos1c2fl2FB1y2HyS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S2FS3pos3DFSS2FS3posS3hAR2FS3pos2fl2PBS2FBSS3hAR2FS3pos1c2fl2FB2Hc2HP3HFB3DFS3FBR4FSL0S3hAR2SP2FS2lo3pos1c2fl2FB3FSH2Hc2HP5LOIMG3SPL3HFB3DFS3FBR4FSL0SS2FS3pos2PBS3pos2PB". (* [comment removed for export] *)
  Lemma sm1_found : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc1 ()) "Pra,(9.&40.)Pgp,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa6,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.Plo,$8.Ppos,$8.Pc,$8.Pr',$8.Ph0,(9.&40.)Pfl,(1>.(9.&8.))Pjunk,(1>.(9.&8.))Psj,(1>.(9.&8.))PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(10.(9.&8.))Pm,P,(9.&40.)(10.(9.&8.))ZFB,$8.(3;.R=.+1.R;.)P,(:.(;.+65?000.R>.)(6.(;.(3.R>.$33.)+7???7000.)(;.+10007???8000.R>.)))P,(;.(3.R?.$33.)(24.VhAR,))P,(>.$8.(?.R10.+1000.)=)P,(:.(;.=R>.)(<.R>.(=.+2.+40.)))P,(>.$8.R10.(?.R?.+2000.))P,(2?.$1:.R7.(3.R13.+8.)(2:.$30.(31.R>.)(2=.$30.)))P,(21.$1:.R8.(3.R14.+5000.)R>.)P,(>.$8.(20.(22.(9.&8.)R?.))+2000.)P,(2?.$1:.R:.R9.(2:.$30.(3>.#80.R?.)(2=.$30.)))P,(2?.$1:.R;.(3<.R:.)(2:.$30.(3>.#10.R?.)(2=.$30.)))P,(23.VCS,R18.$33.)P,(40.R=.)P,(2?.$1:.R>.(3.R1;.-20.)(2:.$30.(31.R29.)(2:.$30.(31.R2;.)(2:.$30.(31.R2<.)(2:.$30.(31.R30.)(2=.$30.))))))P,(32.$1:.R?.R1:.(3.R1<.-20.))P,(;.(24.VhAR,)R1;.)P,(;.R1<.(37.R1>.+20.))P,(;.R1?.(=.+2.+3>.))P,(23.VCS,R1>.(37.R20.R1>.))P,(29.(2:.(2;.$8.$8.)(2<.$8.$8.R1?.R21.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.R20.+8.)(3.R20.+10.))(2:.(2;.$8.$8.)(2<.$8.$8.(3.(3.R20.+5000.)R1>.)(3.(3.(3.R20.+5000.)R1>.)+1.))(2:.(2;.$8.$8.)(2<.$8.$8.R13.(3.R13.+80.))(2:.(2;.$8.$8.)(2<.$8.$8.(3<.R13.)(3.(3<.R13.)+10.))(2=.(2;.$8.$8.)))))))R15.R14.)P,(2>.$1:.R16.R15.)P,(25.$1:.R16.)(26.$1:.VAL,VCS,(41.R24.R23.R22.R21.R20.R39.R38.R37.R36.R35.R34.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R1:.R19.R1=.R18.)(15.(16.R24.R23.R38.(1.&40.=)R37.R36.(1.&40.R1?.)(1.&40.R20.)(1.&40.(3.(3.R23.+5000.)R21.))R33.(1.&40.R21.)R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R1:.(1.&40.$17.)R19.(18.(9.&40.))R17.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo pos c r' h0 fl junk sj F fc m0 m FB
      FSL FSH FSA Hc HP HC FLA FLL FRM FSHD FCS PS FR ST LOIMG SPL SPH SCS MU WM MI.
    unfold kHighMemBeg, kFakeBytes, sm1_regs, A_SM1_FOUND, A_SM1_RA, A_TP in *.
    assert (HFB0 : FB = fsk_frame FS 1 pos) by reflexivity. clearbody FB. unfold shd in *.
    assert (HFB : FB = FS + 36864 + 1048576 + pos * 128) by (rewrite HFB0; unfold fsk_frame; clear; lia).
    pose proof (Z.mod_pos_bound c 8192 ltac:(clear; lia)) as PB. rewrite <- HP in PB.
    pose proof (Z.div_mod FS 4096 ltac:(clear; lia)) as DFS. rewrite FSA, Z.add_0_r in DFS.
    assert (FB8 : FB = (FS / 4096 * 512 + 4608 + 131072 + pos * 16) * 8) by (rewrite HFB; clear -DFS; lia).
    assert (FBD : Z.shiftr FB 3 = FS / 4096 * 512 + 4608 + 131072 + pos * 16) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; rewrite FB8, Z.div_mul; [reflexivity| clear; lia]).
    assert (FBR : FS + 36864 <= FB /\ FB + 128 <= FS + 36864 + 6 * 2^20) by (rewrite HFB; clear -PB; lia).
    assert (SR : 0x80000000 <= 2147450880 + Z.shiftr FB 3 /\ 2147450880 + Z.shiftr FB 3 + 16 <= 0x10007fff8000) by (rewrite FBD; clear -FBR FSL FSH DFS HFB; lia).
    assert (FBA : FB mod 8 = 0) by (rewrite FB8; apply Z_mod_mult).
    clear FB8 FBD.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM.
    pose proof (munch_refl [(lo, SP); (FS + 8, FS + 16); (FS + 20480 + pos, FS + 20480 + pos + 1); (FB, FB + 128); (2147450880 + Z.shiftr FB 3, 2147450880 + Z.shiftr FB 3 + 16)] m) as MUS.
    pose proof (wmono_refl asegs m) as WMS.
    flat constr:(PS) 10%nat. intros _ GSB SBC GMB MB GME ME GHE HE _.
    unfold A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND in GSB, SBC, GMB, MB, GME, ME, GHE, HE.
    lx_hide PS. lx_aceil. flat constr:(FSL) 2%nat. flclear FSL. intros FSL0 FSL1. flat constr:(FLA) 2%nat. flclear FLA. intros FLAb FLAw.
    (* [comment removed for export] *)
    lx_run (PLAN [0x5318c] [] 10%N).
    (* [comment removed for export] *)
    lazymatch goal with FLAl : bytes_at _ ?mx (FS + 20480) fl, WMl : wmono _ m _ |- _ =>
      pose proof (conj FLAl (wr_at_transport _ _ _ _ _ FLAw WMl) : u8arr asegs mx (FS + 20480) fl) as FLAx; clear FLAl FLAb end.
    pose proof (u8arr_store_ok asegs _ (FS + 20480) fl pos _ FLAx ltac:(rewrite FLL; clear -PB; lia) eq_refl) as SOK.
    zstep. change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a ?bs) _) =>
      pose proof (u8arr_write asegs mx (FS + 20480) fl pos (Z_to_bv 8 1) FLAx ltac:(rewrite FLL; clear -PB; lia)) as FLA'
    end.
    store_done. try clear FLAx. try clear SOK.
    flat constr:(FLA') 2%nat. flclear FLA'. intros FLAb2 FLAw2.
    assert (FLz : Z.of_nat (length (upd fl (Z.to_nat pos) (Z_to_bv 8 1))) = 8192) by (rewrite upd_length; exact FLL).
    (* [comment removed for export] *)
    lx_run (PLAN [0x531a4] [] 20%N).
    repeat match goal with |- context [Z_to_bv 64 (?a + ?b)] =>
      lazymatch b with context [pos] => replace (a + b) with FB by (rewrite HFB; clear; lia) end end.
    (* [comment removed for export] *)
    destruct FSL1 as [FSLO|FSHI]; lx_run (PLAN [] [] 90%N); lx_unhide;
      lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m ?mx', FLl : bytes_at _ ?mx'' (FS + 20480) _ |- _ =>
        apply evtA_done; unfold sm1_found_post; cbv zeta; rewrite <- HFB0; unfold shd;
        lx_exs; lx_ands;
        [ lx_mseq
        | eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUl]; lx_subfp]
        | exact (wmono_trans asegs _ _ _ WM WMl)
        | assumption | assumption
        | split; [exact FLl| rewrite upd_length; exact (wr_at_transport _ _ _ _ _ FLAw WMl)]
        | match goal with K : rw_cells _ _ FB [_; _; _; C8 (Z_to_bv 64 ?e)] |- _ => replace e with (FS + 20480 + pos) in K by (clear; lia); exact K end
        | replace (2147450880 + Z.shiftr FB 3) with (Z.shiftr FB 3 + 2147450880) by (clear; lia);
          eapply rw_cells_reshape; [eassumption| cbn; split; [reflexivity| exact I] | vm_compute; reflexivity]
        | eapply (poison_statics_transport _ _ _ PS MUl); intros A' n' H'; cbn; clear -H' LOIMG SPL FSL0 FBR SR PB H; lia
        | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition smalloc1_post (SP FS BLK T CTX lo hint : Z) (fl : list byte)
      (ra gp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc1 ()) "Lms',$5.(7.(9.&40.)Lx5,(9.&40.)(7.(9.&40.)Lx11,(9.&40.)(7.(9.&40.)Lx12,(9.&40.)(7.(9.&40.)Lx13,(9.&40.)(7.(9.&40.)Lx14,(9.&40.)(7.(9.&40.)Lx15,(9.&40.)(7.(9.&40.)Lx16,(9.&40.)(7.(9.&40.)Lx17,(9.&40.)(7.P,(9.&40.)(10.(9.&8.))Lm',P,(9.&40.)(10.(9.&8.))(7.$8.Lr,$8.(:.(>.$5.R;.(15.(0.O17.(1.&40.O1?.)O16.(1.&40.$4.)R:.O15.O14.O13.O12.(1.&40.R1.)R9.R8.R7.R6.R5.R4.R3.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)O3.(3:.O17.)O2.(18.(9.&40.))R2.(19.$1:.)))(:.(2>.$1:.O1.R2.)(:.(25.$1:.R2.)(:.(32.$1:.R2.O1:.O1?.)(:.(34.R2.O1>.O1=.O1<.O1;.)(:.(40.R2.)(7.$8.Lpos,$8.(7.$8.Lc,$8.(7.(9.&8.)Lb,(9.&8.)(7.(1>.(9.&8.))Lj1,(1>.(9.&8.))(7.(1>.(9.&8.))Lj2,(1>.(9.&8.))ZFB,$8.(3;.O1>.+1.R5.)(:.(>.$8.R7.R1.)(:.(:.(;.=R5.)(<.R5.(=.+2.+40.)))(:.(>.$8.R6.(?.R5.+2000.))(:.(>.(10.(9.&8.))(11.(9.&8.)O18.(12.R6.))(13.(9.&8.)R4.))(:.(>.$8.(14.&8.R4.)=)(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.O1:.O1?.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.O1>.+8.)(3.O1>.+10.))(2:.(2;.$8.$8.)(2<.$8.$8.(3.(3.O1>.+5000.)R6.)(3.(3.(3.O1>.+5000.)R6.)+1.))(2:.(2;.$8.$8.)(2<.$8.$8.R1.(3.R1.+80.))(2:.(2;.$8.$8.)(2<.$8.$8.(3<.R1.)(3.(3<.R1.)+10.))(2=.(2;.$8.$8.)))))))O1.R8.)(:.(2?.$1:.R8.(3.O1>.+8.)(2:.$30.(31.(1.&40.(3.R5.+1.)))(2=.$30.)))(:.(21.$1:.R8.(3.O1>.+5000.)(3=.(9.&8.)O18.(12.R6.)(1.&8.+1.)))(:.(2?.$1:.R8.R1.(2:.$30.(3>.#18.R3.)(2:.$30.(31.(1.&40.O1?.))(2:.$30.(3>.#58.R2.)(2:.$30.(31.(1.&40.(3.(3.O1>.+5000.)R6.)))(2=.$30.))))))(2?.$1:.R8.(3<.R1.)(2:.$30.(3>.#10.(3?.(9.&8.)(1.&8.=)#10.))(2=.$30.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L16648947209.1 L17120848823.0 L2106043955.7  L21434465688.5 L21943567510.23L222370686.1   L226564034.2   L22706556426.7 L2416881682.3  L25336979675.2 L25640760266.1 L27157704107.5 L32165929634.0 L36518867962.2 L39188636933.0 L43442053680.7 L45051584734.1 L47128140407.9 L52172457863.2 L54587168821.2 L55588686165.0 L6022035069.3  L62083074719.1 L63489361093.10L63489361093.6 L65271643703.0 L8618464589.2  L9678154644.5  00000400500P00f02>02?02H02^02i02j02n03D03E03N03O03l04004T04U04]04^04j04n05S05j05k06306CS2FSSS3hAR2FS2lo5LOIMG3pos2FB2SRS3hAR2FS2lo5LOIMG4FSH'S3hAR2SP2FS3BLK3CTX2lo2BH2CH3BHI3CHI4SEP14SEP25LOIMG4FSL'4FSH'3pos2PB2FB3HFB2SR2A'2n'2H'FS2FS4FSL'S2SP2FS2lo3pos2FB1y2HyS2SP2lo3SPLFS2FSS3hAR2FS2lo5LOIMG4FSH'SS4hint2i0SS3hAR2FS4FSL'4FSH'3pos2PB3DFSS2FSS3hAR2FS2lo5LOIMG4FSH'3pos2PB2FB3HFBFS2FS3posSS2FS3pos3DFSS2FSS3hAR3BLK3CTX2lo2BH2CH5LOIMG2A'2n'2H'S3hAR2lo5LOIMG2A'2n'2H'SS3pos2PBS2SP2lo2A'2n'2H'". (* [comment removed for export] *)
  Lemma smalloc1_spec : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc1 ()) "Pra,(9.&40.)Pgp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.PBLK,$8.PT,$8.PCTX,$8.Plo,$8.Phint,$8.Pfl,(1>.(9.&8.))PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(10.(9.&8.))P,(:.(;.+1000.R9.)(6.(;.(3.R9.+1000.)+10000.)(;.+65?000.R9.)))P,(;.(3.R:.+1000.)(24.VhAR,))P,(;.+65?000.R9.)P,(;.(3.R:.+10000.)(24.VhAR,))P,(:.(;.+1000.R<.)(6.(;.(3.R<.+1000.)+10000.)(;.+65?000.R<.)))P,(;.(3.R=.+1000.)(24.VhAR,))P,(:.(;.+65?000.R10.)(6.(;.(3.R10.$33.)+7???7000.)(;.+10007???8000.R10.)))P,(;.(3.R11.$33.)(24.VhAR,))P,(>.$8.(?.R12.+1000.)=)P,(:.(;.=R>.)(<.R>.(=.+2.+40.)))P,(:.(:.(;.+1000.R13.)(6.(;.(3.R13.+1000.)+10000.)(;.+65?000.R13.)))(6.(;.(3.R13.+1000.)+7???7000.)(;.+10007???8000.R13.)))P,(:.(;.+65?000.R12.)(6.(;.(3.R12.+10000.)+7???7000.)(;.+10007???8000.R12.)))P,(6.(;.(3.R13.+10000.)R16.)(;.(3.R16.$33.)R13.))P,(6.(;.(3.R16.+1000.)R17.)(;.(3.R17.$33.)R16.))P,(34.R?.R18.R17.R16.R15.)P,(40.R10.)P,(23.VCS,R19.+1000.)P,(23.VCS,R18.+10000.)P,(23.VCS,R1:.+1000.)P,(23.VCS,R1=.$33.)P,(7.(9.&40.)Ltb,(9.&40.)(7.(9.&40.)Lte,(9.&40.)(35.$1:.R17.(3.R1>.+30.)(2:.$30.(31.R2.)(2:.$30.(31.R1.)(2=.$30.))))))P,(35.$1:.R16.(3.R1?.+58.)(2:.$30.(31.(1.&40.+14.))(2:.$30.(36.(1.&8.=))(2=.$30.))))P,(2?.$1:.R17.(3.R20.+8.)(2:.$30.(31.(1.&40.R1;.))(2=.$30.)))P,(21.$1:.R18.(3.R21.+5000.)R1;.)P,(>.$8.(20.(22.(9.&8.)R1<.))+2000.)P,Pi,$8.Pb,(9.&8.)P,(:.(;.=R2.)(<.R2.+2000.))P,(>.(10.(9.&8.))(11.(9.&8.)R20.(12.R3.))(13.(9.&8.)R2.))P,(>.$8.(14.&8.R3.)=)(7.(1>.(9.&8.))Ljunk,(1>.(9.&8.))(7.(1>.(9.&8.))Lsj,(1>.(9.&8.))(:.(2?.$1:.R21.(3;.R2:.+1.R7.)(2:.$30.(3>.#80.R2.)(2=.$30.)))(2?.$1:.R21.(3<.(3;.R2:.+1.R7.))(2:.$30.(3>.#10.R1.)(2=.$30.))))))P,(7.$8.Li0,$8.(7.(9.&8.)Lb0,(9.&8.)(:.(:.(;.=R2.)(<.R2.+2000.))(:.(>.(10.(9.&8.))(11.(9.&8.)R20.(12.R2.))(13.(9.&8.)R1.))(>.$8.(14.&8.R1.)=)))))P,(32.$1:.R1<.R21.R26.)P,(;.(24.VhAR,)R22.)P,(;.R23.(37.R28.+=0.))P,(;.R29.(=.+2.+3>.))P,(23.VCS,R25.(37.R2:.R25.))P,(25.$1:.R21.)(26.$1:.VAL,VCS,(42.R2<.R2;.R2:.R29.R28.R27.R26.R25.R49.R48.R46.R45.R44.R43.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R24.R23.R22.)(15.(0.R49.(1.&40.R2<.)R48.(1.&40.$4.)R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.)R24.(1.&40.(39.+1.))R23.(18.(9.&40.))R22.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint fl F fc m
      BL BH CL CH TL TH FSL FSH FSA HNT BHI CHI SEP1 SEP2 SS PS BCS CCS TCS FCS TT HDR HC FLA FLL HFR FREE ST LOIMG SPL SPH SCS MI.
    pose proof FSL as FSL'. pose proof FSH as FSH'. unfold kHighMemBeg, kFakeBytes in FSL', FSH', BHI, CHI, SEP1, SEP2.
    eapply evtA_cut.
    { eapply (sm1_A ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint F fc m);
        first [eassumption | eapply crange_sub; [exact FCS| clear; lia| unfold kFakeBytes; clear; lia]]. }
    cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1).
    assert (LO1 : forall A' n', A' + n' <= lo -> disjoint_from [(lo, SP)] A' n') by (intros A' n' H'; cbn; clear -H'; lia).
    assert (FLA1 : u8arr asegs m1 (FS + 20480) fl)
      by (eapply u8arr_transport; [exact FLA| exact MU1| exact WM1| apply LO1; rewrite <- (Nat2Z.id (length fl)), FLL; clear -LOIMG FSH'; lia]).
    assert (HC1 : rw_cells asegs m1 (FS + 8) [C8 (Z_to_bv 64 hint)])
      by (eapply rw_cells_transport; [exact HC| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH'; lia]).
    assert (SS1 : smalloc_statics m1 FS BLK T CTX)
      by (eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MU1); intros A' n' H'; apply LO1; clear -H' LOIMG CH BH; lia).
    assert (PS1 : poison_statics m1) by (eapply (poison_statics_transport _ _ _ PS MU1); intros A' n' H'; apply LO1; clear -H' LOIMG; lia).
    eapply evtA_cut.
    { eapply (scan1_loop (Z.to_nat 8192) 8192 hint); first [reflexivity | exact HNT | exact FLA1 | exact FLL | exact MI1 | clear; lia | idtac];
        [eapply crange_sub; [exact FCS| clear; lia| unfold kFakeBytes; clear; lia] | clear -FSL'; lia | exact FSH']. }
    cbv beta. intros ms2 [(r' & c & pos & b & Hc & HP & NTH & Hb & ->) | (ALL & x5 & x12 & x15 & x17 & ->)].
    - assert (PB : 0 <= pos < 8192) by (rewrite HP; apply Z.mod_pos_bound; clear; lia).
      destruct (HFR pos b ltac:(clear -PB; lia) NTH Hb) as (junk & sj & FRM & FSHD).
      set (FB := fsk_frame FS 1 pos) in *.
      assert (HFB : FB = FS + 36864 + 1048576 + pos * 128) by (subst FB; unfold fsk_frame; clear; lia).
      pose proof (Z.div_mod FS 4096 ltac:(clear; lia)) as DFS. rewrite FSA, Z.add_0_r in DFS.
      assert (FBD : Z.shiftr FB 3 = FS / 4096 * 512 + 4608 + 131072 + pos * 16).
      { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
        replace FB with ((FS / 4096 * 512 + 4608 + 131072 + pos * 16) * 8) by (rewrite HFB; clear -DFS; lia). rewrite Z.div_mul; [reflexivity| clear; lia]. }
      assert (SR : 0x80000000 <= shd FB /\ shd FB + 16 <= 0x10007fff8000) by (unfold shd; rewrite FBD; clear -PB FSL' FSH' DFS; lia).
      assert (FRM1 : rw_cells asegs m1 FB [CB 128 junk])
        by (eapply rw_cells_transport; [exact FRM| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH' HFB PB; lia]).
      assert (FSHD1 : rw_cells asegs m1 (shd FB) [CB 16 sj])
        by (eapply rw_cells_transport; [exact FSHD| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG SR; lia]).
      assert (MUW : munch [(lo, SP); (FS + 8, FS + 16); (FS + 20480 + pos, FS + 20480 + pos + 1); (FB, FB + 128); (shd FB, shd FB + 16)] m m1).
      { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros y Hy. lia. }
      eapply evtA_mono.
      { eapply (sm1_found ra gp t1 t2 s0 s1 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo pos c r' _ fl junk sj F fc m m1);
          first [sassumption | cassumption | exact FSL | exact FSH | exact FSA | exact Hc | exact HP | exact HC1 | exact FLA1 | exact FLL | exact FRM1 | exact FSHD1
                | exact FCS | exact PS1 | exact FR1 | exact ST1 | exact LOIMG | exact SCS | exact MUW | exact WM1 | exact MI1
                | clear -SPL; lia | clear -SPH; lia]. }
      cbv beta. intros ms3 (x5 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & m3 & j1 & j2 & -> & MU3 & WM3 & MI3 & HC3 & FLA3 & FRM3 & FSH3 & PS3 & ST3).
      unfold smalloc1_post. exists x5, x11, x12, x13, x14, x15, x16, x17, m3, FB.
      split; [reflexivity|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3|].
      split. { eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MU3). intros A' n' H'. cbn. change (fsk_frame FS 1 pos) with FB.
               clear -H' LOIMG CH BH FSL' FSH' HFB SR PB BHI CHI SEP1 SEP2. lia. }
      split; [exact PS3|].
      exists pos, c, b, j1, j2. cbv zeta.
      split; [reflexivity|]. split; [exact Hc|]. split; [exact HP|]. split; [exact NTH|]. split; [exact Hb|].
      split; [exact MU3|]. split; [exact HC3|]. split; [exact FLA3|]. split; [exact FRM3| exact FSH3].
    - (* [comment removed for export] *)
      exfalso. flat constr:(FREE) 5%nat. flclear FREE. intros i0 b0 Hi0 N0 Z0.
      destruct (ALL ((i0 - hint) mod 8192) ltac:(apply Z.mod_pos_bound; clear; lia)) as (b1 & N1 & Z1).
      rewrite Zplus_mod_idemp_r in N1. replace (hint + (i0 - hint)) with i0 in N1 by (clear; lia).
      rewrite Z.mod_small in N1 by exact Hi0. rewrite N0 in N1. injection N1 as <-. exact (Z1 Z0).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SMalloc1.

End ARUN_1.
