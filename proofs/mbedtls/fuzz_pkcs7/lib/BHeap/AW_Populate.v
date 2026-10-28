(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr Asn1Aux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_Unwind AW_Unwind2 AW_MmapFixed AW_MmapDie AW_Poison.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AW_ClassId AW_Combined AW_Refill AW_GetFrom.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXBW Require Import LxAWTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import ATac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P000bd67aab25fbb9 1 1 16 3 1 1 57 1 60 1 6 44 1 45 1 47 1 58 1 59 1 61 16P0068f51292366f04 1 1 128 1 0 1 2 31 1 64 1P00cb3ac86fdb4e5d 1 1 16 2 1 1 48 1 5 35 1 39 1 40 1 49 1 50 16P01345e7e1f523f4c 0 4 0 1 10 1 12 1 13 1P017049d4eaaea8ba 0 2 0 1 35 1P0174aebd47399ce0 0 4 0 16 38 16 47 16 48 16P01866e4957c9cac7 0 4 0 1 51 1 65 1 66 1P01a67870d87c1ff6 0 4 0 16 38 16 47 16 48 16P01e20126e76223b0 1 1 128 1 0 1 2 38 1 51 1P021fcd05786e4db0 0 2 0 1 38 1P02256090d5b04539 1 1 2048 6 1 16 44 16 45 16 53 16 57 16 58 16 2 32 1 59 1P0237dfc661bed2a5 1 1 16 2 1 1 51 1 5 35 1 42 1 43 1 52 1 53 16P02388b417b703477 0 4 0 16 41 16 50 16 51 16P02a5bbe160cf2e0c 1 1 16 2 1 1 48 1 5 35 1 39 1 40 1 49 1 50 16P0335f3b93457f410 1 1 128 2 1 1 61 1 2 34 1 66 1P034b5268402c4665 0 2 0 1 37 1P03634866a270db23 1 1 2048 7 1 16 42 16 43 16 47 16 49 16 51 16 52 16 2 38 1 53 1P039664fb4a54d26f 1 2 16 3 0 1 57 1 60 1 16 3 1 1 58 1 59 1 2 61 1 62 1P03ae42f11f90a1f1 0 4 0 16 40 16 49 16 50 16P03f0be3574acea0b 2 57 1 1 128 5 0 1 2 1 58 1 64 1 65 1 2 40 1 66 1 1 1 524288 4 0 4096 1 4096 64 4096 65 4096 2 39 1 66 1P03f3f694e73987c0 1 1 128 2 1 1 61 1 2 34 1 66 1P04514d873a1350b3 1 2 16 2 0 1 51 1 16 2 1 1 50 1 2 52 1 53 1P046cae1a1ed3ddca 1 1 2048 7 1 16 41 16 42 16 46 16 48 16 50 16 51 16 2 36 1 52 1P049922c7dd6cf82d 0 4 0 16 41 16 50 16 51 16P04e59650a2ee64bf 1 1 128 2 1 1 60 1 2 39 1 63 1P04faade328d4910d 1 1 2048 7 1 16 42 16 43 16 47 16 49 16 51 16 52 16 2 38 1 53 1P05d6ec22caefeea3 1 1 16 3 0 1 57 1 60 1 6 44 1 45 1 47 1 58 1 59 1 61 16P05db59aa32110c19 0 2 0 1 7 1P06032bbb72c15b22 0 4 0 1 51 1 65 1 66 1P0663e1033ac41255 1 1 128 1 0 1 2 33 1 65 1P0666436c9162c85e 0 4 0 1 10 1 12 1 13 1P06c850154b169b87 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P06e76dbc520b4493 1 1 16 3 0 1 57 1 60 1 6 44 1 45 1 47 1 58 1 59 1 61 16P06e8db09a0ab6e3f 0 4 0 1 22 1 31 1 43 1P0703710564163efb 0 2 0 1 37 1P07173971f727ac53 0 4 0 16 40 16 49 16 50 16P071f5fa9ec4a1302 0 7 1 1 39 1 40 1 44 1 46 1 48 1 49 1P07366cbe6cd34c61 0 4 0 16 40 16 49 16 50 16P076713ef142b573d 1 1 128 1 0 1 2 39 1 50 32P078b5c42de50d6f1 0 4 0 16 40 16 49 16 50 16P07afd0083e2c1f76 0 4 0 1 51 1 65 1 66 1P07bbf10935fb3578 1 1 2048 6 1 16 44 16 45 16 53 16 57 16 58 16 2 32 1 59 1P08372bdead932736 0 4 0 1 51 1 65 1 66 1P0860bf3c51dc207e 1 1 2048 7 1 16 42 16 43 16 47 16 49 16 51 16 52 16 2 38 1 53 1P0862a2a6a773fad5 0 4 0 16 31 16 36 16 37 16P08722157879aaf04 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P0873abd6c7e9d85d 0 7 1 1 39 1 40 1 44 1 46 1 48 1 49 1P08776233466e313b 0 4 0 16 38 16 47 16 48 16P09263e29b8196c3b 0 3 0 1 24 1 25 1P093645dd776ffd07 1 1 2048 7 1 16 41 16 42 16 46 16 48 16 50 16 51 16 2 36 1 52 1P0948cb9d345f49e1 1 1 2048 7 1 16 41 16 42 16 46 16 48 16 50 16 51 16 2 36 1 52 1P0969a0acb3d59a1d 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P0a0b088d3b709db2 0 4 0 16 43 16 56 16 57 16P0a4b2fb38ed58a70 0 4 0 16 38 16 47 16 48 16P0a63c2cdc37dd0a2 0 4 0 16 40 16 49 16 50 16P0aae60846bb0b438 1 1 2048 7 1 16 41 16 42 16 46 16 48 16 50 16 51 16 2 36 1 52 1P0acd511f1dadc949 0 4 0 1 51 1 65 1 66 1P0b092da5bd4e5c54 0 2 0 1 36 1P0b27c44010c76a59 0 3 0 1 54 1 61 1P0b43fdf9907da766 0 2 0 1 44 1P0b57bf30fda16b75 1 1 128 1 0 1 2 31 1 61 1P0b699513f1c6905a 1 1 2048 7 1 16 41 16 42 16 46 16 48 16 50 16 51 16 2 36 1 52 1P0b6a6e355e10acf7 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P0b8ac94d2163b739 0 4 0 16 40 16 49 16 50 16P0bddc239c69a8d22 0 6 1 16 44 16 45 16 46 16 57 16 58 16P0c2b2877812b01c9 0 4 0 16 38 16 47 16 48 16P0c623fd209a6f69f 0 4 0 1 10 1 12 1 13 1P0caa4196736dc3e5 1 2 16 2 0 1 52 1 16 2 1 1 51 1 2 53 1 54 1P0cc25ba69a866021 0 4 0 16 41 16 50 16 51 16P0cfa0c4be6f17cf9 0 4 0 16 40 16 49 16 50 16P0d1b5c00269a4b4b 0 4 0 16 38 16 47 16 48 16P0d2ee0c0839059cd 0 3 0 1 22 1 23 1P0d8f3d92e4ce5a48 0 7 1 1 39 1 40 1 44 1 46 1 48 1 49 1P0de8ca2c253dc041 1 1 16 2 1 1 48 1 5 35 1 39 1 40 1 49 1 50 16P0df217253ec1f93d 1 1 16 3 1 1 57 1 60 1 6 44 1 45 1 47 1 58 1 59 1 61 16P0e974c8f79849794 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P0eaf7a72669e9690 0 4 0 16 40 16 49 16 50 16P0ef2a4ebcda80914 0 4 0 16 40 16 49 16 50 16P0f5bd0b1ccaeeae9 0 2 0 1 37 1P0fb37342bcb335fa 0 4 0 16 31 16 36 16 37 16P101edc2b854f1403 1 1 2048 7 1 16 41 16 42 16 46 16 48 16 50 16 51 16 2 36 1 52 1P101fa379ef21796c 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P103a23e762415a51 1 1 16 2 1 1 51 1 5 35 1 42 1 43 1 52 1 53 16P10621d0b838f1655 0 4 0 16 41 16 50 16 51 16P109199b239ffc4e3 0 2 0 1 37 1P10ae6634fda96bc9 1 2 16 2 0 1 51 1 16 2 1 1 50 1 2 52 1 53 1P112307168abb983a 0 4 0 1 10 1 12 1 13 1P112815e32c6d8473 0 4 0 16 38 16 47 16 48 16P11538047f932eb65 2 51 1 1 128 5 0 1 1 1 52 1 58 1 59 1 2 34 1 60 1 1 1 524288 4 0 4096 2 4096 58 4096 59 4096 2 33 1 60 1P1164aa52436535ac 1 1 128 1 0 1 2 37 1 50 1P121a0566ad8a3cd5 1 1 2048 7 1 16 42 16 43 16 47 16 49 16 51 16 52 16 2 38 1 53 1P121eb79399001c29 1 1 4096 2 0 1 56 1 3 30 1 57 1 58 4096P126bcb4d248b9653 1 2 16 2 0 1 51 1 16 2 1 1 50 1 2 52 1 53 1P127018640e914e57 0 4 0 16 41 16 50 16 51 16P129c5eb3fdb96cb2 1 1 128 2 1 1 60 1 2 39 1 63 1P129fb85790c0c688 1 1 16 2 1 1 50 1 5 35 1 41 1 42 1 51 1 52 16P12c9ba41fdcf1143 0 4 0 16 40 16 49 16 50 16P12fa162580906169 0 4 0 1 10 1 12 1 13 1P13203732dd2e6e10 0 2 0 1 54 1P136add1b9440588b 0 3 0 1 22 1 23 1P138baf45a73e219b 0 4 0 16 31 16 36 16 37 16P13d5620f2fa0d26f 0 4 0 16 38 16 47 16 48 16P144f6c813a039907 0 4 0 16 43 16 56 16 57 16P1465cff12c80c498 0 2 0 1 22 1P14cc90288c5ec840 0 2 0 1 36 1P15287f572bb61fa9 0 2 0 1 22 1P1549d958a9014a70 0 4 0 16 40 16 49 16 50 16P15f4b3fe7d6fefd2 1 2 16 2 0 1 52 1 16 2 1 1 51 1 2 53 1 54 1P161423834dec2e0c 0 4 0 16 41 16 50 16 51 16P16f58513ec777349 0 4 0 16 40 16 49 16 50 16P17791190b83d562e 0 4 0 16 40 16 49 16 50 16P17a2afa9d3bd6ce9 1 1 2048 6 0 16 52 16 53 16 60 16 66 16 67 16 2 33 1 68 1P17ea77ce8ba71e46 0 4 0 1 10 1 12 1 13 1P186d90439ac4c446 0 4 0 16 38 16 47 16 48 16P18d14fa6222d3352 0 4 0 16 38 16 47 16 48 16P18de6495c3c5d8bd 1 1 128 1 0 1 2 38 1 62 1P1953a0b61ff3aee0 0 2 0 32 39 1P198f7377e6d68671 2 51 1 1 128 5 0 1 1 1 52 1 58 1 59 1 2 34 1 60 1 1 1 524288 4 0 4096 2 4096 58 4096 59 4096 2 33 1 60 1P19f483805de3f801 1 1 128 2 1 1 61 1 2 34 1 66 1P1a8dc00d835b3813 1 1 2048 7 1 16 42 16 43 16 47 16 49 16 51 16 52 16 2 38 1 53 1P1b2335024d1823ea 0 4 0 4096 30 4096 56 4096 57 4096P1b3d079afd4d88e1 0 4 0 16 41 16 50 16 51 16P1b64377ef0f98101 0 3 0 1 28 1 33 1P1b902319e6efa561 0 4 0 16 40 16 49 16 50 16P1b938ab81988c5c4 0 4 0 16 41 16 50 16 51 16P1becd4a8dd1f657e 0 4 0 16 31 16 36 16 37 16P1c1342dd8bf465b2 2 51 1 1 128 5 0 1 1 1 52 1 58 1 59 1 2 34 1 60 1 1 1 524288 4 0 4096 2 4096 58 4096 59 4096 2 33 1 60 1P1c3364a7c88654bc 0 2 0 1 33 1P1c4c3d90f28900a3 0 4 0 16 31 16 36 16 37 16P1c7d86746a76a2f1 1 1 128 2 1 1 61 1 2 34 1 66 1P1ca896e8feae2949 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P1ce89070b9773b67 0 4 0 16 43 16 56 16 57 16P1cfbf3e81da9e7b6 0 4 0 16 38 16 47 16 48 16P1d1a250e1e79808d 0 7 0 1 38 128 50 1 51 1 59 1 63 1 64 1P1d4b2920cf454c14 0 4 0 16 40 16 49 16 50 16P1d4fa90a04ac49a7 0 7 0 1 38 128 50 1 51 1 59 1 63 1 64 1P1d6d7676786009a7 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P1da315ff7b45ca41 1 1 16 2 1 1 51 1 5 35 1 42 1 43 1 52 1 53 16P1e6b79ded0b5510b 0 4 0 1 10 1 12 1 13 1P1e7199765b64e7cf 1 1 64 2 0 1 23 1 2 21 1 47 1P1e8700b9d9841716 0 2 0 1 35 1P1ede6d8818cdb82e 1 1 4194304 7 0 32768 54 32768 56 32768 62 32768 63 32768 64 32768 65 32768 2 38 1 66 1P1eed74ea2a252137 0 4 0 16 38 16 47 16 48 16P1f0d266ed5cf1f51 1 1 128 1 0 1 2 37 1 50 1P1f6b4bc09d173bbc 2 55 1 1 128 3 0 1 2 1 58 1 2 40 1 64 1 1 1 128 2 0 1 1 1 2 39 1 64 1P1ff88f45b012d56d 0 6 1 1 32 1 33 1 35 1 37 1 38 1P2022d2ac400891c0 1 1 2048 7 1 16 42 16 43 16 47 16 49 16 51 16 52 16 2 38 1 53 1P20ae1b880fec4953 0 4 0 16 40 16 49 16 50 16P20e65806a48db653 1 1 2048 7 1 16 41 16 42 16 46 16 48 16 50 16 51 16 2 36 1 52 1P20e960d83fbcb76e 1 1 16 2 1 1 37 1 5 30 1 32 1 33 1 38 1 39 16P20eeb656d0daf036 0 4 0 16 41 16 50 16 51 16P21437459a88898c6 0 4 0 16 31 16 36 16 37 16P21ce7b498a85395b 0 7 1 1 39 1 40 1 44 1 46 1 48 1 49 1P21cf561384e050be 0 4 0 1 10 1 12 1 13 1P21d60624b3833e80 1 1 16 2 1 1 50 1 5 35 1 41 1 42 1 51 1 52 16P220a0776963d0c6f 0 4 0 16 40 16 49 16 50 16P22233e70bc4129b2 0 2 0 1 53 1P227f9ca37c874b1a 0 2 0 1 35 1P228d8e3e0599c93d 0 4 0 16 41 16 50 16 51 16P22bc5d758fe11673 1 2 16 3 0 1 57 1 60 1 16 3 1 1 58 1 59 1 2 61 1 62 1P22d49e1dc28b5cd0 1 1 2048 7 1 16 41 16 42 16 46 16 48 16 50 16 51 16 2 36 1 52 1P2310c4327bddbff8 1 1 2048 7 1 16 42 16 43 16 47 16 49 16 51 16 52 16 2 38 1 53 1P23b20bc4756ef90c 1 1 128 1 0 1 2 32 1 65 1P241e484276f74d7b 1 1 16 2 1 1 37 1 5 30 1 32 1 33 1 38 1 39 16P24458d729d81dade 1 1 2048 7 1 16 42 16 43 16 47 16 49 16 51 16 52 16 2 38 1 53 1P248a53b802f76313 0 4 0 16 41 16 50 16 51 16P2498e158622dfcb3 0 4 0 16 41 16 50 16 51 16P24bdaa7a030d82d5 0 3 0 1 25 1 34 1P24d1b4c871a2fe02 1 1 2048 7 1 16 42 16 43 16 47 16 49 16 51 16 52 16 2 38 1 53 1P24d49daf9597fffd 1 1 2048 7 1 16 41 16 42 16 46 16 48 16 50 16 51 16 2 36 1 52 1P24e297d8c3212306 0 7 1 1 39 1 40 1 44 1 46 1 48 1 49 1P24fbfbafa651bea5 1 2 16 2 0 1 51 1 16 2 1 1 50 1 2 52 1 53 1P2558135e737beb9b 0 4 0 16 40 16 49 16 50 16P25607622dcdbbae1 0 4 0 16 41 16 50 16 51 16P256c4ab595c30966 0 2 0 1 35 1P25bc6dbdaf6a1b1c 1 1 16 3 1 1 57 1 60 1 6 44 1 45 1 47 1 58 1 59 1 61 16P25d2e89339c48d11 1 1 128 2 1 1 61 1 2 34 1 66 1P26d8dc8a92cc818a 0 4 0 16 38 16 47 16 48 16P2745e0fde8c63cf7 0 4 0 16 41 16 50 16 51 16P27470573de166dbc 1 2 16 2 0 1 52 1 16 2 1 1 51 1 2 53 1 54 1P275304f841d3a5b9 0 7 1 1 39 1 40 1 44 1 46 1 48 1 49 1P27dd3d8746774737 1 1 16 3 1 1 57 1 60 1 6 44 1 45 1 47 1 58 1 59 1 61 16P27f2adf5666e857f 0 4 0 16 38 16 47 16 48 16P28168350c8822e80 0 4 0 16 40 16 49 16 50 16P28a3a1ac958d3ce9 0 2 0 1 54 1P28c5603687881a83 0 4 0 16 38 16 47 16 48 16P28cf5bf5687013b2 0 4 0 16 40 16 49 16 50 16P28d712d16e1755d8 0 4 0 16 38 16 47 16 48 16P297c73f4a6e0a5c3 1 1 16 2 1 1 50 1 5 35 1 41 1 42 1 51 1 52 16P29c35a244c74d99b 0 6 1 1 32 1 33 1 35 1 37 1 38 1P29f9c42fc19efb6a 0 2 0 1 33 1P2a48add5ac70d236 0 4 0 16 41 16 50 16 51 16P2a9559fe849b2ed0 1 1 4194304 7 0 32768 54 32768 56 32768 62 32768 63 32768 64 32768 65 32768 2 38 1 66 1P2aff96a94a52119c 1 1 128 1 0 1 2 37 1 62 1P2b4816944a08dfde 0 4 0 1 51 1 65 1 66 1P2b6ae7197c8a65af 0 4 0 16 38 16 47 16 48 16P2b9cddc50b98b9cc 0 2 0 1 38 1P2bf17342e8e4d297 0 4 0 16 38 16 47 16 48 16P2c0e75e4ac1784db 0 2 0 1 37 1P2c5ca513e52b6b71 0 4 0 16 41 16 50 16 51 16P2c8dbdb8c74c15aa 1 1 16 2 1 1 57 1 5 41 1 44 1 45 1 58 1 59 16P2ca8819f9fd79ef9 0 4 0 16 41 16 50 16 51 16P2cbcd2347e278bb7 0 4 0 16 38 16 47 16 48 16P2cf1360ace494bd0 0 4 0 16 43 16 56 16 57 16P2d021b722306db0d 1 1 128 1 0 1 2 38 1 62 1P2d6f1baa3c741093 0 4 0 1 24 1 33 1 44 1P2d81e98d86e24355 1 1 16 2 1 1 50 1 5 35 1 41 1 42 1 51 1 52 16P2db7c4f66dc9dbc3 0 4 0 16 38 16 47 16 48 16P2dbbfff6f63a9bd9 1 1 2048 7 1 16 42 16 43 16 47 16 49 16 51 16 52 16 2 38 1 53 1P2dc64942c9600511 0 3 0 1 23 1 32 1P2e2e7b6c2a7ebda8 0 4 0 16 40 16 49 16 50 16P2e3a5d14dd9ecfc7 1 1 128 1 0 1 2 30 1 61 1P2e7e5c2ff1c73c9d 0 2 0 1 17 1P2e9dcd33b292bbc9 1 1 16 2 1 1 57 1 5 41 1 44 1 45 1 58 1 59 16P2ee0514aaef9fd0e 0 6 1 16 44 16 45 16 46 16 57 16 58 16P2ee292d365e3ee63 1 1 2048 7 1 16 41 16 42 16 46 16 48 16 50 16 51 16 2 36 1 52 1P2ee55be8f8e96f72 1 1 128 1 0 1 2 32 1 64 1P2f059ed4dcb676e0 0 4 0 16 41 16 50 16 51 16P2f12f07884c0f9ad 0 4 0 16 40 16 49 16 50 16P2f3c6592b16245ea 1 2 16 2 0 1 58 1 16 2 1 1 57 1 2 59 1 60 1P302eae982190efd4 0 4 0 1 10 1 12 1 13 1P304cde01322df2e8 0 4 0 1 51 1 65 1 66 1P304fdcaaf42e3103 0 2 0 1 37 1P30bc345fa45623e0 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P30d5cea67ca4d0a3 0 4 0 16 43 16 56 16 57 16P318df67f6586cacc 1 1 4096 2 1 1 56 1 3 0 1 57 1 58 4096P32d17fc75ca823d0 0 4 0 16 41 16 50 16 51 16P32d89af6767c1dc8 1 2 16 2 0 1 52 1 16 2 1 1 51 1 2 53 1 54 1P32e83fff47feec3d 1 1 2048 6 1 16 44 16 45 16 53 16 57 16 58 16 2 32 1 59 1P3319ffab0ebff7cc 0 4 0 16 31 16 36 16 37 16P3327fea47b8e6328 0 4 0 1 20 64 22 1 40 1P337288a65a313d1b 1 1 128 1 0 1 2 37 1 51 1P33895cbf91343c0f 0 4 0 16 38 16 47 16 48 16P339420e4eab1de88 0 4 0 16 38 16 47 16 48 16P343ed60ec5600df2 0 4 0 16 40 16 49 16 50 16P354308f9ec8a048a 0 4 0 1 51 1 65 1 66 1P3560b2e98bd090c7 1 1 128 1 0 1 2 37 1 62 1P357fac0a7aaf59d4 0 2 0 1 35 1P36240d918e3d42a4 1 1 128 1 0 1 2 37 1 51 1P3638a37ea5d4070e 1 1 128 2 1 1 60 1 2 39 1 63 1P377f9a043b134770 0 7 1 1 39 1 40 1 44 1 46 1 48 1 49 1P37a3cb618a51e5d2 2 57 1 1 128 5 0 1 2 1 58 1 64 1 65 1 2 40 1 66 1 1 1 524288 4 0 4096 1 4096 64 4096 65 4096 2 39 1 66 1P38a204bd1ae4cddd 0 4 0 16 38 16 47 16 48 16P38d27fbcd63d8dea 1 1 16 2 1 1 48 1 5 35 1 39 1 40 1 49 1 50 16P38df63aa75670fc2 0 2 0 1 37 1P390151bfa6751b76 1 1 16 2 1 1 51 1 5 35 1 42 1 43 1 52 1 53 16P392e487fe597e39a 0 4 0 16 41 16 50 16 51 16P39740a5dc3611403 0 4 0 16 41 16 50 16 51 16P3b5d206965a3645b 1 2 16 2 0 1 49 1 16 2 1 1 48 1 2 50 1 51 1P3b61b42c9158c871 0 7 1 1 39 1 40 1 44 1 46 1 48 1 49 1P3b6addfae4378be6 0 4 0 1 51 1 65 1 66 1P3b762c8e04ef861a 1 1 128 1 0 1 2 38 1 51 1P3b7d68f76a8c3ff3 0 2 0 1 40 1P3b87437617bdeedf 0 4 0 16 41 16 50 16 51 16P3bbce87f3503030b 0 7 1 1 39 1 40 1 44 1 46 1 48 1 49 1P3bdcc933af6cf5bc 0 7 1 1 39 1 40 1 44 1 46 1 48 1 49 1P3bf7f6fa16552a76 2 51 1 1 128 5 0 1 1 1 52 1 58 1 59 1 2 34 1 60 1 1 1 524288 4 0 4096 2 4096 58 4096 59 4096 2 33 1 60 1P3c3df64b57a08b13 1 2 16 2 0 1 38 1 16 2 1 1 37 1 2 39 1 40 1P3c4e170de17aa222 0 4 0 16 41 16 50 16 51 16P3d3d741e346b58e9 0 2 0 1 38 1P3d42d350618c4508 0 4 0 16 41 16 50 16 51 16P3ea5f494d54c0ace 1 1 128 1 0 1 2 39 1 50 32P3efb5aedfd3a1f1c 0 2 0 1 43 1P3f3354922e3fcbbd 0 4 0 16 40 16 49 16 50 16P3f497577254f1787 0 4 0 16 43 16 56 16 57 16P3f8cbdb298cd919e 0 4 0 16 38 16 47 16 48 16N0010c7f50952ea8eN003f2d24b5170882N012059e9f79bb84dN0190b9e56967a383N01a0a2b1af826da6N01a103a578d113c4N01c794c559515786N01ea54488d5f503dN01ee24aa06744317N0213e502777e40d5N0265a25fd1ab182aN02680e63e6cc55bdN02b142bcc08f1518N02b5d54c5435c5ddN05025039b9f40273N056e8db5c7c7d5b4N058a9b44bd703b8fN05952596ced9412cN0653d8453ab71209N06606ff0ead7ab5cN06650ecb86c38d51N069d1417fdeb4c51N074bb7f49fd3c99cN0910112791aa691cN096e37dffbf6c32fN0a456f06abae2097N0b1619d044480efaN0b7dd9b7a44b1863N0ed056aab898c3b4N0f6be99c0ba540f8N1019063b771a6f03N103f401173114cc6N10a5a5ccd1d35248N10eddee622db96f4N1118c0d2538524feN119425bd31e0c470N11cbe208ef945355N1222792457ef5623N125c0e16c0a0a622N1261ce0e0ed9ca56N12b13ff54859d2b8N1301d4ba362eefdfN134450748674e2c8N134853c0614a8a4aN140601d3e5ef908eN14ebe19dc1b03a73N15b4e3b687553e1eN15cfd8ec0408f7e5N161dbb7c71b601a6N168b19030d58f99fN1747356031fda704N18ee329439a80bd3N192029f06a496200N19776d75e9af4f73N19f65238f0d98698N1a80183da49d09b1N1aa33a2fdfb2e99eN1cf7d2829f59b90aN1d3ccc64cb1734fcN1e44dae1d4b13781N1ee77f11e02a15adN1f3eb18439168e2cN1f646221dff6ead7N205b5db383a1488eN221f5ea64c38c0ccN226e697a6a075fb8N22755fc066ad6e13N22ced2102aff91caN230e205be80d7d27N230f0b99bacebcb6N23befee897403fb6N23ee4174c0b60b35N24ac82cb2ae31baaN259ea8f9ff422336N25bbd787d71b2aadN26178842e8b16058N26a93574936070a6N273407cad747a7b0N275bd295797d54b0N277da1fa5441c980N2799053f668c673eN279f09ba457b81cfN28214ae9e943bba6N2844f8a5ab138289N284d470d50a9530fN28b72ef5c8008cb4N28fdd6570889cfd6N29862f01c0f89844N29a14634d3103dfbN2a59099c6c47bb69N2a594718de92ff9aN2bdd64045d4b90dcN2d398029a5e43cc1N2e2f09ed9b3a3236N2e317b0bec2ad06eN2e369d7af6f08358N2ff0a2536b719ab7N302158fe3f3ec5abN30279caf4deaf623N30439e96b99e36deN324dd219e06e7f9bN32c7fd3bcf070f38N33442c4c588a09efN33d4aafcb72ac456N33eab3f6a0edd782N342c12fb2831ba9eN353777dca86a5570N355eec12534ff7bdN3584508ed9c153d3N3600a281ce9cb671N363a7994b679a3fcN36c62a2470a743f3N3776fa475ef9126cN37c1a9e32a6969ffN38a6ac9d7c9b8fbfN38be4a05db7dfc14N39692b85b12f554dN399ed111fc510a64N39bc5367c63fc752N39d693429eda2e63N3aa21c22ca58c11eN3aa38b1691cdbf90N3af7334b503a3c97N3b25a3878817e791N3b38442620358d34N3bece4638d605fe0N3bf0cf23a43fe053N3c0cabeb94fe51a6N3c21f0d2901b2ed5N3c38df3efdcf7743N3cd655cfa2634798N3d453be7df51b64bN3d78d6bd9e09ab33N3e01a35ea5aa952dN3e29b77f8e2d086bN3fd653f9556c8e9d"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_Populate () : Init.string Init.list := ["Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_INITED"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_PTR"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TSD_ARR"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.ivl"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "ARUN_1.thr_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.disjoint_from"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cells_size"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Datatypes.length"; "ARUN_1.A_TOOLNAME_GOT"; "ARUN_1.A_TOOLNAME"; "ARUN_1.A_ASAN_NAME"; "ARUN_1.A_REPORT_GOT"; "ARUN_1.A_PRINTF_CB"; "ARUN_1.A_APPEND_EMB"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_CFLAGS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_CFLAGS"; "ARUN_1.A_CF_LOGSYS"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_GOT_PAGESZ"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind.A_PAGESZ_CELL"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DECORATE"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_MMAP_LIMIT"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_GOT_SEALED2"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_DYING"; "ARUN_1.b12_ro"; "Stdlib.ZArith.BinInt.Z.le"; "ARUN_1.A_EMB"; "Corelib.Init.Logic.not"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.wr_at"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kEmbBytes"; "ARUN_1.emb_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "ARUN_1.b12_statics"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Stdlib.ZArith.BinInt.Z.sub"; "ARUN_1.B12_NEED"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "ARUN_1.A_FMT_OOM1"; "ARUN_1.A_PRINTF"; "Corelib.Init.Logic.or"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "ARUN_1.A_GCTS"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.A_INSTANCE"; "ARUN_1.Populate.popA_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_GetFrom.A_POPULATE"; "ARUN_1.A_NAME_POP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.class_size"; "ARUN_1.A_PREMAPPED"; "ARUN_1.Populate.pop_mwc_regs"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_MmapFixed.A_RAR_MAP"; "ARUN_1.A_INTERVAL"; "ARUN_1.Populate.pop_frame"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "ARUN_1.Populate.popB_post"; "stdpp.bitvector.definitions.bv_unsigned"; "ARUN_1.Populate.pop_exh_ret"; "ARUN_1.Populate.pop_exh_at_printf"].

Section ARUN_1. Context {hAR : arun}.
Set Printing Width 250.

Definition A_GCTS : Z := 0x71f94.          (* [comment removed for export] *)
Definition A_EFS : Z := 0x4a824.           (* [comment removed for export] *)
Definition A_PREMAPPED : Z := A_INSTANCE + 56.   (* [comment removed for export] *)
Definition A_INTERVAL : Z := A_INSTANCE + 40.    (* [comment removed for export] *)
Definition A_NAME_POP : Z := 0x1891d.      (* [comment removed for export] *)
Definition A_NAME_EFS : Z := 0x1a93d.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition thr_statics (m : mem) (CTX T : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "(0.(1.$2.O3.$3.(4.$5.(6.(7.&8.+1.))(4.$5.(8.#3.(4.(9.&8.)(7.&8.=)(4.(9.&8.)(7.&8.=)(4.(9.&8.)(7.&8.=)(:.(9.&8.))))))(4.$5.(;.(7.&40.=))(:.$5.)))))(0.(1.$2.O3.$<.(4.$5.(=.(7.&40.$>.))(:.$5.)))(0.(1.$2.O3.$>.(4.$5.(=.(7.&40.O2.))(:.$5.)))(1.$2.O3.(?.O2.+98.)(4.$5.(=.(7.&40.O1.))(:.$5.))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma thr_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "PW,(10.$11.)Pm,P,(9.&40.)(12.(9.&8.))Pm',P,(9.&40.)(12.(9.&8.))PCTX,$13.PT,$13.P,(14.R4.R2.R1.)P,(15.R6.R5.R4.)P,(16.R7.$3.+8.)P,(16.R8.$<.+8.)P,(16.R9.$>.+8.)P,(16.R:.(?.R7.+98.)+8.)(14.R9.R8.R7.)")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros W m m' CTX T (S1 & S2 & S3 & S4) MU D1 D2 D3 D4. unfold thr_statics.
  repeat split; (eapply ro_cells_transport; [eassumption| exact MU| cbn; assumption]).
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L23369167945.11L24931873411.11L33628179521.13L51696475855.1300000800>00N00XS1A1n2H1S1A2H0S1A1n2H02H11i2HiS1A1n1i2Hi". (* [comment removed for export] *)
#[using="Type"] Lemma wr_at_munch : forall W m m' A n, wr_at asegs m A n -> munch W m m' -> disjoint_from W A n -> wr_at asegs m' A n.
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros W m m' A n (H0 & H1 & H) MU DJ. split; [lia|]. split; [lia|].
  intros i Hi. unfold wview. rewrite (MU (wa (A + i))).
  - apply H. exact Hi.
  - eapply disjoint_outside; [exact DJ|]. rewrite wa_unsigned by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
#[using="Type"] Lemma rw_cells_munch : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "PW,(10.$11.)Pm,P,(9.&40.)(12.(9.&8.))Pm',P,(9.&40.)(12.(9.&8.))PA,$13.Pcs,(10.$5.)P,(17.$2.R4.R2.R1.)P,(15.R6.R5.R4.)P,(16.R7.R4.(18.(19.R3.)))(17.$2.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros W m m' A cs [[Hwf Hb] Hw] MU DJ. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact DJ.
  - eapply wr_at_munch; eauto.
Qed.
#[using="Type"] Lemma u32arr_munch : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "PW,(10.$11.)Pm,P,(9.&40.)(12.(9.&8.))Pm',P,(9.&40.)(12.(9.&8.))PA,$13.Pws,(10.(9.&40.))P,(1:.$2.R4.R2.R1.)P,(15.R6.R5.R4.)P,(16.R7.R4.(1;.+4.(18.(1<.(9.&40.)R3.))))(1:.$2.R6.R5.R4.)")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros W m m' A ws [Hb Hw] MU DJ. split.
  - eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact DJ.
  - eapply wr_at_munch; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition A_PRINTF : Z := 0x7ddd8.            (* [comment removed for export] *)
Definition A_FMT_OOM1 : Z := 0x221b8.          (* [comment removed for export] *)
Definition A_FMT_OOM2 : Z := 0x23fb2.          (* [comment removed for export] *)
Definition A_TOOLNAME_GOT : Z := 0x0f5e88.     (* [comment removed for export] *)
Definition A_TOOLNAME : Z := 0x0f7d18.         (* [comment removed for export] *)
Definition A_ASAN_NAME : Z := 0x240fe.         (* [comment removed for export] *)
Definition A_REPORT_GOT : Z := 0x0f6a18.       (* [comment removed for export] *)
Definition A_PRINTF_CB : Z := 0x19b710.        (* [comment removed for export] *)
Definition A_APPEND_EMB : Z := 0x6b948.         (* [comment removed for export] *)
Definition A_CF_LOGSYS : Z := A_CFLAGS + 64.   (* [comment removed for export] *)
Definition B12_NEED : Z := 1536.               (* [comment removed for export] *)
Definition b12_ro (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "(0.(1.$2.O1.$1=.(4.$5.(=.(7.&40.$1>.))(:.$5.)))(0.(1.$2.O1.$1>.(4.$5.(=.(7.&40.$1?.))(:.$5.)))(0.(1.$2.O1.$20.(4.$5.(=.(7.&40.+1.))(:.$5.)))(0.(1.$2.O1.$21.(4.$5.(=.(7.&40.$22.))(:.$5.)))(0.(1.$2.O1.$23.(4.$5.(=.(7.&40.$24.))(:.$5.)))(0.(1.$2.O1.$25.(4.$5.(6.(7.&8.=))(:.$5.)))(0.(1.$2.O1.$26.(4.$5.(=.(7.&40.$27.))(:.$5.)))(0.(1.$2.O1.$27.(4.$5.(=.(7.&40.+1000.))(:.$5.)))(0.(1.$2.O1.$28.(4.$5.(6.(7.&8.=))(:.$5.)))(0.(1.$2.O1.$29.(4.$5.(=.(7.&40.=))(:.$5.)))(0.(1.$2.O1.$2:.(4.$5.(=.(7.&40.+1.))(:.$5.)))(1.$2.O1.$2;.(4.$5.(;.(7.&40.=))(:.$5.))))))))))))))")
(* [comment removed for export] *).
Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L13811733765.19L15544748165.19L17600832389.19L19104145029.19L24767780997.19L26428365701.19L29843776389.19L3245756165.19 L62411961182.19L62518759301.19L62846120581.19L9917639301.19 00000100200300400500600700800900:00;00<SSSSSSSSSSSS". (* [comment removed for export] *)
#[using="Type"] Lemma b12_ro_transport : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "PW,(10.$11.)Pm,P,(9.&40.)(12.(9.&8.))Pm',P,(9.&40.)(12.(9.&8.))P,(2<.R2.)P,(15.R4.R3.R2.)P,PA,$13.Pn,$13.P,(0.(2=.+10000.R2.)(2=.(?.R2.R1.)+1=;8<8.))(16.R8.R3.R2.)(2<.R4.)")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros W m m' S MU DJ. unfold b12_ro, A_TOOLNAME_GOT, A_TOOLNAME, A_REPORT_GOT, A_PRINTF_CB, A_GOT_CFLAGS, A_CF_LOGSYS, A_CFLAGS,
    A_GOT_PAGESZ, A_PAGESZ_CELL, A_DECORATE, A_MMAP_LIMIT, A_GOT_SEALED2, A_DYING in *.
  decompose [and] S. repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition A_EMB : Z := 0x109268.
Definition emb_cells (P d cap sz : Z) (m : mem) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "(0.(17.$2.O1.$2>.(4.$5.(=.(7.&40.O5.))(:.$5.)))(0.(17.$2.O1.(?.$2>.+10.)(4.$5.(=.(7.&40.=))(:.$5.)))(0.(17.$2.O1.(?.$2>.+20.)(4.$5.(=.(7.&40.O4.))(4.$5.(=.(7.&40.O3.))(4.$5.(=.(7.&40.O2.))(:.$5.)))))P,(2?.(30.$13.O4.=))(31.$2.O1.O4.$32.))))")
(* [comment removed for export] *).
Local Ltac2 Set LiaOrc.tbl := fun () => "0030?L11159069500.15L23978045671.15L24316735975.15000001002003SSS". (* [comment removed for export] *)
#[using="Type"] Lemma emb_cells_transport : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "PW,(10.$11.)Pm,P,(9.&40.)(12.(9.&8.))Pm',P,(9.&40.)(12.(9.&8.))PP,$13.Pd,$13.Pcap,$13.Psz,$13.P,(33.R4.R3.R2.R1.R6.)P,(15.R8.R7.R6.)P,(34.$2.R8.R7.)P,PA,$13.Pn,$13.P,(0.(2=.+10000.R2.)(2=.(?.R2.R1.)+1=;8<8.))(16.R=.R3.R2.)(33.R8.R7.R6.R5.R9.)")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros W m m' P d cap sz (E1 & E2 & E3 & E4) MU WM DJ. unfold emb_cells, A_EMB in *.
  split; [eapply rw_cells_transport; [exact E1| exact MU| exact WM| apply DJ; cbn; lia]|].
  split; [eapply rw_cells_transport; [exact E2| exact MU| exact WM| apply DJ; cbn; lia]|].
  split; [eapply rw_cells_transport; [exact E3| exact MU| exact WM| apply DJ; cbn; lia]|].
  intros D0. eapply wr_at_transport; [exact (E4 D0)| exact WM].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Definition b12_statics (EP EB ECAP ESZ : Z) (m : mem) : Prop := b12_ro m /\ emb_cells EP EB ECAP ESZ m.
#[using="Type"] Lemma b12_statics_transport : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "PW,(10.$11.)PEP,$13.PEB,$13.PECAP,$13.PESZ,$13.Pm,P,(9.&40.)(12.(9.&8.))Pm',P,(9.&40.)(12.(9.&8.))P,(35.R6.R5.R4.R3.R2.)P,(15.R8.R3.R2.)P,(34.$2.R4.R3.)P,PA,$13.Pn,$13.P,(0.(2=.+10000.R2.)(2=.(?.R2.R1.)+1=;8<8.))(16.R=.R3.R2.)(35.R:.R9.R8.R7.R5.)")
(* [comment removed for export] *).
Proof.
  try lx_hide ASB.  (* [comment removed for export] *)
  intros W EP EB ECAP ESZ m m' (S & E) MU WM DJ. split; [exact (b12_ro_transport W m m' S MU DJ)|].
  exact (emb_cells_transport W m m' EP EB ECAP ESZ E MU WM DJ).
Qed.

(* [comment removed for export] *)
Definition b12_prints_stmt (AL : asan_layout) (CS : Z -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP0,$13.PF,(36.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(12.(9.&8.))Pm,P,(9.&40.)(12.(9.&8.))Plo0,$13.Pc,$13.PW,(10.(37.$13.$13.))P,(0.(2=.+1.R2.)(2=.R2.+1?.))P,(2<.R5.)P,(38.$2.R6.R5.R:.)P,(2=.(39.VhAR,)R6.)P,(2=.R7.(3:.R<.$3;.))P,(2=.R=.(3<.+2.+3?.))P,(30.$13.(3=.R>.+10.)=)P,(3>.O1.R:.(3:.R?.R:.))P,(15.(4.(37.$13.$13.)(3?.$13.$13.R;.R10.)R9.)R=.R<.)P,(34.$2.R>.R=.)P,(40.$2.R>.)(41.$2.O2.O1.Lms',$42.(43.(9.&40.)Lt0',(9.&40.)(43.(9.&40.)Lt1',(9.&40.)(43.(9.&40.)Lt2',(9.&40.)(43.(9.&40.)La0',(9.&40.)(43.(9.&40.)La1',(9.&40.)(43.(9.&40.)La2',(9.&40.)(43.(9.&40.)La3',(9.&40.)(43.(9.&40.)La4',(9.&40.)(43.(9.&40.)La5',(9.&40.)(43.(9.&40.)La6',(9.&40.)(43.(9.&40.)La7',(9.&40.)(43.(9.&40.)Lt3',(9.&40.)(43.(9.&40.)Lt4',(9.&40.)(43.(9.&40.)Lt5',(9.&40.)(43.(9.&40.)Lt6',(9.&40.)(43.P,(9.&40.)(12.(9.&8.))Lm',P,(9.&40.)(12.(9.&8.))(0.(30.$42.R11.(44.(45.(7.&40.+4<><0.)(7.&40.R24.)R3>.R3=.R10.R?.R>.(7.&40.R1>.)R39.R=.R<.R;.R:.R9.R8.R7.R6.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R5.R4.R3.R2.)R23.(7.&40.+4<><0.)R22.(46.(9.&40.))R1.(47.$2.)))(0.(15.(4.(37.$13.$13.)(3?.$13.$13.R1?.R24.)R1=.)R21.R1.)(0.(34.$2.R21.R1.)(0.(40.$2.R1.)(38.$2.R1.R1?.R24.)))))))))))))))))))))(44.(45.(7.&40.+4<>4<.)(7.&40.R13.)R2=.R2<.R2;.R2:.R29.(7.&40.R=.)R28.(7.&40.$48.)(7.&40.$1?.)R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.)R12.(7.&40.$49.)R11.(46.(9.&40.))R?.(47.$2.)))")
(* [comment removed for export] *).

Section Populate.
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
  #[using="IMG ALWF CSOK"] Lemma gcts_spec : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "Pra,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$13.PF,(36.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(12.(9.&8.))Pm,P,(9.&40.)(12.(9.&8.))PCTX,$13.PT,$13.Plo,$13.PW,(10.(37.$13.$13.))P,(2=.+65?000.R4.)P,(2=.(?.R5.+10000.)(39.VhAR,))P,(3>.VCS,R6.+10000.)P,(0.(2=.+1000.R6.)(4:.(2=.(?.R6.+1000.)+10000.)(2=.+65?000.R6.)))P,(2=.(?.R7.+1000.)(39.VhAR,))P,(14.R:.R9.R8.)P,(38.$2.R;.R8.R?.)P,(2=.(39.VhAR,)R9.)P,(2=.R:.(3:.R11.+20.))P,(2=.R12.(3<.+2.+3?.))P,(30.$13.(3=.R13.+10.)=)P,(3>.VCS,R=.(3:.R14.R=.))P,(15.(4.(37.$13.$13.)(3?.$13.$13.R>.R15.)R=.)R12.R11.)P,(34.$2.R13.R12.)P,(40.$2.R13.)P,(30.(9.&40.)R34.(7.&40.$4;.))(41.$2.VAL,VCS,Lms',$42.(43.(9.&40.)Lx11,(9.&40.)(43.P,(9.&40.)(12.(9.&8.))Lm',P,(9.&40.)(12.(9.&8.))(0.(30.$42.R3.(44.(45.R3:.(7.&40.R1<.)R39.R38.R37.R36.R35.R34.R33.(7.&40.(?.R16.+:?0.))R2.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.)R1;.(4<.R3:.)R1:.(46.(9.&40.))R1.(47.$2.)))(0.(15.(4.(37.$13.$13.)(3?.$13.$13.R15.R1<.)R14.)R19.R1.)(0.(34.$2.R19.R1.)(0.(40.$2.R1.)(38.$2.R1.R15.R1<.)))))))(44.(45.R37.(7.&40.R19.)R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.)R18.(7.&40.$4=.)R17.(46.(9.&40.))R15.(47.$2.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m0 m CTX T lo W
      C0 C1 CCS T0 T1 (TS1 & TS2 & TS3 & TS4) ST LOIMG SPL SPH SPA SCS MU WM MI ->.
    facts. unfold A_GCTS, A_TSD_INITED, A_TSD_PTR, A_TSD_ARR, A_TP in *.
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP)] m) as MU1. pose proof (wmono_refl asegs m) as WM1. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 40%N).
    lx_unhide. apply evtA_done. lx_exs; lx_ands;
      [> lx_mseq
      | match goal with MUl : munch _ m ?mx |- munch _ _ ?mx' => lx_munch MU MUl end
      | match goal with WMl : wmono _ m ?mx |- wmono _ _ ?mx' => lx_wmono WM WMl end
      | assumption | assumption ].
  Qed.

  (* [comment removed for export] *)
  Definition pop_frame (m : mem) (SP : Z) (q6 q5 q4 q3 q2 q1 q0 qra : word) : Prop :=
    rw_cells asegs m (SP + -64) [C8 q6; C8 q5; C8 q4; C8 q3; C8 q2; C8 q1; C8 q0; C8 qra].

  (* [comment removed for export] *)
  Definition popA_post (SP : Z) (gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a7 ra : word)
      (F : bvmap 5 word) (fc : bv 32) (R STAT RB c k au mu lo : Z) (m0 : mem) : machine_state -> Prop :=
    fun ms' => exists (x15 x16 : word) (m' : mem),
      ms' = MS (mkR ra (Z_to_bv 64 (SP + -64)) gp tp t0 t1 t2 (Z_to_bv 64 R) (Z_to_bv 64 STAT)
                   (Z_to_bv 64 A_INSTANCE) (Z_to_bv 64 (c * 2^32)) (Z_to_bv 64 c) (Z_to_bv 64 au) (Z_to_bv 64 k) x15 x16 a7
                   (Z_to_bv 64 RB) (Z_to_bv 64 (au + class_size c * k)) (Z_to_bv 64 mu) (Z_to_bv 64 (class_size c)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (if au + class_size c * k <=? mu then 0x4ccd4 else 0x4cc00)) fc None m' (seg_rom asegs)
      /\ munch [(lo, SP)] m0 m' /\ wmono asegs m0 m' /\ mem_inv asegs m'
      /\ pop_frame m' SP s6 s5 s4 s3 s2 s1 s0 ra
      /\ stk asegs m' lo (SP + -64).

  (* [comment removed for export] *)
  Ltac popA_leaf HB HAU HMU := apply evtA_done; unfold popA_post, pop_frame, A_INSTANCE;
    try change (class_size 31) with 64; try match goal with E : class_size _ = _ |- _ => rewrite !E end; lx_exs;
    match goal with
    | K : context [zlow 64 _ <? zlow 64 _] |- context [if ?x <=? ?y then _ else _] => first
        [ replace (x <=? y) with true by (symmetry; apply Z.leb_le; clear -K HB HAU HMU; lx_klin; lia)
        | replace (x <=? y) with false by (symmetry; apply Z.leb_gt; clear -K HB HAU HMU; lx_klin; lia) ]
    end;
    lx_ands; [> lx_mseq | ..]; assumption.

  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0?L10004382311.8 L10004382325.8 L10010675444.8 L10122806843.3 L11080624455.93L12970237007.83L14948339867.83L1851551087.83 L1954387751.75 L22369067269.8 L22375361430.8 L2903536899.7  L2903536913.7  L29853191144.85L32255419398.3 L3425026432.7  L3425026432.8  L3425026450.7  L3425026450.8  L3435514625.8  L41816977584.93L41825422607.85L42057149595.7 L42663277175.83L46325095409.93L46333552206.85L55345830223.83L56478003171.75L56936660318.81L59576964155.83L67419966030.7 L67419966044.7 L6755917879.83 L762599083.8   L764697642.8   L764697656.8   00000100A00P00[00h01:01;01E01`02002?02M02N02[02f03503D03X03n04D04N04X04f04g05405A05S05a05n06606J06^06f07<07R07hFS1c1k2au2mu4LXKFS1c1k2au2mu3LXES1c3C173C30S3hAR2SP2SB1cS3hAR2SP1c3HC23C17FS3hAR2SP1cS3hAR2SP1c2lo5LOIMG3SPL3C16S1c1k2au2mu4LXKTS1c1k2au2mu3LXES1k2au2mu4LXKFFS3hAR2SP2SB1cS1c3HC23C31S2au2mu3HAU3HMUS2au2mu3HAU3HMUS1k2au2mu3HAU3HMU2HBS1c1k2au2mu3HAU3HMU2HBS2au2mu3HAU3HMU1c1k2HBS3hAR2SP1cS3hAR2SP1cS1k2au2mu4LXKTFS3hAR2SP2RI1cS3hAR2SP2RI1cS3hAR2SP1c3HC13HC2S3hAR2SP1c3C16S3hAR2SP1k2auS3hAR2SPS1k2au2mu3HAU3HMU2HBS1k2au2mu3HAU3HMU2HBS3hAR2SPS1c1k2au2mu3HAU3HMU2HBS1c1k2au2mu3HAU3HMU2HBS1c1k2au2mu3HAU3HMU2HB". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pop_A : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "Pra,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$13.PF,(36.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(12.(9.&8.))PSB,$13.PRI,$13.PR,$13.PSTAT,$13.Pc,$13.Pk,$13.Pau,$13.Pmu,$13.Plo,$13.P,(2=.+65?000.R9.)P,(2=.(?.(?.R:.(3<.+2.+25.))+1000.)(39.VhAR,))P,(30.$13.R:.(?.R;.(3<.+2.+25.)))P,(30.$13.R:.(?.R;.(1;.+80.R8.)))P,(3>.VCS,R<.+1000.)P,(0.(2=.+1.R:.)(2=.R:.+1?.))P,(0.(2=.+1.R:.)(2=.R:.+10.))P,(0.(2=.=R:.)(2=.R:.R9.))P,(2=.R:.+>0000000.)P,(0.(2=.=R?.)(4>.R?.(3<.+2.+40.)))P,(1.$2.R14.(?.$4?.+20.)(4.$5.(=.(7.&40.R13.))(:.$5.)))P,(17.$2.R15.(?.R12.+20.)(4.$5.(=.(7.&40.R>.))(:.$5.)))P,(17.$2.R16.(?.R13.+30.)(4.$5.(=.(7.&40.R>.))(:.$5.)))P,(38.$2.R17.R>.R1:.)P,(2=.(39.VhAR,)R?.)P,(2=.R10.(3:.R1<.+40.))P,(2=.R1=.(3<.+2.+3?.))P,(30.$13.(3=.R1>.+10.)=)P,(3>.VCS,R13.(3:.R1?.R13.))P,(40.$2.R1=.)(41.$2.VAL,VCS,(50.R21.R39.R38.R37.R36.R35.R34.R33.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R30.R3:.R20.R1?.R1;.R1:.(?.R1=.(1;.R19.(3<.+2.+20.)))R19.R18.R17.R16.R15.R1>.)(44.(45.R3:.(7.&40.R21.)R39.R38.R37.R36.R35.R34.R33.(7.&40.$4?.)(7.&40.R1:.)(7.&40.R19.)(7.&40.R1;.)(7.&40.R18.)R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R20.(7.&40.$51.)R1?.(46.(9.&40.))R1>.(47.$2.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP F fc m SB RI R STAT c k au mu lo
      SB0 SB1 HRI HR RICS HC HK HAU HMU HST SBC AU MU_ ST LOIMG SPL SPH SPA SCS MI.
    facts. unfold A_POPULATE, A_INSTANCE in *. change (1074072 + 32) with 1074104 in *. subst R.
    pose proof (class_size_range c HC) as [CS1 CS2].
    assert (HB : 32 <= class_size c * k <= 65536 * 16) by (clear - CS1 CS2 HK; nia).
    pose proof (munch_refl [(lo, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM. lx_aceil. destruct HC as [HC1 HC2].
    destruct (Z.eq_dec c 31) as [C31|C31].
    { (* [comment removed for export] *)
      subst c. change (class_size 31) with 64 in *.
      lx_run (PLAN [0x4ccd4; 0x4cc00] [] 40%N). all: popA_leaf HB HAU HMU. }
    destruct (Z_lt_le_dec c 17) as [C16|C17].
    { (* [comment removed for export] *)
      assert (CSZ : class_size c = 32 * c).
      { unfold class_size. replace (c =? 31) with false by (symmetry; apply Z.eqb_neq; lia). replace (c <=? 16) with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
      rewrite CSZ in *.
      lx_run (PLAN [0x4ccd4; 0x4cc00] [] 40%N). all: popA_leaf HB HAU HMU. }
    (* [comment removed for export] *)
    assert (C30 : c <= 30) by (clear -C31 HC2; lia).
    lx_run (PLAN [0x4cbc4] [] 40%N).
    do 9 zstep.
    replace (c + -16) with (c - 16) by lia. rewrite (ic_size_ok c) by (clear - C17 C30; lia).
    lx_run (PLAN [0x4ccd4; 0x4cc00] [] 40%N). all: popA_leaf HB HAU HMU.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition pop_mwc_regs (SP : Z) (gp tp t0 t1 t2 x15 x16 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (R STAT RB c k mu : Z) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "(45.(7.&40.+4<<80.)(7.&40.(?.O18.-40.))O17.O16.O15.O14.O13.(7.&40.O6.)(7.&40.O5.)(7.&40.$4?.)(7.&40.(?.O4.O1.))(7.&40.(3<.+2.+12.))(7.&40.$52.)(7.&40.O2.)O12.O11.O10.(7.&40.O4.)(7.&40.(3<.+2.+12.))(7.&40.(?.O4.O1.))(7.&40.(53.O3.))(7.&40.$4?.)O?.O>.O=.O<.O;.O:.O9.O8.O7.)")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00B0?L13836882688.61L1435104433.61 L1952597872.59 L19628432784.59L25094937912.59L29443748633.61L3437544964.59 L3962980812.59 L41617910089.59L45646570579.61L46992131801.59L47803461429.61L48785259801.61L53522113332.61L55852271491.59L58815346851.60L59308630884.3 L8929211664.59 00000100C00^01901H01_02202?02Z03103603M03\04404A04K04V04WFS3hAR2RB1c1k2au2muS3hAR1c1k2au2mu3HCK3HAU3HMUS3hAR1c1k2au2mu3HCK3HAU3HMUS3hAR1c1k2au2muS3hAR2AL1c1k2au2mu4IMG'S3hAR2au2mu3HAU3HEXS3hAR2RI1c2HCS3hAR1c1k2au2mu3HCK3HAU3HMUS3hAR2AL1c1k2au2mu4IMG'S3hARS3hAR1c1k2au2mu3HAU3HEXS3hAR1c1k2au2muS3hAR2AL1c1k2au2mu5ALWF'S3hAR2RI1c2HCS3hAR2RI1cS2mu3HEX2KEF". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pop_A_map2 : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "Pra,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Px11,(9.&40.)Px13,(9.&40.)Px15,(9.&40.)Px16,(9.&40.)Pa7,(9.&40.)PSP,$13.PF,(36.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(12.(9.&8.))PRI,$13.PR,$13.PSTAT,$13.PRB,$13.Pc,$13.Pk,$13.Pau,$13.Pmu,$13.P,(2=.+65?000.R8.)P,(2=.(?.R9.+1000.)(39.VhAR,))P,(30.$13.R9.(?.R:.(1;.+80.R6.)))P,(3>.VCS,R;.+1000.)P,(0.(2=.+1.R8.)(2=.R8.+1?.))P,(0.(2=.+1.R8.)(2=.R8.+10.))P,(2=.(1;.(53.R:.)R9.)(3<.+2.+12.))P,(0.(2=.=R9.)(2=.R9.R8.))P,(4>.R9.(?.R:.(1;.(53.R<.)R;.)))P,(2=.(?.R:.(3<.+2.+12.))+>0000000.)P,(2=.=R?.)P,(2=.(?.R10.+>0000000.)(3<.+2.+2?.))P,(1.$2.R15.$54.(4.$5.(6.(7.&8.=))(:.$5.)))P,(17.$2.R16.(?.R14.+38.)(4.$5.(=.(7.&40.=))(:.$5.)))P,(40.$2.R17.)(41.$2.VAL,VCS,Lms',$42.(43.(9.&40.)Lx15',(9.&40.)(30.$42.R2.(44.(55.R1=.R31.R30.R2?.R2>.R2=.R1.R1?.R1>.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R18.R17.R16.R15.R14.R12.)R1<.(7.&40.$56.)R1;.(46.(9.&40.))R1:.(47.$2.))))(44.(45.R30.(7.&40.(?.R1;.-40.))R2?.R2>.R2=.R2<.R2;.(7.&40.R16.)(7.&40.R15.)(7.&40.$4?.)R20.(7.&40.R13.)R1?.(7.&40.R12.)R1>.R1=.R1<.(7.&40.R14.)(7.&40.(?.R11.(1;.(53.R13.)R12.)))(7.&40.R10.)(7.&40.(53.R13.))R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R1:.(7.&40.+4<<04.)R19.(46.(9.&40.))R18.(47.$2.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x11 x13 x15 x16 a7 SP F fc m RI R STAT RB c k au mu
      R0 R1 HR RICS HC HK HCK HAU HMU HEX RB0 RB1 PRE MM MI.
    facts. unfold A_PREMAPPED, A_INSTANCE, A_NAME_POP, A_RAR_MAP, pop_mwc_regs in *.
    change (1074072 + 56) with 1074128 in *. subst R.
    pose proof (class_size_range c HC) as [CS1 CS2].
    assert (HB : 32 <= class_size c * k) by (clear - CS1 CS2 HK; nia).
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    assert (RD : Z.land ((au + class_size c * k + Z.lxor mu 18446744073709551615) mod 18446744073709551616) 18446744073709289472 = 0).
    { rewrite zb_lxor_ones by lia.
      replace ((au + class_size c * k + (18446744073709551615 - mu)) mod 18446744073709551616) with (au + class_size c * k - mu - 1).
      2:{ replace (au + class_size c * k + (18446744073709551615 - mu)) with ((au + class_size c * k - mu - 1) + 1 * 18446744073709551616) by lia.
          rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
      change 18446744073709289472 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 18))). rewrite land_clear_low by lia.
      rewrite Z.div_small by lia. reflexivity. }
    rewrite RD. change (0 + 262144) with 262144.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. if_cases KE; zify_cond KE. { exfalso. clear - KE HEX. lia. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    replace (mu + RB) with (RB + mu) by lia. change (2^18) with 262144.
    apply evtA_done. eexists. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L1548517294.60 L3437510454.60 L35330236855.60L47314071470.60L53522110595.60L67139913956.6000000500H00I00V00d011S3hARS3hAR2au2mu3HAU3HEXFS3hAR2AL4IMG'S3hAR2AL5ALWF'S3hAR2AL4IMG'". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pop_A_map : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "Pra,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Px13,(9.&40.)Px15,(9.&40.)Px16,(9.&40.)Pa7,(9.&40.)PSP,$13.PF,(36.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(12.(9.&8.))PRI,$13.PR,$13.PSTAT,$13.PRB,$13.Pc,$13.Pk,$13.Pau,$13.Pmu,$13.P,(2=.+65?000.R8.)P,(2=.(?.R9.+1000.)(39.VhAR,))P,(30.$13.R9.(?.R:.(1;.+80.R6.)))P,(3>.VCS,R;.+1000.)P,(0.(2=.+1.R8.)(2=.R8.+1?.))P,(0.(2=.+1.R8.)(2=.R8.+10.))P,(2=.(1;.(53.R:.)R9.)(3<.+2.+12.))P,(0.(2=.=R9.)(2=.R9.R8.))P,(4>.R9.(?.R:.(1;.(53.R<.)R;.)))P,(2=.(?.R:.(3<.+2.+12.))+>0000000.)P,(2=.=R?.)P,(2=.(?.R10.+>0000000.)(3<.+2.+2?.))P,(1.$2.R15.$57.(4.$5.(;.(7.&40.+????????.))(:.$5.)))P,(1.$2.R16.$54.(4.$5.(6.(7.&8.=))(:.$5.)))P,(17.$2.R17.(?.R15.+38.)(4.$5.(=.(7.&40.=))(:.$5.)))P,(40.$2.R18.)(41.$2.VAL,VCS,Lms',$42.(43.(9.&40.)Lx15',(9.&40.)(30.$42.R2.(44.(55.R1>.R31.R30.R2?.R2>.R2=.R1.R20.R1?.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R19.R18.R17.R16.R15.R13.)R1=.(7.&40.$56.)R1<.(46.(9.&40.))R1;.(47.$2.))))(44.(45.R30.(7.&40.(?.R1<.-40.))R2?.R2>.R2=.R2<.R2;.(7.&40.R17.)(7.&40.R16.)(7.&40.$4?.)(7.&40.(1;.R14.(3<.+2.+20.)))(7.&40.R14.)R20.(7.&40.R13.)R1?.R1>.R1=.(7.&40.R15.)(7.&40.(?.R12.(1;.(53.R14.)R13.)))(7.&40.R11.)(7.&40.(53.R14.))R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.)R1;.(7.&40.+4<<00.)R1:.(46.(9.&40.))R19.(47.$2.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x13 x15 x16 a7 SP F fc m RI R STAT RB c k au mu
      R0 R1 HR RICS HC HK HCK HAU HMU HEX RB0 RB1 INT PRE MM MI.
    facts. pose proof INT as INT'. unfold A_INTERVAL, A_INSTANCE in INT'. change (1074072 + 40) with 1074112 in INT'.
    (* [comment removed for export] *)
    zstep. if_cases K0; zify_cond K0.
    - (* [comment removed for export] *)
      unfold A_INSTANCE. zstep. zstep. zstep. zstep.
      rewrite <- K0. eapply pop_A_map2; try eassumption; try lia.
    - eapply pop_A_map2; try eassumption; try lia.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?L13010243267.62L13898324628.62L15356495653.64L16899216451.62L1861975444.62 L19519145923.62L25235114563.62L25934604180.62L29176651982.64L31945609492.62L33024460995.62L37972987028.62L39937688649.62L40480577556.62L40480577556.63L41531883086.64L42001773902.64L4216608462.64 L57792571214.64L61011576259.62L62425380014.63L64553665044.62L6563086147.62 L67178459459.62L67394690510.64L68306003022.64L7872573204.62 00000;00J00R00]00l01701B01Q01Y01h02302B02J02Y02h03003803@03H03S03[03j04504@04H04P04_S3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2lo3SPLS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SPS3hAR2SP2loS3hAR2SPS3hAR2SP2lo3SPLS3hAR2SP2loS3hAR2SP2loS3hAR2SPS3hAR2SPS3hAR2SP2lo3SPL". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pop_B_no : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Pq6,(9.&40.)Pq5,(9.&40.)Pq4,(9.&40.)Pq3,(9.&40.)Pq2,(9.&40.)Pq1,(9.&40.)Pq0,(9.&40.)Pqra,(9.&40.)PSP,$13.PF,(36.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(12.(9.&8.))Pm,P,(9.&40.)(12.(9.&8.))Plo,$13.PW,(10.(37.$13.$13.))P,(58.R3.R7.R?.R>.R=.R<.R;.R:.R9.R8.)P,(38.$2.R4.R3.(?.R8.-40.))P,(2=.(39.VhAR,)R4.)P,(2=.R5.(3:.R:.+40.))P,(2=.R;.(3<.+2.+3?.))P,(30.$13.(3=.R<.+10.)=)P,(3>.VCS,R8.(3:.R=.R8.))P,(15.(4.(37.$13.$13.)(3?.$13.$13.R9.R>.)R8.)R;.R:.)P,(40.$2.R;.)(41.$2.VAL,VCS,Lms',$42.(43.P,(9.&40.)(12.(9.&8.))Lm',P,(9.&40.)(12.(9.&8.))(0.(30.$42.R2.(44.(45.R13.(7.&40.R12.)R36.R35.R34.R33.R32.R14.R15.(7.&40.=)(7.&40.=)R2>.R2=.R2<.R2;.R2:.R29.R16.R17.R18.R19.R1:.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R11.(4<.R13.)R10.(46.(9.&40.))R1.(47.$2.)))(0.(15.(4.(37.$13.$13.)(3?.$13.$13.R=.R12.)R<.)R?.R1.)(0.(40.$2.R1.)(0.(38.$2.R1.R=.R12.)(15.(:.$11.)R>.R1.))))))(44.(45.(7.&40.+4<<80.)(7.&40.(?.R10.-40.))R34.R33.R32.R31.R30.R2?.R2>.(7.&40.=)R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.)R?.(7.&40.+4<<80.)R>.(46.(9.&40.))R<.(47.$2.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q6 q5 q4 q3 q2 q1 q0 qra SP F fc m0 m lo W
      FR ST LOIMG SPL SPH SPA SCS MU MI.
    facts. unfold pop_frame in FR. pose proof (munch_refl [] m) as MU0.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    do 8 zstep. zstep. replace (SP + -64 + 64) with SP by lia. zstep.
    release_frame FR ST SP.
    apply evtA_done. eexists. split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption| exact MU0].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition popB_post (SP : Z) (gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (R RB T CTX c au mu lo : Z) (W : list (Z * Z)) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "Lms',$42.(43.(9.&40.)Lx5,(9.&40.)(43.(9.&40.)Lx6,(9.&40.)(43.(9.&40.)Lx7,(9.&40.)(43.(9.&40.)Lx11,(9.&40.)(43.(9.&40.)Lx12,(9.&40.)(43.(9.&40.)Lx14,(9.&40.)(43.(9.&40.)Lx15,(9.&40.)(43.(9.&40.)Lx16,(9.&40.)(43.(9.&40.)Lx17,(9.&40.)(43.(9.&40.)Lx28,(9.&40.)(43.(9.&40.)Lx29,(9.&40.)(43.(9.&40.)Lx30,(9.&40.)(43.(9.&40.)Lx31,(9.&40.)(43.P,(9.&40.)(12.(9.&8.))Lm',P,(9.&40.)(12.(9.&8.))(43.(9.&40.)Lj1,(9.&40.)(43.(9.&40.)Lj2,(9.&40.)(43.(9.&40.)Lj3,(9.&40.)(0.(30.$42.R12.(44.(45.(7.&40.+4<<:0.)(7.&40.(?.O14.-40.))O13.O12.R11.R10.R?.(7.&40.O:.)(7.&40.(?.O8.+:>8.))(7.&40.$4?.)R>.R=.(7.&40.O5.)R<.R;.R:.R9.(7.&40.O9.)(7.&40.(3<.+2.+12.))(7.&40.(?.O4.(3<.+2.+12.)))(7.&40.(53.O6.))(7.&40.$4?.)O11.O10.O?.O>.O=.R8.R7.R6.R5.)O<.(7.&40.+4<<=4.)O;.(46.(9.&40.))R4.(47.$2.)))(0.(15.(4.(37.$13.$13.)(3?.$13.$13.O3.(?.O14.-40.))(4.(37.$13.$13.)(3?.$13.$13.(?.+7???8000.(59.(?.O9.O4.)+8.))(?.(?.+7???8000.(59.(?.O9.O4.)+8.))+8000.))(4.(37.$13.$13.)(3?.$13.$13.(?.O8.+;38.)(?.O8.+;48.))(4.(37.$13.$13.)(3?.$13.$13.(?.O8.+:>8.)(?.O8.+:?0.))(4.(37.$13.$13.)(3?.$13.$13.(?.O:.+30.)(?.O:.+38.))O2.)))))O1.R4.)(0.(34.$2.O1.R4.)(0.(40.$2.R4.)(0.(17.$2.R4.(?.+7???8000.(59.(?.O9.O4.)+8.))(4.$5.(8.(5:.+8000.)(5;.(9.&8.)(7.&8.+?:.)(5:.+8000.)))(:.$5.)))(0.(17.$2.R4.(?.O8.+;38.)(4.$5.(=.R3.)(4.$5.(=.R2.)(:.$5.))))(0.(17.$2.R4.(?.O8.+:>8.)(4.$5.(=.R1.)(:.$5.)))(0.(17.$2.R4.(?.O:.+30.)(4.$5.(=.(7.&40.(?.O4.(3<.+2.+12.))))(:.$5.)))(0.(17.$2.R4.(?.O:.+20.)(4.$5.(=.(7.&40.O5.))(:.$5.)))(0.(5<.R4.)(0.(14.R4.O7.O8.)(38.$2.R4.O3.(?.O14.-40.))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "01@0@L11312306781.129L13029490285.3  L13894079552.22 L13922587162.20 L14068907240.2  L17121661550.1  L18926384029.20 L19217292616.120L19266537020.2  L2033144296.2   L22991783080.130L23183433069.3  L24273509525.1  L24326855769.120L24499737212.124L25920437881.3  L27845984990.1  L27846297964.3  L28305712366.1  L28725181897.130L30251788590.22 L30252105037.86 L30308130329.2  L33066364120.20 L33450913236.86 L35358368095.129L36121181739.3  L36253492957.20 L37957899641.3  L38237949960.3  L39904692110.20 L41015213144.20 L43499003787.124L44637234084.16 L45953837954.109L46256863012.16 L46491065419.86 L46595273239.111L47481350080.22 L48014437652.129L48078543413.20 L49436905241.2  L49509889741.20 L49698585326.128L50165924257.0  L51489811757.92 L51489811759.94 L53767143545.3  L5493885805.3   L55588686165.0  L56958148372.129L56991032216.128L57064992863.129L57622410744.112L57731194532.16 L57773706861.124L57908281192.2  L58527319883.86 L58807237918.16 L58817773446.111L58817773446.112L59308633593.5  L61473319449.2  L61757215345.89 L61757218028.88 L63366608683.3  L63925430760.2  L64059417709.3  L65811955577.3  L66848392508.2  L68250320218.120L68594525926.20 L68630208887.20 L7251391720.2   L7644748892.20  L8050295400.2   L8281716796.2   L8431465664.22  L9113772860.2   L9407832852.129 00000V00W01Q02802902=02O02\02]02^04G04H04L04Y05P05Q05R05Y05Z06G07N08Z08`09209M0:G0:H0:^0:_0:c0;T0;o0<C0<b0<c0=B0=]0=^0>X0?a0@H0@I0@[0A80A90AX0B90B:0B;0B<0CE0C\0DV0F90FX0Fl0Fm0GH0H?0IE0Jd0K60K<0L20Le0Lf0Lg0Lh0Li0Lj0M@0N90Nj0Nk0OD0OE0OF0P@0PA0QJS3hAR2j32SP2RB1T2mu3MU02HB5Ha_st5Hl_stFS3hAR2SP2RI2RB1T3CTX1c2mu2lo2HC3RB03RB13MU02T02C02CT5LOIMGS3hAR2SP2RB2mu2lo3RB03MU05LOIMG3SPL3SPAFS2SPS3hAR2SP2RB2mu3MU0S3hAR2RB1T2muFFS3hAR2j32SP2RI2RB1T3CTX1c2mu2lo2HC3RB03RB14RBAL3MU04MUAL2T02C04TSEP2CT2CR5LOIMG3SPL3SPA2KZ2HB5Ha_st5Hl_stFS2SPS3hAR2RB1T2muS3hAR2SP2RB1T2mu2lo3RB04RBAL3MU04MUAL3TAL5LOIMG3SPL3SPAFFS2SP2loFS3hAR2j32SP2RB1T3CTX2mu3MU02CT2HB5Ha_st5Hl_stS3hAR2SP2RI2RB1T3CTX1c2mu2lo2R12HC3RB03RB13MU03HEX2T02C02C12CT2CR5LOIMGS3hAR2SP2RI2RB1T1c2mu2lo2R12HC3RB03RB14RBAL3MU04MUAL3HEX2T05LOIMG3SPL3SPA2KZS2RI1cS3hAR2SP2RB2mu3MU0S3hAR2SP2RB1T2mu2lo3MU03SPLS3hAR2j32SP2RB1T2mu2lo3RB03MU02T15LOIMG3SPL2HB5Ha_st5Hl_stFS3hAR2SP2RB2mu3MU03SPHFS2loS3hAR2SP2RB2mu2lo3RB04RBAL3MU04MUAL5LOIMG3SPL3SPAS3hAR2SP2RB2mu2lo3MU05LOIMGS3hAR2SP2RB1T2mu3MU0S3hAR2SP2RB2mu2lo3RB03MU05LOIMGFS3hAR2SP2RB2mu2lo3RB03MU05LOIMGS3hAR2SP2RB1T2mu2lo3MU03SPLFS3hAR2SP2RI2RB1T3CTX1c2mu2lo2HC3RB03RB13MU02T02C02CT5LOIMGS3hAR2j32SP2RB1T2mu2lo3RB04RBAL3MU04MUAL3TAL5LOIMG3SPL3SPA2HB5Ha_st5Hl_stS3hAR2SP2RB2mu2lo3RB03MU05LOIMG3SPL3SPAFS3hAR2SP2RB2mu3MU0S3hAR2SP2RB1T2mu3MU02HB5Ha_stSS3hAR2SP2RI2RB1T1c2mu3MU01y3H20S3hAR2SP2RI2RB1T1c2mu2lo3MU01y2HyFFSS3hAR2j32SP2RB1T2mu2lo3RB04RBAL3MU04MUAL3TAL5LOIMG3SPL3SPA2HB5Ha_st5Hl_stS3hAR2SP2RB1T2mu3MU02HBS3hAR2j32SP2RB1T2mu2lo3RB03MU02T15LOIMG3SPL2HB5Ha_st5Hl_stS3hAR2SP2RI2RB1T3CTX2mu2lo2R13RB03RB14RBAL3MU04MUAL3HEX2T02T12C15LOIMG3SPL3SPA2KZ3x151H1c2HC4TSEP1WS3hAR2SP2RB2mu2lo3RB03MU05LOIMGS3hAR2SP2RB1T2mu3MU0FS3hAR2SP2RB1T2mu2lo3MU03SPLS3hAR2SP2RI2RB3CTX2mu2lo2R13RB03RB13MU03HEX2C02C15LOIMGS3hAR2SP2RI2RB1T1c2mu2lo2R12HC3RB03RB14RBAL3MU04MUAL3HEX5LOIMG3SPL3SPAS3hAR2SP2RI2RB1T3CTX2mu2lo2R13RB03RB14RBAL3MU04MUAL3HEX2T02T12C02C14TSEP2CT2CR5LOIMG3SPL3SPA2KZS2RB2mu3RB03MU02KZS2RI1cS3hAR2SP2RB1T2mu3MU02KE2RI2lo2R13RB03RB13HEX5LOIMG3SPLS3hAR2SP2RI2RB1T2mu2lo2R13RB03RB13MU03HEX5LOIMG3SPLFFFFFS3hAR2RB1T2mu2T02T12KZS3hAR2SP2RI2RB1T1c2mu2lo2HC3RB03RB13MU02T05LOIMG2A'2n'2H'S3hAR2SP2RI2RB2mu2lo2R13RB03RB13MU03HEX5LOIMG3SPLFS3hAR2SP2RB2mu2lo3MU03SPLFFS3hAR2SP2RI2RB1T3CTX1c2mu2lo2HC3RB03RB13MU02T02C02CT5LOIMGFS3hAR2j32SP2RB1T2mu2lo3RB04RBAL3MU04MUAL3TAL5LOIMG3SPL3SPA2HB5Ha_st5Hl_st". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK ASB"] Lemma pop_B_ok : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Pj1,(9.&40.)Pj2,(9.&40.)Pj3,(9.&40.)Pjunk,(10.(9.&8.))PSP,$13.PF,(36.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(12.(9.&8.))Pm,P,(9.&40.)(12.(9.&8.))PRI,$13.PR,$13.PSTAT,$13.PRB,$13.PT,$13.PCTX,$13.Pc,$13.Pk,$13.Pau,$13.Pmu,$13.Plo,$13.PW,(10.(37.$13.$13.))Zbeg,$13.(?.R9.R3.)P,(2=.+65?000.R=.)P,(2=.(?.R>.+1000.)(39.VhAR,))P,(30.$13.R>.(?.R?.(1;.+80.R9.)))P,(3>.VCS,R10.+1000.)P,(0.(2=.+1.R;.)(2=.R;.+1?.))P,(2=.+10007???9000.R?.)P,(2=.(?.R10.+>0000000.)R13.)P,(30.$13.(3=.R11.+1000.)=)P,(2=.=R<.)P,(30.$13.(3=.R=.+8.)=)P,(2=.(?.R>.(3<.+2.+12.))+>0000000.)P,(2=.=R10.)P,(3>.VCS,R=.(3<.+2.+12.))P,(0.(0.(2=.+1000.R16.)(4:.(2=.(?.R16.+1000.)+10000.)(2=.+65?000.R16.)))(4:.(2=.(?.R16.+1000.)+7???7000.)(2=.+10007???8000.R16.)))P,(2=.(?.R17.+1000.)(39.VhAR,))P,(30.$13.(3=.R18.+1000.)=)P,(3>.VCS,R19.+1000.)P,(30.$13.R1<.(?.R1:.+:=0.))P,(0.(2=.+65?000.R1:.)(4:.(2=.(?.R1:.+10000.)+7???7000.)(2=.+10007???8000.R1:.)))P,(2=.(?.R1;.+10000.)(39.VhAR,))P,(3>.VCS,R1<.+10000.)P,(4:.(2=.(?.R1>.+1000.)R1?.)(2=.(?.R22.+1000.)R1>.))P,(4:.(2=.(?.R1>.+10000.)R1?.)(2=.(?.R1?.+1000.)R1>.))P,(4:.(2=.(?.R1?.+10000.)R21.)(2=.(?.R24.+1000.)R1?.))P,(17.$2.R26.(?.+7???8000.(59.R19.+8.))(4.$5.(8.(5:.+8000.)R2;.)(:.$5.)))P,(5<.R27.)P,(14.R28.R22.R23.)P,(17.$2.R29.(?.R24.+;38.)(4.$5.(=.R31.)(4.$5.(=.R30.)(:.$5.))))P,(17.$2.R2:.(?.R25.+:>8.)(4.$5.(=.R30.)(:.$5.)))P,(17.$2.R2;.(?.R29.+30.)(4.$5.(=.(7.&40.R21.))(:.$5.)))P,(17.$2.R2<.(?.R2:.+20.)(4.$5.(=.(7.&40.R23.))(:.$5.)))P,(38.$2.R2=.R22.(?.R31.-40.))P,(2=.(39.VhAR,)R23.)P,(2=.R24.(3:.(3:.R33.+40.)+40.))P,(2=.R34.(3<.+2.+3?.))P,(30.$13.(3=.R35.+10.)=)P,(3>.VCS,R27.(3:.R36.R27.))P,(15.(4.(37.$13.$13.)(3?.$13.$13.R28.(?.R37.-40.))(4.(37.$13.$13.)(3?.$13.$13.(?.+7???8000.(59.R26.+8.))(?.(?.+7???8000.(59.R26.+8.))+8000.))(4.(37.$13.$13.)(3?.$13.$13.(?.R2>.+;38.)(?.R2>.+;48.))(4.(37.$13.$13.)(3?.$13.$13.(?.R2>.+:>8.)(?.R2>.+:?0.))(4.(37.$13.$13.)(3?.$13.$13.(?.R31.+30.)(?.R31.+38.))R27.)))))R34.R33.)P,(34.$2.R35.R34.)P,(40.$2.R35.)P,(30.(9.&40.)R52.(7.&40.$4;.))(41.$2.VAL,VCS,(5=.R3;.R54.R53.R48.R47.R46.R45.R44.R3:.R39.R35.R33.R32.R31.R30.R2>.R2=.R2<.R2;.R38.)(44.(45.(7.&40.+4<<80.)(7.&40.(?.R3;.-40.))R54.R53.R52.R51.R50.(7.&40.R35.)(7.&40.R34.)(7.&40.R2:.)R4?.R4>.R4=.R4<.R4;.R4:.R49.(7.&40.R33.)(7.&40.(3<.+2.+12.))(7.&40.R2:.)(7.&40.(53.R30.))(7.&40.$4?.)R48.R47.R46.R45.R44.R43.R42.R41.R40.)R3:.(7.&40.+4<<80.)R39.(46.(9.&40.))R37.(47.$2.)))")
(* [comment removed for export] *).
  Proof.
    intros gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s7 s8 s9 s10 s11 t3 t4 t5 t6 j1 j2 j3 junk SP F fc m0 m RI R STAT RB T CTX c k au mu lo W beg
      R0 R1 HR RICS HC RB0 RB1 RBAL MU0 MUAL HEX HAU BCS T0 T1 TAL TCS HST C0 C1 CCS TSEP CT CR SH PS TS TJ SJ MUC AUC ST LOIMG SPL SPH SPA SCS MU WM MI TP.
    facts. unfold A_INSTANCE in *. subst R STAT beg.
    pose proof (munch_refl [(lo, SP + -64); (0x7fff8000 + (RB + mu) / 8, 0x7fff8000 + (RB + mu) / 8 + 32768); (T + 2872, T + 2888); (T + 2792, T + 2800);
                            (RI + 128 * c + 48, RI + 128 * c + 56)] m) as MUme.
    (* [comment removed for export] *)
    zstep. if_cases KZ; zify_cond KZ. { exfalso. clear - KZ RB0 MU0. lia. }
    zstep. zstep. if_cases KE; zify_cond KE. { exfalso. apply KE. reflexivity. }
    zstep. zstep. zstep. zstep. change (2^18) with 262144 in *.
    pose proof (munch_refl [(lo, SP + -64); (2147450880 + (RB + mu) / 8, 2147450880 + (RB + mu) / 8 + 32768)] m) as MUm.
    callxA (eapply (poison_spec AL IMG ALWF CS CSOK ASB) with (W := []) (lo := lo) (m0 := m) (junk := junk);
      [ lazymatch goal with
           | |- rw_cells _ _ _ [CB _ _] => exact SH
           | |- poison_statics _ => exact PS
           | |- stk _ _ _ _ => exact ST
           | |- crange _ _ _ => first [exact BCS | eapply crange_sub; [exact SCS| clear - SPL; lia| clear - SPL; lia]]
           | |- munch _ _ _ => apply munch_refl
           | |- wmono _ _ _ => apply wmono_refl
           | |- mem_inv _ _ => exact MI
           | |- _ => clear - R0 R1 HC RB0 RB1 RBAL MU0 MUAL HEX LOIMG SPL SPH SPA; lia end .. ]).
    lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mc _) =>
      assert (TS' : thr_statics mc CTX T) by (eapply thr_statics_transport; [exact TS| exact MUm| | | |]; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; cbn;
                                                clear - LOIMG SPL RB0 RB1 R1 MU0 C0 C1 HEX; lia);
      destruct TS' as (TS1 & TS2 & TS3 & TS4); unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR in TS1, TS2, TS3;
      lx_hide MU; lx_hide WM; lx_hide MUme; clear MUm;
      match goal with PC : rw_cells _ mc _ [CB _ (repeat _ _)] |- _ => lx_hide PC end;
      pose proof (munch_refl [(lo, SP + -64); (T + 2872, T + 2888); (T + 2792, T + 2800); (RI + 128 * c + 48, RI + 128 * c + 56)] mc) as MU2;
      pose proof (wmono_refl asegs mc) as WM2 end.
    subst tp. unfold A_TP. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x4ccc0] [] 60%N).
    (* [comment removed for export] *)
    zstep.
    (* [comment removed for export] *)
    lx_run (PLAN [0x4ccd4] [] 20%N). lx_stk_grow lo. lx_unhide.
    lazymatch goal with MUl : munch _ ?mc lxm, PC : rw_cells _ ?mc' _ [CB _ (repeat _ _)] |- _ =>
      change (262144 / 8) with 32768 in PC;
      assert (MUF : munch [(lo, SP + -64); (0x7fff8000 + (RB + mu) / 8, 0x7fff8000 + (RB + mu) / 8 + 32768); (T + 2872, T + 2888); (T + 2792, T + 2800);
                            (RI + 128 * c + 48, RI + 128 * c + 56)] m lxm) by (lx_munch MUme MUl) end.
    apply evtA_done. unfold popB_post, A_INSTANCE. change (2^18) with 262144.
    lx_exs; lx_ands;
      [ lx_mseq
      | match goal with MUl : munch _ _ lxm |- _ => lx_munch MU MUl end
      | match goal with WMl : wmono _ _ lxm |- _ => lx_wmono WM WMl end
      | assumption
      | match goal with MUl : munch _ ?mc lxm, WMl : wmono _ ?mc lxm, PC : rw_cells _ ?mc _ [CB _ (repeat _ _)] |- _ => lx_tr_rw PC MUl WMl end
      | eassumption
      | eassumption
      | match goal with K : rw_cells _ lxm _ [C8 (Z_to_bv 64 _)] |- _ => lx_rwx K end
      | match goal with K : rw_cells _ lxm _ [C8 (Z_to_bv 64 au)] |- _ => lx_rwx K end
      | eapply poison_statics_transport; [exact PS| exact MUF |]; intros A' n' H'; cbn; clear - H' LOIMG SPL RB0 RB1 R1 MU0 T0 HC HEX; lia
      | eapply thr_statics_transport; [exact TS| exact MUF | | | |]; unfold A_TSD_INITED, A_TSD_PTR, A_TSD_ARR; cbn;
          clear - LOIMG SPL RB0 RB1 R1 MU0 C0 C1 T0 HC HEX CT CR; lia
      | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition pop_exh_ret (qra : word) (SP : Z) (gp tp q0 q1 q2 q3 q4 q5 q6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m' : mem) (ms' : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "(43.(9.&40.)Lt0',(9.&40.)(43.(9.&40.)Lt1',(9.&40.)(43.(9.&40.)Lt2',(9.&40.)(43.(9.&40.)La2',(9.&40.)(43.(9.&40.)La3',(9.&40.)(43.(9.&40.)La4',(9.&40.)(43.(9.&40.)La5',(9.&40.)(43.(9.&40.)La6',(9.&40.)(43.(9.&40.)La7',(9.&40.)(43.(9.&40.)Lt3',(9.&40.)(43.(9.&40.)Lt4',(9.&40.)(43.(9.&40.)Lt5',(9.&40.)(43.(9.&40.)Lt6',(9.&40.)(30.$42.O1.(44.(45.O14.(7.&40.O13.)O12.O11.R=.R<.R;.O10.O?.(7.&40.=)(7.&40.=)R:.R9.R8.R7.R6.R5.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.R4.R3.R2.R1.)O4.(4<.O14.)O3.(46.(9.&40.))O2.(47.$2.))))))))))))))))")
(* [comment removed for export] *).
  Definition pop_exh_at_printf (SP : Z) (gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (c : Z) (m' : mem) (ms' : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "(43.(9.&40.)Lx5,(9.&40.)(43.(9.&40.)Lx6,(9.&40.)(43.(9.&40.)Lx7,(9.&40.)(43.(9.&40.)Lx9,(9.&40.)(43.(9.&40.)Lx12,(9.&40.)(43.(9.&40.)Lx13,(9.&40.)(43.(9.&40.)Lx14,(9.&40.)(43.(9.&40.)Lx15,(9.&40.)(43.(9.&40.)Lx16,(9.&40.)(43.(9.&40.)Lx17,(9.&40.)(43.(9.&40.)Lx18,(9.&40.)(43.(9.&40.)Lx19,(9.&40.)(43.(9.&40.)Lx20,(9.&40.)(43.(9.&40.)Lx21,(9.&40.)(43.(9.&40.)Lx22,(9.&40.)(43.(9.&40.)Lx28,(9.&40.)(43.(9.&40.)Lx29,(9.&40.)(43.(9.&40.)Lx30,(9.&40.)(43.(9.&40.)Lx31,(9.&40.)(30.$42.O1.(44.(45.(7.&40.+4<>4<.)(7.&40.(?.O=.-40.))O<.O;.R13.R12.R11.(7.&40.O3.)R10.(7.&40.$48.)(7.&40.$1?.)R?.R>.R=.R<.R;.R:.R9.R8.R7.R6.R5.O:.O9.O8.O7.O6.R4.R3.R2.R1.)O5.(7.&40.$49.)O4.(46.(9.&40.))O2.(47.$2.))))))))))))))))))))))")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "0050>L16462390431.1L18614817987.2L36418395939.2L40228640085.0L46992137518.200000300900?00@00AS1sS1s2HsS1s2HsSS". (* [comment removed for export] *)
  Lemma land_m18_wrap : forall s, 0 <= s < 2^18 -> Z.land (s + 2^64) 18446744073709289472 = 0.
  Proof.
    intros s Hs. change 18446744073709289472 with (Z.land (Z.ones 64) (Z.lnot (Z.ones 18))).
    rewrite Z.land_assoc, Z.land_ones by (clear; lia).
    replace ((s + 2 ^ 64) mod 2 ^ 64) with (Z.land s (Z.ones 64)).
    2:{ rewrite Z.land_ones by (clear; lia). replace (s + 2^64) with (s + 1 * 2^64) by (clear; lia). rewrite Z_mod_plus_full. reflexivity. }
    rewrite <- Z.land_assoc, land_clear_low by (clear -Hs; lia). rewrite Z.div_small by (clear -Hs; lia). reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00=0?L1952597872.8  L19954783385.2 L2693120384.3  L2695217590.3  L32530611373.6 L38908070661.4 L42209532941.3 L4921251499.4  L51491909288.84L53504412434.3 L53506509604.3 L59310615780.4 L65825703765.3 00000G00M00S00Y00d00e01001<01S01T01U01a01mS1c1k2au2mu3HCK3HAU3HMUS2RI1cS1u2RuS1u2RuS1c1k2au2muSS1u2Ru4LXKFS2mu3EXH3MUXS3hAR2SP2RI1c1y3H163H15SSS2mu3EXH3LXES1u2Ru5LXKT0". (* [comment removed for export] *)
  #[using="IMG ALWF CSOK"] Lemma pop_A_exh_pre : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "Pra,(9.&40.)Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Px13,(9.&40.)Px15,(9.&40.)Px16,(9.&40.)Pa7,(9.&40.)Pq6,(9.&40.)Pq5,(9.&40.)Pq4,(9.&40.)Pq3,(9.&40.)Pq2,(9.&40.)Pq1,(9.&40.)Pq0,(9.&40.)Pqra,(9.&40.)Pexb,(9.&8.)PSP,$13.PF,(36.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(12.(9.&8.))Pm,P,(9.&40.)(12.(9.&8.))PRI,$13.PR,$13.PSTAT,$13.PRB,$13.Pc,$13.Pk,$13.Pau,$13.Pmu,$13.Plo,$13.PW,(10.(37.$13.$13.))P,(2=.+65?000.R:.)P,(2=.(?.R;.+1000.)(39.VhAR,))P,(30.$13.R;.(?.R<.(1;.+80.R8.)))P,(3>.VCS,R=.+1000.)P,(0.(2=.+1.R:.)(2=.R:.+1?.))P,(0.(2=.+1.R:.)(2=.R:.+10.))P,(2=.(1;.(53.R<.)R;.)(3<.+2.+12.))P,(0.(2=.=R;.)(2=.R;.R:.))P,(4>.R;.(?.R<.(1;.(53.R>.)R=.)))P,(4>.+>0000000.(?.R<.(3<.+2.+12.)))P,(2=.R=.+>0000000.)P,(2=.=R12.)P,(2=.(?.R13.+>0000000.)(3<.+2.+2?.))P,(17.$2.R18.(?.R16.+38.)(4.$5.(=.(7.&40.=))(:.$5.)))P,(17.$2.R19.(?.R17.+44.)(4.$5.(6.R1>.)(:.$5.)))P,(2<.R1:.)P,(58.R1;.R1?.R28.R27.R26.R25.R24.R23.R22.R21.)P,(38.$2.R1<.R13.(?.R20.-40.))P,(2=.(39.VhAR,)R14.)P,(2=.R15.(3:.R22.+40.))P,(2=.R23.(3<.+2.+3?.))P,(30.$13.(3=.R24.+10.)=)P,(3>.VCS,R18.(3:.R25.R18.))P,(15.(4.(37.$13.$13.)(3?.$13.$13.R19.R26.)(4.(37.$13.$13.)(3?.$13.$13.(?.R20.+44.)(?.R20.+45.))R18.))R23.R22.)P,(34.$2.R24.R23.)P,(40.$2.R24.)(41.$2.VAL,VCS,Lms',$42.(43.P,(9.&40.)(12.(9.&8.))Lm',P,(9.&40.)(12.(9.&8.))(0.(15.(4.(37.$13.$13.)(3?.$13.$13.R1>.R2;.)(4.(37.$13.$13.)(3?.$13.$13.(?.R25.+44.)(?.R25.+45.))R1=.))R28.R1.)(0.(34.$2.R28.R1.)(0.(40.$2.R1.)(4:.(0.(2?.(30.$13.(5>.&8.R2<.)=))(0.(38.$2.R1.R1>.R2;.)(0.(17.$2.R1.(?.R25.+44.)(4.$5.(6.R2<.)(:.$5.)))(5?.R2=.R2;.R47.R46.R2>.R2?.R30.R31.R32.R33.R34.R41.R40.R3?.R3>.R3=.R2:.R29.R1.R2.))))(0.(30.$13.(5>.&8.R2<.)=)(0.(38.$2.R1.R1>.(?.R2;.-40.))(0.(17.$2.R1.(?.R25.+44.)(4.$5.(6.(7.&8.+1.))(:.$5.)))(0.(58.R1.R2;.R34.R33.R32.R31.R30.R2?.R2>.R2=.)(60.R2;.R47.R46.R41.R40.R3?.R3>.R3=.R2:.R29.R22.R1.R2.))))))))))(44.(45.R46.(7.&40.(?.R29.-40.))R45.R44.R43.R42.R41.(7.&40.R23.)(7.&40.R22.)(7.&40.$4?.)(7.&40.(1;.R20.(3<.+2.+20.)))(7.&40.R20.)R36.(7.&40.R1?.)R35.R34.R33.(7.&40.R21.)(7.&40.(?.R1>.(1;.(53.R20.)R1?.)))(7.&40.R1=.)(7.&40.(53.R20.))R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.)R28.(7.&40.+4<<00.)R27.(46.(9.&40.))R25.(47.$2.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros ra gp tp t0 t1 t2 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x13 x15 x16 a7 q6 q5 q4 q3 q2 q1 q0 qra exb SP F fc m0 m RI R STAT RB c k au mu lo W
      R0 R1 HR RICS HC HK HCK HAU HMU EXH MUX RB0 RB1 M56 EX B12 FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    pose proof (lxw_byte_range exb) as Ru. rewrite <- (lxw_b8_of_unsigned exb) in EX. remember (bv_unsigned exb) as u eqn:Hu in *.
    facts. pose proof B12 as (TG & TN & RG & PCB & GCF & LSY).
    unfold A_TOOLNAME_GOT, A_TOOLNAME, A_REPORT_GOT, A_PRINTF_CB, A_GOT_CFLAGS, A_CF_LOGSYS, A_CFLAGS, A_INSTANCE in *.
    change (1074072 + 56) with 1074128 in *. subst R. unfold pop_frame in FR |- *.
    pose proof (class_size_range c HC) as [CS1 CS2].
    assert (HB : 32 <= class_size c * k) by (clear - CS1 CS2 HK; nia).
    change (2^18) with 262144 in *. unfold A_PRINTF, A_FMT_OOM1, A_ASAN_NAME, A_GOT_PAGESZ, A_PAGESZ_CELL in *.
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP); (RI + 128 * c + 68, RI + 128 * c + 69)] m) as MU1. pose proof (wmono_refl asegs m) as WM1. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [0x7ddd8] [] 40%N).
    all: lx_unhide.
    1: { apply evtA_done. exists lxm. lx_ands;
         [ match goal with MUl : munch _ m lxm |- _ => lx_munch MU MUl end
         | match goal with WMl : wmono _ m lxm |- _ => lx_wmono WM WMl end
         | assumption
         | right; lx_ands;
           [ match goal with K : context [zlow 64 u =? zlow 64 0] |- _ => clear -K Ru; lx_klin; lia end
           | assumption
           | match goal with K : rw_cells _ lxm _ [C1 _] |- _ => lx_rwx K end
           | assumption
           | unfold pop_exh_at_printf; lx_exs; lx_mseq ] ]. }
    1: { apply evtA_done. exists lxm. lx_ands;
         [ match goal with MUl : munch _ m lxm |- _ => lx_munch MU MUl end
         | match goal with WMl : wmono _ m lxm |- _ => lx_wmono WM WMl end
         | assumption
         | left; lx_ands;
           [ match goal with K : context [zlow 64 u =? zlow 64 0] |- _ => clear -K Ru; lx_klin; lia end
           | assumption
           | rewrite <- (lxw_b8_of_unsigned exb), <- Hu; match goal with K : rw_cells _ lxm _ [C1 _] |- _ => lx_rwx K end
           | unfold pop_exh_ret; lx_exs; lx_mseq ] ]. }
    (* [comment removed for export] *)
    match goal with K : context [Z.land ?x 18446744073709289472] |- _ =>
      replace (Z.land x 18446744073709289472) with 0 in K;
      [| symmetry; replace x with ((au + class_size c * k - mu - 1) + 2^64) by (clear -HAU HMU; lia); apply land_m18_wrap; clear -HAU HMU HCK HB; lia] end.
    match goal with K : context [zlow 64 _ <? zlow 64 3758096385] |- _ => clear -K EXH MUX; lx_klin; lia end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  #[using="IMG ALWF CSOK"] Lemma pop_A_exh_post : ltac2:(CDefT.buildp (gd_tbl_AW_Populate ()) "Pgp,(9.&40.)Ptp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)Pq6,(9.&40.)Pq5,(9.&40.)Pq4,(9.&40.)Pq3,(9.&40.)Pq2,(9.&40.)Pq1,(9.&40.)Pq0,(9.&40.)Pqra,(9.&40.)PSP,$13.PF,(36.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(12.(9.&8.))Pm,P,(9.&40.)(12.(9.&8.))Pc,$13.Plo,$13.PW,(10.(37.$13.$13.))P,(58.R4.R8.R10.R?.R>.R=.R<.R;.R:.R9.)P,(38.$2.R5.R3.(?.R9.-40.))P,(2=.(39.VhAR,)R4.)P,(2=.R5.(3:.R;.+40.))P,(2=.R<.(3<.+2.+3?.))P,(30.$13.(3=.R=.+10.)=)P,(3>.VCS,R8.(3:.R>.R8.))P,(15.(4.(37.$13.$13.)(3?.$13.$13.R9.R?.)R8.)R<.R;.)P,(34.$2.R=.R<.)P,(40.$2.R=.)(41.$2.VAL,VCS,Lms',$42.(43.P,(9.&40.)(12.(9.&8.))Lm',P,(9.&40.)(12.(9.&8.))(0.(15.(4.(37.$13.$13.)(3?.$13.$13.R>.R14.)R=.)R11.R1.)(0.(34.$2.R11.R1.)(0.(40.$2.R1.)(0.(38.$2.R1.R>.R14.)(5?.R15.R14.R38.R37.R16.R17.R18.R19.R1:.R1;.R1<.R25.R24.R23.R22.R21.R13.R12.R1.R2.))))))(44.(45.(7.&40.+4<><0.)(7.&40.(?.R12.-40.))R36.R35.R34.R33.R32.(7.&40.R=.)R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.)R11.(7.&40.+4<><0.)R10.(46.(9.&40.))R>.(47.$2.)))")
(* [comment removed for export] *).
  Proof.
    try lx_hide ASB.  (* [comment removed for export] *)
    intros gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 q6 q5 q4 q3 q2 q1 q0 qra SP F fc m0 m c lo W
      FR ST LOIMG SPL SPH SPA SCS MU WM MI.
    unfold pop_frame in FR.
    lx_hide MU. lx_hide WM. pose proof (munch_refl [(lo, SP)] m) as MU1. pose proof (wmono_refl asegs m) as WM1. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_unhide. lx_same.
    apply evtA_done. eexists. lx_ands; [exact MU | exact WM | exact MI | assumption | unfold pop_exh_ret; lx_exs; lx_mseq].
  Qed.

End Populate.

End ARUN_1.
