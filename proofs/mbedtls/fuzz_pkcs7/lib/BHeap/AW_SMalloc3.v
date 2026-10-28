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
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P007740a730ae90a6 1 1 8 4 2 1 44 1 67 1 70 1 4 39 1 68 1 69 1 71 8P008f237dc6eea510 0 2 1 1 40 1P00bbadbbac04400b 1 1 4088 7 0 512 50 1 64 1 65 512 66 1 67 1 68 512 6 35 512 50 1 64 1 66 1 67 1 69 8P010c85981bae6e1e 0 6 0 8 36 8 65 8 66 8 67 8 68 8P012be34d03996def 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P01f938a1bb79ea72 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P020989fd41c0057b 0 2 1 1 40 1P02137b81577dff4e 1 2 56 6 0 4096 50 8 64 8 66 512 67 8 68 4096 262144 5 35 4608 50 9 64 9 67 9 69 1 3 45 1 67 1 70 4096P032cdec5bc048a7f 0 2 0 1 13 1P03bb271e658fce15 1 1 14680064 7 0 4096 35 258048 50 512 64 512 66 512 67 512 68 4096 3 45 1 67 1 69 4096P03c23cd613ff7484 1 2 56 6 0 4096 50 8 64 8 66 512 67 8 68 4096 262144 5 35 4608 50 9 64 9 67 9 69 1 3 45 1 67 1 70 4096P04ee8119915d73fe 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P05694a6242be0e6d 0 2 1 1 40 1P056eba67a44a49c9 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P07395aa94982d011 0 4 1 1 18 1 20 1 21 1P07627b89cc387b9f 0 6 0 8 36 8 65 8 66 8 67 8 68 8P07bcd2bd9840f9c5 0 2 0 1 7 1P08f1f62cd07387e5 0 2 0 1 19 1P09c32efec1e5eff3 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P09f74680b6972897 0 6 0 8 36 8 65 8 66 8 67 8 68 8P0a1ceb130f891b50 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P0a54a45e160212a5 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P0a9f3ac20affbfd6 0 2 0 1 54 1P0b9fe3a172094490 1 1 8 2 0 1 65 1 3 5 1 66 1 67 8P0cb944e9c5bcbcd7 0 2 1 1 40 1P0cee732e9e478f46 0 2 0 1 19 1P0d66a01fbf352386 0 4 1 1 18 1 20 1 21 1P0d708acbf9ecfbfe 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P0d719548b3d69db8 0 2 1 1 40 1P0d83879df3a04550 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P0d8943446c77e95e 0 6 0 8 36 8 65 8 66 8 67 8 68 8P0dbc9406f30ddaaf 0 6 0 8 36 8 65 8 66 8 67 8 68 8P0e3dd2aa593de397 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P0e6e02e376e49932 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P0e7bd115eceec04f 0 2 1 1 40 1P0eb523f41055a90a 1 1 8 4 2 1 44 1 67 1 70 1 4 39 512 68 512 69 512 71 4096P0f23e6cf535f9734 0 2 1 1 40 1P0f5c1ccd21b87223 1 2 56 6 0 4096 50 8 64 8 66 512 67 8 68 4096 262144 5 35 4608 50 9 64 9 67 9 69 1 3 45 1 67 1 70 4096P0ffa6d9cc9420434 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P10d20781140eee23 0 2 1 1 40 1P10e48bf67f4cad67 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P112b25f90ed9ffeb 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1136273372a956fe 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P121cae34e90a3a0b 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P12298abbb78cd625 0 6 0 8 36 8 65 8 66 8 67 8 68 8P1287fccdd2c745b2 0 2 1 1 40 1P12a0910205395f97 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P12aa3ee95e896faa 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P12e901f700dfffaf 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P13aa150c1e896db4 0 4 1 1 20 1 21 1 22 1P14093469f612212b 0 2 1 1 40 1P1436fa801850016a 0 2 1 1 40 1P144d2bf48321907a 0 2 1 1 40 1P14b22fd46f96cdc7 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P14d562066ea02fb1 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P15293603a63779bf 0 2 1 1 40 1P157475def515c733 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P157a92bab9b2fed7 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P159169f2012b8ec1 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P15a4f457185db349 0 2 0 1 19 1P16279a5e9b23f00d 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P16359a3c724eee8b 0 2 1 1 40 1P16ca8294fc181cc5 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P16d637b4ec4b1db9 0 2 0 1 13 1P16f3301014a5246f 0 2 0 1 19 1P17064609551957c2 0 2 1 1 40 1P171843f1138adb16 0 2 1 1 40 1P173c81bcdb79a631 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P185787b7969f3f3c 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1873e798d43962bf 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P189034a83ace4fc3 0 6 0 8 36 8 65 8 66 8 67 8 68 8P1907777921bdffdb 0 2 1 1 40 1P190bd6f797964d8c 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P1948ecd5c2f04199 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P197598948974f68d 0 6 0 8 36 8 65 8 66 8 67 8 68 8P19837fe2b324f20d 0 4 1 1 20 1 21 1 22 1P19ab56bf4a85ec85 0 2 0 1 54 1P1a766a60b6c98457 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P1afb9e4b351e0f78 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1b3d41c1ea968290 0 2 1 1 40 1P1b42cdef19ee0f03 0 2 0 1 54 1P1b641345a37ea652 0 4 1 1 20 1 21 1 22 1P1bc01ec0ad1b7049 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P1bc8096958452561 0 4 1 1 18 1 20 1 21 1P1bca082dc0dbfee8 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P1bf2efcedd9d6806 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P1c1d04644a53f48e 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P1c6b4293908482e7 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P1d128dc6f5dce68c 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P1d52a7b35db9ba0c 1 1 8 3 1 1 66 1 69 1 4 38 1 67 1 68 1 70 8P1ef35ad67e8c8c82 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P1ef8a3a9131b57cf 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P1f1b8c73398bee53 0 2 0 1 13 1P1f4781b1136a7f90 0 2 0 1 13 1P1f7a5a5b0f51fe76 0 2 0 1 13 1P1fb380373f1ce207 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P2017f78aebaa7550 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P2049242890a08733 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P204f4035e5e06dea 0 2 0 1 54 1P205189ab7bb08240 0 2 0 1 19 1P20580d28cbd3fb1b 1 1 4088 7 0 512 50 1 64 1 65 512 66 1 67 1 68 512 6 35 512 50 1 64 1 66 1 67 1 69 8P20c0f4f7e07342bc 0 2 1 1 40 1P21197153b0143f36 0 2 0 1 19 1P214669992a55d2a8 0 2 1 1 40 1P21830bb1fd26574f 0 2 1 1 40 1P220e169c581030f2 0 2 0 1 19 1P229508e4266b1845 0 2 1 1 40 1P22ba1fc5484153de 0 4 1 1 18 1 20 1 21 1P22e7ec65f82875f1 1 1 8 2 0 1 65 1 3 5 1 66 1 67 8P22f585369a71415b 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P23127bd3ad20486f 0 4 1 1 20 1 21 1 22 1P233ad0186593bad0 0 2 0 1 15 1P23c5b32b577bf2d9 0 2 1 1 40 1P23e8983a57ffded1 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P23f5b31688faba37 1 1 8 3 0 1 39 1 68 1 4 36 1 45 1 67 1 69 8P23f82a36789fdfc0 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P24aa7aae2df5fee1 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P24ceba47b2cf4778 0 2 1 1 40 1P253e5ad0f4db7fd8 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P25506240536924ec 0 4 1 1 20 1 21 1 22 1P256ec97087f3ee23 0 6 0 8 36 8 65 8 66 8 67 8 68 8P2598870616550162 0 2 1 1 40 1P2775f0922337beb1 0 2 0 1 54 1P27d58ff7bb932f47 1 1 8 4 2 1 44 1 67 1 70 1 4 39 1 68 1 69 1 71 8P27f61ee4794d5d63 0 2 1 1 40 1P286a0b41749d5bae 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P294c9c32fb9053a0 1 1 8 2 0 1 65 1 4 37 1 45 1 66 1 67 8P29809cd4f750b13d 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P2a098c670ca59cbc 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P2a0dee2d974543a6 0 4 0 8 4 8 65 8 66 8P2a6cca3adc18886c 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P2ac1cec76efcf8e4 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P2acac9f9278b118b 0 4 0 1 14 1 15 1 16 1P2adcaa559973f702 0 2 0 1 42 1P2b8237230730daf4 0 2 0 1 19 1P2bc6130cd9d970b3 0 2 0 1 19 1P2c15a9893a4d108d 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P2c2010b52cbd7182 0 2 1 1 40 1P2c6db019a4cd61a6 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P2c6e8187f7010453 0 5 0 8 36 8 45 8 65 8 66 8P2cfa7257a705bb9f 0 2 1 1 40 1P2d0aaa1f1d2800b3 0 4 0 8 4 8 65 8 66 8P2d5a9c507ed5b982 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P2d60c573193080dd 0 6 0 8 36 8 65 8 66 8 67 8 68 8P2d6e2dc51c10bd6d 1 1 4088 7 0 512 50 1 64 1 65 512 66 1 67 1 68 512 6 35 512 50 1 64 1 66 1 67 1 69 8P2db4312da5a2e8b4 1 2 56 6 0 4096 50 8 64 8 66 512 67 8 68 4096 262144 5 35 4608 50 9 64 9 67 9 69 1 3 45 1 67 1 70 4096P2e56b25666382b2c 0 2 0 1 42 1P2e60e9bd9274d660 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P2f14f597dd811eb8 0 2 1 1 40 1P2fb1887eaef031ed 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P3027f3dc82c1a80d 0 1 1 1P303d5b2cb37c3f3e 0 2 1 1 40 1P303ee75b721b06d7 0 2 1 1 40 1P308304b6aa9c26b0 0 2 1 1 40 1P30e842707d12a7bc 0 6 0 8 36 8 65 8 66 8 67 8 68 8P30e98048e066a2ba 0 2 1 1 40 1P3113f8a79a99a48e 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P31282e4c37130791 1 1 8 3 0 1 63 1 64 1 4 38 1 62 1 65 1 66 8P318433f72c1f59bb 1 1 4088 7 0 512 50 1 64 1 65 512 66 1 67 1 68 512 6 35 512 50 1 64 1 66 1 67 1 69 8P31c88357ac35d502 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P3226cd090faee1a2 0 2 1 1 40 1P3227e200d81c0778 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P322cc1f9c8640c7a 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P32af43a99d9d23f7 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P32c5c9979e6fca4d 1 2 56 6 0 4096 50 8 64 8 66 512 67 8 68 4096 262144 5 35 4608 50 9 64 9 67 9 69 1 3 45 1 67 1 70 4096P33066cdd68ab663f 0 2 0 1 54 1P33663f07dc9dc418 1 1 8 2 1 1 66 1 4 38 1 47 1 67 1 68 8P336d76fa5535bd0f 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P338e94677272caff 0 2 0 1 15 1P339701bc189581d0 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P34064ab59fa780f5 0 2 0 1 54 1P341f4f791d206171 0 6 0 8 36 8 65 8 66 8 67 8 68 8P3424f53dad10c715 1 1 8 3 0 1 62 1 63 1 4 37 1 61 1 64 1 65 8P356f70d13db15fe8 0 2 0 1 19 1P3580f3a7daac67ac 0 4 1 1 20 1 21 1 22 1P35e773d9930a759e 0 6 0 8 36 8 65 8 66 8 67 8 68 8P35fe32006714ec31 0 2 1 1 40 1P36665a5601321c98 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P36bce10885cbca22 0 2 0 1 54 1P36f9be8115215363 0 7 0 8 37 8 55 8 56 8 61 8 66 8 67 8P370deeec874354c6 0 2 1 1 40 1P377d18e3b8ba7744 0 2 0 1 19 1P38783e7c52648891 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P38c3249489a106d6 0 2 1 1 40 1P3915c62339f8ef9c 0 2 0 1 19 1P3991d47bfe972800 1 2 56 6 0 4096 50 8 64 8 66 512 67 8 68 4096 262144 5 35 4608 50 9 64 9 67 9 69 1 3 45 1 67 1 70 4096P39f0eb2ed9020fc8 0 6 0 8 36 8 65 8 66 8 67 8 68 8P3a14701e9228c67d 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P3a2a16e3df20c4b0 0 6 0 8 36 8 65 8 66 8 67 8 68 8P3a4a93c8644868c0 1 1 8 3 0 1 61 1 64 1 4 36 1 62 1 63 1 65 8P3a4c6bb8594b8b09 1 1 8 2 0 1 65 1 4 37 1 45 1 66 1 67 8P3aab871d600f59f2 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P3ac1dd4b99b6c533 1 2 56 6 0 4096 50 8 64 8 66 512 67 8 68 4096 262144 5 35 4608 50 9 64 9 67 9 69 1 3 45 1 67 1 70 4096P3b01f9416e2e4f70 1 1 4096 2 1 1 62 1 3 43 1 63 1 64 4096P3b228aba93889262 1 2 8 2 66 1 67 1 7 3 0 1 68 1 69 1 4 36 1 45 1 67 1 70 8P3b5498645ae410c7 1 2 8 3 37 1 66 1 67 1 3584 3 0 1 68 1 69 1 3 45 1 67 1 70 4096P3bbc9e851ad356d3 1 1 8 3 0 1 66 1 67 1 4 36 1 65 1 68 1 69 8P3c439cda17bf61ef 0 4 1 1 20 1 21 1 22 1P3c7fe5c477ff1839 0 6 0 8 36 8 65 8 66 8 67 8 68 8P3c9b9d508ae67367 1 1 8 2 1 1 66 1 4 38 1 46 1 67 1 68 8P3cbb3c02547d4aae 0 2 1 1 40 1P3cd3f6b5dc9a6b82 0 2 0 1 54 1P3cd5c99ef9be042d 0 2 1 1 40 1P3d1a6901ae957a77 0 2 0 1 54 1P3d2c956ab092ccc4 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P3d59eb748a6905a2 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P3da77da131575128 1 1 8 4 2 1 44 1 67 1 70 1 4 39 512 68 512 69 512 71 4096P3dd96bfbd79f21a4 0 8 0 8 34 4096 40 8 49 8 60 8 63 8 65 8 66 8P3f48c09722fc61ff 1 1 8 3 0 1 65 1 68 1 4 37 1 66 1 67 1 69 8P3f7c191d15079340 0 6 0 1 51 1 52 1 57 1 62 1 63 1P3f840d1b7d9fdf5d 0 4 1 1 20 1 21 1 22 1P3fd0547ae5ab42e9 0 2 1 1 40 1N0057f5df24fbab5fN007278c672266e8aN010f7512ebb99bcaN01242fdc69da2ef1N014e642da708f94dN015496c7a57e7489N017b8d92627a0411N0187b92f4844dd96N01c1a7e6ce487d28N01d7bfc2042f2b96N02984d5de851feb7N02b0fd713b66554fN02baac64878fa6b6N02e69615c9395b87N0384d8a3b182e897N03f2cb43496ab15fN0433d17f40e21b76N043574d9c90b4530N0443fa0330f531acN046a195d1da18e03N04d5b7d7a1f0ad06N04edaf5e324c096cN0508e461dd5d7d26N052e88f1fdbe6e0fN052f60d0fefed738N05599f5e1b4167e5N056263d61b8a6f08N057ee1e6592ae54aN05a3f993fde72ce7N05e5846b539224abN06268c4b664d8569N063cfafc5a09bd14N069348f6aeb900efN06acf946b305acfaN06b464a6d7975179N06f9b28aaf1f83a6N0735c8a37d63ae61N0752261f34176898N07f80a9ea47cb181N080119e330d769d1N080b41aca887ee04N0845b6d9d8d687a4N0898ca86af43eb66N08a2765da3865e68N08d1637045dc6371N090876ee593eaa7fN096274131d172b4eN09e3c27a304b6b12N09eb6a534fbb3ed4N0a856562ad180441N0b66bda20f055a9dN0babf827b1cc4506N0bfdae584732ccdbN0c080bac9a6f98e3N0c1ffdbac6bcfd40N0c3687d5962018e6N0c7590531c16a83dN0cc4d9e10ad1958cN0d3c8aea937463a9N0d7ae9b994730b9bN0da7ba12d5e920e6N0da93477a7c8f29bN0daffe44f2c01f06N0e036e159ac074ecN0e0c830b8f30f351N0e700974ab250451N0eebadee3f504275N0f20841926ca4044N0f98a25d73a04170N0fb59b4abaada22bN10066d7381809908N101d4f2211f65e9eN1030d58a63ef8199N10d9e68503293fe6N10f759f8bbe7ebe4N10fbf8271b72be09N1102a0079311cdfcN112156c3370c2182N1122cd49ae4eb4c0N1144a1fb93eba590N115f8e0a40cdbc7bN117b3019d015dfceN118e9d55f1bf35faN11f54dff820a2047N122e873f1d9895b8N1239a295f9a1bf11N1263755030226fbdN12db88e6e183fa86N12e2ffed4505a710N12ee967ebc3383ffN1331b772e9a144daN145d412cf6e4e908N14715e72ce37a033N14b3cc57bdec589dN14bc0c6669395388N1532ef1cd44d1903N155069cf95f0504aN1565a3849e500705N159d017c662f890bN15d04a28253cc745N162fe5cca90fdeddN163c01b0f1ffe7a1N1651d2eada91562cN1659488737053894N169b84c95de5ae7cN16c82ccd2ea784a4N172036e0843057bbN173203642e345aeeN18078de1ba597381N180e9a5de22ab4e5N181391c6da00d720N1862f01826ef98ffN18a1b2a46c704662N18bc63e17001b5eaN18e59c12c33749f0N18efe638b67fdcbfN1906c722b2f29d0aN192afb116fff72e6N199743764b108729N19db9d5b60c2a288N19e8c681a553ef8dN1a1d7f7f7806d58dN1a86e961747d14fbN1a901f3d3191afd2N1abe5d9f24794673N1affe988260b8143N1b3762fe96dc735eN1b88b5e4df827f84N1bc6001a03c6f786N1bc7c4d1f661a61cN1bcce8a32781bcaeN1bd53200ca210c66N1bedd911be2d46bbN1c5c2384eec23059N1c7a756aaff95d47N1c7f30f717b96b7eN1c97db1cca390e08N1d6ed37b7e657be9N1e4bf9cdca01c0c7N1e4e2e2fd5041b20N1e534224c4c445c4N1e937d5f577cc15dN1e984971e7ce21d2N1ea0a00bbab20c1aN1f098c8f27ee1306N1f1c0ffdf903beddN1f2ec30d62cd3ac7N1f4bf15e4c32ff80N1f6533c8136c8c35N1f7b251c16700664N1fe110a4d0240d59N201752990ecbd457N2028c0e48570421dN2079574fe2002de8N2085c6d7d5eabb14N20c278619a1dc0e9N2100bb0741846d9bN211a7a5e826ef9e6N214a1d799b149715N21596673559d0366N21612fbfcd0d95fdN218f1ed9a6d59506N21919a874bbc0a60N21abe3acf107af5dN21b34354f0d7506bN2231f568a4d67319N2286e6f5ded048e9N22901bd78211634dN229915fda630bb52N22a6c788b5fca485N22d6b79ae0eea43fN22e09ebe04fa2c26N2308eaf1853d8cb1N230ab89e2a09d3c6N2334f17901cb1871N2353fe22c6b8d3bfN23834f401ec02d20N23a586537a8b305fN23af2b4338e72a69N23dc35f89a635e2bN23e0e33da928b856N23eb700193faed9fN242323db425fa8eeN242e4442680ffdb7N244f961cbde2a6e2N24be6bf9b039b6acN24e5acb964395ed1N254242da2846d823N25ce9a70d9face3dN25dbd9b1cdf422d8N25e9ca0757c63aa4N2636b76e6885063cN2665da4b8c58bf02N267ae7a44c7c7fccN2683807e7b8f4c10N2697f60bbf44c2b9N26a71f5993b3db4aN26a7874634b88703N26d8a407883c356dN2715942f3baf23e6N27e59b8796644b25N285c2eba097383aaN2925b2c7504dc639N2941098a1f6b85e6N29b3d4c0ebdd300aN29bd0c9b64b548dbN2a8c2363ff25bd60N2a9d62e8b2f9103fN2b0812995df93b9fN2b564db397737903N2b637d015410eaadN2bbfd6a5a8c0907cN2bce51e3bff62b63N2bf346778d370442N2c72ace895cc2369N2c88d14e396b5199N2cc63af45d232922N2d291af56df0915bN2d6e680cf0a25d0fN2dd19fe91a68871aN2dddcb330c69150aN2e97bb0c245b49bdN2ec27f84ee2bc1bbN2f340358e8876b07N2fa2e7a248e10ce5N2fcd5e50ff28e4c5N2fd6c53f7eabdfeaN300acf9fa03dd941N303a0d124aad2cfaN308d16a99fa4fb9bN30d2807066282315N30e061861be7f870N314135dc0b1d4982N31a54c22483e55cbN31cbeb55b3c4c2c5N31ff9ba4dbf69b13N32360405108c2ce7N3242d18da95ed8eaN3242e4bbe7ddccc4N32609ae7bc68c8f3N32e5e7bcb2a717afN330b973d67d86cdeN3324a21d49662e6bN334744b597a3ac26N342d3df3291afaefN349f69313366873dN34c97ce0c984a6cfN353bab08414a9c3aN35779dcaa9e69e43N35ba50326a16288fN36108b0f027e2923N362ff37b6d281ab9N3638dafe06895d13N365c7e7be3ac4a10N36830a5656dd6374N36925a278aa0079bN36e44cca9fa69e52N373fe186c9142f8fN374c67a85cee79e6N37bdd37c99ada498N37d7ada8071c8187N3813ee9702b2c510N381a6810777499acN381e045a402fd156N3870a86e9600908aN387df6b825021117N38b23c7380e4958bN38b61e17f4f9b0b5N38b9c480b268bdabN38e46f302217bc06N39337543de0106a9N39366f8c2a48a03bN398cbf16041ea569N39ec7bbaaef5090fN3a083c1bdd17695cN3a1a81c6d37141ccN3a26717aa4f0f149N3a65762d082e0f0fN3b2608213ec57d0fN3b915e1f908124eaN3bbf0613b8209aa5N3bc0e06909b54552N3c50f960dc56ca7cN3c7033a1b859cf87N3ca81bb4497e82afN3cedf52619eb070eN3d705887c87616daN3d85f04fcaea6360N3e188a6932554428N3e59f0765890b892N3e8c368b58fe2aa7N3edf0d6618d6f390N3ee7fa1bab97b73bN3eea096612c6b7b4N3ef2b2d922abf68aN3f1b9cfb3dcf143dN3f3a54b6eb31d8b6N3f4e268a0c732f62N3f840a9c181ddc17N3fa55375bac4e814N3ff620df1db776a0"%lxh.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Ltac2 gd_tbl_AW_SMalloc3 () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.A_SM3_RA"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Unwind2.A_TP"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "Corelib.Numbers.BinNums.Z"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.option"; "Stdlib.Lists.List.nth_error"; "Stdlib.ZArith.BinInt.Z.to_nat"; "Corelib.Init.Datatypes.Some"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "ARUN_1.SMalloc3.sm3_regs"; "ARUN_1.A_SM3_FOUND"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Logic.not"; "ARUN_1.A_SM3_NONE"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.of_nat"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u8arr"; "Corelib.Init.Datatypes.length"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "ARUN_1.SMalloc3.scan3_post"; "ARUN_1.A_SM3_LOOP"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SMalloc.smalloc_statics"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C1"; "Stdlib.ZArith.BinInt.Z.sub"; "ARUN_1.SMalloc3.sm3_A_post"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_SMalloc.A_SMALLOC"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.fsk_frame"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_FakeDefs.shd"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.upd"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.BHeap.AW_Poison.poison_statics"; "ARUN_1.SMalloc3.sm3_found_post"; "ARUN_1.SMalloc3.smalloc3_post"].

Section ARUN_1. Context {hAR : arun}.
Definition A_SM3_RA : Z := 0x533bc.      (* [comment removed for export] *)
Definition A_SM3_LOOP : Z := 0x5342c.    (* [comment removed for export] *)
Definition A_SM3_NONE : Z := 0x53448.    (* [comment removed for export] *)
Definition A_SM3_FOUND : Z := 0x534a4.   (* [comment removed for export] *)

Section SMalloc3.
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
  Definition sm3_regs (SP FS : Z) (gp x5 t1 t2 a0 a2 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) : bvmap 5 word := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc3 ()) "(0.(1.&40.$2.)(1.&40.(3.O18.-20.))O16.(1.&40.$4.)O15.O14.O13.(1.&40.O18.)(1.&40.O17.)O12.(1.&40.(3.O17.+1000.))O11.(1.&40.(3.O17.+8000.))(1.&40.+7??.)O10.O?.O>.(1.&40.+14.)O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.O2.O1.)")
(* [comment removed for export] *).

  (* [comment removed for export] *)
  Definition scan3_post (SP FS : Z) (gp t1 t2 a6 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (fl : list byte) (m : mem) (r cur : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc3 ()) "Lms',$5.(6.(7.$8.Lr',$8.(7.$8.Lc,$8.(7.$8.Lpos,$8.(7.(9.&8.)Lb,(9.&8.)(:.(:.(;.=R3.)(<.R3.(=.+2.+40.)))(:.(>.$8.R2.(?.R3.+800.))(:.(>.(10.(9.&8.))(11.(9.&8.)O4.(12.R2.))(13.(9.&8.)R1.))(:.(>.$8.(14.&8.R1.)=)(>.$5.R5.(15.(16.O19.O18.O17.(1.&40.=)O16.O15.(1.&40.R4.)(1.&40.R3.)(1.&40.(3.(3.O18.+8000.)R2.))O14.(1.&40.R2.)O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.(1.&40.$17.)O5.(18.(9.&40.))O3.(19.$1:.)))))))))))(:.Pj,$8.P,(:.(;.=R1.)(<.R1.O2.))(7.(9.&8.)Lb,(9.&8.)(:.(>.(10.(9.&8.))(11.(9.&8.)O4.(12.(?.(3.O1.R3.)+800.)))(13.(9.&8.)R1.))(1;.(>.$8.(14.&8.R1.)=))))(7.(9.&40.)Lx5,(9.&40.)(7.(9.&40.)Lx12,(9.&40.)(7.(9.&40.)Lx15,(9.&40.)(7.(9.&40.)Lx17,(9.&40.)(>.$5.R5.(15.(16.O19.O18.O17.R4.O16.O15.(1.&40.=)R3.R2.O14.R1.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.)O6.(1.&40.$1<.)O5.(18.(9.&40.))O3.(19.$1:.)))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L11608399893.9L3579524304.1200000100?SS3cur1j1q2rr1D". (* [comment removed for export] *)
  Lemma scan3_shift : forall cur j, (((cur + 1) mod 2^64) + (j - 1)) mod 2048 = (cur + j) mod 2048.
  Proof.
    intros cur j. pose proof (Z.div_mod (cur + 1) (2^64) ltac:(lia)) as D.
    set (q := (cur + 1) / 2^64) in *. set (rr := (cur + 1) mod 2^64) in *.
    replace (cur + j) with ((rr + (j - 1)) + (q * (2^64 / 2048)) * 2048) by (change (2^64 / 2048) with 9007199254740992; lia).
    rewrite Z_mod_plus_full. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Local Ltac2 Set LiaOrc.tbl := fun () => "00?0?L12529075241.4 L13278302029.2 L16980495076.53L18941427511.49L23970772284.56L2625671488.7  L28925203287.44L29008555810.55L3396492593.5  L36364150030.53L59310648043.5 L60519880076.2 L6343387025.5  L64930759789.5 L8929160544.6  00000;00C00]00m01D01U03<03S03b04<04O04U04^04m05:S1r1j2Hj2NES3cur2PBS3hAR2nn1r3cur2FS2fl2Hn2PBS3hAR2nn1r2fl2HnS3hAR2nn1r3cur2fl2Hn2HrS2nn1r2Hn2Kr1j2HjS3hAR2AL2CS1r3cur2gp2x52t12t22a63x153x172s32s42s52s62s72s82s93s103s112t32t42t52t62SP2FS2fl1F2fc1m2Hn2HrS3hAR2nn1r3cur2fl2Hn2HrS2nn1r2Hn2Hr2KrS3hAR2nn1r3cur2FS2fl2Hn2PBS3cur2fl3FLL2PB3NTHS1r2HrS2nn1r2HnS2nn1r2Hn2Hr2KrS2nn1r3cur2Hn". (* [comment removed for export] *)
  Lemma scan3_loop : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc3 ()) "Pnn,$1=.Pr,$8.Pcur,$8.Pgp,(9.&40.)Px5,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Pa6,(9.&40.)Px15,(9.&40.)Px17,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.Pfl,(1>.(9.&8.))PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(10.(9.&8.))P,(>.$8.(20.R1=.)R1<.)P,(:.(;.+1.R1=.)(;.R1=.+800.))P,(:.(;.=R1=.)(<.R1=.(=.+2.+40.)))P,(21.$1:.R4.(3.R8.+8000.)R7.)P,(>.$8.(20.(22.(9.&8.)R8.))+800.)P,(23.VCS,(3.R:.+8000.)+800.)P,(;.+65?000.R;.)P,(;.(3.R<.+;09000.)(24.VhAR,))P,(25.$1:.R9.)(26.$1:.VAL,VCS,(27.R?.R>.R23.R21.R20.R1?.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.R<.R;.R=.R:.R25.R24.)(15.(16.R?.R>.R23.R22.R21.R20.(1.&40.R25.)(1.&40.R24.)R1>.R1?.R1=.R1<.R1;.R1:.R19.R18.R17.R16.R15.R14.R13.R12.R11.R10.)R<.(1.&40.$28.)R;.(18.(9.&40.))R:.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    induction nn as [|nn IH]; intros r cur gp x5 t1 t2 a6 x15 x17 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS fl F fc m
      Hn Hr Hc FLA FLL FLCS FS0 FS1 MI; [lia|].
    facts. unfold sm3_regs, A_SM3_LOOP, A_SM3_RA, A_TP in *.
    pose proof (Z.mod_pos_bound cur 2048 ltac:(lia)) as PB.
    destruct (nth_error fl (Z.to_nat (cur mod 2048))) as [b|] eqn:NTH; [| apply nth_error_None in NTH; exfalso; clear -NTH PB FLL; lia].
    pose proof (u8arr_read asegs m (FS + 32768) fl (cur mod 2048) b _ FLA NTH ltac:(clear -PB; lia) eq_refl) as RD.
    (* [comment removed for export] *)
    zstep. first [rewrite (land_2047 cur) | rewrite Z.land_comm, (land_2047 cur)].
    zstep. zstep. clear RD.
    zstep. if_cases Kb; zify_cond Kb.
    - cbv beta. pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
      rewrite ?Z.mod_small in Kb by (clear -BR; lia).
      replace (Z_to_bv 64 (bv_unsigned b)) with (Z_to_bv 64 0) by (rewrite Kb; reflexivity).
      apply evtA_done. left. exists r, cur, (cur mod 2048), b.
      split; [exact Hc|]. split; [reflexivity|]. split; [exact NTH|]. split; [exact Kb| reflexivity].
    - (* [comment removed for export] *)
      cbv beta in Kb. pose proof (bv_unsigned_in_range 8 b) as BR. change (bv_modulus 8) with 256 in BR.
      rewrite ?Z.mod_small in Kb by (clear -BR; lia).
      assert (NZ0 : exists b0 : byte, nth_error fl (Z.to_nat ((cur + 0) mod 2048)) = Some b0 /\ bv_unsigned b0 <> 0).
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
          destruct (ALL (j - 1) ltac:(clear -Hj NE; lia)) as (b1 & N1 & Z1). exists b1. rewrite <- (scan3_shift cur j). split; [exact N1| exact Z1].
      + apply evtA_done. right. split.
        * intros j Hj. replace j with 0 by (clear -Kr Hr Hn Hj; lia). exact NZ0.
        * unfold A_SM3_NONE. replace (r + -1) with 0 by (clear -Kr Hr Hn; lia). do 4 eexists. reflexivity.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition sm3_A_post (SP FS lo hint : Z) (ra gp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc3 ()) "Lms',$5.(7.P,(9.&40.)(10.(9.&8.))Lm1,P,(9.&40.)(10.(9.&8.))(:.(>.$5.R2.(15.(16.O1=.O1<.O18.O17.O16.O15.(1.&40.+800.)(1.&40.O1:.)(1.&40.(3.O1:.+7??.))(1.&40.(3.O1:.+800.))O12.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)O3.(1.&40.$28.)O2.(18.(9.&40.))R1.(19.$1:.)))(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.O1;.O1=.)(2=.(2;.$8.$8.)))O1.R1.)(:.(2>.$1:.O1.R1.)(:.(25.$1:.R1.)(:.(2?.$1:.R1.(3.O1=.-20.)(2:.$30.(31.O11.)(2:.$30.(31.O13.)(2:.$30.(31.O14.)(2:.$30.(31.O19.)(2=.$30.))))))(32.$1:.R1.O1;.(3.O1=.-20.))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L11330676608.7 L11923395103.4 L15151186337.0 L16143243576.5 L26238223716.5 L26680464573.65L27846297964.3 L29753927507.3 L38235734261.1 L3958017386.4  L3958017390.4  L41599022925.2 L59787711800.5 L9448615682.3  L9448615686.2  L9678154644.12 00000F00T00U00j01:01J01Q01\01`01a01b01i02>02?02G02oS3hAR2SP1T2lo2TH5LOIMGS3hAR2lo5LOIMGSS3hAR2FS2lo3FSH5LOIMGS2SP2lo2A'2n'2H'S3hAR2SP2lo1y2HyS2SP2loS2SP2lo3SPLS2loFFS2SP2loS3hAR2FS2lo3FSH5LOIMGFS2SP3SPHS3hAR2SP3BLK3CTX2lo2BH2CH5LOIMG2A'2n'2H'". (* [comment removed for export] *)
  Lemma sm3_A : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc3 ()) "Pra,(9.&40.)Pgp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.PBLK,$8.PT,$8.PCTX,$8.Plo,$8.Phint,$8.PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(10.(9.&8.))P,(:.(;.+1000.R8.)(6.(;.(3.R8.+1000.)+10000.)(;.+65?000.R8.)))P,(;.(3.R9.+1000.)(24.VhAR,))P,(;.+65?000.R8.)P,(;.(3.R9.+10000.)(24.VhAR,))P,(:.(;.+1000.R;.)(6.(;.(3.R;.+1000.)+10000.)(;.+65?000.R;.)))P,(;.(3.R<.+1000.)(24.VhAR,))P,(:.(;.+65?000.R?.)(6.(;.(3.R?.$33.)+7???7000.)(;.+10007???8000.R?.)))P,(;.(3.R10.$33.)(24.VhAR,))P,(:.(;.=R<.)(<.R<.(=.+2.+40.)))P,(34.R:.R12.R11.R10.R?.)P,(23.VCS,R12.+1000.)P,(23.VCS,R11.+10000.)P,(23.VCS,R13.+1000.)P,(7.(9.&40.)Ltb,(9.&40.)(7.(9.&40.)Lte,(9.&40.)(35.$1:.R10.(3.R16.+30.)(2:.$30.(31.R2.)(2:.$30.(31.R1.)(2=.$30.))))))P,(35.$1:.R?.(3.R17.+58.)(2:.$30.(31.(1.&40.+14.))(2:.$30.(36.(1.&8.=))(2=.$30.))))P,(2?.$1:.R10.(3.R18.+18.)(2:.$30.(31.(1.&40.R13.))(2=.$30.)))P,(23.VCS,R19.+1000.)P,(32.$1:.R12.R16.R1;.)P,(;.(24.VhAR,)R17.)P,(;.R18.(37.R1=.+=0.))P,(;.R1>.(=.+2.+3>.))P,(23.VCS,R1:.(37.R1?.R1:.))P,(25.$1:.R17.)(26.$1:.VAL,VCS,(38.R21.R20.R1<.R1;.R3>.R3=.R3<.R3;.R3:.R39.R38.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R1:.R19.R18.)(15.(0.R3>.(1.&40.R21.)R3=.(1.&40.$4.)R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.)R1:.(1.&40.(39.+3.))R19.(18.(9.&40.))R18.(19.$1:.)))")
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
    unfold A_TP in *; replace (ret_pc (Z_to_bv 64 0x533bc)) with (Z_to_bv 64 0x533bc) by (symmetry; apply ret_pc_even; [ clear; lia | reflexivity ]).
    assert (LO1 : forall A' n', A' + n' <= lo -> disjoint_from [(lo, SP + -32)] A' n') by (intros A' n' H'; cbn; clear -H'; lia).
    lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m _, FRl : rw_cells _ _ (SP + -32) _, TPl : ro_cells _ _ 6539920 _,
                        HDRl : ro_cells _ ?mx' (FS + 88) _, HCl : rw_cells _ ?mx'' (FS + 24) _ |- _ =>
      assert (FR1 : rw_cells asegs mA (SP + -32) [C8 s2; C8 s1; C8 s0; C8 ra])
        by (eapply rw_cells_transport; [exact FRl| exact MU1| exact WM1| cbn; clear; lia]);
      assert (TPFS' : ro_cells asegs mA 6539920 [C8 (Z_to_bv 64 FS)])
        by (eapply ro_cells_transport; [exact TPl| exact MU1| apply LO1; cbn; clear -LOIMG H; lia]);
      assert (HDR1 : ro_cells asegs mA (FS + 88) [C8 (Z_to_bv 64 20); C1 (Z_to_bv 8 0)])
        by (eapply ro_cells_transport; [exact HDRl| exact MU1| apply LO1; cbn; clear -LOIMG FSH; lia]);
      assert (HC1 : rw_cells asegs mA (FS + 24) [C8 (Z_to_bv 64 hint)])
        by (eapply rw_cells_transport; [exact HCl| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH; lia]);
      assert (MU2 : munch [(lo, SP)] m mA) by (lx_munch MUl MU1);
      pose proof (wmono_trans asegs _ _ _ WMl WM1) as WM2;
      clear MU1 WM1 ST MI TPFS HDR HC SS TT; lx_clear_mem mx; rename MU2 into MU; rename WM2 into WM; rename MI1 into MI; rename ST1 into ST
    end.
    (* [comment removed for export] *)
    lx_run (PLAN [0x5342c] [] 40%N).
    apply evtA_done. unfold sm3_A_post, sm3_regs, A_SM3_LOOP, A_SM3_RA, A_TP. exists lxm.
    lx_ands; [ lx_mseq | assumption | assumption | assumption | assumption | assumption ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Lemma sm3_none : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc3 ()) "Pra,(9.&40.)Pgp,(9.&40.)Px5,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Px12,(9.&40.)Px15,(9.&40.)Px17,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.Plo,$8.Phint,$8.PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(10.(9.&8.))Pm,P,(9.&40.)(10.(9.&8.))P,(:.(;.+65?000.R7.)(6.(;.(3.R7.$33.)+7???7000.)(;.+10007???8000.R7.)))P,(;.(3.R8.$33.)(24.VhAR,))P,(2?.$1:.R3.(3.R9.+18.)(2:.$30.(31.(1.&40.R7.))(2=.$30.)))P,(23.VCS,R:.+1000.)P,(2?.$1:.R5.(3.R<.-20.)(2:.$30.(31.R1:.)(2:.$30.(31.R1>.)(2:.$30.(31.R1?.)(2:.$30.(31.R24.)(2=.$30.))))))P,(32.$1:.R6.R;.(3.R=.-20.))P,(;.(24.VhAR,)R<.)P,(;.R=.(37.R?.+20.))P,(;.R10.(=.+2.+3>.))P,(23.VCS,R?.(37.R11.R?.))P,(29.(2:.(2;.$8.$8.)(2<.$8.$8.R10.R12.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.R11.+18.)(3.R11.+20.))(2=.(2;.$8.$8.))))R<.R;.)P,(2>.$1:.R=.R<.)P,(25.$1:.R=.)(26.$1:.VAL,VCS,Lms',$5.(7.P,(9.&40.)(10.(9.&8.))Lm',P,(9.&40.)(10.(9.&8.))(:.(>.$5.R2.(15.(0.R2?.(1.&40.R17.)R2>.(1.&40.$4.)R2=.R2<.R2;.R2:.R29.(1.&40.=)(1.&40.(3.R16.+1000.))R28.(1.&40.(3.R16.+8000.))(1.&40.+7??.)R27.(1.&40.(3.R14.+800.))R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R13.(3:.R2?.)R12.(18.(9.&40.))R1.(19.$1:.)))(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.R15.R17.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.R16.+18.)(3.R16.+20.))(2=.(2;.$8.$8.))))R11.R1.)(:.(2>.$1:.R11.R1.)(:.(25.$1:.R1.)(:.(2?.$1:.R1.(3.R16.+18.)(2:.$30.(31.(1.&40.(3.R14.+800.)))(2=.$30.)))(32.$1:.R1.R15.R17.)))))))(15.(16.R15.R14.R2<.R2;.R2:.R29.(1.&40.=)R26.R25.(1.&40.(3.R12.+800.))R24.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.R17.R16.)R11.(1.&40.$1<.)R10.(18.(9.&40.))R>.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp x5 t1 t2 s0 s1 x12 x15 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo hint F fc m0 m
      FSL FSH HC FCS FR ST LOIMG SPL SPH SCS MU WM MI.
    unfold kHighMemBeg, kFakeBytes, sm3_regs, A_SM3_NONE, A_SM3_RA, A_TP in *. lx_aceil.
    (* [comment removed for export] *)
    lx_run (PLAN [] [] 20%N). lx_post.
  Qed.

  Definition sm3_found_post (SP FS lo pos c : Z) (ra gp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (fl : list byte) (m0 : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc3 ()) "Lms',$5.(7.(9.&40.)Lx5,(9.&40.)(7.(9.&40.)Lx11,(9.&40.)(7.(9.&40.)Lx12,(9.&40.)(7.(9.&40.)Lx13,(9.&40.)(7.(9.&40.)Lx14,(9.&40.)(7.(9.&40.)Lx15,(9.&40.)(7.(9.&40.)Lx16,(9.&40.)(7.(9.&40.)Lx17,(9.&40.)(7.P,(9.&40.)(10.(9.&8.))Lm',P,(9.&40.)(10.(9.&8.))(7.(1>.(9.&8.))Lj1,(1>.(9.&8.))(7.(1>.(9.&8.))Lj2,(1>.(9.&8.))ZFB,$8.(3;.O1<.+3.O1:.)(:.(>.$5.R=.(15.(0.O18.(1.&40.O1=.)O17.(1.&40.$4.)R<.O16.O15.O14.O13.(1.&40.R1.)R;.R:.R9.R8.R7.R6.R5.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.)O4.(3:.O18.)O3.(18.(9.&40.))R4.(19.$1:.)))(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.O1;.O1=.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.O1<.+18.)(3.O1<.+20.))(2:.(2;.$8.$8.)(2<.$8.$8.(3.(3.O1<.+8000.)O1:.)(3.(3.(3.O1<.+8000.)O1:.)+1.))(2:.(2;.$8.$8.)(2<.$8.$8.R1.(3.R1.+200.))(2:.(2;.$8.$8.)(2<.$8.$8.(3<.R1.)(3.(3<.R1.)+40.))(2=.(2;.$8.$8.)))))))O1.R4.)(:.(2>.$1:.O1.R4.)(:.(25.$1:.R4.)(:.(2?.$1:.R4.(3.O1<.+18.)(2:.$30.(31.(1.&40.(3.O19.+1.)))(2=.$30.)))(:.(21.$1:.R4.(3.O1<.+8000.)(3=.(9.&8.)O2.(12.O1:.)(1.&8.+1.)))(:.(2?.$1:.R4.R1.(2:.$30.(3>.#18.R3.)(2:.$30.(31.(1.&40.O1=.))(2:.$30.(3>.#1=8.R2.)(2:.$30.(31.(1.&40.(3.(3.O1<.+8000.)O1:.)))(2=.$30.))))))(:.(2?.$1:.R4.(3<.R1.)(2:.$30.(3>.#40.(3?.(9.&8.)(1.&8.=)#40.))(2=.$30.)))(:.(40.R4.)(32.$1:.R4.O1;.O1=.)))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00T0@L10187340561.104L11343735747.3  L12378669435.2  L12381266366.102L13335596837.101L13335596837.102L14650188599.9  L1641455751.101 L17120848823.0  L18520647869.2  L21943567510.16 L24642758929.104L24973756177.104L25456994354.101L25458997615.103L27048764373.97 L29984749841.104L30075863093.2  L3129187939.104 L35842253073.104L38303561818.2  L38364278545.104L39188636933.0  L44706278166.104L45867630865.104L51469501667.104L51489812398.73 L53830988561.104L54923320920.3  L54961663500.97 L55204150092.1  L55588686165.0  L57794683085.104L62746513610.104L65271643703.0  L8618464589.2   00000T00`00h01<01`02D02g03A03B03C04604Z05>05f06N06`07D07L07M08108908]08^09Y0:=0:T0;30;W0;b0<40<80<90<d0=c0=d0=lS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S2FS3pos3DFSS2FS3posS3hAR2FS3pos1c2fl2FBS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos2FB3FSL3FSH3HFB3DFS3FBRS3hAR2SP2FS2lo3pos1c2fl2FBSFS3hAR2SP2FS2lo3pos2FB5LOIMG2PB3FBR2SR4FSL02A'2n'2H'S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB3FSH2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB3FSH2Hc3HFB3FBR4FSL0S3hAR2FS3pos2fl2PBS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S2FS3posFS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S2FS3posS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0SS3hAR2FS3pos1c2fl2FB3FSA2Hc2HP3HFB3DFS3FBR2SR3FBA4FSL04FSL1S3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S3hAR2FS3pos1c2fl2FB2PBS3hAR2SP2FS2lo3pos1c2fl2FB1y2HyS3hAR2FS3pos1c2fl2FB2Hc3HFB3FBR4FSL0S2FS3pos2PBS3hAR2FS3pos2fl2PBS2FBSS3hAR2FS3pos1c2fl2FB2Hc2HP3HFB3DFS3FBR4FSL0S3hAR2SP2FS2lo3pos1c2fl2FB3FSH2Hc2HP5LOIMG3SPL3HFB3DFS3FBR4FSL0SS3pos2PB". (* [comment removed for export] *)
  Lemma sm3_found : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc3 ()) "Pra,(9.&40.)Pgp,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa6,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.Plo,$8.Ppos,$8.Pc,$8.Pr',$8.Ph0,(9.&40.)Pfl,(1>.(9.&8.))Pjunk,(1>.(9.&8.))Psj,(1>.(9.&8.))PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm0,P,(9.&40.)(10.(9.&8.))Pm,P,(9.&40.)(10.(9.&8.))ZFB,$8.(3;.R=.+3.R;.)P,(:.(;.+65?000.R>.)(6.(;.(3.R>.$33.)+7???7000.)(;.+10007???8000.R>.)))P,(;.(3.R?.$33.)(24.VhAR,))P,(>.$8.(?.R10.+1000.)=)P,(:.(;.=R>.)(<.R>.(=.+2.+40.)))P,(>.$8.R10.(?.R?.+800.))P,(2?.$1:.R7.(3.R13.+18.)(2:.$30.(31.R>.)(2=.$30.)))P,(21.$1:.R8.(3.R14.+8000.)R>.)P,(>.$8.(20.(22.(9.&8.)R?.))+800.)P,(2?.$1:.R:.R9.(2:.$30.(3>.#200.R?.)(2=.$30.)))P,(2?.$1:.R;.(3<.R:.)(2:.$30.(3>.#40.R?.)(2=.$30.)))P,(23.VCS,R18.$33.)P,(40.R=.)P,(2?.$1:.R>.(3.R1;.-20.)(2:.$30.(31.R29.)(2:.$30.(31.R2;.)(2:.$30.(31.R2<.)(2:.$30.(31.R30.)(2=.$30.))))))P,(32.$1:.R?.R1:.(3.R1<.-20.))P,(;.(24.VhAR,)R1;.)P,(;.R1<.(37.R1>.+20.))P,(;.R1?.(=.+2.+3>.))P,(23.VCS,R1>.(37.R20.R1>.))P,(29.(2:.(2;.$8.$8.)(2<.$8.$8.R1?.R21.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.R20.+18.)(3.R20.+20.))(2:.(2;.$8.$8.)(2<.$8.$8.(3.(3.R20.+8000.)R1>.)(3.(3.(3.R20.+8000.)R1>.)+1.))(2:.(2;.$8.$8.)(2<.$8.$8.R13.(3.R13.+200.))(2:.(2;.$8.$8.)(2<.$8.$8.(3<.R13.)(3.(3<.R13.)+40.))(2=.(2;.$8.$8.)))))))R15.R14.)P,(2>.$1:.R16.R15.)P,(25.$1:.R16.)(26.$1:.VAL,VCS,(41.R24.R23.R22.R21.R20.R39.R38.R37.R36.R35.R34.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R1:.R19.R1=.R18.)(15.(16.R24.R23.R38.(1.&40.=)R37.R36.(1.&40.R1?.)(1.&40.R20.)(1.&40.(3.(3.R23.+8000.)R21.))R33.(1.&40.R21.)R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.)R1:.(1.&40.$17.)R19.(18.(9.&40.))R17.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t1 t2 s0 s1 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo pos c r' h0 fl junk sj F fc m0 m FB
      FSL FSH FSA Hc HP HC FLA FLL FRM FSHD FCS PS FR ST LOIMG SPL SPH SCS MU WM MI.
    unfold kHighMemBeg, kFakeBytes, sm3_regs, A_SM3_FOUND, A_SM3_RA, A_TP in *.
    assert (HFB0 : FB = fsk_frame FS 3 pos) by reflexivity. clearbody FB. unfold shd in *.
    assert (HFB : FB = FS + 36864 + 3145728 + pos * 512) by (rewrite HFB0; unfold fsk_frame; clear; lia).
    pose proof (Z.mod_pos_bound c 2048 ltac:(clear; lia)) as PB. rewrite <- HP in PB.
    pose proof (Z.div_mod FS 4096 ltac:(clear; lia)) as DFS. rewrite FSA, Z.add_0_r in DFS.
    assert (FB8 : FB = (FS / 4096 * 512 + 4608 + 393216 + pos * 64) * 8) by (rewrite HFB; clear -DFS; lia).
    assert (FBD : Z.shiftr FB 3 = FS / 4096 * 512 + 4608 + 393216 + pos * 64) by (rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; rewrite FB8, Z.div_mul; [reflexivity| clear; lia]).
    assert (FBR : FS + 36864 <= FB /\ FB + 512 <= FS + 36864 + 6 * 2^20) by (rewrite HFB; clear -PB; lia).
    assert (SR : 0x80000000 <= 2147450880 + Z.shiftr FB 3 /\ 2147450880 + Z.shiftr FB 3 + 64 <= 0x10007fff8000) by (rewrite FBD; clear -FBR FSL FSH DFS HFB; lia).
    assert (FBA : FB mod 8 = 0) by (rewrite FB8; apply Z_mod_mult).
    clear FB8 FBD.
    (* [comment removed for export] *)
    lx_hide MU. lx_hide WM.
    pose proof (munch_refl [(lo, SP); (FS + 24, FS + 32); (FS + 32768 + pos, FS + 32768 + pos + 1); (FB, FB + 512); (2147450880 + Z.shiftr FB 3, 2147450880 + Z.shiftr FB 3 + 64)] m) as MUS.
    pose proof (wmono_refl asegs m) as WMS.
    flat constr:(PS) 10%nat. intros _ GSB SBC GMB MB GME ME GHE HE _.
    unfold A_GOT_SB, A_SBCELL, A_GOT_MIDBEG, A_MIDBEG, A_GOT_MIDEND, A_MIDEND, A_GOT_HIGHEND, A_HIGHEND in GSB, SBC, GMB, MB, GME, ME, GHE, HE.
    lx_hide PS. lx_aceil. flat constr:(FSL) 2%nat. flclear FSL. intros FSL0 FSL1. flat constr:(FLA) 2%nat. flclear FLA. intros FLAb FLAw.
    (* [comment removed for export] *)
    lx_run (PLAN [0x534b4] [] 10%N).
    (* [comment removed for export] *)
    lazymatch goal with FLAl : bytes_at _ ?mx (FS + 32768) fl, WMl : wmono _ m _ |- _ =>
      pose proof (conj FLAl (wr_at_transport _ _ _ _ _ FLAw WMl) : u8arr asegs mx (FS + 32768) fl) as FLAx; clear FLAl FLAb end.
    pose proof (u8arr_store_ok asegs _ (FS + 32768) fl pos _ FLAx ltac:(rewrite FLL; clear -PB; lia) eq_refl) as SOK.
    zstep. change (le1 (Z_to_bv 64 1)) with [Z_to_bv 8 1].
    lazymatch goal with |- _ (MS _ _ _ _ _ (write_to_mem ?mx ?a ?bs) _) =>
      pose proof (u8arr_write asegs mx (FS + 32768) fl pos (Z_to_bv 8 1) FLAx ltac:(rewrite FLL; clear -PB; lia)) as FLA'
    end.
    store_done. try clear FLAx. try clear SOK.
    flat constr:(FLA') 2%nat. flclear FLA'. intros FLAb2 FLAw2.
    assert (FLz : Z.of_nat (length (upd fl (Z.to_nat pos) (Z_to_bv 8 1))) = 2048) by (rewrite upd_length; exact FLL).
    (* [comment removed for export] *)
    lx_run (PLAN [0x534d4] [] 20%N).
    repeat match goal with |- context [Z_to_bv 64 (?a + ?b)] =>
      lazymatch b with context [pos] => replace (a + b) with FB by (rewrite HFB; clear; lia) end end.
    (* [comment removed for export] *)
    destruct FSL1 as [FSLO|FSHI]; lx_run (PLAN [] [] 90%N); lx_unhide;
      lazymatch goal with MUl : munch _ m ?mx, WMl : wmono _ m ?mx', FLl : bytes_at _ ?mx'' (FS + 32768) _ |- _ =>
        apply evtA_done; unfold sm3_found_post; cbv zeta; rewrite <- HFB0; unfold shd;
        lx_exs; lx_ands;
        [ lx_mseq
        | eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MUl]; lx_subfp]
        | exact (wmono_trans asegs _ _ _ WM WMl)
        | assumption | assumption
        | split; [exact FLl| rewrite upd_length; exact (wr_at_transport _ _ _ _ _ FLAw WMl)]
        | match goal with K : rw_cells _ _ FB [_; _; _; C8 (Z_to_bv 64 ?e)] |- _ => replace e with (FS + 32768 + pos) in K by (clear; lia); exact K end
        | replace (2147450880 + Z.shiftr FB 3) with (Z.shiftr FB 3 + 2147450880) by (clear; lia);
          eapply rw_cells_reshape; [eassumption| cbn; split; [reflexivity| exact I] | vm_compute; reflexivity]
        | eapply (poison_statics_transport _ _ _ PS MUl); intros A' n' H'; cbn; clear -H' LOIMG SPL FSL0 FBR SR PB H; lia
        | assumption ] end.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Definition smalloc3_post (SP FS BLK T CTX lo hint : Z) (fl : list byte)
      (ra gp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc3 ()) "Lms',$5.(7.(9.&40.)Lx5,(9.&40.)(7.(9.&40.)Lx11,(9.&40.)(7.(9.&40.)Lx12,(9.&40.)(7.(9.&40.)Lx13,(9.&40.)(7.(9.&40.)Lx14,(9.&40.)(7.(9.&40.)Lx15,(9.&40.)(7.(9.&40.)Lx16,(9.&40.)(7.(9.&40.)Lx17,(9.&40.)(7.P,(9.&40.)(10.(9.&8.))Lm',P,(9.&40.)(10.(9.&8.))(7.$8.Lr,$8.(:.(>.$5.R;.(15.(0.O17.(1.&40.O1?.)O16.(1.&40.$4.)R:.O15.O14.O13.O12.(1.&40.R1.)R9.R8.R7.R6.R5.R4.R3.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.)O3.(3:.O17.)O2.(18.(9.&40.))R2.(19.$1:.)))(:.(2>.$1:.O1.R2.)(:.(25.$1:.R2.)(:.(32.$1:.R2.O1:.O1?.)(:.(34.R2.O1>.O1=.O1<.O1;.)(:.(40.R2.)(7.$8.Lpos,$8.(7.$8.Lc,$8.(7.(9.&8.)Lb,(9.&8.)(7.(1>.(9.&8.))Lj1,(1>.(9.&8.))(7.(1>.(9.&8.))Lj2,(1>.(9.&8.))ZFB,$8.(3;.O1>.+3.R5.)(:.(>.$8.R7.R1.)(:.(:.(;.=R5.)(<.R5.(=.+2.+40.)))(:.(>.$8.R6.(?.R5.+800.))(:.(>.(10.(9.&8.))(11.(9.&8.)O18.(12.R6.))(13.(9.&8.)R4.))(:.(>.$8.(14.&8.R4.)=)(:.(29.(2:.(2;.$8.$8.)(2<.$8.$8.O1:.O1?.)(2:.(2;.$8.$8.)(2<.$8.$8.(3.O1>.+18.)(3.O1>.+20.))(2:.(2;.$8.$8.)(2<.$8.$8.(3.(3.O1>.+8000.)R6.)(3.(3.(3.O1>.+8000.)R6.)+1.))(2:.(2;.$8.$8.)(2<.$8.$8.R1.(3.R1.+200.))(2:.(2;.$8.$8.)(2<.$8.$8.(3<.R1.)(3.(3<.R1.)+40.))(2=.(2;.$8.$8.)))))))O1.R8.)(:.(2?.$1:.R8.(3.O1>.+18.)(2:.$30.(31.(1.&40.(3.R5.+1.)))(2=.$30.)))(:.(21.$1:.R8.(3.O1>.+8000.)(3=.(9.&8.)O18.(12.R6.)(1.&8.+1.)))(:.(2?.$1:.R8.R1.(2:.$30.(3>.#18.R3.)(2:.$30.(31.(1.&40.O1?.))(2:.$30.(3>.#1=8.R2.)(2:.$30.(31.(1.&40.(3.(3.O1>.+8000.)R6.)))(2=.$30.))))))(2?.$1:.R8.(3<.R1.)(2:.$30.(3>.#40.(3?.(9.&8.)(1.&8.=)#40.))(2=.$30.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

  Local Ltac2 Set LiaOrc.tbl := fun () => "00L0?L14650220848.7 L16648947209.1 L17120848823.0 L2106043955.7  L21943567510.23L222370686.1   L226564034.2   L22706556426.7 L2416881682.3  L25336979675.2 L25640760266.1 L27157704107.5 L30075863093.2 L32165929634.0 L36518867962.2 L39188636933.0 L45051584734.1 L46284349053.3 L47128140407.9 L52172457863.2 L55588686165.0 L59785778328.5 L62083074719.1 L63489361093.10L63489361093.6 L65271643703.0 L8618464589.2  L9678154644.5  00000M00Q00R00m02E02F02O02e03003103503K03S03T03]03^03b03n04R04S04T04j04n05S05j05k06306CS3hAR2FS4FSL'4FSH'3pos2PB3DFSS2FSSS3hAR2FS2lo5LOIMG3pos2FB2SRS3hAR2SP2FS3BLK3CTX2lo2BH2CH3BHI3CHI4SEP14SEP25LOIMG4FSL'4FSH'3pos2PB2FB3HFB2SR2A'2n'2H'FS2FS4FSL'S2SP2FS2lo3pos2FB1y2HyS2SP2lo3SPLFS2FSS3hAR2FS2lo5LOIMG4FSH'S2FS3posSS4hint2i0SS2FSS2FS3pos3DFSS3hAR2FS2lo5LOIMG4FSH'3pos2PB2FB3HFBFSS3hAR2FS2lo5LOIMG4FSH'S2FSS3hAR3BLK3CTX2lo2BH2CH5LOIMG2A'2n'2H'S3hAR2lo5LOIMG2A'2n'2H'SS3pos2PBS2SP2lo2A'2n'2H'". (* [comment removed for export] *)
  Lemma smalloc3_spec : ltac2:(CDefT.buildp (gd_tbl_AW_SMalloc3 ()) "Pra,(9.&40.)Pgp,(9.&40.)Pt0,(9.&40.)Pt1,(9.&40.)Pt2,(9.&40.)Ps0,(9.&40.)Ps1,(9.&40.)Pa0,(9.&40.)Pa1,(9.&40.)Pa2,(9.&40.)Pa3,(9.&40.)Pa4,(9.&40.)Pa5,(9.&40.)Pa6,(9.&40.)Pa7,(9.&40.)Ps2,(9.&40.)Ps3,(9.&40.)Ps4,(9.&40.)Ps5,(9.&40.)Ps6,(9.&40.)Ps7,(9.&40.)Ps8,(9.&40.)Ps9,(9.&40.)Ps10,(9.&40.)Ps11,(9.&40.)Pt3,(9.&40.)Pt4,(9.&40.)Pt5,(9.&40.)Pt6,(9.&40.)PSP,$8.PFS,$8.PBLK,$8.PT,$8.PCTX,$8.Plo,$8.Phint,$8.Pfl,(1>.(9.&8.))PF,(1?.&5.(9.&40.))Pfc,(9.&20.)Pm,P,(9.&40.)(10.(9.&8.))P,(:.(;.+1000.R9.)(6.(;.(3.R9.+1000.)+10000.)(;.+65?000.R9.)))P,(;.(3.R:.+1000.)(24.VhAR,))P,(;.+65?000.R9.)P,(;.(3.R:.+10000.)(24.VhAR,))P,(:.(;.+1000.R<.)(6.(;.(3.R<.+1000.)+10000.)(;.+65?000.R<.)))P,(;.(3.R=.+1000.)(24.VhAR,))P,(:.(;.+65?000.R10.)(6.(;.(3.R10.$33.)+7???7000.)(;.+10007???8000.R10.)))P,(;.(3.R11.$33.)(24.VhAR,))P,(>.$8.(?.R12.+1000.)=)P,(:.(;.=R>.)(<.R>.(=.+2.+40.)))P,(:.(:.(;.+1000.R13.)(6.(;.(3.R13.+1000.)+10000.)(;.+65?000.R13.)))(6.(;.(3.R13.+1000.)+7???7000.)(;.+10007???8000.R13.)))P,(:.(;.+65?000.R12.)(6.(;.(3.R12.+10000.)+7???7000.)(;.+10007???8000.R12.)))P,(6.(;.(3.R13.+10000.)R16.)(;.(3.R16.$33.)R13.))P,(6.(;.(3.R16.+1000.)R17.)(;.(3.R17.$33.)R16.))P,(34.R?.R18.R17.R16.R15.)P,(40.R10.)P,(23.VCS,R19.+1000.)P,(23.VCS,R18.+10000.)P,(23.VCS,R1:.+1000.)P,(23.VCS,R1=.$33.)P,(7.(9.&40.)Ltb,(9.&40.)(7.(9.&40.)Lte,(9.&40.)(35.$1:.R17.(3.R1>.+30.)(2:.$30.(31.R2.)(2:.$30.(31.R1.)(2=.$30.))))))P,(35.$1:.R16.(3.R1?.+58.)(2:.$30.(31.(1.&40.+14.))(2:.$30.(36.(1.&8.=))(2=.$30.))))P,(2?.$1:.R17.(3.R20.+18.)(2:.$30.(31.(1.&40.R1;.))(2=.$30.)))P,(21.$1:.R18.(3.R21.+8000.)R1;.)P,(>.$8.(20.(22.(9.&8.)R1<.))+800.)P,Pi,$8.Pb,(9.&8.)P,(:.(;.=R2.)(<.R2.+800.))P,(>.(10.(9.&8.))(11.(9.&8.)R20.(12.R3.))(13.(9.&8.)R2.))P,(>.$8.(14.&8.R3.)=)(7.(1>.(9.&8.))Ljunk,(1>.(9.&8.))(7.(1>.(9.&8.))Lsj,(1>.(9.&8.))(:.(2?.$1:.R21.(3;.R2:.+3.R7.)(2:.$30.(3>.#200.R2.)(2=.$30.)))(2?.$1:.R21.(3<.(3;.R2:.+3.R7.))(2:.$30.(3>.#40.R1.)(2=.$30.))))))P,(7.$8.Li0,$8.(7.(9.&8.)Lb0,(9.&8.)(:.(:.(;.=R2.)(<.R2.+800.))(:.(>.(10.(9.&8.))(11.(9.&8.)R20.(12.R2.))(13.(9.&8.)R1.))(>.$8.(14.&8.R1.)=)))))P,(32.$1:.R1<.R21.R26.)P,(;.(24.VhAR,)R22.)P,(;.R23.(37.R28.+=0.))P,(;.R29.(=.+2.+3>.))P,(23.VCS,R25.(37.R2:.R25.))P,(25.$1:.R21.)(26.$1:.VAL,VCS,(42.R2<.R2;.R2:.R29.R28.R27.R26.R25.R49.R48.R46.R45.R44.R43.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R24.R23.R22.)(15.(0.R49.(1.&40.R2<.)R48.(1.&40.$4.)R47.R46.R45.R44.R43.R42.R41.R40.R3?.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.)R24.(1.&40.(39.+3.))R23.(18.(9.&40.))R22.(19.$1:.)))")
(* [comment removed for export] *).
  Proof.
    intros ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint fl F fc m
      BL BH CL CH TL TH FSL FSH FSA HNT BHI CHI SEP1 SEP2 SS PS BCS CCS TCS FCS TT HDR HC FLA FLL HFR FREE ST LOIMG SPL SPH SCS MI.
    pose proof FSL as FSL'. pose proof FSH as FSH'. unfold kHighMemBeg, kFakeBytes in FSL', FSH', BHI, CHI, SEP1, SEP2.
    eapply evtA_cut.
    { eapply (sm3_A ra gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS BLK T CTX lo hint F fc m);
        first [eassumption | eapply crange_sub; [exact FCS| clear; lia| unfold kFakeBytes; clear; lia]]. }
    cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FR1 & ST1).
    assert (LO1 : forall A' n', A' + n' <= lo -> disjoint_from [(lo, SP)] A' n') by (intros A' n' H'; cbn; clear -H'; lia).
    assert (FLA1 : u8arr asegs m1 (FS + 32768) fl)
      by (eapply u8arr_transport; [exact FLA| exact MU1| exact WM1| apply LO1; rewrite <- (Nat2Z.id (length fl)), FLL; clear -LOIMG FSH'; lia]).
    assert (HC1 : rw_cells asegs m1 (FS + 24) [C8 (Z_to_bv 64 hint)])
      by (eapply rw_cells_transport; [exact HC| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH'; lia]).
    assert (SS1 : smalloc_statics m1 FS BLK T CTX)
      by (eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MU1); intros A' n' H'; apply LO1; clear -H' LOIMG CH BH; lia).
    assert (PS1 : poison_statics m1) by (eapply (poison_statics_transport _ _ _ PS MU1); intros A' n' H'; apply LO1; clear -H' LOIMG; lia).
    eapply evtA_cut.
    { eapply (scan3_loop (Z.to_nat 2048) 2048 hint); first [reflexivity | exact HNT | exact FLA1 | exact FLL | exact MI1 | clear; lia | idtac];
        [eapply crange_sub; [exact FCS| clear; lia| unfold kFakeBytes; clear; lia] | clear -FSL'; lia | exact FSH']. }
    cbv beta. intros ms2 [(r' & c & pos & b & Hc & HP & NTH & Hb & ->) | (ALL & x5 & x12 & x15 & x17 & ->)].
    - assert (PB : 0 <= pos < 2048) by (rewrite HP; apply Z.mod_pos_bound; clear; lia).
      destruct (HFR pos b ltac:(clear -PB; lia) NTH Hb) as (junk & sj & FRM & FSHD).
      set (FB := fsk_frame FS 3 pos) in *.
      assert (HFB : FB = FS + 36864 + 3145728 + pos * 512) by (subst FB; unfold fsk_frame; clear; lia).
      pose proof (Z.div_mod FS 4096 ltac:(clear; lia)) as DFS. rewrite FSA, Z.add_0_r in DFS.
      assert (FBD : Z.shiftr FB 3 = FS / 4096 * 512 + 4608 + 393216 + pos * 64).
      { rewrite Z.shiftr_div_pow2 by (clear; lia). change (2^3) with 8.
        replace FB with ((FS / 4096 * 512 + 4608 + 393216 + pos * 64) * 8) by (rewrite HFB; clear -DFS; lia). rewrite Z.div_mul; [reflexivity| clear; lia]. }
      assert (SR : 0x80000000 <= shd FB /\ shd FB + 64 <= 0x10007fff8000) by (unfold shd; rewrite FBD; clear -PB FSL' FSH' DFS; lia).
      assert (FRM1 : rw_cells asegs m1 FB [CB 512 junk])
        by (eapply rw_cells_transport; [exact FRM| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG FSH' HFB PB; lia]).
      assert (FSHD1 : rw_cells asegs m1 (shd FB) [CB 64 sj])
        by (eapply rw_cells_transport; [exact FSHD| exact MU1| exact WM1| apply LO1; cbn; clear -LOIMG SR; lia]).
      assert (MUW : munch [(lo, SP); (FS + 24, FS + 32); (FS + 32768 + pos, FS + 32768 + pos + 1); (FB, FB + 512); (shd FB, shd FB + 64)] m m1).
      { eapply munch_weaken; [| exact MU1]. unfold sub_fp; cbn [outside]. clear. intros y Hy. lia. }
      eapply evtA_mono.
      { eapply (sm3_found ra gp t1 t2 s0 s1 _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SP FS lo pos c r' _ fl junk sj F fc m m1);
          first [sassumption | cassumption | exact FSL | exact FSH | exact FSA | exact Hc | exact HP | exact HC1 | exact FLA1 | exact FLL | exact FRM1 | exact FSHD1
                | exact FCS | exact PS1 | exact FR1 | exact ST1 | exact LOIMG | exact SCS | exact MUW | exact WM1 | exact MI1
                | clear -SPL; lia | clear -SPH; lia]. }
      cbv beta. intros ms3 (x5 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & m3 & j1 & j2 & -> & MU3 & WM3 & MI3 & HC3 & FLA3 & FRM3 & FSH3 & PS3 & ST3).
      unfold smalloc3_post. exists x5, x11, x12, x13, x14, x15, x16, x17, m3, FB.
      split; [reflexivity|]. split; [exact WM3|]. split; [exact MI3|]. split; [exact ST3|].
      split. { eapply (smalloc_statics_transport _ _ _ _ _ _ _ SS MU3). intros A' n' H'. cbn. change (fsk_frame FS 3 pos) with FB.
               clear -H' LOIMG CH BH FSL' FSH' HFB SR PB BHI CHI SEP1 SEP2. lia. }
      split; [exact PS3|].
      exists pos, c, b, j1, j2. cbv zeta.
      split; [reflexivity|]. split; [exact Hc|]. split; [exact HP|]. split; [exact NTH|]. split; [exact Hb|].
      split; [exact MU3|]. split; [exact HC3|]. split; [exact FLA3|]. split; [exact FRM3| exact FSH3].
    - (* [comment removed for export] *)
      exfalso. flat constr:(FREE) 5%nat. flclear FREE. intros i0 b0 Hi0 N0 Z0.
      destruct (ALL ((i0 - hint) mod 2048) ltac:(apply Z.mod_pos_bound; clear; lia)) as (b1 & N1 & Z1).
      rewrite Zplus_mod_idemp_r in N1. replace (hint + (i0 - hint)) with i0 in N1 by (clear; lia).
      rewrite Z.mod_small in N1 by exact Hi0. rewrite N0 in N1. injection N1 as <-. exact (Z1 Z0).
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End SMalloc3.

End ARUN_1.
